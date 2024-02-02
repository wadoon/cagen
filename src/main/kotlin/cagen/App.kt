@file:Suppress("unused", "MemberVisibilityCanBePrivate")

package cagen

import cagen.Util.infoln
import cagen.code.CCodeUtils
import cagen.draw.Dot
import cagen.draw.TikzPrinter
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.findObject
import com.github.ajalt.clikt.core.findOrSetObject
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import java.io.File
import java.io.PrintWriter
import java.lang.System
import java.nio.file.StandardWatchEventKinds
import kotlin.io.path.div
import kotlin.io.path.writeText

object Util {
    private const val LOG_FORMAT = "[%5d] %s%s%s"
    private val startTime = System.currentTimeMillis()
    private const val ESC = 27.toChar()

    var verbose = false

    fun putln(s: String, colorOn: String = "", colorOff: String = "") =
        println(LOG_FORMAT.format((System.currentTimeMillis() - startTime), colorOn, s, colorOff))

    fun putln(s: String, color: Int) = putln(s, "$ESC[${color}m", "$ESC[0m")

    fun infoln(s: String) = putln(s)
    fun warnln(s: String) = putln(s, 32)
    fun errorln(s: String) = putln(s, 33)
}

class AppContext(verbose: Boolean, var version: String? = null, var variants: List<String> = listOf()) {
    init {
        Util.verbose = verbose
    }

    fun load(file: File): Model {
        val model = ParserFacade.loadFile(file)
        val vv = (version?.let { listOf(Version(it)) } ?: listOf()) +
                variants.map {
                    model.findVariant(it)
                        ?: error("Could not find variant $it. Check your `variants` definition in the given file")
                }
        if (vv.isNotEmpty())
            model.activateVersion(vv)
        return model
    }
}

class Tool : CliktCommand(allowMultipleSubcommands = true) {
    val verbose by option().flag("--no-verbose")
    val version by option("--version")
    val variants by option("--variant").multiple()

    val context by findOrSetObject { AppContext(verbose, version, variants) }

    override fun run() {}
}

class DotCommand : CliktCommand() {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val tempFile by option("-o", "--output").default(File.createTempFile("cagen", ".dot").toString())
    val watch by option().flag()
    val topLevelSystem by option("--tl", "--entry").required()

    val context by findObject<AppContext>()

    override fun run() {
        if (watch) watchMode()
        else {
            val dot = getDot()
            if (tempFile == "-")
                println(dot)
            else
                File(tempFile).writeText(dot)
        }
    }

    private fun watchMode() {
        val path = inputFile.toPath()
        val ws = path.fileSystem.newWatchService()
        val wd = path.register(ws, StandardWatchEventKinds.ENTRY_MODIFY)
        val outFile = File.createTempFile("cagen_", ".svg")
        ws.use {
            while (true) {
                val event = ws.poll()
                if (event == wd) {
                    triggerPipeline(outFile)
                }
            }
        }
    }

    private fun triggerPipeline(outFile: File) {
        val dot = getDot()
        File(tempFile).writeText(dot)
        val dotProcess = ProcessBuilder("dot", "-T", "svg", "-o", outFile.toString(), tempFile).start()
        val el = dotProcess.waitFor()
        if (el == 0) {
            ProcessBuilder("xdg-open", outFile.toString()).start()
        } else {
            dotProcess.errorStream.transferTo(System.out)
        }
    }

    private fun getDot(): String {
        val model = context!!.load(inputFile)
        val dot = Dot.asString {
            printDot(
                model.findSystemByName(topLevelSystem)
                    ?: error("Could not find system by name $topLevelSystem.")
            )
        }
        return dot
    }
}

class TikzCommand : CliktCommand() {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val fragment by option().flag()
    val output by option("-o", "--output").default("-")

    val context by findObject<AppContext>()

    override fun run() {
        val (sys, contracts) = context!!.load(inputFile)
        val s = if (!fragment)
            TikzPrinter.asString { tikz_standalone(sys + contracts) }
        else
            TikzPrinter.asString { tikz(sys + contracts) }
        if (output == "-")
            println(s)
        else
            File(output).writeText(s)
    }
}

class VVSlice : CliktCommand(
    name = "vvslice", help = """Slices a given system model given by the version and variants information. 
    |Use with an empty version or variants results into a pretty printed and identical system.""".trimMargin()
) {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val output by option("-o", "--output").default("-")

    val context by findObject<AppContext>()

    override fun run() {
        val model = context!!.load(inputFile)
        val result = PrettyPrinter.asString { pp(model) }
        if (output == "-")
            println(result)
        else
            File(output).writeText(result)
    }
}


class ConstructCA : CliktCommand(name = "construct") {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val systemName by argument()

    val context by findObject<AppContext>()

    override fun run() {
        val (sys, _) = context!!.load(inputFile)
        val system = sys.find { it.name == systemName }
            ?: error("The provided systemName can not be find in the given file $inputFile")
        val uc = ConstructCAFacade.construct(system)
        print(PrettyPrinter(PrintWriter(System.out)).pp(uc.contract))
    }
}


class ExtractCode : CliktCommand() {
    val outputFolder by option("-o", "--output").file().default(File("output"))
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val context by findObject<AppContext>()

    override fun run() {
        val (sys, contracts) = context!!.load(inputFile)
        infoln("Write to $outputFolder")
        outputFolder.mkdirs()
        sys.forEach {
            CCodeUtils.writeSystemCode(it, outputFolder.toPath())
        }

        contracts.forEach {
            CCodeUtils.writeContractAutomata(it, outputFolder.toPath())
        }
    }
}

class Verify : CliktCommand() {
    val outputFolder by option("-o", "--output").file().default(File("output"))
    val inputFile by argument("SYSTEM")
        .file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val context by findObject<AppContext>()

    override fun run() {
        val model = context!!.load(inputFile)
        val pos = createProofObligations(model)
        infoln("Proof Obligation found:")
        for (po in pos) {
            println("\t- ${po.name}")
        }

        val tasks = pos.flatMap { it.createFiles(outputFolder.toPath()) }

        (outputFolder.toPath() / "Makefile").writeText(
            buildString {
                tasks.forEach { (name, command) ->
                    appendLine("$name:")
                    appendLine("\t$command")
                }
            }
        )
    }
}


fun main(args: Array<String>) = Tool()
    .subcommands(ExtractCode(), DotCommand(), TikzCommand(), Verify(), ConstructCA(), VVSlice())
    .main(args)
