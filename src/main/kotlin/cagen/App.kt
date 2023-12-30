package cagen

import cagen.code.CCodeUtils
import cagen.draw.Tikz
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import java.io.File
import kotlin.io.path.div
import kotlin.io.path.writeText

class Tool : CliktCommand() {
    val verbose by option().flag("--no-verbose")
    override fun run() {
        //echo("Verbose mode is ${if (verbose) "on" else "off"}")
    }
}

class DotCommmand : CliktCommand() {
    override fun run() {
        echo("executing")
    }
}

class TikzCommand : CliktCommand() {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val fragment by option().flag()

    override fun run() {
        val (sys, contracts) = ParserFacade.loadFile(inputFile)
        //val comps = ParserFacade.loadFile(inputFile)
        if (!fragment)
            Tikz.tikz_standalone(sys + contracts)
        else
            Tikz.tikz(sys + contracts)
    }
}

class ConstructCA : CliktCommand(name = "construct") {
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    val systemName by argument()
    override fun run() {
        val (sys, contracts) = ParserFacade.loadFile(inputFile)
        val system = sys.find { it.name == systemName }
            ?: error("The provided systemName can not be find in the given file $inputFile")

        ConstructCAFacade.construct(system)
    }
}


class ExtractCode : CliktCommand() {
    val outputFolder by option("-o", "--output").file().default(File("output"))
    val inputFile by argument("SYSTEM").file(mustExist = true, canBeDir = false, mustBeReadable = true)
    override fun run() {
        val (sys, contracts) = ParserFacade.loadFile(inputFile)
        println("Write to $outputFolder")
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

    override fun run() {
        val model = ParserFacade.loadFile(inputFile)
        val pos = createProofObligations(model)
        println("Proof Obligation found:")
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
    .subcommands(ExtractCode(), DotCommmand(), TikzCommand(), Verify(), ConstructCA())
    .main(args)
