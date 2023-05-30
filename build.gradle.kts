import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.kotlin.jvm") version "1.8.21"
    id("com.github.johnrengelman.shadow") version "7.1.2"
    application
    antlr
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
    //implementation("org.antlr:stringtemplate:4.0.2")
    implementation("com.github.ajalt.clikt:clikt:3.5.2")

    // graph drawing
    implementation("org.eclipse.elk:org.eclipse.elk.core:0.8.1")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.common:0.8.1")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.layered:0.8.1")


    implementation("io.kpeg:kpeg:0.1.2")

    implementation("org.antlr:antlr4-runtime:4.13.0")
    antlr("org.antlr:antlr4:4.13.0")
}

val compileJava by tasks.existing(JavaCompile::class)
val compileKotlin by tasks.existing(KotlinCompile::class)
val generateGrammarSource by tasks.existing(AntlrTask::class)

compileKotlin { dependsOn(generateGrammarSource) }

generateGrammarSource {
    this.arguments.add("-visitor")
    this.arguments.add("-package")
    this.arguments.add("cagen.parser")
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useKotlinTest()
        }
    }
}

application {
    mainClass.set("cagen.AppKt")
}
