import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.kotlin.jvm") version "2.0.0-Beta2"
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
    implementation("com.github.ajalt.clikt:clikt:3.5.2")
    implementation("org.yaml:snakeyaml:2.2")

    // graph drawing
    implementation("org.eclipse.elk:org.eclipse.elk.core:0.8.1")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.common:0.8.1")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.layered:0.8.1")

    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.10.1")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.10.1")
    testImplementation("org.junit.jupiter:junit-jupiter-params:5.10.1")

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

tasks.getByName("compileTestKotlin").dependsOn("generateTestGrammarSource")

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useJUnitJupiter("5.10.1")
        }
    }
}

application {
    mainClass.set("cagen.AppKt")
}
