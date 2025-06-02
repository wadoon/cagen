import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.kotlin.jvm") version "2.1.21"
    id("com.github.johnrengelman.shadow") version "8.1.1"
    application
    antlr
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(platform("org.jetbrains.kotlin:kotlin-bom"))
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
    implementation("com.github.ajalt.clikt:clikt:5.0.3")
    implementation("org.yaml:snakeyaml:2.4")

    // graph drawing
    implementation("org.eclipse.elk:org.eclipse.elk.core:0.10.0")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.common:0.10.0")
    implementation("org.eclipse.elk:org.eclipse.elk.alg.layered:0.10.0")

    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.13.0")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.13.0")
    testImplementation("org.junit.jupiter:junit-jupiter-params:5.13.0")
    testImplementation("org.assertj:assertj-core:3.27.3")

    implementation("org.antlr:antlr4-runtime:4.13.2")
    antlr("org.antlr:antlr4:4.13.2")
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
            useJUnitJupiter("5.11.4")
        }
    }
}

application {
    mainClass.set("cagen.AppKt")
}

val javaVersion = 21

kotlin {
    jvmToolchain(javaVersion)
    compilerOptions {}
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(javaVersion))
    }
}
tasks.withType(JavaCompile::class) {
    options.release.set(javaVersion)
}
