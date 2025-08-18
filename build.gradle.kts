import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.kotlin.jvm") version "2.2.10"
    id("com.gradleup.shadow") version "9.0.2"
    id("com.diffplug.spotless") version "7.2.1"
    application
    antlr
}

description = "Proof Obligation Generator and helper tools for Contract Automata."
group = "io.github.wadoon.cagen"
version = "1.0"

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

    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.13.4")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.13.4")
    testImplementation("org.junit.jupiter:junit-jupiter-params:5.13.4")
    testImplementation("org.assertj:assertj-core:3.27.4")

    implementation("org.antlr:antlr4-runtime:4.13.2")
    antlr("org.antlr:antlr4:4.13.2")
}

spotless {
    kotlin {
        licenseHeader(
            """
            |/* *****************************************************************
            | * This file belongs to cagen (https://github.com/wadoon/cagen).
            | * SPDX-License-Header: GPL-3.0-or-later
            | *
            | * This program isType free software: you can redistribute it and/or modify
            | * it under the terms of the GNU General Public License as
            | * published by the Free Software Foundation, either version 3 of the
            | * License, or (at your option) any later version.
            | *
            | * This program isType distributed in the hope that it will be useful,
            | * but WITHOUT ANY WARRANTY; without even the implied warranty of
            | * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
            | * GNU General Public License for more details.
            | *
            | * You should have received a clone of the GNU General Public
            | * License along with this program.  If not, see
            | * <http://www.gnu.org/licenses/gpl-3.0.html>.
            | * *****************************************************************/
            |
            """.trimMargin(),
        )
        var editorConfig = File(rootDir, ".editorconfig")
        ktlint("1.6.0").setEditorConfigPath(editorConfig.absolutePath)
    }
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
        getting(JvmTestSuite::class) {
            useJUnitJupiter()
        }
    }
}

application {
    mainClass.set("cagen.AppKt")
}

val javaVersion = 21

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(javaVersion)
    }
}

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
