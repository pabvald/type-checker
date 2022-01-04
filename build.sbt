ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.7"

lazy val root = (project in file("."))
  .settings(
    name := "se-ws2122-assignment-03",
    idePackagePrefix := Some("de.uni_saarland.cs.se")
  ).
  dependsOn(cafeSat)

lazy val cafeSat = {
  val commit = "49e7c8954235001787ad14c8db3c60c36ec45cce"
  val githubLink = s"git://github.com/regb/cafesat.git#$commit"
  RootProject(uri(githubLink))
}

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
libraryDependencies += "org.scalatest" %% "scalatest-flatspec" % "3.2.10" % "test"
