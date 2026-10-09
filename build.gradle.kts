plugins {
    // Applied per-module; declared here (apply false) so the version is shared and the Android
    // Gradle Plugin is on the shared buildscript classpath (so modules can apply the KMP Android
    // library plugin). AGP 9 renamed the KMP library plugin to com.android.kotlin.multiplatform.library
    // (androidKmpLibrary); androidLibrary (com.android.library) is kept for any plain-Android consumer.
    alias(libs.plugins.kotlinMultiplatform) apply false
    alias(libs.plugins.androidLibrary) apply false
    alias(libs.plugins.androidKmpLibrary) apply false
}
