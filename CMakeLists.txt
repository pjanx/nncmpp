cmake_minimum_required (VERSION 3.0)
project (nncmpp VERSION 2.0.0 LANGUAGES C)

# Moar warnings
if ("${CMAKE_C_COMPILER_ID}" MATCHES "GNU" OR CMAKE_COMPILER_IS_GNUCC)
	set (wdisabled "-Wno-unused-function")
	set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=gnu99 -Wall -Wextra ${wdisabled}")
endif ()

# For custom modules
set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/liberty/cmake)

# Collect important build toggles for our simple preprocessor
# (cpp(1) isn't part of POSIX, otherwise we could reuse config.h)
set (options)
macro (add_option variable help value)
	option (${ARGV})
	list (APPEND options "${variable}=$<BOOL:${${variable}}>")
endmacro ()

# Dependencies
find_package (Ncursesw REQUIRED)
find_package (PkgConfig REQUIRED)
find_package (Unistring REQUIRED)
pkg_check_modules (curl REQUIRED libcurl)

include (AddThreads)

find_package (Termo QUIET NO_MODULE)
add_option (USE_SYSTEM_TERMO
	"Don't compile our own termo library, use the system one" "${Termo_FOUND}")
if (USE_SYSTEM_TERMO)
	if (NOT Termo_FOUND)
		message (FATAL_ERROR "System termo library not found")
	endif ()
else ()
	# We don't want the library to install, but EXCLUDE_FROM_ALL ignores tests
	add_subdirectory (termo EXCLUDE_FROM_ALL)
	file (WRITE ${PROJECT_BINARY_DIR}/CTestCustom.cmake
		"execute_process (COMMAND ${CMAKE_COMMAND} --build termo)")

	# We don't have many good choices; this is a relatively clean approach
	# (other possibilities: setting a variable in the parent scope, using
	# a cache variable, writing a special config file with build paths in it
	# and including it here, or setting a custom property on the targets)
	get_directory_property (Termo_INCLUDE_DIRS
		DIRECTORY termo INCLUDE_DIRECTORIES)
	set (Termo_LIBRARIES termo-static)
endif ()

pkg_check_modules (fftw fftw3 fftw3f)
add_option (WITH_FFTW
	"Use FFTW to enable spectrum visualisation" "${fftw_FOUND}")
if (WITH_FFTW)
	if (NOT fftw_FOUND)
		message (FATAL_ERROR "FFTW not found")
	endif ()
	list (APPEND extra_libraries ${fftw_LIBRARIES})
endif ()

pkg_check_modules (libpulse libpulse)
add_option (WITH_PULSE
	"Enable PulseAudio sink volume control" "${libpulse_FOUND}")
if (WITH_PULSE)
	if (NOT libpulse_FOUND)
		message (FATAL_ERROR "libpulse not found")
	endif ()
	list (APPEND extra_libraries ${libpulse_LIBRARIES})
endif ()

pkg_check_modules (x11 x11 xrender xft fontconfig)
add_option (WITH_X11 "Build with X11 support" "${x11_FOUND}")
if (WITH_X11)
	if (NOT x11_FOUND)
		message (FATAL_ERROR "Some X11 libraries were not found")
	endif ()
	list (APPEND extra_libraries ${x11_LIBRARIES})
endif ()

include_directories (${Unistring_INCLUDE_DIRS}
	${Ncursesw_INCLUDE_DIRS} ${Termo_INCLUDE_DIRS} ${curl_INCLUDE_DIRS}
	${fftw_INCLUDE_DIRS} ${libpulse_INCLUDE_DIRS} ${x11_INCLUDE_DIRS})
link_directories (${curl_LIBRARY_DIRS}
	${fftw_LIBRARY_DIRS} ${libpulse_LIBRARY_DIRS} ${x11_LIBRARY_DIRS})

# Configuration
if ("${CMAKE_SYSTEM_NAME}" MATCHES "BSD")
	# Need this for SIGWINCH in FreeBSD and OpenBSD respectively;
	# our POSIX version macros make it undefined
	add_definitions (-D__BSD_VISIBLE=1 -D_BSD_SOURCE=1)
elseif (APPLE)
	add_definitions (-D_DARWIN_C_SOURCE)
endif ()

include (CheckFunctionExists)
set (CMAKE_REQUIRED_LIBRARIES ${Ncursesw_LIBRARIES})
CHECK_FUNCTION_EXISTS ("resizeterm" HAVE_RESIZETERM)

# -lm may or may not be a part of libc
foreach (extra m)
	find_library (extra_lib_${extra} ${extra})
	if (extra_lib_${extra})
		list (APPEND extra_libraries ${extra_lib_${extra}})
	endif ()
endforeach ()

# Generate a configuration file
include (GNUInstallDirs)
configure_file (${PROJECT_SOURCE_DIR}/config.h.in
	${PROJECT_BINARY_DIR}/config.h)
include_directories (${PROJECT_SOURCE_DIR} ${PROJECT_BINARY_DIR})

set (actions_list ${PROJECT_SOURCE_DIR}/nncmpp.actions)
set (actions_awk ${PROJECT_SOURCE_DIR}/nncmpp.actions.awk)
set (actions ${PROJECT_BINARY_DIR}/nncmpp-actions.h)
add_custom_command (OUTPUT ${actions}
	COMMAND env LC_ALL=C ${options}
		awk -f ${actions_awk} ${actions_list} > ${actions}
	DEPENDS ${actions_awk} ${actions_list} VERBATIM)

# Build the main executable and link it
add_executable (${PROJECT_NAME} ${PROJECT_NAME}.c ${actions})
target_link_libraries (${PROJECT_NAME} ${Unistring_LIBRARIES}
	${Ncursesw_LIBRARIES} termo-static ${curl_LIBRARIES} ${extra_libraries})
add_threads (${PROJECT_NAME})

# Installation
install (TARGETS ${PROJECT_NAME} DESTINATION ${CMAKE_INSTALL_BINDIR})
install (FILES LICENSE DESTINATION ${CMAKE_INSTALL_DOCDIR})
install (DIRECTORY contrib DESTINATION ${CMAKE_INSTALL_DATADIR}/${PROJECT_NAME})
install (DIRECTORY info DESTINATION ${CMAKE_INSTALL_DATADIR}/${PROJECT_NAME})
if (WITH_X11)
	install (FILES ${PROJECT_NAME}.svg
		DESTINATION ${CMAKE_INSTALL_DATADIR}/icons/hicolor/scalable/apps)
	install (FILES ${PROJECT_NAME}.desktop
		DESTINATION ${CMAKE_INSTALL_DATADIR}/applications)
endif ()

# Generate documentation from text markup
find_program (ASCIIDOCTOR_EXECUTABLE asciidoctor)
find_program (A2X_EXECUTABLE a2x)
if (NOT ASCIIDOCTOR_EXECUTABLE AND NOT A2X_EXECUTABLE)
	message (WARNING "Neither asciidoctor nor a2x were found, "
		"falling back to a substandard manual page generator")
endif ()

foreach (page ${PROJECT_NAME})
	set (page_output "${PROJECT_BINARY_DIR}/${page}.1")
	list (APPEND project_MAN_PAGES "${page_output}")
	if (ASCIIDOCTOR_EXECUTABLE)
		add_custom_command (OUTPUT ${page_output}
			COMMAND ${ASCIIDOCTOR_EXECUTABLE} -b manpage
				-a release-version=${PROJECT_VERSION}
				-o "${page_output}"
				"${PROJECT_SOURCE_DIR}/${page}.adoc"
			DEPENDS ${page}.adoc
			COMMENT "Generating man page for ${page}" VERBATIM)
	elseif (A2X_EXECUTABLE)
		add_custom_command (OUTPUT ${page_output}
			COMMAND ${A2X_EXECUTABLE} --doctype manpage --format manpage
				-a release-version=${PROJECT_VERSION}
				-D "${PROJECT_BINARY_DIR}"
				"${PROJECT_SOURCE_DIR}/${page}.adoc"
			DEPENDS ${page}.adoc
			COMMENT "Generating man page for ${page}" VERBATIM)
	else ()
		set (ASCIIMAN ${PROJECT_SOURCE_DIR}/liberty/tools/asciiman.awk)
		add_custom_command (OUTPUT ${page_output}
			COMMAND env LC_ALL=C asciidoc-release-version=${PROJECT_VERSION}
				awk -f ${ASCIIMAN} "${PROJECT_SOURCE_DIR}/${page}.adoc"
				> ${page_output}
			DEPENDS ${page}.adoc ${ASCIIMAN}
			COMMENT "Generating man page for ${page}" VERBATIM)
	endif ()
endforeach ()

add_custom_target (docs ALL DEPENDS ${project_MAN_PAGES})

foreach (page ${project_MAN_PAGES})
	string (REGEX MATCH "\\.([0-9])$" manpage_suffix "${page}")
	install (FILES "${page}"
		DESTINATION "${CMAKE_INSTALL_MANDIR}/man${CMAKE_MATCH_1}")
endforeach ()

# Testing
option (BUILD_TESTING "Build tests" OFF)
if (BUILD_TESTING)
	enable_testing ()

	find_program (xmlwf_EXECUTABLE xmlwf)
	find_program (xmllint_EXECUTABLE xmllint)
	foreach (xml ${PROJECT_NAME}.svg)
		if (xmlwf_EXECUTABLE)
			add_test (test-xmlwf-${xml} ${xmlwf_EXECUTABLE}
				${PROJECT_SOURCE_DIR}/${xml})
		endif ()
		if (xmllint_EXECUTABLE)
			add_test (test-xmllint-${xml} ${xmllint_EXECUTABLE} --noout
				${PROJECT_SOURCE_DIR}/${xml})
		endif ()
	endforeach ()

	find_program (dfv_EXECUTABLE desktop-file-validate)
	if (dfv_EXECUTABLE)
		foreach (df ${PROJECT_NAME}.desktop)
			add_test (test-dfv-${df} ${dfv_EXECUTABLE}
				${PROJECT_SOURCE_DIR}/${df})
		endforeach ()
	endif ()
endif ()

# CPack
set (CPACK_PACKAGE_DESCRIPTION_SUMMARY "Terminal/X11 MPD client")
set (CPACK_PACKAGE_VENDOR "Premysl Eric Janouch")
set (CPACK_PACKAGE_CONTACT "Přemysl Eric Janouch <p@janouch.name>")
set (CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/LICENSE")
set (CPACK_GENERATOR "TGZ;ZIP")
set (CPACK_PACKAGE_FILE_NAME
	"${PROJECT_NAME}-${PROJECT_VERSION}-${CMAKE_SYSTEM_NAME}-${CMAKE_SYSTEM_PROCESSOR}")
set (CPACK_PACKAGE_INSTALL_DIRECTORY "${PROJECT_NAME}-${PROJECT_VERSION}")
set (CPACK_SOURCE_GENERATOR "TGZ;ZIP")
set (CPACK_SOURCE_IGNORE_FILES "/\\\\.git;/build;/CMakeLists.txt.user")
set (CPACK_SOURCE_PACKAGE_FILE_NAME "${PROJECT_NAME}-${PROJECT_VERSION}")

set (CPACK_SET_DESTDIR TRUE)
include (CPack)
