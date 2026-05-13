PROJECT_NAME=SatQMCert

.PHONY: clean

all: ${PROJECT_NAME}.mla

${PROJECT_NAME}.mla: src/${PROJECT_NAME}.mpl
	maple ./scripts/installation_script.mpl

clean:
	rm -rf ${PROJECT_NAME}.mla
