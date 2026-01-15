#!/bin/bash

if [[ "$OSTYPE" == "linux-gnu"* ]]; then
	export SED=sed
elif [[ "$OSTYPE" == "darwin"* ]]; then
        export SED=gsed
fi

$SED -i -ne "$! N; /^.*\s*\n\s*<\/pre>/ { s/\s*\n\s*//; p; b }; $ { p; q }; P; D" $1