#!/usr/bin/env bash

SCHEME=${SCHEME:-scheme}

# Check for correct number of arguments
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <filename>"
    exit 1
fi

original_file="$1"
formatted_file="${original_file}.fmt"

# Check if file exists
if [ ! -f "$original_file" ]; then
    echo "Error: File '$original_file' not found."
    exit 1
fi

# Check for shebang and create temp file
shebang_line=""
temp_script=$(mktemp)

if IFS= read -r first_line < "$original_file" && [[ "$first_line" == \#!* ]]; then
    shebang_line="$first_line"
    tail -n +2 "$original_file" > "$temp_script"
else
    cat "$original_file" > "$temp_script"
fi

# Format
${SCHEME} <<< "(pretty-file \"$temp_script\" \"$formatted_file\")" > /dev/null

# Capture exit code
exit_code=$?

# Handle shebang restoration if needed
if [ -n "$shebang_line" ] && [ -f "$formatted_file" ]; then
    temp_output=$(mktemp)
    echo "$shebang_line" > "$temp_output"
    cat "$formatted_file" >> "$temp_output"
    mv "$temp_output" "$formatted_file"
fi

# Cleanup temporary files
rm -f "$temp_script"

# Exit with Chez Scheme's status code
exit $exit_code
