for file in *.mpl; do
  echo ">< Working with $file"
  time maple "$file"
done
