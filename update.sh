# Maybe we can make this git independent or safer?

# Vars
FILE="$(realpath -s "$0")"
DIR="$(dirname $FILE)"
PKGDIR="$(dirname $DIR)"


cd "$DIR" 

# Update main package
echo "Updating StarAlge package."
git pull -q origin master 

echo "Now updating dependencies."

# Sylver update
if [ -f "$PKGDIR/Sylver/update.sh" ]
then
    sh "$PKGDIR/Sylver/update.sh"
else
    echo "Could not find Sylver, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/Sylver
    echo "Installing Sylver..."
    sh "$PKGDIR/Sylver/install.sh"
fi

# StarAlge update
if [ -f "$PKGDIR/StarAlge/update.sh" ]
then
    sh "$PKGDIR/StarAlge/update.sh"
else
    echo "Could not find StarAlge, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/StarAlge
    echo "Installing StarAlge..."
    sh "$PKGDIR/StarAlge/install.sh"
fi

# TensorSpace update
if [ -f "$PKGDIR/TensorSpace/update.sh" ]
then
    sh "$PKGDIR/TensorSpace/update.sh"
else
    echo "Could not find TensorSpace, downloading..."
    cd "$PKGDIR"
    git clone -q https://github.com/algeboy/TensorSpace
    echo "Installing TensorSpace..."
    sh "$PKGDIR/TensorSpace/install.sh"
fi

echo "Successfully updated!"

