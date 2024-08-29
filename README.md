CTenC is a Cartesian TENsor Calculus package for performing manipulations of tensor expressions using index notation in Mathematica. The package is designed and optimized for problems in engineering and material science, including solutions of field equations (Stokes, Laplace, etc.) and developing constitutive equations in tensor-based formalisms such as GENERIC. Functions are given for the manipulations of free and dummy indices. Tensors in the package can be assigned symmetries (symmetric, antisymmetric, irreducible, mixed) and these symmetries are automatically accounted for through the use of projection operators in differentiation. Several scalar and tensor functions are built into the package (norm, trace, determinant, matrix power, etc.). The package is easily extensible through the addition of new functions.

# Usage
The package is stored in `CTenC.wl` and can be loaded in a Mathematica notebook using
```
Get["NewTensor'"]
```
A tutorial describing the basic usage of the package is given in `Tutorial.nb`.