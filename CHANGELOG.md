# Version 1.0.0
Initial version

## 1.0.1
* Improved pattern matching for projection operators and IndexHarmonics
* Made `DependsQ` orderless
* Added automatic Dirac delta simplification for partial derivatives
* Fixed a bug where partial derivatives of tensors with symmetries could return incorrect result
* Fixed a bug where `IndexSimplify` would return incorrect answer

## Version 1.1.0
* Added `IndexSet`, which generates functions with unique dummy indices each time it is evaluated
* Rank now works correctly on projection operators
* Improved tutorial