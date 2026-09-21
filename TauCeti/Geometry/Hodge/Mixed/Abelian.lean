/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.CoimageImage
public import TauCeti.Geometry.Hodge.Mixed.Prod

/-!
# The abelian category of mixed Hodge structures

Mixed Hodge structures form an abelian category. The finite products supplied by
`Mixed.Prod`, together with the existing kernels, cokernels and invertible coimage–image
comparisons, give the abelian structure by
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`.

## References

Deligne, *Théorie de Hodge II*, 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

/-- Mixed Hodge structures, with rational Hodge morphisms, form an abelian category. -/
noncomputable instance abelian : Abelian MixedHodgeStructureCat.{u} :=
  Abelian.ofCoimageImageComparisonIsIso

end TauCeti.Hodge.MixedHodgeStructureCat
