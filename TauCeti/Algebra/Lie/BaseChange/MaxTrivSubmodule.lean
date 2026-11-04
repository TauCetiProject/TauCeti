/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.Weights.BaseChange

/-!
# Invariant vectors under extension of scalars

For a Lie module `M` over a Lie algebra `L` over a commutative ring `R`, the invariant vectors form
the Lie submodule `LieModule.maxTrivSubmodule R L M`. This file compares the invariants of the
extension of scalars `A ⊗[R] M`, as a module over `A ⊗[R] L`, with the extension of the
invariants of `M`:

```text
maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) = (maxTrivSubmodule R L M).baseChange A.
```

The containment `⊇` holds for every coefficient algebra. The reverse containment holds when `A` is
flat over `R` and `L` is finitely generated as an `R`-module. Both are the zero-weight cases of the
ordinary weight-space comparisons in `TauCeti.Algebra.Lie.Weights.BaseChange`.

The equality is what lets an invariant vector found after extending scalars be traded for one over
the original ring: if every invariant vector of `M` lies in a submodule `N`, then every invariant
vector of `A ⊗[R] M` lies in `N.baseChange A`. Weyl's complete reducibility theorem over a field
of characteristic zero is descended from the algebraically closed case in exactly this way.

## Main results

* `LieModule.baseChange_maxTrivSubmodule_le`: the extension of an invariant vector is invariant.
* `LieModule.maxTrivSubmodule_baseChange`: over a flat coefficient algebra, and for a finitely
  generated Lie algebra, the invariants of the extension are the extension of the invariants.
-/

public section

open TensorProduct

namespace LieModule

variable (R A L M : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The extension of an invariant vector is invariant**, over any coefficient algebra. -/
theorem baseChange_maxTrivSubmodule_le :
    (maxTrivSubmodule R L M).baseChange A ≤ maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) := by
  simpa only [map_zero, weightSpace_coe_zero] using
    baseChange_weightSpace_le (A := A) (M := M) (0 : Module.Dual R L)

/-- **Over a flat coefficient algebra, extension of scalars commutes with taking invariants**, for
a Lie algebra that is finitely generated as a module. -/
theorem maxTrivSubmodule_baseChange [Module.Flat R A] [Module.Finite R L] :
    maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) = (maxTrivSubmodule R L M).baseChange A := by
  simpa only [map_zero, weightSpace_coe_zero] using
    weightSpace_baseChange (A := A) (M := M) (0 : Module.Dual R L)

end LieModule
