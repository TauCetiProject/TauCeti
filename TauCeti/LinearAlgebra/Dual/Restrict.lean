/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.Module.Projective.Complement

/-!
# Extending functionals from a direct summand

Mathlib's `Subspace.dualRestrict_surjective` says that over a field every functional on a subspace
extends to the ambient space. Over a ring the same holds for a complemented submodule `W`: compose
the functional with the projection onto `W` along a complement. In particular it holds when the
quotient by `W` is projective, since `W` is then the kernel of a surjection onto a projective
module.

## Main results

* `Submodule.dualRestrict_surjective_of_isComplemented`: restriction of functionals to a
  complemented submodule is surjective.
* `Submodule.dualRestrict_surjective_of_projective`: restriction of functionals to a submodule
  with projective quotient is surjective.
-/

public section

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Functionals extend from a complemented submodule.** -/
theorem dualRestrict_surjective_of_isComplemented {W : Submodule R M} (h : IsComplemented W) :
    Function.Surjective W.dualRestrict :=
  LinearMap.surjective_comp_subtype_of_isComplemented h

/-- **Functionals extend from a submodule with projective quotient**, which is a direct summand. -/
theorem dualRestrict_surjective_of_projective (W : Submodule R M) [Module.Projective R (M ⧸ W)] :
    Function.Surjective W.dualRestrict := by
  refine dualRestrict_surjective_of_isComplemented ?_
  simpa using W.mkQ.isComplemented_ker_of_surjective W.mkQ_surjective

end Submodule
