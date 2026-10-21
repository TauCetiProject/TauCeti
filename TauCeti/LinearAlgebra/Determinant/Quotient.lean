/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Projection

/-!
# The determinant of an endomorphism induced on a quotient

An endomorphism `f` of a module `M` that preserves a submodule `p` induces an endomorphism
`Submodule.mapQ p p f _` of `M ⧸ p`. Given a complement `q` of `p`, the determinant of that
induced endomorphism equals the determinant of the **compression** of `f` to `q`: inclusion into
`M`, then `f`, then projection onto `q` along `p`. This gives a basis-free handle on the quotient
determinant inside `M` itself, where it can be computed and varies continuously with `f`.

## Main results

* `LinearMap.det_mapQ_of_isCompl`: the determinant of the endomorphism induced on `M ⧸ p` is the
  determinant of the compression to a complement of `p`.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The determinant of a quotient endomorphism is that of its compression to a complement.** -/
theorem det_mapQ_of_isCompl {p q : Submodule R M} (hpq : IsCompl p q) (f : M →ₗ[R] M)
    (hf : p ≤ p.comap f) :
    LinearMap.det (Submodule.mapQ p p f hf) =
      LinearMap.det (q.projectionOnto p hpq.symm ∘ₗ f ∘ₗ q.subtype) := by
  rw [← LinearMap.det_conj (Submodule.mapQ p p f hf) (Submodule.quotientEquivOfIsCompl p q hpq)]
  refine congrArg LinearMap.det (LinearMap.ext fun x => ?_)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype,
    Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk]

end LinearMap
