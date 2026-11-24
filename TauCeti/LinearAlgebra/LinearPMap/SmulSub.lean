/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Shift

/-!
# The shift `c • x - A x` of a partial linear map as a linear map on its domain

For a partial linear map `A : E →ₗ.[R] E` and a scalar `c`, the shift `x ↦ c • x - A x` is a
linear map from the domain of `A` to `E`.  Bundling it (`LinearPMap.smulSub`) gives access to the
`LinearMap` API, in particular to its range as a submodule, for arguments about resolvents,
deficiency shifts and dissipativity, where surjectivity or density of this range is the question.
Up to sign it is the scalar shift `LinearPMap.subScalar A c = A - c • 1` of
`TauCeti.LinearAlgebra.LinearPMap.Shift`, regarded as a linear map on the domain
(`smulSub_apply_eq_neg_subScalar`), so results about the kernel or range of either form transfer to
the other.

## Main declarations

* `LinearPMap.smulSub`: the bundled shift `x ↦ c • x - A x` on the domain of `A`.
* `LinearPMap.smulSub_apply` and `LinearPMap.coe_range_smulSub`: its values and its range.
* `LinearPMap.smulSub_apply_eq_neg_subScalar`: `smulSub c A` is `-(subScalar A c)` pointwise.
* `LinearPMap.mem_ker_smulSub_iff` and `LinearPMap.ker_smulSub_eq_bot_iff`: kernel equivalence with
  `subScalar A c`.
* `LinearPMap.exists_linearMap_inverse_smul_sub`: a bijective shift has a linear two-sided inverse
  `E → E` with values in the domain of `A`.
* `LinearPMap.surjective_neg_smul_sub_iff_surjective_add_smul`: the shift `x ↦ (-c) • x - A x` is
  surjective if and only if `x ↦ A x + c • x` is surjective.
-/

public section

namespace LinearPMap

section Ring

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The shift `x ↦ (-c) • x - A x` on the domain of `A` is surjective if and only if
`x ↦ A x + c • x` is surjective, since the two maps are negatives of one another. -/
theorem surjective_neg_smul_sub_iff_surjective_add_smul (A : E →ₗ.[R] E) (c : R) :
    (Function.Surjective fun x : A.domain => (-c) • (x : E) - A x) ↔
      Function.Surjective fun x : A.domain => A x + c • (x : E) := by
  have hneg : (fun x : A.domain => (-c) • (x : E) - A x) =
      (Equiv.neg E) ∘ fun x : A.domain => A x + c • (x : E) := by
    ext x
    simp only [Function.comp_apply, Equiv.neg_apply, _root_.neg_smul, neg_add_rev, sub_eq_add_neg]
  rw [hneg]
  exact (Equiv.neg E).comp_surjective _

end Ring

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- The shift `x ↦ c • x - A x` of a partial linear map, as a linear map on the domain of `A`. -/
def smulSub (c : R) (A : E →ₗ.[R] E) : A.domain →ₗ[R] E :=
  c • A.domain.subtype - A.toFun

@[simp]
theorem smulSub_apply (c : R) (A : E →ₗ.[R] E) (x : A.domain) :
    A.smulSub c x = c • (x : E) - A x :=
  (rfl)

/-- The bundled shift `c • x - A x` is the negative of the scalar shift `subScalar A c = A - c • 1`
of the same domain, pointwise. -/
theorem smulSub_apply_eq_neg_subScalar (c : R) (A : E →ₗ.[R] E) (x : A.domain) :
    A.smulSub c x = -subScalar A c
      ⟨x, (subScalar_domain A c).symm ▸ x.property⟩ := by
  rw [A.smulSub_apply, subScalar_apply, neg_sub]

/-- A domain element lies in the kernel of `A.smulSub c` if and only if its coercion lies in the
kernel of `A.subScalar c`. -/
theorem mem_ker_smulSub_iff (c : R) (A : E →ₗ.[R] E) (x : A.domain) :
    x ∈ LinearMap.ker (A.smulSub c) ↔ (x : E) ∈ (A.subScalar c).ker := by
  rw [LinearMap.mem_ker, A.smulSub_apply_eq_neg_subScalar c x, neg_eq_zero,
    ← LinearPMap.coe_mem_ker_iff]

/-- The kernel of `A.smulSub c` is trivial if and only if the kernel of `A.subScalar c` is
trivial. -/
theorem ker_smulSub_eq_bot_iff (c : R) (A : E →ₗ.[R] E) :
    LinearMap.ker (A.smulSub c) = ⊥ ↔ (A.subScalar c).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot', LinearPMap.ker_eq_bot']
  constructor
  · intro h x hx
    have hx' : A.smulSub c ⟨x, A.subScalar_domain c ▸ x.property⟩ = 0 := by
      rw [A.smulSub_apply_eq_neg_subScalar, neg_eq_zero]
      exact hx
    exact Subtype.ext (by simpa using congrArg Subtype.val (h _ hx'))
  · intro h x hx
    rw [A.smulSub_apply_eq_neg_subScalar c x, neg_eq_zero] at hx
    exact Subtype.ext (by simpa using congrArg Subtype.val (h _ hx))

/-- The range of the bundled shift is the range of the shift. -/
theorem coe_range_smulSub (c : R) (A : E →ₗ.[R] E) :
    ((A.smulSub c).range : Set E) = Set.range (fun x : A.domain => c • (x : E) - A x) := by
  ext y
  simp only [SetLike.mem_coe, LinearMap.mem_range, smulSub_apply, Set.mem_range]

/-- A bijective shift `x ↦ c • x - A x` has a linear two-sided inverse `J : E →ₗ[R] E` taking
values in the domain of `A`. -/
theorem exists_linearMap_inverse_smul_sub {A : E →ₗ.[R] E} {c : R}
    (h : Function.Bijective fun x : A.domain => c • (x : E) - A x) :
    ∃ (J : E →ₗ[R] E) (hJ : ∀ y, J y ∈ A.domain),
      (∀ y, c • J y - A ⟨J y, hJ y⟩ = y) ∧ ∀ x : A.domain, J (c • (x : E) - A x) = x := by
  have hfun : ⇑(A.smulSub c) = fun x : A.domain => c • (x : E) - A x := funext (smulSub_apply c A)
  let e := LinearEquiv.ofBijective (A.smulSub c) (hfun ▸ h)
  let J : E →ₗ[R] E := A.domain.subtype ∘ₗ e.symm.toLinearMap
  have hJ (y : E) : J y = (e.symm y : E) := by
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]
  refine ⟨J, fun y => hJ y ▸ (e.symm y).property, fun y => ?_, fun x => ?_⟩
  · have hx : (⟨J y, hJ y ▸ (e.symm y).property⟩ : A.domain) = e.symm y := Subtype.ext (hJ y)
    rw [hx, hJ, ← smulSub_apply]
    exact e.apply_symm_apply y
  · rw [hJ, ← smulSub_apply]
    exact congrArg Subtype.val (e.symm_apply_apply x)

end LinearPMap

end
