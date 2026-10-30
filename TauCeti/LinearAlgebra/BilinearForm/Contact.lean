/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Contact covectors

A covector `a` on a vector space `V` is **contact** for a bilinear form `B` when `a ≠ 0` and `B`
restricts to a nondegenerate form on the hyperplane `ker a`
(`Module.Dual.IsContact`). This is the pointwise linear algebra of a contact form on a manifold:
a one-form `α` is contact exactly when, at every point `x`, the covector `α_x` is contact for the
bilinear form `dα_x`.

The condition only depends on `B` through its values on `ker a × ker a`
(`Module.Dual.isContact_congr`), and is unchanged when `a` or `B` is multiplied by a nonzero
scalar. Together these give the pointwise form of the rescaling law for contact forms: since
`d(f α) = df ∧ α + f dα`, and `df ∧ α` vanishes on `ker α × ker α`, the forms `α` and `f α` are
contact together whenever `f` vanishes nowhere.

For an alternating `B`, the hyperplane `ker a` carries a nondegenerate alternating form, so it has
even dimension and `V` has odd dimension (`Module.Dual.IsContact.odd_finrank`).

A **Reeb vector** of `a` and `B` is a vector `r` with `a r = 1` and `B r = 0`
(`Module.Dual.IsReebVector`). For a contact covector it is unique, and for an alternating `B` in
finite dimension it exists (`Module.Dual.IsContact.existsUnique_isReebVector`): it is the preimage
of `a` under the injective map `v ↦ B v + a v • a` from `V` to its dual. This is the pointwise
linear algebra of the Reeb vector field of a contact form.

## Main declarations

* `Module.Dual.IsContact`: `a ≠ 0` and `B` is nondegenerate on `ker a`.
* `Module.Dual.isContact_iff_of_isRefl`: for a reflexive `B`, the elementwise criterion: the only
  vector of `ker a` which is `B`-orthogonal to all of `ker a` is zero.
* `Module.Dual.isContact_congr`, `Module.Dual.isContact_smul_iff`,
  `Module.Dual.isContact_smul_bilinForm_iff`: invariance under changes of `B` off `ker a` and
  under nonzero rescaling of `a` and of `B`.
* `Module.Dual.IsContact.even_finrank_ker`, `Module.Dual.IsContact.odd_finrank`: the dimension
  count.
* `Module.Dual.IsReebVector`: `a r = 1` and `B r v = 0` for every `v`.
* `Module.Dual.IsContact.isReebVector_iff_forall_add_mul_eq`: the Reeb vector is the preimage of
  `a` under `v ↦ B v + a v • a`.
* `Module.Dual.IsContact.existsUnique_isReebVector`: existence and uniqueness of the Reeb vector.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

open Module

namespace Module.Dual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {a : Module.Dual K V} {B B' : LinearMap.BilinForm K V}

/-- A covector `a` is **contact** for a bilinear form `B` when it is nonzero and `B` restricts to a
nondegenerate bilinear form on the hyperplane `ker a`. For a one-form `α` on a manifold, the
covector `α_x` being contact for `dα_x` at every point `x` is the contact condition. -/
def IsContact (a : Module.Dual K V) (B : LinearMap.BilinForm K V) : Prop :=
  a ≠ 0 ∧ (B.restrict (LinearMap.ker a)).Nondegenerate

theorem isContact_def :
    a.IsContact B ↔ a ≠ 0 ∧ (B.restrict (LinearMap.ker a)).Nondegenerate :=
  Iff.rfl

/-- A contact covector is nonzero. -/
theorem IsContact.ne_zero (h : a.IsContact B) : a ≠ 0 :=
  h.1

/-- A contact covector's bilinear form is nondegenerate on its kernel. -/
theorem IsContact.nondegenerate_restrict (h : a.IsContact B) :
    (B.restrict (LinearMap.ker a)).Nondegenerate :=
  h.2

/-- For a reflexive bilinear form, and in particular for an alternating one, a covector `a` is
contact exactly when it is nonzero and no nonzero vector of `ker a` is `B`-orthogonal to all of
`ker a`. -/
theorem isContact_iff_of_isRefl (hB : B.IsRefl) :
    a.IsContact B ↔
      a ≠ 0 ∧ ∀ v, a v = 0 → (∀ w, a w = 0 → B v w = 0) → v = 0 := by
  have hrefl : (B.restrict (LinearMap.ker a)).IsRefl := fun v w h ↦ hB v w h
  rw [isContact_def, LinearMap.BilinForm.Nondegenerate,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl]
  refine and_congr_right fun _ ↦ ⟨fun h v hv hvw ↦ ?_, fun h v hv ↦ ?_⟩
  · have := h ⟨v, hv⟩ fun w ↦ hvw w w.2
    simpa using congrArg Subtype.val this
  · exact Subtype.ext <| h v v.2 fun w hw ↦ hv ⟨w, hw⟩

/-- Whether `a` is contact for `B` only depends on the values of `B` on `ker a × ker a`. -/
theorem isContact_congr (h : ∀ v w, a v = 0 → a w = 0 → B v w = B' v w) :
    a.IsContact B ↔ a.IsContact B' := by
  have hrestrict : B.restrict (LinearMap.ker a) = B'.restrict (LinearMap.ker a) := by
    ext v w
    exact h v w v.2 w.2
  rw [isContact_def, isContact_def, hrestrict]

/-- A nonzero multiple of a covector is contact for `B` exactly when the covector is. -/
@[simp]
theorem isContact_smul_iff {c : K} (hc : c ≠ 0) : (c • a).IsContact B ↔ a.IsContact B := by
  rw [isContact_def, isContact_def, LinearMap.ker_smul _ _ hc, smul_ne_zero_iff_right hc]

/-- A covector is contact for a nonzero multiple of `B` exactly when it is contact for `B`. -/
@[simp]
theorem isContact_smul_bilinForm_iff {c : K} (hc : c ≠ 0) :
    a.IsContact (c • B) ↔ a.IsContact B := by
  have hrestrict : (c • B).restrict (LinearMap.ker a) = c • B.restrict (LinearMap.ker a) := by
    ext v w
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.smul_apply]
  rw [isContact_def, isContact_def, hrestrict,
    TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)]

/-- For an alternating `B`, the kernel of a contact covector has even dimension. -/
theorem IsContact.even_finrank_ker [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B) :
    Even (finrank K (LinearMap.ker a)) :=
  LinearMap.BilinForm.IsAlt.even_finrank (B := B.restrict (LinearMap.ker a))
    (fun v ↦ hB v) h.nondegenerate_restrict

/-- A finite-dimensional space carrying a covector which is contact for an alternating bilinear
form has odd dimension. -/
theorem IsContact.odd_finrank [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B) :
    Odd (finrank K V) := by
  rw [← finrank_ker_add_one_of_ne_zero h.ne_zero]
  exact (h.even_finrank_ker hB).add_one

/-! ### Reeb vectors -/

/-- A vector `r` is a **Reeb vector** of a covector `a` and a bilinear form `B` when `a r = 1` and
`B r v = 0` for every `v`. For a contact form `α` on a manifold, the Reeb vector of `α_x` and
`dα_x` is the value at `x` of the Reeb vector field. -/
def IsReebVector (a : Module.Dual K V) (B : LinearMap.BilinForm K V) (r : V) : Prop :=
  a r = 1 ∧ ∀ v, B r v = 0

theorem isReebVector_iff {r : V} : a.IsReebVector B r ↔ a r = 1 ∧ ∀ v, B r v = 0 :=
  Iff.rfl

/-- If `r` is a Reeb vector of `a` and `B`, then `c⁻¹ r` is a Reeb vector of `c a` and `c B`, for
a nonzero scalar `c`. -/
theorem IsReebVector.smul {r : V} (hr : a.IsReebVector B r) {c : K} (hc : c ≠ 0) :
    (c • a).IsReebVector (c • B) (c⁻¹ • r) :=
  ⟨by simp [hr.1, hc], fun v ↦ by simp [hr.2]⟩

/-- A Reeb vector of a contact covector is unique. -/
theorem IsContact.isReebVector_unique (h : a.IsContact B) {r r' : V} (hr : a.IsReebVector B r)
    (hr' : a.IsReebVector B r') : r = r' := by
  have hker : r - r' ∈ LinearMap.ker a := by
    rw [LinearMap.mem_ker, map_sub, hr.1, hr'.1, sub_self]
  have h₀ := h.nondegenerate_restrict.1 ⟨r - r', hker⟩ fun w ↦ by
    simp [hr.2, hr'.2]
  exact sub_eq_zero.1 (congrArg Subtype.val h₀)

/-- For an alternating `B` and a contact covector `a`, the linear map `v ↦ B v + a v • a` from `V`
to its dual is injective: a vector `v` with `B v w + a v * a w = 0` for every `w` is zero. -/
theorem IsContact.eq_zero_of_forall_add_mul_eq_zero (hB : B.IsAlt) (h : a.IsContact B) {v : V}
    (hv : ∀ w, B v w + a v * a w = 0) : v = 0 := by
  -- Testing against `v` itself gives `a v ^ 2 = 0`, so `v ∈ ker a`, and then `B v` vanishes.
  have hav : a v = 0 := by
    simpa [hB.self_eq_zero v] using hv v
  have h₀ := h.nondegenerate_restrict.1 ⟨v, hav⟩ fun w ↦ by
    simpa [hav] using hv w
  simpa using congrArg Subtype.val h₀

/-- For an alternating `B` and a contact covector `a`, the Reeb vector is the preimage of `a`
under the linear map `v ↦ B v + a v • a`: a vector `r` is a Reeb vector exactly when
`B r w + a r * a w = a w` for every `w`. -/
theorem IsContact.isReebVector_iff_forall_add_mul_eq (hB : B.IsAlt) (h : a.IsContact B)
    {r : V} : a.IsReebVector B r ↔ ∀ w, B r w + a r * a w = a w := by
  refine ⟨fun hr w ↦ by rw [hr.1, hr.2, zero_add, one_mul], fun hr ↦ ?_⟩
  -- Testing against `r` gives `a r ^ 2 = a r`. The case `a r = 0` would put `r` in `ker a` with
  -- `B r = a`, forcing first `r = 0` and then `a = 0`.
  have har : a r = 1 := by
    have hsq : a r * a r = a r := by simpa [hB.self_eq_zero r] using hr r
    refine (mul_left_eq_self₀.1 hsq).resolve_right fun har ↦ h.ne_zero ?_
    have hr' : ∀ w, B r w = a w := fun w ↦ by simpa [har] using hr w
    have h₀ := h.nondegenerate_restrict.1 ⟨r, har⟩ fun w ↦ by
      simp [hr']
    have hr₀ : r = 0 := by simpa using congrArg Subtype.val h₀
    ext w
    simp [← hr' w, hr₀]
  exact ⟨har, fun w ↦ by simpa [har] using hr w⟩

/-- **Existence and uniqueness of the Reeb vector.** In finite dimension, a covector which is
contact for an alternating bilinear form has a unique Reeb vector. -/
theorem IsContact.existsUnique_isReebVector [FiniteDimensional K V] (hB : B.IsAlt)
    (h : a.IsContact B) : ∃! r, a.IsReebVector B r := by
  -- The map `v ↦ B v + a v • a` is injective, hence onto the dual, which has the same dimension.
  let Φ : V →ₗ[K] Module.Dual K V := B + a.smulRight a
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun v hv ↦ h.eq_zero_of_forall_add_mul_eq_zero hB ?_
    intro w
    simpa [Φ] using LinearMap.congr_fun hv w
  obtain ⟨r, hr⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).1 hΦ a
  have hrReeb : a.IsReebVector B r :=
    (h.isReebVector_iff_forall_add_mul_eq hB).2 fun w ↦ by simpa [Φ] using LinearMap.congr_fun hr w
  exact ⟨r, hrReeb, fun r' hr' ↦ h.isReebVector_unique hr' hrReeb⟩

end Module.Dual
