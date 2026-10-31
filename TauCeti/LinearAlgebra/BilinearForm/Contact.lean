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

For an alternating `B` and a contact covector `a`, the bilinear form `B + a ⊗ a`,
`(v, w) ↦ B v w + a v * a w`, is left-separating
(`Module.Dual.IsContact.separatingLeft_add_smulRight`), so in finite dimension `v ↦ B v + a(v) a`
is an isomorphism onto the dual. This is the pointwise contact flat map `X ↦ ι_X dα + α(X) α` of a
contact form. The preimage of `a` itself is characterized by the Reeb equations: `B r + a(r) a = a`
exactly when `a r = 1` and `B r = 0` (`Module.Dual.IsContact.add_smulRight_apply_eq_self_iff`).

A contact covector `a` on a finite-dimensional space has a **Reeb vector** `r = a.reebVector B`
(`Module.Dual.reebVector`): the unique vector with `a r = 1` which is `B`-orthogonal to `ker a`.
For alternating `B` it spans the kernel of `B`, and `V = ker a ⊕ K r`. Replacing `a` by `c a` and
`B` by a form agreeing with `c B` up to a term `l ∧ a` changes `r` into `c⁻¹ r` plus an explicit
correction in `ker a` (`Module.Dual.IsContact.reebVector_smul_eq_inv_smul_add_iff`). This is the
pointwise form of the Reeb vector field of a contact form and of its rescaling law.

## Main declarations

* `Module.Dual.IsContact`: `a ≠ 0` and `B` is nondegenerate on `ker a`.
* `Module.Dual.isContact_iff_of_isRefl`: for a reflexive `B`, the elementwise criterion: the only
  vector of `ker a` which is `B`-orthogonal to all of `ker a` is zero.
* `Module.Dual.isContact_congr`, `Module.Dual.isContact_smul_iff`,
  `Module.Dual.isContact_smul_bilinForm_iff`: invariance under changes of `B` off `ker a` and
  under nonzero rescaling of `a` and of `B`.
* `Module.Dual.IsContact.even_finrank_ker`, `Module.Dual.IsContact.odd_finrank`: the dimension
  count.
* `Module.Dual.IsContact.separatingLeft_add_smulRight`: `B + a ⊗ a` is left-separating.
* `Module.Dual.IsContact.add_smulRight_apply_eq_self_iff`: the preimage of `a` under
  `v ↦ B v + a(v) a`.
* `Module.Dual.reebVector`, `Module.Dual.IsContact.eq_reebVector_iff`: the Reeb vector and its
  characterization.
* `Module.Dual.IsContact.ker_eq_span_reebVector`,
  `Module.Dual.IsContact.isCompl_ker_span_reebVector`: the Reeb line is the kernel of `B` and is
  complementary to `ker a`.
* `Module.Dual.IsContact.reebVector_smul_eq_inv_smul_add_iff`: the rescaling law.

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

/-! ### The contact flat map -/

/-- For an alternating `B` and a contact covector `a`, the bilinear form `B + a ⊗ a`,
`(v, w) ↦ B v w + a v * a w`, is left-separating. This is the linear algebra behind the
contact flat map `v ↦ ι_v dα + α(v) α` of a contact form, which is invertible in finite
dimension. -/
theorem IsContact.separatingLeft_add_smulRight (hB : B.IsAlt) (h : a.IsContact B) :
    (B + a.smulRight a).SeparatingLeft := by
  intro v hv
  have hvv : a v = 0 := by
    simpa [hB v] using hv v
  refine Subtype.ext_iff.1 (h.nondegenerate_restrict.1 ⟨v, hvv⟩ fun w ↦ ?_)
  simpa [w.2] using hv w

/-- For an alternating `B` and a contact covector `a`, a vector `r` solves `B r + a(r) a = a`
exactly when `a r = 1` and `r` is `B`-orthogonal to everything: these are the Reeb equations. -/
theorem IsContact.add_smulRight_apply_eq_self_iff (hB : B.IsAlt) (h : a.IsContact B) {r : V} :
    (B + a.smulRight a) r = a ↔ a r = 1 ∧ B r = 0 := by
  refine ⟨fun hr ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by ext w; simp [h₁, h₂]⟩
  have hr' (w : V) : B r w + a r * a w = a w := by
    simpa using LinearMap.congr_fun hr w
  -- Evaluating at `r` itself gives `a r * a r = a r`, so `a r` is `0` or `1`.
  have hrr : a r * a r = a r := by
    simpa [hB r] using hr' r
  have h₁ : a r = 1 := by
    by_cases h₀ : a r = 0
    · -- If `a r = 0`, then `r ∈ ker a` is `B`-orthogonal to `ker a`, so `r = 0` and `a = 0`.
      have hr₀ : r = 0 := Subtype.ext_iff.1 <| h.nondegenerate_restrict.1 ⟨r, h₀⟩ fun w ↦ by
        simpa [h₀, w.2] using hr' w
      exact absurd (LinearMap.ext fun w ↦ by simpa [hr₀] using (hr' w).symm) h.ne_zero
    · exact (mul_eq_left₀ h₀).1 hrr
  exact ⟨h₁, LinearMap.ext fun w ↦ by simpa [h₁] using hr' w⟩

/-! ### The Reeb vector -/

open Classical in
/-- The **Reeb vector** of a covector `a` for a bilinear form `B`: a vector `r` with `a r = 1` which
is `B`-orthogonal to the hyperplane `ker a`, that is `B r w = 0` whenever `a w = 0`. When `a` is
contact for `B` on a finite-dimensional space, there is exactly one such vector
(`Module.Dual.IsContact.eq_reebVector_iff`). If there is none, `a.reebVector B` is `0`. -/
noncomputable def reebVector (a : Module.Dual K V) (B : LinearMap.BilinForm K V) : V :=
  if h : ∃ r, a r = 1 ∧ ∀ w, a w = 0 → B r w = 0 then h.choose else 0

/-- The Reeb vector only depends on `B` through its values on `V × ker a`. -/
theorem reebVector_congr (h : ∀ v w, a w = 0 → B v w = B' v w) :
    a.reebVector B = a.reebVector B' := by
  have hp : (fun r ↦ a r = 1 ∧ ∀ w, a w = 0 → B r w = 0) =
      fun r ↦ a r = 1 ∧ ∀ w, a w = 0 → B' r w = 0 := by
    ext r
    exact and_congr_right fun _ ↦ forall_congr' fun w ↦ imp_congr_right fun hw ↦ by rw [h r w hw]
  unfold reebVector
  rw [hp]

/-- The Reeb vector does not change when `B` is multiplied by a nonzero scalar. -/
@[simp]
theorem reebVector_smul_bilinForm {c : K} (hc : c ≠ 0) :
    a.reebVector (c • B) = a.reebVector B := by
  have hp : (fun r ↦ a r = 1 ∧ ∀ w, a w = 0 → (c • B) r w = 0) =
      fun r ↦ a r = 1 ∧ ∀ w, a w = 0 → B r w = 0 := by
    ext r
    simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]
  unfold reebVector
  rw [hp]

/-- Two vectors on which a contact covector takes the value `1`, both `B`-orthogonal to its
kernel, are equal. -/
private theorem IsContact.eq_of_apply_eq_one (h : a.IsContact B) {r r' : V} (hr : a r = 1)
    (hrB : ∀ w, a w = 0 → B r w = 0) (hr' : a r' = 1) (hrB' : ∀ w, a w = 0 → B r' w = 0) :
    r = r' := by
  have hmem : r - r' ∈ LinearMap.ker a := by
    rw [LinearMap.mem_ker, map_sub, hr, hr', sub_self]
  have := h.nondegenerate_restrict.1 ⟨r - r', hmem⟩ fun w ↦ by
    simp [hrB w w.2, hrB' w w.2]
  exact sub_eq_zero.1 (congrArg Subtype.val this)

variable [FiniteDimensional K V]

/-- A contact covector has a vector on which it takes the value `1` and which is `B`-orthogonal
to its kernel. -/
private theorem IsContact.exists_apply_eq_one (h : a.IsContact B) :
    ∃ r, a r = 1 ∧ ∀ w, a w = 0 → B r w = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra! hv
    exact h.ne_zero (LinearMap.ext hv)
  set v₀ := (a v)⁻¹ • v
  have hv₀ : a v₀ = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  -- Represent `B v₀` on `ker a` by a vector `u` of `ker a`, using nondegeneracy there.
  set u := ((B.restrict (LinearMap.ker a)).toDual h.nondegenerate_restrict).symm
    ((B v₀).domRestrict (LinearMap.ker a))
  have hu : ∀ w : LinearMap.ker a, B u w = B v₀ w := fun w ↦
    LinearMap.BilinForm.apply_toDual_symm_apply (B := B.restrict (LinearMap.ker a)) _ w
  refine ⟨v₀ - u, ?_, fun w hw ↦ ?_⟩
  · rw [map_sub, hv₀, LinearMap.mem_ker.1 u.2, sub_zero]
  · rw [map_sub, LinearMap.sub_apply, ← hu ⟨w, hw⟩, sub_self]

/-- **Characterization of the Reeb vector.** For a contact covector `a`, the Reeb vector is the
unique vector `r` with `a r = 1` which is `B`-orthogonal to `ker a`. -/
theorem IsContact.eq_reebVector_iff (h : a.IsContact B) {r : V} :
    r = a.reebVector B ↔ a r = 1 ∧ ∀ w, a w = 0 → B r w = 0 := by
  have hex := h.exists_apply_eq_one
  have hspec : a (a.reebVector B) = 1 ∧ ∀ w, a w = 0 → B (a.reebVector B) w = 0 := by
    rw [reebVector, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  refine ⟨fun hr ↦ hr ▸ hspec, fun hr ↦ ?_⟩
  exact h.eq_of_apply_eq_one hr.1 hr.2 hspec.1 hspec.2

/-- A contact covector takes the value `1` on its Reeb vector. -/
@[simp]
theorem IsContact.apply_reebVector (h : a.IsContact B) : a (a.reebVector B) = 1 :=
  (h.eq_reebVector_iff.1 rfl).1

/-- The Reeb vector is `B`-orthogonal to the kernel of the contact covector. -/
theorem IsContact.apply_reebVector_of_apply_eq_zero (h : a.IsContact B) {w : V} (hw : a w = 0) :
    B (a.reebVector B) w = 0 :=
  (h.eq_reebVector_iff.1 rfl).2 w hw

/-- The Reeb vector of a contact covector is nonzero. -/
theorem IsContact.reebVector_ne_zero (h : a.IsContact B) : a.reebVector B ≠ 0 := fun h0 ↦ by
  simpa [h0] using h.apply_reebVector

/-- The Reeb vector of a contact covector does not lie in its kernel. -/
theorem IsContact.reebVector_notMem_ker (h : a.IsContact B) :
    a.reebVector B ∉ LinearMap.ker a := by
  simp [LinearMap.mem_ker, h.apply_reebVector]

/-- The kernel of a contact covector and the line spanned by its Reeb vector are complementary:
`V = ker a ⊕ K r`. -/
theorem IsContact.isCompl_ker_span_reebVector (h : a.IsContact B) :
    IsCompl (LinearMap.ker a) (K ∙ a.reebVector B) := by
  refine isCompl_ker_of_disjoint_of_ne_bot h.ne_zero ?_ (by simpa using h.reebVector_ne_zero)
  rw [Submodule.disjoint_def]
  rintro v hv hvr
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hvr
  rw [LinearMap.mem_ker, map_smul, h.apply_reebVector, smul_eq_mul, mul_one] at hv
  rw [hv, zero_smul]

/-- Rescaling a contact covector by a nonzero scalar `c` divides its Reeb vector by `c`. -/
theorem IsContact.reebVector_smul (h : a.IsContact B) {c : K} (hc : c ≠ 0) :
    (c • a).reebVector B = c⁻¹ • a.reebVector B := by
  refine (((isContact_smul_iff hc).2 h).eq_reebVector_iff.2 ⟨?_, fun w hw ↦ ?_⟩).symm
  · rw [LinearMap.smul_apply, map_smul, h.apply_reebVector, smul_eq_mul, smul_eq_mul, mul_one,
      mul_inv_cancel₀ hc]
  · rw [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc] at hw
    rw [map_smul, LinearMap.smul_apply, h.apply_reebVector_of_apply_eq_zero hw, smul_zero]

/-- **Rescaling law for the Reeb vector**, pointwise. Let `a` be contact for `B`, let `c ≠ 0`,
and let `B'` be a bilinear form with `B' v w = c B v w - l w a v` for `w ∈ ker a`. This is the
situation of the contact form `f α`, where `c = f x`, `l = df_x` and `B' = d(f α)_x`. Then the Reeb
vector of `c a` for `B'` is `c⁻¹ r + y`, where `r` is the Reeb vector of `a` for `B` and `y` is the
unique vector of `ker a` with `B y w = l w / c ^ 2` for all `w ∈ ker a`. -/
theorem IsContact.reebVector_smul_eq_inv_smul_add_iff (h : a.IsContact B) {c : K} (hc : c ≠ 0)
    {l : Module.Dual K V} (hB' : ∀ v w, a w = 0 → B' v w = c * B v w - l w * a v) (y : V) :
    (c • a).reebVector B' = c⁻¹ • a.reebVector B + y ↔
      a y = 0 ∧ ∀ w, a w = 0 → B y w = l w / c ^ 2 := by
  have h' : (c • a).IsContact B' := by
    rw [isContact_smul_iff hc, isContact_congr (B' := c • B) fun v w hv hw ↦ by
      rw [hB' v w hw, hv, mul_zero, sub_zero, LinearMap.smul_apply, LinearMap.smul_apply,
        smul_eq_mul]]
    exact (isContact_smul_bilinForm_iff hc).2 h
  have hker : ∀ w, (c • a) w = 0 ↔ a w = 0 := fun w ↦ by
    rw [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc]
  have hval : (c • a) (c⁻¹ • a.reebVector B + y) = 1 + c * a y := by
    rw [LinearMap.smul_apply, map_add, map_smul, h.apply_reebVector, smul_eq_mul, smul_eq_mul,
      mul_add, mul_one, mul_inv_cancel₀ hc]
  rw [eq_comm, h'.eq_reebVector_iff, hval, add_eq_left, mul_eq_zero, or_iff_right hc]
  refine and_congr_right fun hy ↦ forall_congr' fun w ↦ ?_
  rw [hker]
  refine imp_congr_right fun hw ↦ ?_
  simp only [hB' _ w hw, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hy,
    h.apply_reebVector, h.apply_reebVector_of_apply_eq_zero hw, smul_eq_mul, mul_zero, mul_one]
  have key : c⁻¹ * (0 - l w) + (c * B y w - 0) = (B y w * c ^ 2 - l w) / c := by
    field_simp
    ring
  rw [key, div_eq_zero_iff, or_iff_left hc, sub_eq_zero, eq_div_iff (pow_ne_zero 2 hc)]

section IsAlt

variable (hB : B.IsAlt)
include hB

/-- For an alternating `B`, the Reeb vector of a contact covector lies in the kernel of `B`:
`B r w = 0` for every `w`, not only for `w ∈ ker a`. -/
@[simp]
theorem IsContact.apply_reebVector_left (h : a.IsContact B) (w : V) :
    B (a.reebVector B) w = 0 := by
  have hw : a (w - a w • a.reebVector B) = 0 := by
    rw [map_sub, map_smul, h.apply_reebVector, smul_eq_mul, mul_one, sub_self]
  have := h.apply_reebVector_of_apply_eq_zero hw
  rwa [map_sub, map_smul, hB, smul_zero, sub_zero] at this

/-- For an alternating `B`, every vector is `B`-orthogonal to the Reeb vector from the left. -/
@[simp]
theorem IsContact.apply_reebVector_right (h : a.IsContact B) (w : V) :
    B w (a.reebVector B) = 0 := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq hB, h.apply_reebVector_left hB, neg_zero]

/-- For an alternating `B`, the Reeb vector of a contact covector lies in the kernel of `B`. -/
theorem IsContact.reebVector_mem_ker (h : a.IsContact B) : a.reebVector B ∈ LinearMap.ker B :=
  LinearMap.mem_ker.2 <| LinearMap.ext fun w ↦ by
    rw [h.apply_reebVector_left hB, LinearMap.zero_apply]

/-- For an alternating `B`, the Reeb vector of a contact covector is the unique vector `r` with
`a r = 1` and `B r = 0`. -/
theorem IsContact.eq_reebVector_iff_of_isAlt (h : a.IsContact B) {r : V} :
    r = a.reebVector B ↔ a r = 1 ∧ B r = 0 := by
  refine ⟨fun hr ↦ hr ▸ ⟨h.apply_reebVector, LinearMap.mem_ker.1 (h.reebVector_mem_ker hB)⟩,
    fun hr ↦ h.eq_reebVector_iff.2 ⟨hr.1, fun w _ ↦ by rw [hr.2, LinearMap.zero_apply]⟩⟩

/-- For an alternating `B`, the kernel of `B` is the line spanned by the Reeb vector of a contact
covector. -/
theorem IsContact.ker_eq_span_reebVector (h : a.IsContact B) :
    LinearMap.ker B = K ∙ a.reebVector B := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  refine ⟨fun hv ↦ ⟨a v, ?_⟩, ?_⟩
  · have hmem : v - a v • a.reebVector B ∈ LinearMap.ker a := by
      rw [LinearMap.mem_ker, map_sub, map_smul, h.apply_reebVector, smul_eq_mul, mul_one,
        sub_self]
    have := h.nondegenerate_restrict.1 ⟨_, hmem⟩ fun w ↦ by
      simp [hv, h.apply_reebVector_left hB]
    exact (sub_eq_zero.1 (congrArg Subtype.val this)).symm
  · rintro ⟨t, rfl⟩
    rw [map_smul, LinearMap.mem_ker.1 (h.reebVector_mem_ker hB), smul_zero]

end IsAlt

end Module.Dual
