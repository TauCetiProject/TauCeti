/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Nijenhuis
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# The operators `∂` and `∂bar` on an almost complex manifold

Let `J` be a smooth almost complex structure on a manifold `M` and let `F` be a complex normed
space. On a complex-valued smooth form `φ` of type `(p,q)`, the operators `∂` and `∂bar` of `J` are
the components of type `(p+1,q)` and `(p,q+1)` of the exterior derivative `dφ`; on an arbitrary
smooth form they are defined by additivity over its type decomposition. They are complex-linear,
raise the bidegree by `(1,0)` and `(0,1)`, are exchanged by complex conjugation of the
coefficients, and commute with pullback along smooth pseudoholomorphic maps.

On an almost complex manifold `d` has two further components, of bidegrees `(2,-1)` and
`(-1,2)`, so `d ≠ ∂ + ∂bar` in general and `∂`, `∂bar` need not square to zero. On functions
`d = ∂ + ∂bar` always holds, and the squares of `∂` and `∂bar` on functions are given by the
Nijenhuis tensor `N_J = TauCeti.SmoothAlmostComplexStructure.nijenhuis`:
`∂bar ∂bar f(v, w) = -∂f(N_J(v, w)) / 4` and `∂∂f(v, w) = -∂bar f(N_J(v, w)) / 4`. These are the
evaluations of the components `∂bar ∂bar f` and `∂∂f` of `d²f = 0`, by the formulas of
`TauCeti.Geometry.Manifold.DifferentialForm.Nijenhuis` for the components of bidegree `(-1,2)`
and `(2,-1)` of `d` on one-forms. The component of type `(1,1)` of `d²f = 0` gives
`∂ ∂bar f + ∂bar ∂f = 0` on every almost complex manifold. When `N_J = 0`, `∂² = 0` and
`∂bar² = 0` on functions and `d = ∂ + ∂bar` on one-forms.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.del`, `TauCeti.SmoothAlmostComplexStructure.delBar`: the
  operators `∂` and `∂bar` on complex-valued smooth forms.
* `TauCeti.SmoothForm.IsOfType.del_eq`, `TauCeti.SmoothForm.IsOfType.delBar_eq`: on a form of type
  `(p,q)`, they are the type-`(p+1,q)` and type-`(p,q+1)` components of `d`.
* `TauCeti.SmoothForm.IsOfType.mextDerivₗ_eq_add_del_add_delBar_add`: the four bidegrees of `d`.
* `TauCeti.SmoothAlmostComplexStructure.delBar_delBar_apply`,
  `TauCeti.SmoothAlmostComplexStructure.del_del_apply`: the squares of `∂bar` and `∂` on functions
  through the Nijenhuis tensor.
* `TauCeti.SmoothAlmostComplexStructure.del_delBar_add_delBar_del`: `∂ ∂bar f + ∂bar ∂f = 0`.
* `TauCeti.SmoothAlmostComplexStructure.mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero`:
  `d = ∂ + ∂bar` on one-forms when `N_J = 0`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.3 and 2.6.
-/

public section

noncomputable section

open scoped Manifold ContDiff ComplexConjugate

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

namespace TauCeti

/-! ### The operators `∂` and `∂bar` -/

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- The operator `∂` of an almost complex structure `J` on complex-valued smooth `k`-forms. On a
form of type `(p,q)` it is the type-`(p+1,q)` component of the exterior derivative, and it is
additive over the type decomposition. -/
def del : SmoothForm I M F k →ₗ[ℂ] SmoothForm I M F (k + 1) where
  toFun φ := ∑ pq ∈ Finset.antidiagonal k,
    J.typeProjection (pq.1 + 1) pq.2 (mextDerivₗ I k (J.typeProjection pq.1 pq.2 φ))
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' c φ := by simp [Finset.smul_sum]

/-- The operator `∂bar` of an almost complex structure `J` on complex-valued smooth `k`-forms. On a
form of type `(p,q)` it is the type-`(p,q+1)` component of the exterior derivative, and it is
additive over the type decomposition. -/
def delBar : SmoothForm I M F k →ₗ[ℂ] SmoothForm I M F (k + 1) where
  toFun φ := ∑ pq ∈ Finset.antidiagonal k,
    J.typeProjection pq.1 (pq.2 + 1) (mextDerivₗ I k (J.typeProjection pq.1 pq.2 φ))
  map_add' φ ψ := by simp [Finset.sum_add_distrib]
  map_smul' c φ := by simp [Finset.smul_sum]

/-- `∂φ` is the sum over all types `(p,q)` of the type-`(p+1,q)` component of the exterior
derivative of the type-`(p,q)` component of `φ`. -/
theorem del_apply (φ : SmoothForm I M F k) :
    J.del φ = ∑ pq ∈ Finset.antidiagonal k,
      J.typeProjection (pq.1 + 1) pq.2 (mextDerivₗ I k (J.typeProjection pq.1 pq.2 φ)) :=
  (rfl)

/-- `∂bar φ` is the sum over all types `(p,q)` of the type-`(p,q+1)` component of the exterior
derivative of the type-`(p,q)` component of `φ`. -/
theorem delBar_apply (φ : SmoothForm I M F k) :
    J.delBar φ = ∑ pq ∈ Finset.antidiagonal k,
      J.typeProjection pq.1 (pq.2 + 1) (mextDerivₗ I k (J.typeProjection pq.1 pq.2 φ)) :=
  (rfl)

end SmoothAlmostComplexStructure

namespace SmoothForm

open SmoothAlmostComplexStructure

variable {J : SmoothAlmostComplexStructure I M} {φ : SmoothForm I M F k} {p q : ℕ}

/-- On a smooth form of type `(p,q)`, `∂` is the type-`(p+1,q)` component of the exterior
derivative. -/
theorem IsOfType.del_eq (h : φ.IsOfType J p q) :
    J.del φ = J.typeProjection (p + 1) q (mextDerivₗ I k φ) := by
  rw [del_apply]
  exact h.sum_typeProjection_eq (fun pq ψ ↦ J.typeProjection (pq.1 + 1) pq.2 (mextDerivₗ I k ψ))
    fun _ ↦ by simp

/-- On a smooth form of type `(p,q)`, `∂bar` is the type-`(p,q+1)` component of the exterior
derivative. -/
theorem IsOfType.delBar_eq (h : φ.IsOfType J p q) :
    J.delBar φ = J.typeProjection p (q + 1) (mextDerivₗ I k φ) := by
  rw [delBar_apply]
  exact h.sum_typeProjection_eq (fun pq ψ ↦ J.typeProjection pq.1 (pq.2 + 1) (mextDerivₗ I k ψ))
    fun _ ↦ by simp

/-- `∂` maps smooth forms of type `(p,q)` to smooth forms of type `(p+1,q)`. -/
theorem IsOfType.del (h : φ.IsOfType J p q) : (J.del φ).IsOfType J (p + 1) q := by
  rw [h.del_eq]
  exact J.isOfType_typeProjection (by rw [← h.add_eq]; ring) _

/-- `∂bar` maps smooth forms of type `(p,q)` to smooth forms of type `(p,q+1)`. -/
theorem IsOfType.delBar (h : φ.IsOfType J p q) : (J.delBar φ).IsOfType J p (q + 1) := by
  rw [h.delBar_eq]
  exact J.isOfType_typeProjection (by rw [← h.add_eq]; ring) _

/-- **The four bidegrees of `d`.** The exterior derivative of a smooth form of type `(p,q)` is the
sum of its components of types `(p+2,q-1)` and `(p-1,q+2)` and of `∂φ` and `∂bar φ`. -/
theorem IsOfType.mextDerivₗ_eq_add_del_add_delBar_add (h : φ.IsOfType J p q) :
    mextDerivₗ I k φ =
      J.typeProjection (p + 2) (q - 1) (mextDerivₗ I k φ) + J.del φ + J.delBar φ +
        J.typeProjection (p - 1) (q + 2) (mextDerivₗ I k φ) := by
  rw [h.del_eq, h.delBar_eq]
  exact h.mextDerivₗ_eq_typeProjection_add

end SmoothForm

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-! ### Type components of `∂` and `∂bar` -/

/-- The type-`(p+1,q)` component of `∂φ` is `∂` of the type-`(p,q)` component of `φ`. -/
theorem typeProjection_del (p q : ℕ) (φ : SmoothForm I M F k) :
    J.typeProjection (p + 1) q (J.del φ) = J.del (J.typeProjection p q φ) := by
  by_cases hpq : p + q = k
  · conv_lhs => rw [← J.sum_typeProjection φ]
    rw [map_sum, map_sum, Finset.sum_eq_single (p, q)]
    · exact (J.isOfType_typeProjection hpq φ).del.typeProjection_self
    · intro pq hmem hne
      have h := J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hmem) φ
      refine h.del.typeProjection_of_ne ?_
      simpa [Prod.ext_iff, eq_comm] using hne
    · exact fun h ↦ absurd (Finset.mem_antidiagonal.2 hpq) h
  · simp [J.typeProjection_eq_zero hpq,
      J.typeProjection_eq_zero (show p + 1 + q ≠ k + 1 by omega)]

/-- The type-`(p,q+1)` component of `∂bar φ` is `∂bar` of the type-`(p,q)` component of `φ`. -/
theorem typeProjection_delBar (p q : ℕ) (φ : SmoothForm I M F k) :
    J.typeProjection p (q + 1) (J.delBar φ) = J.delBar (J.typeProjection p q φ) := by
  by_cases hpq : p + q = k
  · conv_lhs => rw [← J.sum_typeProjection φ]
    rw [map_sum, map_sum, Finset.sum_eq_single (p, q)]
    · exact (J.isOfType_typeProjection hpq φ).delBar.typeProjection_self
    · intro pq hmem hne
      have h := J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hmem) φ
      refine h.delBar.typeProjection_of_ne ?_
      simpa [Prod.ext_iff, eq_comm] using hne
    · exact fun h ↦ absurd (Finset.mem_antidiagonal.2 hpq) h
  · simp [J.typeProjection_eq_zero hpq,
      J.typeProjection_eq_zero (show p + (q + 1) ≠ k + 1 by omega)]

/-- `∂φ` has no component of type `(0,q)`. -/
@[simp]
theorem typeProjection_zero_left_del_eq_zero (q : ℕ) (φ : SmoothForm I M F k) :
    J.typeProjection 0 q (J.del φ) = 0 := by
  conv_lhs => rw [← J.sum_typeProjection φ]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun pq hmem ↦ ?_
  exact (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hmem) φ).del.typeProjection_of_ne
    (by simp)

/-- `∂bar φ` has no component of type `(p,0)`. -/
@[simp]
theorem typeProjection_zero_right_delBar_eq_zero (p : ℕ) (φ : SmoothForm I M F k) :
    J.typeProjection p 0 (J.delBar φ) = 0 := by
  conv_lhs => rw [← J.sum_typeProjection φ]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun pq hmem ↦ ?_
  exact (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hmem) φ).delBar.typeProjection_of_ne
    (by simp)

/-! ### Coefficient maps and pullback -/

section MapCoeff

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {L : F →L[ℝ] G}

/-- A complex-linear coefficient map commutes with `∂`. -/
theorem mapCoeff_del (hL : ∀ (c : ℂ) v, L (c • v) = c • L v) (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.del φ) = J.del (SmoothForm.mapCoeff L φ) := by
  simp only [del_apply, map_sum, J.mapCoeff_typeProjection hL, ← SmoothForm.mextDerivₗ_mapCoeff]

/-- A complex-linear coefficient map commutes with `∂bar`. -/
theorem mapCoeff_delBar (hL : ∀ (c : ℂ) v, L (c • v) = c • L v) (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.delBar φ) = J.delBar (SmoothForm.mapCoeff L φ) := by
  simp only [delBar_apply, map_sum, J.mapCoeff_typeProjection hL, ← SmoothForm.mextDerivₗ_mapCoeff]

/-- A conjugate-linear coefficient map, such as complex conjugation, turns `∂` into `∂bar`. -/
theorem mapCoeff_del_of_map_smul_conj (hL : ∀ (c : ℂ) v, L (c • v) = conj c • L v)
    (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.del φ) = J.delBar (SmoothForm.mapCoeff L φ) := by
  simp only [del_apply, delBar_apply, map_sum, J.mapCoeff_typeProjection_of_map_smul_conj hL,
    ← SmoothForm.mextDerivₗ_mapCoeff]
  exact Finset.Nat.sum_antidiagonal_swap (f := fun pq ↦
    J.typeProjection pq.1 (pq.2 + 1)
      (mextDerivₗ I k (J.typeProjection pq.1 pq.2 (SmoothForm.mapCoeff L φ))))

/-- A conjugate-linear coefficient map, such as complex conjugation, turns `∂bar` into `∂`. -/
theorem mapCoeff_delBar_of_map_smul_conj (hL : ∀ (c : ℂ) v, L (c • v) = conj c • L v)
    (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.delBar φ) = J.del (SmoothForm.mapCoeff L φ) := by
  simp only [del_apply, delBar_apply, map_sum, J.mapCoeff_typeProjection_of_map_smul_conj hL,
    ← SmoothForm.mextDerivₗ_mapCoeff]
  exact Finset.Nat.sum_antidiagonal_swap (f := fun pq ↦
    J.typeProjection (pq.1 + 1) pq.2
      (mextDerivₗ I k (J.typeProjection pq.1 pq.2 (SmoothForm.mapCoeff L φ))))

end MapCoeff

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {J' : SmoothAlmostComplexStructure I' M'} {u : M → M'}

/-- Pullback along a smooth pseudoholomorphic map commutes with `∂`. -/
theorem mpullback_del (hu : ContMDiff I I' ∞ u) (hJ : IsPseudoholomorphic J J' u)
    (φ : SmoothForm I' M' F k) :
    SmoothForm.mpullback u hu (J'.del φ) = J.del (SmoothForm.mpullback u hu φ) := by
  simp only [del_apply, map_sum, mpullback_typeProjection hu hJ, ← SmoothForm.mextDerivₗ_mpullback]

/-- Pullback along a smooth pseudoholomorphic map commutes with `∂bar`. -/
theorem mpullback_delBar (hu : ContMDiff I I' ∞ u) (hJ : IsPseudoholomorphic J J' u)
    (φ : SmoothForm I' M' F k) :
    SmoothForm.mpullback u hu (J'.delBar φ) = J.delBar (SmoothForm.mpullback u hu φ) := by
  simp only [delBar_apply, map_sum, mpullback_typeProjection hu hJ,
    ← SmoothForm.mextDerivₗ_mpullback]

end Pullback

/-! ### Functions -/

/-- On functions, `d = ∂ + ∂bar`. -/
theorem del_add_delBar_eq_mextDerivₗ (f : SmoothForm I M F 0) :
    J.del f + J.delBar f = mextDerivₗ I 0 f := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.del_eq, hf.delBar_eq]
  exact J.typeProjection_one_zero_add_zero_one _

/-- On functions, the exterior derivative of `∂bar f` is minus that of `∂f`. -/
private theorem mextDerivₗ_delBar (f : SmoothForm I M F 0) :
    mextDerivₗ I 1 (J.delBar f) = -mextDerivₗ I 1 (J.del f) := by
  rw [eq_neg_iff_add_eq_zero, ← map_add, add_comm (J.delBar f), del_add_delBar_eq_mextDerivₗ,
    ← LinearMap.comp_apply, mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply]

/-- On every almost complex manifold, `∂ ∂bar f + ∂bar ∂f = 0` for functions `f`. This is the
type-`(1,1)` component of `d²f = 0`. -/
theorem del_delBar_add_delBar_del (f : SmoothForm I M F 0) :
    J.del (J.delBar f) + J.delBar (J.del f) = 0 := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.delBar.del_eq, hf.del.delBar_eq, mextDerivₗ_delBar, map_neg, neg_add_cancel]

variable [FiniteDimensional ℝ E]

/-- **`∂bar²` on functions is the Nijenhuis tensor.** For a smooth function `f`,
`∂bar ∂bar f(v, w) = -∂f(N_J(v, w)) / 4`. -/
theorem delBar_delBar_apply (f : SmoothForm I M F 0) (x : M) (v w : TangentSpace I x) :
    (J.delBar (J.delBar f)).1 x ![v, w] = -(4 : ℂ)⁻¹ • (J.del f).1 x ![J.nijenhuis x v w] := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.delBar.delBar_eq, mextDerivₗ_delBar, map_neg, SmoothForm.neg_toRoughForm, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, neg_smul]
  exact congrArg Neg.neg (hf.del.typeProjection_zero_two_mextDerivₗ_apply x v w)

/-- **`∂²` on functions is the Nijenhuis tensor.** For a smooth function `f`,
`∂∂f(v, w) = -∂bar f(N_J(v, w)) / 4`. -/
theorem del_del_apply (f : SmoothForm I M F 0) (x : M) (v w : TangentSpace I x) :
    (J.del (J.del f)).1 x ![v, w] = -(4 : ℂ)⁻¹ • (J.delBar f).1 x ![J.nijenhuis x v w] := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.del.del_eq, ← neg_eq_iff_eq_neg.2 (mextDerivₗ_delBar J f), map_neg,
    SmoothForm.neg_toRoughForm, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, neg_smul]
  exact congrArg Neg.neg (hf.delBar.typeProjection_two_zero_mextDerivₗ_apply x v w)

/-- If the Nijenhuis tensor vanishes, `∂bar ∂bar f = 0` for every smooth function `f`. -/
theorem delBar_delBar_eq_zero_of_nijenhuis_eq_zero (hJ : J.nijenhuis = 0)
    (f : SmoothForm I M F 0) : J.delBar (J.delBar f) = 0 := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.delBar.delBar_eq, mextDerivₗ_delBar, map_neg,
    hf.del.typeProjection_zero_two_mextDerivₗ_eq_zero hJ, neg_zero]

/-- If the Nijenhuis tensor vanishes, `∂∂f = 0` for every smooth function `f`. -/
theorem del_del_eq_zero_of_nijenhuis_eq_zero (hJ : J.nijenhuis = 0)
    (f : SmoothForm I M F 0) : J.del (J.del f) = 0 := by
  have hf := SmoothForm.isOfType_zero_zero f J
  rw [hf.del.del_eq, ← neg_eq_iff_eq_neg.2 (mextDerivₗ_delBar J f), map_neg,
    hf.delBar.typeProjection_two_zero_mextDerivₗ_eq_zero hJ, neg_zero]

/-! ### One-forms -/

/-- If the Nijenhuis tensor vanishes, `d = ∂ + ∂bar` on smooth one-forms. -/
theorem mextDerivₗ_eq_del_add_delBar_of_nijenhuis_eq_zero (hJ : J.nijenhuis = 0)
    (α : SmoothForm I M F 1) : mextDerivₗ I 1 α = J.del α + J.delBar α := by
  have h₁₀ := J.isOfType_typeProjection (F := F) (k := 1) (p := 1) (q := 0) rfl α
  have h₀₁ := J.isOfType_typeProjection (F := F) (k := 1) (p := 0) (q := 1) rfl α
  rw [← J.typeProjection_one_zero_add_zero_one α, map_add, map_add, map_add,
    h₁₀.mextDerivₗ_eq_add_del_add_delBar_add,
    h₀₁.mextDerivₗ_eq_add_del_add_delBar_add, h₁₀.typeProjection_zero_two_mextDerivₗ_eq_zero hJ,
    h₀₁.typeProjection_two_zero_mextDerivₗ_eq_zero hJ]
  simp only [Nat.reduceAdd, Nat.zero_sub, J.typeProjection_eq_zero (show 3 + 0 ≠ 2 by omega),
    J.typeProjection_eq_zero (show 0 + 3 ≠ 2 by omega), LinearMap.zero_apply, zero_add, add_zero]
  abel

end SmoothAlmostComplexStructure

end TauCeti
