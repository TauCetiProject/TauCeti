/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproximationDomain
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MixedImage
public import TauCeti.NumberTheory.NumberField.FinitePlace.ValueFloor

import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ModuleCovolume
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Volume and covolume of approximation domains

An approximation domain `TauCeti.NumberField.approxDomain S₀ L c Q` in `ι → K` separates into a
finite-place `𝓞 K`-submodule `TauCeti.NumberField.approxModule S₀ L c Q` and an infinite-place
convex body `TauCeti.NumberField.approxBody L c Q` in `ι → mixedSpace K`. When the linear forms
`L v` are linearly independent at every infinite place and every `v ∈ S₀`, and `0 < Q`, the mixed
image of `approxModule` is a full `ℤ`-lattice in `ι → mixedSpace K` and `approxBody` is a compact
symmetric convex neighbourhood of the origin. Geometry-of-numbers arguments on `approxDomain` hinge
on comparing the Lebesgue volume of the body with the covolume of the lattice as `Q` grows.

At the infinite places, `approxBody L c Q` is the preimage of a product of closed-ball boxes in
`mixedSpace K` under a single `mixedSpace K`-linear endomorphism of `ι → mixedSpace K` whose
`(i, j)` entry collects the `w`-embeddings of `L w i (Pi.basisFun K ι j)`. By
`LinearMap.det_restrictScalars`, its real determinant is the `ℝ`-algebra norm of its `mixedSpace K`
determinant, with absolute value `∏ w, w (det (L w)) ^ w.mult`, giving an exact volume formula with
no coordinate splitting place by place.

At the finite places, a real bound `Q ^ c v i` need not lie in the discrete value group of `v`, so
the condition `v (L v i x) ≤ Q ^ c v i` is equivalent to `v (L v i x) ≤ v.floorValue (Q ^ c v i)`.
Evaluating `Submodule.covolume_mixedImage` place by place shows that the largest value of `v` on
determinants of `card ι` vectors of `approxModule` is `1` outside `S₀` and
`v (det (L v))⁻¹ * ∏ i, v.floorValue (Q ^ c v i)` on `S₀`. Consequently, the covolume is an exact
product in the rounded bounds `v.floorValue (Q ^ c v i)`, whereas passing to the unrounded real
powers `Q ^ c v i` loses at most a factor of `∏ v ∈ S₀, N 𝔭_v ^ card ι`. At the `2`-adic place of
`ℚ` in one variable with `L = id`, `c = 1` and `Q = 3 / 2`, the module is `ℤ` of covolume `1`
rather than `(3 / 2)⁻¹ = 2 / 3`.

No public declaration in this file assumes `DecidableEq ι`: determinants of families of linear forms
on `ι → K` are written as `LinearMap.det (LinearMap.pi (L v))`.

## Main definitions

* `TauCeti.NumberField.approxWeight S₀ c`: the weight
  `∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ S₀, ∑ i, c v.1 i`, the total exponent of
  `Q` across all local bounds.
* `TauCeti.NumberField.approxAbsWeight S₀ c`: the absolute weight, the same sum over `|c v.1 i|`.
* `TauCeti.NumberField.approxConst S₀ L`: the `Q`-independent leading constant in the
  volume-to-covolume ratio, namely `2 ^ (r₁ · card ι) · π ^ (r₂ · card ι)` divided by
  `covol (𝓞 K) ^ card ι` and the local determinants at all infinite places and at `S₀`.

## Main results

* `TauCeti.NumberField.rpow_approxWeight`: for `0 < Q`, `Q ^ approxWeight S₀ c` equals the product
  of `(∏ i, Q ^ c v.1 i) ^ v.mult` over infinite places times `∏ v ∈ S₀, ∏ i, Q ^ c v.1 i`.
* `TauCeti.NumberField.discreteTopology_mixedImage_approxModule` and
  `TauCeti.NumberField.isZLattice_mixedImage_approxModule`: the mixed image of `approxModule` is
  discrete when the forms at `S₀` are linearly independent, and a full `ℤ`-lattice when also
  `Q ≠ 0`.
* `TauCeti.NumberField.covolume_approxLattice`: for `0 < Q`, the covolume of
  `(approxModule S₀ L c Q).mixedImage` is
  `(∏ v ∈ S₀, v (det (L v)) * ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) * covol (𝓞 K) ^ card ι`.
* `TauCeti.NumberField.volume_approxBody` and `TauCeti.NumberField.volume_real_approxBody`: the
  `ℝ≥0∞`- and `ℝ`-valued volumes of `approxBody L c Q`.
* `TauCeti.NumberField.approxConst_eq_discr`: `approxConst S₀ L` expressed in terms of `discr K`.
* `TauCeti.NumberField.volume_div_covolume_eq` and `TauCeti.NumberField.volume_div_covolume_empty`:
  the exact ratio `vol (approxBody) / covol (approxModule.mixedImage)` in terms of `floorValue`,
  specializing when `S₀ = ∅` to `approxConst ∅ L * Q ^ approxWeight ∅ c`.
* `TauCeti.NumberField.volume_div_covolume_le` and `TauCeti.NumberField.le_volume_div_covolume`:
  two-sided comparison of `vol (approxBody) / covol (approxModule.mixedImage)` with
  `Q ^ approxWeight S₀ c`, sharp up to `∏ v ∈ S₀, N 𝔭_v ^ card ι`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.6, Lemma 7.5.7 and Corollary 7.5.8.
* The statements and proof architecture follow Ralf Stephan's
  `DiophantineApproximation/ApproximationVolume.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

noncomputable section

open MeasureTheory Module NNReal NumberField NumberField.mixedEmbedding
open NumberField.InfinitePlace
open scoped ENNReal Matrix

namespace TauCeti.NumberField

/-! ### Weights of exponent families -/

section Weight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **The weight of an exponent family** on `S₀` and the infinite places (Bombieri–Gubler 7.5.6):
the total exponent `∑ v : InfinitePlace K, v.mult * ∑ i, c v.1 i + ∑ v ∈ S₀, ∑ i, c v.1 i` of `Q`
in the product of all local bounds of `approxDomain S₀ L c Q`. -/
def approxWeight (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) : ℝ :=
  ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, c v.1 i + ∑ v ∈ S₀, ∑ i, c v.1 i

/-- **The absolute weight of an exponent family** on `S₀` and the infinite places: the weight of
`fun v i ↦ |c v i|`. -/
def approxAbsWeight (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) : ℝ :=
  ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, |c v.1 i| + ∑ v ∈ S₀, ∑ i, |c v.1 i|

/-- Explicit sum formula for `approxWeight`. -/
theorem approxWeight_def (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight S₀ c =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, c v.1 i + ∑ v ∈ S₀, ∑ i, c v.1 i := by
  rfl

/-- Explicit sum formula for `approxAbsWeight`. -/
theorem approxAbsWeight_def (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxAbsWeight S₀ c =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ i, |c v.1 i| + ∑ v ∈ S₀, ∑ i, |c v.1 i| := by
  rfl

/-- The absolute weight is the weight of the pointwise absolute value of `c`. -/
theorem approxAbsWeight_eq_approxWeight_abs (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxAbsWeight S₀ c = approxWeight S₀ fun v i ↦ |c v i| := by
  rfl

/-- The weight of the zero exponent family is `0`. -/
@[simp]
theorem approxWeight_zero (S₀ : Finset (FinitePlace K)) :
    approxWeight S₀ (0 : AbsoluteValue K ℝ → ι → ℝ) = 0 := by
  simp [approxWeight]

/-- The absolute weight of the zero exponent family is `0`. -/
@[simp]
theorem approxAbsWeight_zero (S₀ : Finset (FinitePlace K)) :
    approxAbsWeight S₀ (0 : AbsoluteValue K ℝ → ι → ℝ) = 0 := by
  simp [approxAbsWeight]

/-- Over an empty index type, `approxWeight` vanishes. -/
@[simp]
theorem approxWeight_isEmpty [IsEmpty ι] (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) : approxWeight S₀ c = 0 := by
  simp [approxWeight]

/-- Over an empty index type, `approxAbsWeight` vanishes. -/
@[simp]
theorem approxAbsWeight_isEmpty [IsEmpty ι] (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) : approxAbsWeight S₀ c = 0 := by
  simp [approxAbsWeight]

/-- `approxWeight S₀ c` depends on `c` only at the infinite places and the places of `S₀`. -/
theorem approxWeight_congr {S₀ : Finset (FinitePlace K)} {c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ}
    (hInf : ∀ (v : InfinitePlace K) (i : ι), c₁ v.1 i = c₂ v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : ι, c₁ v.1 i = c₂ v.1 i) :
    approxWeight S₀ c₁ = approxWeight S₀ c₂ := by
  rw [approxWeight, approxWeight]
  congr 1
  · exact Finset.sum_congr rfl fun v _ ↦ by simp_rw [hInf v]
  · exact Finset.sum_congr rfl fun v hv ↦ Finset.sum_congr rfl fun i _ ↦ hFin v hv i

/-- `approxAbsWeight S₀ c` depends on `c` only at the infinite places and the places of `S₀`. -/
theorem approxAbsWeight_congr {S₀ : Finset (FinitePlace K)} {c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ}
    (hInf : ∀ (v : InfinitePlace K) (i : ι), c₁ v.1 i = c₂ v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : ι, c₁ v.1 i = c₂ v.1 i) :
    approxAbsWeight S₀ c₁ = approxAbsWeight S₀ c₂ := by
  rw [approxAbsWeight_eq_approxWeight_abs, approxAbsWeight_eq_approxWeight_abs]
  exact approxWeight_congr (fun v i ↦ congrArg abs (hInf v i))
    fun v hv i ↦ congrArg abs (hFin v hv i)

/-- `approxWeight S₀` is additive in the exponent family. -/
theorem approxWeight_add (S₀ : Finset (FinitePlace K)) (c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight S₀ (c₁ + c₂) = approxWeight S₀ c₁ + approxWeight S₀ c₂ := by
  simp only [approxWeight, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  ring

/-- `approxWeight S₀` commutes with negation. -/
@[simp]
theorem approxWeight_neg (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight S₀ (-c) = -approxWeight S₀ c := by
  simp only [approxWeight, Pi.neg_apply, Finset.sum_neg_distrib, mul_neg]
  ring

/-- `approxWeight S₀` commutes with subtraction. -/
theorem approxWeight_sub (S₀ : Finset (FinitePlace K)) (c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight S₀ (c₁ - c₂) = approxWeight S₀ c₁ - approxWeight S₀ c₂ := by
  rw [sub_eq_add_neg, approxWeight_add, approxWeight_neg, sub_eq_add_neg]

/-- `approxWeight S₀` is homogeneous with respect to real scalar multiplication. -/
theorem approxWeight_smul (S₀ : Finset (FinitePlace K)) (r : ℝ)
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxWeight S₀ (r • c) = r * approxWeight S₀ c := by
  simp only [approxWeight, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_add]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

/-- `approxAbsWeight S₀` is invariant under negation. -/
@[simp]
theorem approxAbsWeight_neg (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxAbsWeight S₀ (-c) = approxAbsWeight S₀ c := by
  simp [approxAbsWeight]

/-- `approxAbsWeight S₀` scales by `|r|` under scalar multiplication by `r`. -/
theorem approxAbsWeight_smul (S₀ : Finset (FinitePlace K)) (r : ℝ)
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    approxAbsWeight S₀ (r • c) = |r| * approxAbsWeight S₀ c := by
  simp_rw [approxAbsWeight_eq_approxWeight_abs, Pi.smul_apply, smul_eq_mul, abs_mul,
    ← approxWeight_smul]
  rfl

/-- `approxWeight S₀` is monotone with respect to pointwise inequalities at the infinite places and
`S₀`. -/
theorem approxWeight_mono {S₀ : Finset (FinitePlace K)} {c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ}
    (hInf : ∀ (v : InfinitePlace K) (i : ι), c₁ v.1 i ≤ c₂ v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : ι, c₁ v.1 i ≤ c₂ v.1 i) :
    approxWeight S₀ c₁ ≤ approxWeight S₀ c₂ := by
  rw [approxWeight, approxWeight]
  refine add_le_add (Finset.sum_le_sum fun v _ ↦ ?_)
    (Finset.sum_le_sum fun v hv ↦ Finset.sum_le_sum fun i _ ↦ hFin v hv i)
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hInf v i) (Nat.cast_nonneg _)

/-- `approxWeight S₀ c` is nonnegative when `c` is nonnegative at the infinite places and `S₀`. -/
theorem approxWeight_nonneg {S₀ : Finset (FinitePlace K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    (hInf : ∀ (v : InfinitePlace K) (i : ι), 0 ≤ c v.1 i)
    (hFin : ∀ v ∈ S₀, ∀ i : ι, 0 ≤ c v.1 i) : 0 ≤ approxWeight S₀ c := by
  simpa using approxWeight_mono (c₁ := 0) hInf hFin

/-- `approxAbsWeight S₀ c` is always nonnegative. -/
theorem approxAbsWeight_nonneg (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    0 ≤ approxAbsWeight S₀ c := by
  rw [approxAbsWeight_eq_approxWeight_abs]
  exact approxWeight_nonneg (fun _ _ ↦ abs_nonneg _) fun _ _ _ ↦ abs_nonneg _

/-- The absolute value of `approxWeight S₀ c` is bounded by `approxAbsWeight S₀ c`. -/
theorem abs_approxWeight_le_approxAbsWeight (S₀ : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    |approxWeight S₀ c| ≤ approxAbsWeight S₀ c := by
  rw [abs_le, approxAbsWeight_eq_approxWeight_abs, ← approxWeight_neg]
  exact ⟨approxWeight_mono (fun _ _ ↦ neg_abs_le _) fun _ _ _ ↦ neg_abs_le _,
    approxWeight_mono (fun _ _ ↦ le_abs_self _) fun _ _ _ ↦ le_abs_self _⟩

/-- Triangle inequality for `approxAbsWeight S₀`. -/
theorem approxAbsWeight_add_le (S₀ : Finset (FinitePlace K)) (c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ) :
    approxAbsWeight S₀ (c₁ + c₂) ≤ approxAbsWeight S₀ c₁ + approxAbsWeight S₀ c₂ := by
  rw [approxAbsWeight_eq_approxWeight_abs, approxAbsWeight_eq_approxWeight_abs S₀ c₁,
    approxAbsWeight_eq_approxWeight_abs S₀ c₂, ← approxWeight_add]
  exact approxWeight_mono (fun _ _ ↦ abs_add_le _ _) fun _ _ _ ↦ abs_add_le _ _

/-- **A positive level raised to `approxWeight` splits into the local bounds.** -/
theorem rpow_approxWeight (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 < Q) :
    Q ^ approxWeight S₀ c =
      (∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult) *
        ∏ v ∈ S₀, ∏ i, Q ^ c v.1 i := by
  rw [approxWeight, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [mul_comm, Real.rpow_mul hQ.le, Real.rpow_natCast, Real.rpow_sum_of_pos hQ]
  · exact Finset.prod_congr rfl fun v _ ↦ Real.rpow_sum_of_pos hQ _ _

end Weight

/-! ### Lattice structure and covolume of the finite-place module -/

section Covolume

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- When the forms at `S₀` are linearly independent, the mixed image of `approxModule S₀ L c Q` is
discrete in `ι → mixedSpace K`. -/
theorem discreteTopology_mixedImage_approxModule [Finite ι] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) :
    DiscreteTopology (approxModule S₀ L c Q).mixedImage :=
  Submodule.discreteTopology_mixedImage_iff.mpr (fg_approxModule hL c Q)

variable [Fintype ι]

open scoped Classical in
/-- When the forms at `S₀` are linearly independent and `Q ≠ 0`, the mixed image of
`approxModule S₀ L c Q` is a full `ℤ`-lattice in `ι → mixedSpace K`. -/
theorem isZLattice_mixedImage_approxModule {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0) :
    haveI := discreteTopology_mixedImage_approxModule hL c Q
    IsZLattice ℝ (approxModule S₀ L c Q).mixedImage :=
  letI := discreteTopology_mixedImage_approxModule hL c Q
  Submodule.isZLattice_mixedImage (span_approxModule_eq_top S₀ L c hQ)

/-- Ultrametric column-product bound on the determinant of a matrix at a finite place. -/
private theorem apply_det_le_prod [DecidableEq ι] (v : FinitePlace K) (M : Matrix ι ι K)
    {b : ι → ℝ} (hM : ∀ i j, v (M i j) ≤ b j) : v M.det ≤ ∏ j, b j := by
  rw [Matrix.det_apply]
  obtain ⟨σ, -, hσ⟩ := IsNonarchimedean.finset_image_add_of_nonempty _
    (fun y z ↦ v.add_le y z) (Finset.univ_nonempty (α := Equiv.Perm ι))
  refine hσ.trans ?_
  have hsign (y : K) : v (Equiv.Perm.sign σ • y) = v y := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hsign, map_prod]
  gcongr with j
  exact hM (σ j) j

omit [NumberField K] in
/-- Matrix representation of `(L u i (x k))_{k, i}` as `Matrix.of x * (toMatrix' (pi (L u)))ᵀ`. -/
private theorem matrix_apply_forms_eq_mul_transpose [DecidableEq ι]
    (l : ι → Dual K (ι → K)) (x : ι → ι → K) :
    Matrix.of (fun k i ↦ l i (x k)) = Matrix.of x * (LinearMap.toMatrix' (LinearMap.pi l))ᵀ := by
  ext k i
  conv_lhs => rw [Matrix.of_apply, ← (Pi.basisFun K ι).sum_repr (x k), map_sum]
  simp [Matrix.mul_apply, LinearMap.toMatrix'_apply]

/-- Outside `S₀`, the largest value of `v` on the determinants of `card ι` vectors of
`approxModule S₀ L c Q` is `1`. -/
private theorem isGreatest_apply_det_approxModule_of_notMem [DecidableEq ι]
    {S₀ : Finset (FinitePlace K)} (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0) {v : FinitePlace K} (hv : v ∉ S₀) :
    IsGreatest ((fun x : ι → ι → K ↦ v (Matrix.of x).det) ''
      Set.univ.pi fun _ ↦ (approxModule S₀ L c Q : Set (ι → K))) 1 := by
  have hQc (w : FinitePlace K) (i : ι) : 0 < |Q| ^ c w.1 i :=
    Real.rpow_pos_of_pos (abs_pos.mpr hQ) _
  set S : FinitePlace K → ℝ := fun w ↦ ∑ i, ∑ j, w (L w.1 i (Pi.basisFun K ι j)) / |Q| ^ c w.1 i
  have hS0 (w : FinitePlace K) : 0 ≤ S w :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      div_nonneg (apply_nonneg _ _) (hQc w i).le
  have hS (w : FinitePlace K) (i j : ι) :
      w (L w.1 i (Pi.basisFun K ι j)) ≤ S w * |Q| ^ c w.1 i := by
    rw [← div_le_iff₀ (hQc w i)]
    refine (Finset.single_le_sum (f := fun j ↦ w (L w.1 i (Pi.basisFun K ι j)) / |Q| ^ c w.1 i)
      (fun _ _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum
      (f := fun i ↦ ∑ j, w (L w.1 i (Pi.basisFun K ι j)) / |Q| ^ c w.1 i)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le)
      (Finset.mem_univ i)
  obtain ⟨d, hdv, hdS⟩ := v.exists_apply_eq_one_forall_mul_apply_le hv fun w _ ↦ hS0 w
  refine ⟨⟨fun k ↦ (d : K) • Pi.basisFun K ι k, fun k _ ↦ ?_, ?_⟩, ?_⟩
  · refine mem_approxModule.mpr ⟨fun w hw i ↦ ?_, fun w _ j ↦ ?_⟩
    · dsimp only
      rw [map_smul, smul_eq_mul, map_mul]
      calc w (d : K) * w (L w.1 i (Pi.basisFun K ι k))
          ≤ w (d : K) * (S w * |Q| ^ c w.1 i) :=
            mul_le_mul_of_nonneg_left (hS w i k) (apply_nonneg _ _)
        _ = w (d : K) * S w * |Q| ^ c w.1 i := (mul_assoc _ _ _).symm
        _ ≤ |Q| ^ c w.1 i := mul_le_of_le_one_left (hQc w i).le (hdS w hw)
    · dsimp only
      rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp [w.apply_le_one d]
  · dsimp only
    have hmat :
        Matrix.of (fun k : ι ↦ (d : K) • Pi.basisFun K ι k) = (d : K) • (1 : Matrix ι ι K) := by
      ext k j
      simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, Algebra.smul_def, eq_comm]
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, hdv, one_pow]
  · rintro _ ⟨x, hx, rfl⟩
    refine (apply_det_le_prod v (Matrix.of x) fun k j ↦ ?_).trans_eq Finset.prod_const_one
    exact (mem_approxModule.mp (hx k (Set.mem_univ k))).2 v hv j

/-- At a place `v ∈ S₀` where `L v.1` is linearly independent, the largest value of `v` on the
determinants of `card ι` vectors of `approxModule S₀ L c Q` is
`(v (det (L v.1)))⁻¹ * ∏ i, v.floorValue (|Q| ^ c v.1 i)`. -/
private theorem isGreatest_apply_det_approxModule_of_mem [DecidableEq ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0) {v : FinitePlace K} (hv : v ∈ S₀)
    (hvL : LinearIndependent K (L v.1)) :
    IsGreatest ((fun x : ι → ι → K ↦ v (Matrix.of x).det) ''
      Set.univ.pi fun _ ↦ (approxModule S₀ L c Q : Set (ι → K)))
      ((v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, v.floorValue (|Q| ^ c v.1 i)) := by
  have hQc (w : FinitePlace K) (i : ι) : 0 < |Q| ^ c w.1 i :=
    Real.rpow_pos_of_pos (abs_pos.mpr hQ) _
  have hdet_pos : 0 < v (LinearMap.det (LinearMap.pi (L v.1))) :=
    FinitePlace.pos_iff.mpr hvL.det_pi_ne_zero
  have hdet0 : v (LinearMap.det (LinearMap.pi (L v.1))) ≠ 0 := hdet_pos.ne'
  -- Invert `L v.1` on a diagonal realizing `v.floorValue (|Q| ^ c v.1 i)`, then scale by an
  -- algebraic integer that is a unit at `v` and clears all other bad places.
  choose u _ hu using fun i : ι ↦ v.exists_apply_eq_floorValue (hQc v i)
  let e : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofBijective (LinearMap.pi (L v.1)) hvL.bijective_pi
  let y : ι → ι → K := fun k ↦ e.symm (Pi.single (M := fun _ : ι ↦ K) k (u k))
  have hLy (k i : ι) : L v.1 i (y k) = Pi.single (M := fun _ : ι ↦ K) k (u k) i :=
    congrFun (e.apply_symm_apply (Pi.single (M := fun _ : ι ↦ K) k (u k))) i
  classical
  let T₁ : Finset (FinitePlace K) :=
    Finset.univ.biUnion fun p : ι × ι ↦
      (FinitePlace.hasFiniteMulSupport_max_one (y p.1 p.2)).toFinset
  let T : Finset (FinitePlace K) := S₀.erase v ∪ (T₁ \ S₀)
  have hvT : v ∉ T := by simp [T, hv]
  let R : FinitePlace K → ℝ := fun w ↦
    (∑ k, ∑ i, w (L w.1 i (y k)) / |Q| ^ c w.1 i) + ∑ k, ∑ j, w (y k j)
  have hR0 (w : FinitePlace K) : 0 ≤ R w :=
    add_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun i _ ↦
      div_nonneg (apply_nonneg _ _) (hQc w i).le)
      (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _)
  obtain ⟨d, hdv, hdR⟩ := v.exists_apply_eq_one_forall_mul_apply_le hvT fun w _ ↦ hR0 w
  refine ⟨⟨fun k ↦ (d : K) • y k, fun k _ ↦ ?_, ?_⟩, ?_⟩
  · refine mem_approxModule.mpr ⟨fun w hw i ↦ ?_, fun w hw j ↦ ?_⟩
    · dsimp only
      rw [map_smul, smul_eq_mul, map_mul]
      by_cases hwv : w = v
      · subst hwv
        rw [hdv, one_mul, hLy, Pi.single_apply]
        split_ifs with hki
        · subst hki
          exact (hu i).le.trans (w.floorValue_le (hQc w i).le)
        · simp [(hQc w i).le]
      · have hwT : w ∈ T := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwv, hw⟩)
        have hleR : w (L w.1 i (y k)) ≤ R w * |Q| ^ c w.1 i := by
          rw [← div_le_iff₀ (hQc w i)]
          refine le_trans ?_ (le_add_of_nonneg_right
            (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _))
          refine (Finset.single_le_sum (f := fun i ↦ w (L w.1 i (y k)) / |Q| ^ c w.1 i)
            (fun i _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le) (Finset.mem_univ i)).trans ?_
          exact Finset.single_le_sum (f := fun k ↦ ∑ i, w (L w.1 i (y k)) / |Q| ^ c w.1 i)
            (fun _ _ ↦ Finset.sum_nonneg fun i _ ↦ div_nonneg (apply_nonneg _ _) (hQc w i).le)
            (Finset.mem_univ k)
        calc w (d : K) * w (L w.1 i (y k))
            ≤ w (d : K) * (R w * |Q| ^ c w.1 i) :=
              mul_le_mul_of_nonneg_left hleR (apply_nonneg _ _)
          _ = w (d : K) * R w * |Q| ^ c w.1 i := (mul_assoc _ _ _).symm
          _ ≤ |Q| ^ c w.1 i := mul_le_of_le_one_left (hQc w i).le (hdR w hwT)
    · dsimp only
      rw [Pi.smul_apply, smul_eq_mul, map_mul]
      by_cases hwT₁ : w ∈ T₁
      · have hwT : w ∈ T := Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwT₁, hw⟩)
        have hleR : w (y k j) ≤ R w := by
          refine le_trans ?_ (le_add_of_nonneg_left
            (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun i _ ↦
              div_nonneg (apply_nonneg _ _) (hQc w i).le))
          refine (Finset.single_le_sum (f := fun j ↦ w (y k j))
            (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_univ j)).trans ?_
          exact Finset.single_le_sum (f := fun k ↦ ∑ j, w (y k j))
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _) (Finset.mem_univ k)
        exact (mul_le_mul_of_nonneg_left hleR (apply_nonneg _ _)).trans (hdR w hwT)
      · have hy1 : w (y k j) ≤ 1 := by
          by_contra! hgt
          refine hwT₁ (Finset.mem_biUnion.mpr ⟨(k, j), Finset.mem_univ _, ?_⟩)
          exact (Set.Finite.mem_toFinset _).mpr
            (Function.mem_mulSupport.mpr (ne_of_gt (lt_max_of_lt_left hgt)))
        exact (mul_le_mul (w.apply_le_one d) hy1 (apply_nonneg _ _) zero_le_one).trans_eq
          (one_mul 1)
  · dsimp only
    have hdiag : Matrix.of (fun k i ↦ L v.1 i ((d : K) • y k)) =
        Matrix.diagonal fun k ↦ (d : K) * u k := by
      ext k i
      rw [Matrix.of_apply, map_smul, smul_eq_mul, hLy, Pi.single_apply, Matrix.diagonal_apply]
      by_cases hki : k = i
      · subst hki; simp
      · simp [hki, Ne.symm hki]
    have hmul := congrArg (fun M ↦ v M.det) (matrix_apply_forms_eq_mul_transpose (L v.1)
      fun k ↦ (d : K) • y k)
    rw [hdiag, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix',
      map_mul, map_prod] at hmul
    apply mul_left_cancel₀ hdet0
    rw [← mul_assoc, mul_inv_cancel₀ hdet0, one_mul, mul_comm, ← hmul]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [map_mul, hdv, one_mul, hu k]
  · -- Upper bound: apply the ultrametric determinant inequality to `(L v.1 i (x k))_{k, i}`.
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    refine (le_inv_mul_iff₀ hdet_pos).mpr ?_
    have hmul := congrArg (fun M ↦ v M.det) (matrix_apply_forms_eq_mul_transpose (L v.1) x)
    rw [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', map_mul, mul_comm] at hmul
    rw [← hmul]
    refine apply_det_le_prod v _ fun k i ↦ (v.apply_le_iff_le_floorValue (hQc v i) _).mp ?_
    exact (mem_approxModule.mp (hx k (Set.mem_univ k))).1 v hv i

open scoped Classical in
/-- **Covolume of the lattice of an approximation domain** (Bombieri–Gubler, Lemma 7.5.7, finite
part, corrected with `FinitePlace.floorValue`): for `0 < Q` and linearly independent forms at `S₀`,
the covolume of `(approxModule S₀ L c Q).mixedImage` in `ι → mixedSpace K` is
`(∏ v ∈ S₀, v (det (L v.1)) * ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) * covol (𝓞 K) ^ card ι`. -/
theorem covolume_approxLattice {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ZLattice.covolume (approxModule S₀ L c Q).mixedImage =
      (∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1))) *
        ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) *
        ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  let B : FinitePlace K → ℝ := fun v ↦
    if v ∈ S₀ then
      (v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, v.floorValue (Q ^ c v.1 i)
    else 1
  have hB (v : FinitePlace K) : IsGreatest ((fun x : ι → ι → K ↦ v (Matrix.of x).det) ''
      Set.univ.pi fun _ ↦ (approxModule S₀ L c Q : Set (ι → K))) (B v) := by
    by_cases hv : v ∈ S₀
    · simpa only [B, hv, ↓reduceIte, abs_of_pos hQ] using
        isGreatest_apply_det_approxModule_of_mem c hQ.ne' hv (hL v hv)
    · simpa only [B, hv, ↓reduceIte] using
        isGreatest_apply_det_approxModule_of_notMem L c hQ.ne' hv
  have hsupp : Function.mulSupport B ⊆ (S₀ : Set (FinitePlace K)) := by
    intro v hv
    by_contra hnot
    have hnot' : v ∉ S₀ := Finset.mem_coe.not.mp hnot
    exact hv (by simp [B, hnot'])
  rw [Submodule.covolume_mixedImage (fg_approxModule hL c Q)
      (span_approxModule_eq_top S₀ L c hQ.ne') hB,
    finprod_eq_prod_of_mulSupport_subset B hsupp, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  simp only [B, hv, ↓reduceIte, mul_inv_rev, inv_inv, ← Finset.prod_inv_distrib, mul_comm]

open scoped Classical in
/-- The covolume of `(approxModule S₀ L c Q).mixedImage` is positive when `Q ≠ 0` and the forms at
`S₀` are linearly independent. -/
theorem covolume_approxLattice_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (hL : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : Q ≠ 0) :
    0 < ZLattice.covolume (approxModule S₀ L c Q).mixedImage := by
  have := discreteTopology_mixedImage_approxModule hL c Q
  have := isZLattice_mixedImage_approxModule hL c hQ
  exact ZLattice.covolume_pos (approxModule S₀ L c Q).mixedImage volume

end Covolume

/-! ### Volume of the archimedean body -/

section Volume

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **Volume of the body of an approximation domain** (Bombieri–Gubler, Lemma 7.5.7, archimedean
part): when the linear forms `L w.1` are linearly independent at every infinite place `w`, the
`ℝ≥0∞`-volume of `approxBody L c Q` in `ι → mixedSpace K` is `convexBodyLTFactor K ^ card ι` times
the product over infinite places `v` of
`(ENNReal.ofReal ((v (det (L v.1)))⁻¹) * ∏ i, ENNReal.ofReal (Q ^ c v.1 i)) ^ v.mult`.

Proved by a single `mixedSpace K`-linear change of variables on `ι → mixedSpace K`, whose real
determinant is computed at all infinite places at once via `LinearMap.det_restrictScalars`. -/
theorem volume_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (Q : ℝ) :
    volume (approxBody L c Q) =
      convexBodyLTFactor K ^ Fintype.card ι *
        ∏ v : InfinitePlace K,
          (ENNReal.ofReal ((v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹) *
            ∏ i, ENNReal.ofReal (Q ^ c v.1 i)) ^ v.mult := by
  -- Assemble the `w`-embeddings of the coefficients of `L w` into one matrix over `mixedSpace K`.
  let a : ι → ι → mixedSpace K := fun i j ↦
    (fun w ↦ (mixedEmbedding K (L w.1.1 i (Pi.basisFun K ι j))).1 w,
     fun w ↦ (mixedEmbedding K (L w.1.1 i (Pi.basisFun K ι j))).2 w)
  let A : Matrix ι ι (mixedSpace K) := Matrix.of a
  let φ : (ι → mixedSpace K) →ₗ[ℝ] (ι → mixedSpace K) := (Matrix.toLin' A).restrictScalars ℝ
  let evalReal (w : {w : InfinitePlace K // IsReal w}) : mixedSpace K →+* ℝ :=
    (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  let evalComplex (w : {w : InfinitePlace K // IsComplex w}) : mixedSpace K →+* ℂ :=
    (Pi.evalRingHom _ w).comp (RingHom.snd _ _)
  -- At each infinite place `w`, `(φ z) i` has the same `w`-norm as the action of `L w.1 i` on `z`.
  have hnorm_apply (w : InfinitePlace K) (i : ι) (z : ι → mixedSpace K) :
      normAtPlace w ((φ z) i) =
        normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j) := by
    have hφz : (φ z) i = ∑ j, a i j * z j := by
      simp [φ, A, Matrix.mulVec, dotProduct]
    rw [hφz]
    by_cases hw : IsReal w
    · simp only [normAtPlace_apply_of_isReal hw]
      congr 1
      change evalReal ⟨w, hw⟩ (∑ j, a i j * z j) =
        evalReal ⟨w, hw⟩ (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j)
      simp only [map_sum, map_mul]
      rfl
    · have hwc : IsComplex w := not_isReal_iff_isComplex.mp hw
      simp only [normAtPlace_apply_of_isComplex hwc]
      congr 1
      change evalComplex ⟨w, hwc⟩ (∑ j, a i j * z j) =
        evalComplex ⟨w, hwc⟩ (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j)
      simp only [map_sum, map_mul]
      rfl
  -- Hence `approxBody L c Q` is the preimage under `φ` of a product of closed-ball boxes.
  have hpre : approxBody L c Q =
      φ ⁻¹' (Set.univ.pi fun i ↦ {x : mixedSpace K | ∀ w, normAtPlace w x ≤ Q ^ c w.1 i}) := by
    ext z
    simp only [mem_approxBody, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_ofPred_eq, hnorm_apply]
    exact forall_comm
  -- Likewise, the `w`-coordinate of `A.det` is the `w`-embedding of `det (pi (L w.1))`.
  have hmat_det (u : AbsoluteValue K ℝ) :
      (Matrix.of fun i j ↦ L u i (Pi.basisFun K ι j)).det = LinearMap.det (LinearMap.pi (L u)) := by
    rw [← LinearMap.det_toMatrix' (LinearMap.pi (L u))]
    rfl
  have hnorm_det (w : InfinitePlace K) :
      normAtPlace w A.det = w (LinearMap.det (LinearMap.pi (L w.1))) := by
    rw [← normAtPlace_apply, ← hmat_det]
    by_cases hw : IsReal w
    · simp only [normAtPlace_apply_of_isReal hw]
      congr 1
      change evalReal ⟨w, hw⟩ A.det =
        ((evalReal ⟨w, hw⟩).comp (mixedEmbedding K))
          (Matrix.of fun i j ↦ L w.1 i (Pi.basisFun K ι j)).det
      rw [RingHom.map_det, RingHom.map_det]
      rfl
    · have hwc : IsComplex w := not_isReal_iff_isComplex.mp hw
      simp only [normAtPlace_apply_of_isComplex hwc]
      congr 1
      change evalComplex ⟨w, hwc⟩ A.det =
        ((evalComplex ⟨w, hwc⟩).comp (mixedEmbedding K))
          (Matrix.of fun i j ↦ L w.1 i (Pi.basisFun K ι j)).det
      rw [RingHom.map_det, RingHom.map_det]
      rfl
  have habs_det : |LinearMap.det φ| =
      ∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', abs_algebraNorm,
      mixedEmbedding.norm_apply]
    exact Finset.prod_congr rfl fun v _ ↦ by rw [hnorm_det]
  have hdet_pos : 0 < ∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult :=
    Finset.prod_pos fun v _ ↦ pow_pos (InfinitePlace.pos_iff.mpr (hL v).det_pi_ne_zero) _
  have hdet_ne : LinearMap.det φ ≠ 0 := by
    rw [← abs_ne_zero, habs_det]
    exact hdet_pos.ne'
  rw [hpre, Measure.addHaar_preimage_linearMap volume hdet_ne, abs_inv, habs_det,
    ENNReal.ofReal_inv_of_pos hdet_pos, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ by positivity),
    volume_pi_pi]
  simp_rw [volume_setOf_forall_normAtPlace_le, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  rw [mul_left_comm]
  congr 1
  rw [Finset.prod_comm, ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr ENNReal.ofReal_ne_top),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hv0 : 0 < v (LinearMap.det (LinearMap.pi (L v.1))) :=
    InfinitePlace.pos_iff.mpr (hL v).det_pi_ne_zero
  rw [ENNReal.ofReal_pow hv0.le, ENNReal.inv_pow, ← ENNReal.ofReal_inv_of_pos hv0, mul_pow,
    Finset.prod_pow Finset.univ v.mult (fun i ↦ ENNReal.ofReal (Q ^ c v.1 i))]

open scoped Classical in
/-- **Real-valued volume of the body of an approximation domain** (Bombieri–Gubler, Lemma 7.5.7,
archimedean part): for `0 ≤ Q` and linearly independent forms at every infinite place, the real
volume of `approxBody L c Q` is `2 ^ (r₁ · card ι) · π ^ (r₂ · card ι)` times
`∏ v : InfinitePlace K, ((v (det (L v.1)))⁻¹ * ∏ i, Q ^ c v.1 i) ^ v.mult`. -/
theorem volume_real_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    volume.real (approxBody L c Q) =
      2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) *
        ∏ v : InfinitePlace K,
          ((v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, Q ^ c v.1 i) ^ v.mult := by
  rw [measureReal_def, volume_approxBody hL c Q, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_prod]
  have hfactor : (convexBodyLTFactor K : ℝ≥0∞).toReal ^ Fintype.card ι =
      2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) := by
    simp only [convexBodyLTFactor, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
      NNReal.coe_real_pi]
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hfactor]
  congr 1
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hv0 : 0 < v (LinearMap.det (LinearMap.pi (L v.1))) :=
    InfinitePlace.pos_iff.mpr (hL v).det_pi_ne_zero
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hv0.le),
    ENNReal.toReal_prod]
  congr 2
  exact Finset.prod_congr rfl fun i _ ↦ ENNReal.toReal_ofReal (Real.rpow_nonneg hQ _)

open scoped Classical in
/-- For `0 < Q` and linearly independent forms at every infinite place, the real volume of
`approxBody L c Q` is strictly positive. -/
theorem volume_real_approxBody_pos {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 < Q) : 0 < volume.real (approxBody L c Q) := by
  rw [volume_real_approxBody hL c hQ.le]
  refine mul_pos ?_ (Finset.prod_pos fun v _ ↦ pow_pos (mul_pos ?_ ?_) _)
  · exact mul_pos (pow_pos zero_lt_two _) (pow_pos Real.pi_pos _)
  · exact inv_pos.mpr (InfinitePlace.pos_iff.mpr (hL v).det_pi_ne_zero)
  · exact Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos hQ _

end Volume

/-! ### Leading constant and comparison of `vol B / covol Λ` with `Q ^ approxWeight` -/

section Comparison

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **The leading constant in the volume-to-covolume ratio of an approximation domain**
(Bombieri–Gubler, Corollary 7.5.8): `2 ^ (r₁ · card ι) · π ^ (r₂ · card ι)` divided by
`covol (𝓞 K) ^ card ι` and the local determinants of `L` at all infinite places (with multiplicity)
and at `S₀`. -/
def approxConst (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) : ℝ :=
  2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
    (ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
      (∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) *
      ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1))))

open scoped Classical in
/-- Explicit quotient formula for `approxConst`. -/
theorem approxConst_def (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    approxConst S₀ L =
      2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
        (ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
          (∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) *
          ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1)))) := by
  rfl

/-- `approxConst S₀ L` depends on `L` only at the infinite places and the places of `S₀`. -/
theorem approxConst_congr {S₀ : Finset (FinitePlace K)}
    {L₁ L₂ : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hInf : ∀ v : InfinitePlace K, L₁ v.1 = L₂ v.1)
    (hFin : ∀ v ∈ S₀, L₁ v.1 = L₂ v.1) :
    approxConst S₀ L₁ = approxConst S₀ L₂ := by
  rw [approxConst_def, approxConst_def]
  have h₁ : (∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L₁ v.1))) ^ v.mult) =
      ∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L₂ v.1))) ^ v.mult :=
    Finset.prod_congr rfl fun v _ ↦ by rw [hInf v]
  have h₂ : (∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L₁ v.1)))) =
      ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L₂ v.1))) :=
    Finset.prod_congr rfl fun v hv ↦ by rw [hFin v hv]
  rw [h₁, h₂]

/-- **Discriminant formula for `approxConst`** (Bombieri–Gubler, Corollary 7.5.8): substituting
`covol (𝓞 K) = 2 ^ (-r₂) * √|discr K|` expresses `approxConst S₀ L` in terms of the Minkowski
factor `(2 ^ r₁ * (2 * π) ^ r₂ / √|discr K|) ^ card ι`. -/
theorem approxConst_eq_discr (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    approxConst S₀ L =
      (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K / √|(discr K : ℝ)|) ^
        Fintype.card ι /
        ((∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) *
          ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1)))) := by
  have hcov :
      2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
          ((2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ Fintype.card ι =
        (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K / √|(discr K : ℝ)|) ^
          Fintype.card ι := by
    rw [mul_pow, ← pow_mul, inv_pow, div_pow, mul_pow, mul_pow (2 : ℝ) Real.pi, mul_pow,
      ← pow_mul, ← pow_mul, ← pow_mul]
    have hdiscr : √|(discr K : ℝ)| ≠ 0 := by
      rw [Real.sqrt_ne_zero (abs_nonneg _), abs_ne_zero, Int.cast_ne_zero]
      exact NumberField.discr_ne_zero K
    have h2 : (2 : ℝ) ^ (nrComplexPlaces K * Fintype.card ι) ≠ 0 :=
      pow_ne_zero _ two_ne_zero
    field_simp
  rw [approxConst_def, mixedEmbedding.covolume_integerLattice]
  calc _ = 2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
        (((2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ Fintype.card ι *
          ((∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) *
            ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1))))) :=
        congrArg _ (mul_assoc _ _ _)
    _ = (2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
          ((2⁻¹) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ Fintype.card ι) /
        ((∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) *
          ∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1)))) :=
        div_mul_eq_div_div _ _ _
    _ = _ := congrArg (· / _) hcov

/-- When the linear forms are linearly independent at every infinite place and every `v ∈ S₀`, the
constant `approxConst S₀ L` is strictly positive. -/
theorem approxConst_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    0 < approxConst S₀ L := by
  classical
  rw [approxConst_def]
  refine div_pos (mul_pos (pow_pos zero_lt_two _) (pow_pos Real.pi_pos _))
    (mul_pos (mul_pos ?_ ?_) ?_)
  · exact pow_pos (ZLattice.covolume_pos (mixedEmbedding.integerLattice K) volume) _
  · exact Finset.prod_pos fun v _ ↦ pow_pos (InfinitePlace.pos_iff.mpr (hLInf v).det_pi_ne_zero) _
  · exact Finset.prod_pos fun v hv ↦ FinitePlace.pos_iff.mpr (hLFin v hv).det_pi_ne_zero

open scoped Classical in
/-- **Exact ratio of the volume of `approxBody` to the covolume of `approxModule.mixedImage`**: for
`0 < Q` and linearly independent forms at the infinite places and `S₀`, the ratio equals
`approxConst S₀ L` times the archimedean bounds `(∏ i, Q ^ c v.1 i) ^ v.mult` and the rounded
finite-place bounds `v.floorValue (Q ^ c v.1 i)`. -/
theorem volume_div_covolume_eq {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    volume.real (approxBody L c Q) / ZLattice.covolume (approxModule S₀ L c Q).mixedImage =
      approxConst S₀ L *
        ((∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult) *
          ∏ v ∈ S₀, ∏ i, v.floorValue (Q ^ c v.1 i)) := by
  rw [volume_real_approxBody hLInf c hQ.le, covolume_approxLattice hLFin c hQ, approxConst_def]
  have hInf_eq : (∏ v : InfinitePlace K,
      ((v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, Q ^ c v.1 i) ^ v.mult) =
      (∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult)⁻¹ *
        ∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult := by
    simp_rw [mul_pow, Finset.prod_mul_distrib, inv_pow, ← Finset.prod_inv_distrib]
  have hFin_eq : (∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1))) *
      ∏ i, (v.floorValue (Q ^ c v.1 i))⁻¹) =
      (∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1)))) *
        (∏ v ∈ S₀, ∏ i, v.floorValue (Q ^ c v.1 i))⁻¹ := by
    simp_rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (ZLattice.covolume_ne_zero (mixedEmbedding.integerLattice K) volume)
  have hInf0 : (∏ v : InfinitePlace K, v (LinearMap.det (LinearMap.pi (L v.1))) ^ v.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦
      pow_ne_zero _ (InfinitePlace.pos_iff.mpr (hLInf v).det_pi_ne_zero).ne'
  have hFin0 : (∏ v ∈ S₀, v (LinearMap.det (LinearMap.pi (L v.1)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v hv ↦
      (FinitePlace.pos_iff.mpr (hLFin v hv).det_pi_ne_zero).ne'
  have hfloor0 : (∏ v ∈ S₀, ∏ i, v.floorValue (Q ^ c v.1 i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦ Finset.prod_ne_zero_iff.mpr fun i _ ↦
      (v.floorValue_pos (Real.rpow_pos_of_pos hQ _)).ne'
  rw [hInf_eq, hFin_eq]
  field_simp

open scoped Classical in
/-- When `S₀ = ∅`, there is no finite-place rounding loss and the volume-to-covolume ratio equals
`approxConst ∅ L * Q ^ approxWeight ∅ c` on the nose. -/
theorem volume_div_covolume_empty {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    volume.real (approxBody L c Q) / ZLattice.covolume (approxModule ∅ L c Q).mixedImage =
      approxConst ∅ L * Q ^ approxWeight ∅ c := by
  rw [volume_div_covolume_eq hLInf (by simp) c hQ, rpow_approxWeight ∅ c hQ]
  simp

open scoped Classical in
/-- **Upper bound on the volume-to-covolume ratio** in terms of `Q ^ approxWeight S₀ c`: since
`v.floorValue t ≤ t`, the ratio is at most `approxConst S₀ L * Q ^ approxWeight S₀ c`. -/
theorem volume_div_covolume_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    volume.real (approxBody L c Q) / ZLattice.covolume (approxModule S₀ L c Q).mixedImage ≤
      approxConst S₀ L * Q ^ approxWeight S₀ c := by
  rw [volume_div_covolume_eq hLInf hLFin c hQ, rpow_approxWeight S₀ c hQ]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_)
    (approxConst_pos hLInf hLFin).le
  · exact Finset.prod_le_prod₀
      (fun v _ ↦ Finset.prod_nonneg fun _ _ ↦ v.floorValue_nonneg _)
      fun v _ ↦ Finset.prod_le_prod₀
        (fun _ _ ↦ v.floorValue_nonneg _)
        fun i _ ↦ v.floorValue_le (Real.rpow_pos_of_pos hQ _).le
  · exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg
      (Finset.prod_nonneg fun _ _ ↦ (Real.rpow_pos_of_pos hQ _).le) _

open scoped Classical in
/-- **Lower bound on the volume-to-covolume ratio** in terms of `Q ^ approxWeight S₀ c`: rounding
each finite-place bound down to the value group of `v ∈ S₀` loses strictly less than `N 𝔭_v` per
coordinate, so the ratio is at least
`approxConst S₀ L / (∏ v ∈ S₀, N 𝔭_v ^ card ι) * Q ^ approxWeight S₀ c`. -/
theorem le_volume_div_covolume {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    approxConst S₀ L / (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) *
        Q ^ approxWeight S₀ c ≤
      volume.real (approxBody L c Q) / ZLattice.covolume (approxModule S₀ L c Q).mixedImage := by
  have hfin_le :
      (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι)⁻¹ *
          (∏ v ∈ S₀, ∏ i, Q ^ c v.1 i) ≤
        ∏ v ∈ S₀, ∏ i, v.floorValue (Q ^ c v.1 i) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀
      (fun v _ ↦ mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
        (Finset.prod_nonneg fun _ _ ↦ (Real.rpow_pos_of_pos hQ _).le)) fun v _ ↦ ?_
    rw [← inv_pow, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀
      (fun _ _ ↦ mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Real.rpow_pos_of_pos hQ _).le) fun i _ ↦ ?_
    have hN : (0 : ℝ) < v.maximalIdeal.asIdeal.absNorm := by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos
    rw [inv_mul_le_iff₀ hN]
    exact (v.lt_absNorm_mul_floorValue (Real.rpow_pos_of_pos hQ _)).le
  rw [volume_div_covolume_eq hLInf hLFin c hQ, rpow_approxWeight S₀ c hQ]
  calc
    approxConst S₀ L / (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) *
        ((∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult) * ∏ v ∈ S₀, ∏ i, Q ^ c v.1 i)
      = approxConst S₀ L * ((∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult) *
          ((∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι)⁻¹ *
            ∏ v ∈ S₀, ∏ i, Q ^ c v.1 i)) := by ring
    _ ≤ approxConst S₀ L * ((∏ v : InfinitePlace K, (∏ i, Q ^ c v.1 i) ^ v.mult) *
          ∏ v ∈ S₀, ∏ i, v.floorValue (Q ^ c v.1 i)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin_le ?_)
        (approxConst_pos hLInf hLFin).le
      exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg
        (Finset.prod_nonneg fun _ _ ↦ (Real.rpow_pos_of_pos hQ _).le) _

end Comparison

/-! ### Discreteness of finite-place bounds and `DecidableEq`-freedom checks -/

-- Check that none of the public theorems in this file carry `[DecidableEq ι]`.
section NoDecidableEqCheck

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
example (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    approxConst S₀ L / (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) *
        Q ^ approxWeight S₀ c ≤
      volume.real (approxBody L c Q) / ZLattice.covolume (approxModule S₀ L c Q).mixedImage ∧
    volume.real (approxBody L c Q) / ZLattice.covolume (approxModule S₀ L c Q).mixedImage ≤
      approxConst S₀ L * Q ^ approxWeight S₀ c :=
  ⟨le_volume_div_covolume hLInf hLFin c hQ, volume_div_covolume_le hLInf hLFin c hQ⟩

end NoDecidableEqCheck

-- At the `2`-adic place of `ℚ` in one variable (`ι = Unit`) with `L = id`, `c = 1` and `Q = 3 / 2`,
-- the approximation module is `(𝓞 ℚ)^Unit ≃ ℤ` and its mixed lattice has covolume `1`, whereas
-- substituting `Q ^ c` without `floorValue` would give `(3 / 2)⁻¹ = 2 / 3`.
open scoped Classical in
example :
    let L₀ : AbsoluteValue ℚ ℝ → Unit → Dual ℚ (Unit → ℚ) := fun _ ↦ LinearMap.proj
    ∃ v : FinitePlace ℚ, v.maximalIdeal.asIdeal.absNorm = 2 ∧
      (∀ x : Unit → ℚ,
        x ∈ approxModule (ι := Unit) {v} L₀ 1 (3 / 2) ↔
          ∀ u : FinitePlace ℚ, u (x ()) ≤ 1) ∧
      ZLattice.covolume (approxModule (ι := Unit) {v} L₀ 1 (3 / 2)).mixedImage = 1 := by
  intro L₀
  obtain ⟨P, hP⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq Nat.prime_two
  let v : FinitePlace ℚ := FinitePlace.mk P
  have hv2 : v.maximalIdeal.asIdeal.absNorm = 2 := by
    simpa [v, FinitePlace.maximalIdeal_mk] using hP
  have hfloor : v.floorValue (3 / 2) = 1 := by
    rw [v.floorValue_of_pos (by norm_num), hv2]
    have hf : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
    norm_num [Int.log, hf, Nat.log_of_lt]
  refine ⟨v, hv2, fun x ↦ ?_, ?_⟩
  · simp only [L₀, mem_approxModule, Finset.mem_singleton, Unique.forall_iff, forall_eq,
      LinearMap.proj_apply, Pi.one_apply, Real.rpow_one]
    rw [show |(3 / 2 : ℝ)| = 3 / 2 by norm_num, v.apply_le_iff_le_floorValue (by norm_num), hfloor]
    exact ⟨fun ⟨hx, hx'⟩ u ↦ by by_cases hu : u = v <;> [exact hu ▸ hx; exact hx' u hu],
      fun hx ↦ ⟨hx v, fun u _ ↦ hx u⟩⟩
  · have hLI : ∀ w ∈ ({v} : Finset (FinitePlace ℚ)), LinearIndependent ℚ (L₀ w.1) := by
      intro _ _
      rw [Fintype.linearIndependent_iff]
      intro g hg ⟨⟩
      simpa [L₀] using LinearMap.congr_fun hg 1
    rw [covolume_approxLattice hLI 1 (by norm_num : (0 : ℝ) < 3 / 2)]
    have hpi : LinearMap.pi (LinearMap.proj (R := ℚ) (φ := fun _ : Unit ↦ ℚ)) = LinearMap.id := by
      ext x ⟨⟩; rfl
    simp only [L₀, Finset.prod_singleton, Finset.prod_const_one, Pi.one_apply, Real.rpow_one,
      hfloor, inv_one, mul_one, hpi, LinearMap.det_id, map_one, one_mul, Fintype.card_unit, pow_one,
      mixedEmbedding.covolume_integerLattice,
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ), pow_zero,
      Rat.numberField_discr, Int.cast_one, abs_one, Real.sqrt_one]

end TauCeti.NumberField
