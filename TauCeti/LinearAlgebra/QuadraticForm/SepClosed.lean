/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Normalization
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.CharTwo

/-!
# Quadratic forms over a separably closed field

This file proves that a finite-dimensional nondegenerate quadratic form over a separably closed
field of characteristic different from two is equivalent to a sum of squares, so that such forms
are classified up to equivalence by their dimension, and that such a form has a basis whose Gram
matrix is the identity. It also characterizes representation by the dimension inequality and
proves isotropy in dimension at least two.

## Main results

* `QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed`: a nondegenerate quadratic form is
  equivalent to the standard sum of squares.
* `QuadraticForm.exists_toMatrix_eq_one_of_isSepClosed`: a nondegenerate quadratic form has a
  basis whose Gram matrix is the identity.
* `QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed`: nondegenerate quadratic forms on spaces
  of the same dimension are equivalent.
* `QuadraticForm.equivalent_iff_finrank_eq_of_isSepClosed`: nondegenerate quadratic forms are
  equivalent exactly when their dimensions agree.
* `QuadraticForm.equivalent_weightedSumSquares_one_iff_finrank_eq`: a nondegenerate form is
  equivalent to the standard sum of squares on `Fin n` exactly when its dimension is `n`.
* `QuadraticForm.isRepresentedBy_iff_finrank_le_of_isSepClosed`: representation of nondegenerate
  quadratic forms is characterized by the inequality of their dimensions.
* `QuadraticForm.not_anisotropic_of_isSepClosed`: every form in dimension at least two is isotropic.

In characteristic two, `TauCeti.equivalent_binaryQuadraticForm_zero_of_isSepClosed` splits
the binary planes using `IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'`.
The symplectic basis decomposition `QuadraticMap.isometryEquivPiBinaryQuadraticForm` then gives
the hyperbolic normal forms in characteristic two. In other characteristics they follow from
classification by dimension. The results are
`QuadraticForm.equivalent_pi_binaryQuadraticForm_zero_of_isSepClosed` in even rank, and
the corresponding `QuadraticMap.Nondegenerate` normal form in odd rank, where the additional
line carries a nonzero multiple of the square.

## References

* Mathlib's `QuadraticForm.isometryEquivSumSquaresUnits` and
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` supply the normalization argument
  adapted here from algebraically closed to separably closed fields.
* SGA 7 II, Exposé XII, Proposition 1.2, for the normal forms in characteristic two.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsSepClosed K]

private noncomputable def isometryEquivSumSquaresUnits [NeZero (2 : K)] (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K fun i ↦ (w i : K))
      (weightedSumSquares K (1 : ι → K)) := by
  classical
  refine isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.isSquare (w i : K)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.isSquare (w i : K)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.isSquare (w i : K)).choose_spec]

/-- A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is equivalent to the standard sum of squares. -/
theorem equivalent_weightedSumSquares_of_isSepClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

/-- Over a separably closed field of characteristic different from two, a finite-dimensional
nondegenerate quadratic form has a basis indexed by `Fin (finrank K M)` whose Gram matrix is the
identity. -/
theorem exists_toMatrix_eq_one_of_isSepClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] (Q : QuadraticForm K M)
    (hQ : (associated Q).SeparatingLeft) :
    ∃ b : Module.Basis (Fin (Module.finrank K M)) K M, Q.toMatrix b = 1 :=
  (equivalent_weightedSumSquares_one_iff_exists_toMatrix_eq_one Q).1
    (Q.equivalent_weightedSumSquares_of_isSepClosed hQ)

/-- Nondegenerate quadratic forms over a separably closed field of characteristic different from
two, on possibly different finite-dimensional spaces, are equivalent when their dimensions
agree. -/
theorem equivalent_of_finrank_eq_of_isSepClosed [Invertible (2 : K)] {M N : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (Q : QuadraticForm K M) (R : QuadraticForm K N) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (h : Module.finrank K M = Module.finrank K N) : Q.Equivalent R := by
  have hQ' := Q.equivalent_weightedSumSquares_of_isSepClosed
    (nondegenerate_associated_iff.mpr hQ).1
  rw [h] at hQ'
  exact hQ'.trans (R.equivalent_weightedSumSquares_of_isSepClosed
    (nondegenerate_associated_iff.mpr hR).1).symm

/-- Two regular quadratic forms over a separably closed field are equivalent precisely when
their dimensions agree. -/
@[simp] theorem equivalent_iff_finrank_eq_of_isSepClosed
    {K W₁ W₂ : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank K W₁ = Module.finrank K W₂ := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · exact QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed Q R hQ hR

/-- Over a separably closed field a regular quadratic form is isometric to the standard sum
of squares on `Fin n` exactly when its space has dimension `n`. -/
@[simp]
theorem equivalent_weightedSumSquares_one_iff_finrank_eq
    {K W : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (n : ℕ) :
    Q.Equivalent (weightedSumSquares K (1 : Fin n → K)) ↔ Module.finrank K W = n := by
  constructor
  · rintro ⟨e⟩
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  · rintro rfl
    exact Q.equivalent_weightedSumSquares_of_isSepClosed
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1

/-- A regular quadratic form over a separably closed field is represented by another regular
form exactly when the dimension of its space is no larger. -/
@[simp]
theorem isRepresentedBy_iff_finrank_le_of_isSepClosed
    {K W₁ W₂ : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsRepresentedBy R ↔ Module.finrank K W₁ ≤ Module.finrank K W₂ := by
  constructor
  · rw [QuadraticMap.isRepresentedBy_iff]
    rintro ⟨f, hf, -⟩
    exact LinearMap.finrank_le_finrank_of_injective hf
  · intro h
    let S : QuadraticForm K (Fin (Module.finrank K W₂ - Module.finrank K W₁) → K) :=
      weightedSumSquares K
        (1 : Fin (Module.finrank K W₂ - Module.finrank K W₁) → K)
    have hS : S.Nondegenerate := nondegenerate_weightedSumSquares_iff.mpr fun _ ↦ isRegular_one
    have hprod : (Q.prod S).Nondegenerate := hQ.prod hS
    have hrank : Module.finrank K
          (W₁ × (Fin (Module.finrank K W₂ - Module.finrank K W₁) → K)) =
        Module.finrank K W₂ := by
      simp only [Module.finrank_prod, Module.finrank_fin_fun]
      omega
    obtain ⟨e⟩ := QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed
      (Q.prod S) R hprod hR hrank
    rw [QuadraticMap.isRepresentedBy_iff]
    exact ⟨(e.toIsometry.comp (QuadraticMap.Isometry.inl Q S)).toLinearMap,
      e.injective.comp LinearMap.inl_injective, fun x ↦ by simp⟩

/-- A form over a separably closed field of characteristic not two has a nonzero isotropic
vector when its space has dimension at least two (the dimension being finite, since `finrank` is
zero otherwise). -/
theorem not_anisotropic_of_isSepClosed
    {K W : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (h : 2 ≤ Module.finrank K W) : ¬ Q.Anisotropic := by
  classical
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  intro hQ
  have he := Q.equivalent_weightedSumSquares_of_isSepClosed
    (QuadraticMap.separatingLeft_of_anisotropic Q hQ)
  have hstandard := he.anisotropic_iff.mp hQ
  obtain ⟨i, hi⟩ := IsSepClosed.isSquare (-1 : K)
  let i₀ : Fin (Module.finrank K W) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank K W) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁]
  -- The two coordinate values contribute `1` and `-1` to the sum of squares.
  have hzero := hstandard (Pi.single i₀ 1 + Pi.single i₁ i) (by
    simp [weightedSumSquares_apply, Pi.single_apply, mul_add, add_mul, hne, hne.symm,
      Finset.sum_add_distrib, Finset.sum_ite_eq', ← hi])
  have : (1 : K) = 0 := by simpa [hne] using congrFun hzero i₀
  exact one_ne_zero this

end QuadraticForm

namespace TauCeti

/-- A binary form `a x² + xy + b y²` over a separably closed field of characteristic two
is isometric to `xy` (SGA 7 II, Exposé XII, Proposition 1.2). -/
theorem equivalent_binaryQuadraticForm_zero_of_isSepClosed {K : Type*} [Field K]
    [IsSepClosed K] [CharP K 2] (a b : K) :
    (binaryQuadraticForm K a b).Equivalent (binaryQuadraticForm K 0 0) := by
  have hiso : ¬ (binaryQuadraticForm K a b).Anisotropic := by
    obtain ⟨t, ht⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'
      2 2 b 1 a dvd_rfl le_rfl one_ne_zero
    refine (not_anisotropic_iff_exists _).mpr ⟨![(1 : K), t], ?_, ?_⟩
    · intro h
      exact one_ne_zero (by simpa only [Matrix.cons_val_zero, Pi.zero_apply] using congrFun h 0)
    · simpa only [binaryQuadraticForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow,
        mul_one, one_mul, add_comm, add_left_comm, add_assoc] using ht
  exact (QuadraticMap.equivalent_binaryQuadraticForm_zero_iff_not_anisotropic
    (by simp) (nondegenerate_polarBilin_binaryQuadraticForm a b)).mpr hiso

end TauCeti

namespace QuadraticMap

open TauCeti Module

variable {K V : Type*} [Field K] [IsSepClosed K] [AddCommGroup V] [Module K V]

/-- A quadratic form with nondegenerate polar form on a space of dimension `2 * m` over a
separably closed field is a sum of `m` hyperbolic planes, including in characteristic two
(SGA 7 II, Exposé XII, Proposition 1.2). -/
theorem _root_.QuadraticForm.equivalent_pi_binaryQuadraticForm_zero_of_isSepClosed
    [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0) := by
  by_cases h2 : (2 : K) = 0
  · let : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq hQ hdim
    exact Equivalent.trans ⟨Q.isometryEquivPiBinaryQuadraticForm b hb⟩
      (Equivalent.pi fun _ ↦ equivalent_binaryQuadraticForm_zero_of_isSepClosed _ _)
  · let := invertibleOfNonzero h2
    refine QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed Q _
      (nondegenerate_of_nondegenerate_polarBilin hQ)
      (nondegenerate_of_nondegenerate_polarBilin (nondegenerate_polarBilin_pi_iff.mpr
        fun _ ↦ nondegenerate_polarBilin_binaryQuadraticForm_zero)) ?_
    simp [hdim, Module.finrank_pi_fintype, mul_comm]

/-- A nondegenerate quadratic form on a space of dimension `2 * m + 1`
over a separably closed field is the orthogonal sum of `m` hyperbolic planes and a line
with form `z ↦ a * z²` for some nonzero `a`, including in characteristic two
(SGA 7 II, Exposé XII, Proposition 1.2). -/
theorem Nondegenerate.exists_equivalent_pi_binaryQuadraticForm_zero_prod_smul_sq_of_isSepClosed
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {m : ℕ} (hdim : finrank K V = 2 * m + 1) :
    ∃ a : Kˣ, Q.Equivalent
      ((QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0).prod
        ((a : K) • QuadraticMap.sq (R := K) (A := K))) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  by_cases h2 : (2 : K) ≠ 0
  · let := invertibleOfNonzero h2
    refine ⟨1, QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed Q _ hQ ?_ ?_⟩
    · rw [← nondegenerate_polar_iff, nondegenerate_polarBilin_prod_iff]
      exact ⟨nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
        nondegenerate_polarBilin_binaryQuadraticForm_zero,
        nondegenerate_polar_iff.mpr (nondegenerate_smul_sq (Units.ne_zero _))⟩
    · simp [hdim, Module.finrank_prod, Module.finrank_pi_fintype, mul_comm]
  let : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (not_ne_iff.mp h2)
  let L := LinearMap.ker Q.polarBilin
  obtain ⟨W, hW⟩ := L.exists_isCompl
  have horth : LinearMap.BilinForm.orthogonal Q.polarBilin W = L := by
    rw [LinearMap.BilinForm.orthogonal, ← Submodule.orthogonalBilin_sup_ker Q.polarBilin W,
      hW.symm.sup_eq_top, ← LinearMap.BilinForm.orthogonal,
      LinearMap.BilinForm.orthogonal_top_eq_ker Q.isRefl_polarBilin]
  have hWpol : (Q.restrict W).polarBilin.Nondegenerate := by
    rw [polarBilin_restrict]
    exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _
      Q.isRefl_polarBilin (horth.symm ▸ hW.disjoint.symm)
  have hsum := Submodule.finrank_add_eq_of_isCompl hW
  have ⟨hL, hdimW⟩ : finrank K L = 1 ∧ finrank K W = 2 * m := by
    have hle : finrank K L ≤ 1 := Module.finrank_le_of_rank_le
      (by simpa only [Nat.cast_one] using hQ.rank_rad_polar_le)
    obtain ⟨k, hk⟩ := even_finrank_of_nondegenerate_polarBilin hWpol
    exact ⟨by lia, by lia⟩
  let e : K ≃ₗ[K] L := LinearEquiv.ofFinrankEq _ _ ((Module.finrank_self K).trans hL.symm)
  have ha : Q (e 1 : V) ≠ 0 := by
    intro hz
    have hm : (e 1 : V) ∈ Q.radical := mem_radical_iff.mpr ⟨hz,
      LinearMap.mem_ker.mp (e 1).property⟩
    rw [hQ.radical_eq_bot, Submodule.mem_bot] at hm
    exact one_ne_zero (e.map_eq_zero_iff.mp (Subtype.ext hm))
  have hline (z : K) : (Q.restrict L) (e z) =
      (((Units.mk0 _ ha : Kˣ) : K) • QuadraticMap.sq (R := K) (A := K)) z := by
    have he : e z = z • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    simp only [he, restrict_apply, Submodule.coe_smul, Q.map_smul, smul_apply,
      smul_eq_mul, sq_apply, Units.val_mk0, mul_comm]
  have hsplit : Q.Equivalent ((Q.restrict W).prod (Q.restrict L)) :=
    horth ▸ ⟨(IsometryEquiv.prodRestrictOrthogonal Q W (horth.symm ▸ hW.symm)).symm⟩
  exact ⟨Units.mk0 _ ha, hsplit.trans
    ((QuadraticForm.equivalent_pi_binaryQuadraticForm_zero_of_isSepClosed
      (Q.restrict W) hWpol hdimW).prod
      ⟨(IsometryEquiv.mk e hline).symm⟩)⟩

end QuadraticMap
