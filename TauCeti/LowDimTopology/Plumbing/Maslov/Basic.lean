/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Finsupp
public import TauCeti.LowDimTopology.Plumbing.Differential

/-!
# Relative Maslov grading of plumbing chains

For a characteristic covector `k`, the monomial `U ^ j C` has integer degree
`C.dimension - 2 * characteristicWeight P k C - 2 * j`. The chain module carries the
resulting internal grading over `ZMod 2`: homogeneous pieces are coefficient submodules,
since multiplication by `U` lowers degree by two. The weighted differential lowers degree
by one. Neither construction requires negative definiteness.

The private coordinate equivalence separates cube and polynomial coordinates. Transporting
the supported grading along it ensures unique finite homogeneous decomposition; the public
membership criterion is stated solely in terms of polynomial coefficients.

## References

The homological degree convention follows P. Ozsváth, A. Stipsicz and Z. Szabó,
*Knots in lattice homology*, §2.3, Lemma 2.5,
[arXiv:1208.2617](https://arxiv.org/abs/1208.2617). The overall rational normalization
involving the covector square is omitted here. The cubical weight model follows A. Némethi,
*Lattice cohomology of normal surface singularities*, §3.1,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841); its cohomological plus tower uses a
different grading convention.
-/

public section

namespace TauCeti

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace PlumbingCube

/-- The relative Maslov degree of the monomial `U ^ j C` for the characteristic weight. -/
noncomputable def maslovDegree (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) (j : ℕ) : ℤ :=
  (C.dimension : ℤ) - 2 * characteristicWeight P k C - 2 * (j : ℤ)

/-- The relative monomial degree in terms of dimension, cube weight and exponent. -/
theorem maslovDegree_def (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) (j : ℕ) :
    maslovDegree P k C j =
      (C.dimension : ℤ) - 2 * characteristicWeight P k C - 2 * (j : ℤ) := (rfl)

/-- Multiplication by `U` lowers the relative monomial degree by two. -/
@[simp]
theorem maslovDegree_succ (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) (j : ℕ) :
    maslovDegree P k C (j + 1) = maslovDegree P k C j - 2 := by
  simp only [maslovDegree_def, Nat.cast_add, Nat.cast_one]
  omega

/-- A lattice point with coefficient `U ^ j` has degree `-2 * χ_k(x) - 2 * j`. -/
@[simp]
theorem maslovDegree_mk_empty (P : PlumbingGraph V) (k : P.characteristicVectors)
    (x : V → ℤ) (j : ℕ) :
    maslovDegree P k (⟨x, ∅⟩ : PlumbingCube V) j =
      -2 * P.characteristicWeight k x - 2 * (j : ℤ) := by
  simp [maslovDegree_def, dimension, characteristicWeight_def]

/-- The weighted lower face term has relative degree one less than its source. -/
theorem maslovDegree_lowerFace (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) (j : ℕ) :
    maslovDegree P k (C.lowerFace v hv)
        (j + characteristicLowerFaceExponent P k C v) = maslovDegree P k C j - 1 := by
  have hdim : 0 < C.dimension := Finset.card_pos.mpr ⟨v, hv⟩
  have hexp := characteristicLowerFaceExponent_natCast_lowerFace P k C hv
  simp only [maslovDegree_def, dimension_lowerFace_of_mem, Nat.cast_add]
  omega

/-- The weighted upper face term has relative degree one less than its source. -/
theorem maslovDegree_upperFace (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) {v : V} (hv : v ∈ C.directions) (j : ℕ) :
    maslovDegree P k (C.upperFace v hv)
        (j + characteristicUpperFaceExponent P k C hv) = maslovDegree P k C j - 1 := by
  have hdim : 0 < C.dimension := Finset.card_pos.mpr ⟨v, hv⟩
  have hexp := characteristicUpperFaceExponent_natCast P k C hv
  simp only [maslovDegree_def, dimension_upperFace_of_mem, Nat.cast_add]
  omega

end PlumbingCube

namespace PlumbingGraph

private noncomputable def chainCoefficientEquiv :
    PlumbingChain V ≃ₗ[ZMod 2] (PlumbingCube V × ℕ →₀ ZMod 2) :=
  (Finsupp.mapRange.linearEquiv
    ((Polynomial.toFinsuppIsoLinear (ZMod 2)).trans
      (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)))).trans
    (Finsupp.curryLinearEquiv (ZMod 2)).symm

omit [DecidableEq V] [Fintype V] in
private theorem chainCoefficientEquiv_apply (c : PlumbingChain V) (C : PlumbingCube V)
    (j : ℕ) : chainCoefficientEquiv c (C, j) = (c C).coeff j := by
  simp [chainCoefficientEquiv, Polynomial.toFinsuppIsoLinear, Polynomial.toFinsupp_apply]

/-- The internal relative Maslov grading of plumbing chains over the coefficient field.
The monomial `U ^ j C` lies in degree `C.dimension - 2 * w(C) - 2 * j`. -/
noncomputable def latticeChainMaslovGrading (P : PlumbingGraph V)
    (k : P.characteristicVectors) : InternalGrading (ZMod 2) (PlumbingChain V) :=
  (InternalGrading.finsupp (ZMod 2) fun i : PlumbingCube V × ℕ =>
    PlumbingCube.maslovDegree P k i.1 i.2).map chainCoefficientEquiv.symm

/-- A chain is homogeneous precisely when each nonzero polynomial coefficient has the
specified relative Maslov degree. -/
@[simp]
theorem mem_latticeChainMaslovGrading_piece_iff (P : PlumbingGraph V)
    (k : P.characteristicVectors) {p : ℤ} {c : PlumbingChain V} :
    c ∈ (P.latticeChainMaslovGrading k).piece p ↔
      ∀ C j, (c C).coeff j ≠ 0 → PlumbingCube.maslovDegree P k C j = p := by
  rw [latticeChainMaslovGrading, InternalGrading.mem_map_piece_iff,
    LinearEquiv.symm_symm, InternalGrading.mem_finsupp_piece_iff]
  simp only [Prod.forall, chainCoefficientEquiv_apply]

/-- A single polynomial monomial is homogeneous in its relative Maslov degree. -/
theorem single_monomial_mem_latticeChainMaslovGrading_piece (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (j : ℕ) (a : ZMod 2) :
    Finsupp.single C (Polynomial.monomial j a) ∈
      (P.latticeChainMaslovGrading k).piece (PlumbingCube.maslovDegree P k C j) := by
  classical
  rw [mem_latticeChainMaslovGrading_piece_iff]
  intro B n hn
  by_cases hBC : B = C
  · subst B
    simp only [Finsupp.single_eq_same, Polynomial.coeff_monomial] at hn
    split_ifs at hn with hnj
    · subst n
      rfl
    · exact (hn rfl).elim
  · simp [hBC] at hn

/-- Multiplication by `U` lowers relative Maslov degree by two. -/
theorem X_smul_mem_latticeChainMaslovGrading_piece (P : PlumbingGraph V)
    (k : P.characteristicVectors) {p : ℤ} {c : PlumbingChain V}
    (hc : c ∈ (P.latticeChainMaslovGrading k).piece p) :
    (Polynomial.X : PlumbingCoefficient) • c ∈ (P.latticeChainMaslovGrading k).piece (p - 2) := by
  rw [mem_latticeChainMaslovGrading_piece_iff] at hc ⊢
  intro C j hj
  simp only [Finsupp.smul_apply, smul_eq_mul] at hj
  cases j with
  | zero => simp at hj
  | succ j =>
    rw [Polynomial.coeff_X_mul] at hj
    rw [PlumbingCube.maslovDegree_succ, hc C j hj]

/-- The differential of a single monomial is homogeneous of relative degree one less. -/
theorem latticeDifferential_single_monomial_mem_maslov_piece (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) (j : ℕ) (a : ZMod 2) :
    P.latticeDifferential k (Finsupp.single C (Polynomial.monomial j a)) ∈
      (P.latticeChainMaslovGrading k).piece (PlumbingCube.maslovDegree P k C j - 1) := by
  classical
  rw [latticeDifferential_single, latticeDifferentialOnGenerator_def, Finset.smul_sum]
  refine Submodule.sum_mem _ fun v _ => ?_
  rw [smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul,
    Polynomial.monomial_mul_X_pow, Polynomial.monomial_mul_X_pow]
  apply Submodule.add_mem
  · rw [← PlumbingCube.maslovDegree_lowerFace P k C v.property j]
    exact P.single_monomial_mem_latticeChainMaslovGrading_piece k _ _ a
  · rw [← PlumbingCube.maslovDegree_upperFace P k C v.property j]
    exact P.single_monomial_mem_latticeChainMaslovGrading_piece k _ _ a

/-- The lattice differential lowers relative Maslov degree by one on all homogeneous chains. -/
theorem latticeDifferential_mem_latticeChainMaslovGrading_piece (P : PlumbingGraph V)
    (k : P.characteristicVectors) {p : ℤ} {c : PlumbingChain V}
    (hc : c ∈ (P.latticeChainMaslovGrading k).piece p) :
    P.latticeDifferential k c ∈ (P.latticeChainMaslovGrading k).piece (p - 1) := by
  classical
  rw [mem_latticeChainMaslovGrading_piece_iff] at hc
  nth_rw 1 [← c.sum_single]
  rw [Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun C _ => ?_
  nth_rw 1 [← Polynomial.sum_monomial_eq (c C)]
  rw [Polynomial.sum, Finsupp.single_finsetSum, map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [← hc C j (Polynomial.mem_support_iff.mp hj)]
  exact P.latticeDifferential_single_monomial_mem_maslov_piece k C j _

/-- The lattice differential is a homogeneous map of relative Maslov degree `-1`. -/
theorem latticeDifferential_isHomogeneous_maslov (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    LinearMap.IsHomogeneous (P.latticeDifferential k)
      (P.latticeChainMaslovGrading k).piece (P.latticeChainMaslovGrading k).piece (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro p c hc
  simpa only [sub_eq_add_neg] using P.latticeDifferential_mem_latticeChainMaslovGrading_piece k hc

end PlumbingGraph

end TauCeti
