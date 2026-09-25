/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Uniform Chevalley pinning for the Demazure construction

The pinned rational Lie algebra of a valid Dynkin type carries Bourbaki-numbered generators
(`TauCeti.DynkinType.lieBasis`): raising generators `e i` and lowering generators `f i` that
are nilpotent matrices, Cartan generators `h i`, satisfying the Cartan-matrix relations
(`TauCeti.DynkinType.lie_lieBasis_h_e`, `TauCeti.DynkinType.lie_lieBasis_h_f`) and exchanged
by the Chevalley involution (`TauCeti.DynkinType.chevalleyInvolution_lieBasis_e`).

This module packages the uniform exponential `exp(u • e i)`, the pinning isomorphism
`𝔾_a → U_i` that is the input to the Chevalley-Demazure group-scheme construction. The
nilpotency makes the exponential a finite sum, hence a polynomial map over any `ℚ`-algebra.

## Main definitions

* `TauCeti.DynkinType.pinnedExp`: the uniform exponential `u ↦ exp(u • e_i)` as a matrix
  over any `ℚ`-algebra, defined as a finite sum using the matrix dimension as bound.

## Main results

* `TauCeti.DynkinType.pinnedExp_zero`: the exponential at zero is the identity matrix.
* `TauCeti.DynkinType.pinnedExpNeg`: the uniform lowering exponential `u ↦ exp(u • f_i)`.
* `TauCeti.DynkinType.pinnedExpNeg_zero`: its value at zero.
* `TauCeti.DynkinType.pinnedExp_comm_of_matrix_comm`: commuting generators give commuting
  exponentials, the group-level form of a vanishing Lie bracket.
* `TauCeti.DynkinType.pinnedExp_comm_of_cartan_eq_zero`: the Chevalley commutator relation
  (commuting case) — when the Cartan matrix entry is zero (i.e., `α_i + α_j` is not a root),
  the root subgroups commute, via the Serre relation.
* `TauCeti.DynkinType.lie_lieBasis_e_e_e_of_cartan_eq_neg_one`: for a length-one root
  string (`A_{ji} = -1`), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes — the Heisenberg
  Lie-algebra structure underlying the non-commuting Chevalley commutator formula.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

Roadmap: ReductiveGroups (Layer 9, uniform pinned Chevalley-Demazure construction).
-/

public section

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-! ## The uniform exponential -/

/-- The uniform exponential of the `i`-th simple raising generator: `exp(u • e_i)` as a
finite sum over `k < Fintype.card (t.GeckIndex ht)`. Since `e_i` is nilpotent
(`TauCeti.DynkinType.isNilpotent_coe_lieBasis_e`), terms beyond the nilpotency index vanish,
so the matrix-dimension bound is safe. -/
def pinnedExp (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The exponential at `u = 0` is the identity matrix: only the `k = 0` term survives. -/
theorem pinnedExp_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExp ht R i 0 = 1 := by
  unfold pinnedExp
  have h0mem : (0 : ℕ) ∈ Finset.range (Fintype.card (t.GeckIndex ht)) := by
    simp only [Finset.mem_range]
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  rw [Finset.sum_eq_single_of_mem _ h0mem]
  · simp
  · intro k _ hk
    rw [zero_pow hk]
    simp

/-- The uniform lowering exponential `u ↦ exp(u • f_i)`, defined as the same finite sum with
the lowering generator. -/
def pinnedExpNeg (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The lowering exponential at `u = 0` is the identity matrix. -/
theorem pinnedExpNeg_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExpNeg ht R i 0 = 1 := by
  unfold pinnedExpNeg
  have h0mem : (0 : ℕ) ∈ Finset.range (Fintype.card (t.GeckIndex ht)) := by
    simp only [Finset.mem_range]
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  rw [Finset.sum_eq_single_of_mem _ h0mem]
  · simp
  · intro k _ hk
    rw [zero_pow hk]
    simp

/-! ## Commutator relations -/

/-- If the simple raising generators commute as matrices, their uniform exponentials commute.
This is the group-level reflection of a vanishing Lie bracket: when `⁅e_i, e_j⁆ = 0`, the
corresponding root subgroups commute. -/
theorem pinnedExp_comm_of_matrix_comm (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (u v : R)
    (hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  unfold pinnedExp
  -- Expand both products as double sums
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  -- Swap summation order on the left to match the right
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  -- Term-wise: (c_k • A^k) * (d_l • B^l) = (d_l • B^l) * (c_k • A^k)
  -- Scalars commute (commutative ring), matrices commute by hypothesis
  let Ei : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e i
  let Ej : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e j
  have hmat : ((Ei ^ k).map (algebraMap ℚ R)) * ((Ej ^ l).map (algebraMap ℚ R)) =
      ((Ej ^ l).map (algebraMap ℚ R)) * ((Ei ^ k).map (algebraMap ℚ R)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have hcomm' : Commute Ei Ej := hcomm
    exact (hcomm'.pow_pow k l).eq
  -- Distribute scalars: (c • A) * (d • B) = (c * d) • (A * B)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Use matrix commutativity to align the matrix factors
  rw [hmat]
  -- Now both sides have (B^l * A^k); scalars commute
  rw [mul_comm (u ^ k * _) (v ^ l * _)]

/-- The Lie bracket of distinct simple raising generators vanishes when the corresponding
Cartan matrix entry is zero. This is the Serre relation: when `A_{ji} = 0`, the exponent
`(-Aᵀ_{ij}).toNat = 0`, so `(ad e_i)^0 [e_i, e_j] = [e_i, e_j] = 0`. -/
theorem lie_lieBasis_e_e_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji}
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 0 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM, pow_zero] at hserre
  simpa using hserre

/-- When the Cartan matrix entry vanishes, the simple raising generators commute as matrices.
The Lie bracket in the matrix Lie algebra is the commutator, so a vanishing bracket gives
commuting matrices. -/
theorem coe_lieBasis_e_comm_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
    ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) := by
  have hbracket := t.lie_lieBasis_e_e_of_cartan_eq_zero ht i j hA
  -- The inclusion of the Lie subalgebra preserves brackets
  have hcoe : ((((⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ : t.lieAlgebra ht))) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      ⁅(((t.lieBasis ht).e i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ),
       (((t.lieBasis ht).e j) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)⁆ :=
    LieSubalgebra.coe_bracket (t.lieAlgebra ht) _ _
  rw [hbracket] at hcoe
  -- The coercion of 0 is 0
  simp only [ZeroMemClass.coe_zero] at hcoe
  -- For matrices, ⁅A, B⁆ = A * B - B * A
  have hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
      ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) -
      ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
      ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) = 0 := by
    have h := hcoe
    rw [LieRing.of_associative_ring_bracket] at h
    exact h.symm
  exact sub_eq_zero.mp hcomm

/-- The Chevalley commutator relation (commuting case): when the Cartan matrix entry is zero
— i.e., when `α_i + α_j` is not a root — the corresponding root subgroups commute. This
connects the root-theoretic hypothesis to the group-level commutativity via the Serre
relation and the matrix commutator. -/
theorem pinnedExp_comm_of_cartan_eq_zero (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (hA : t.cartanMatrix j i = 0) (u v : R) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  apply t.pinnedExp_comm_of_matrix_comm ht R i j u v
  exact t.coe_lieBasis_e_comm_of_cartan_eq_zero ht i j hA

/-! ## Length-one root strings: Heisenberg Lie algebra structure -/

/-- For a length-one root string (`A_{ji} = -1`, i.e., `α_i + α_j` is a root but
`2α_i + α_j` is not), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes. This is the Serre
relation: `(ad e_i)^{-A_{ji}}(⁅e_i, e_j⁆) = (ad e_i)(⁅e_i, e_j⁆) = 0`. Together with the symmetric
statement, this says the subalgebra generated by `e_i, e_j` is Heisenberg, the Lie-algebra
input to the Chevalley commutator formula
`[x_{α_i}(u), x_{α_j}(v)] = x_{α_i+α_j}(N_{ij} uv)`. -/
theorem lie_lieBasis_e_e_e_of_cartan_eq_neg_one (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = -1) :
    ⁅(t.lieBasis ht).e i, ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji} = -1
  -- So (-(Aᵀ)_{ij}).toNat = (-(-1)).toNat = 1
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 1 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM] at hserre
  -- (ad e_i)^1(⁅e_i, e_j⁆) = ⁅e_i, ⁅e_i, e_j⁆⁆
  simpa using hserre

/-- Symmetric version: for `A_{ij} = -1`, the bracket `⁅e_j, ⁅e_j, e_i⁆⁆` vanishes.
By antisymmetry of the bracket, this is `⁅e_j, ⁅e_i, e_j⁆⁆ = 0` up to sign, the other
Heisenberg centrality needed for the length-one commutator formula. -/
theorem lie_lieBasis_e_e_e_of_cartan_eq_neg_one' (i j : Fin t.rank)
    (hA : t.cartanMatrix i j = -1) :
    ⁅(t.lieBasis ht).e j, ⁅(t.lieBasis ht).e j, (t.lieBasis ht).e i⁆⁆ = 0 :=
  t.lie_lieBasis_e_e_e_of_cartan_eq_neg_one ht j i hA

end

end TauCeti.DynkinType
