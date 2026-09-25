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
  over any `ℚ`-algebra, as Mathlib's `IsNilpotent.exp` of the scalar multiple of the mapped
  generator.

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
* `TauCeti.DynkinType.pinnedExp_mul_pinnedExp_neg`: the uniform exponential is inverted by
  negating the parameter, via `IsNilpotent.exp_mul_exp_neg_self`.

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

/-- A scalar multiple of a nilpotent rational matrix, mapped to a `ℚ`-algebra, stays
nilpotent: map the rational nilpotency along `algebraMap ℚ R`, then scale. This feeds the
hypotheses of Mathlib's `IsNilpotent.exp` lemmas. -/
private theorem isNilpotent_smul_map (X : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (hX : IsNilpotent X) (R : Type*) [CommRing R] [Algebra ℚ R] (u : R) :
    IsNilpotent (u • (X.map (algebraMap ℚ R))) :=
  (hX.map (algebraMap ℚ R).mapMatrix).smul u

/-! ## The uniform exponential -/

/-- The uniform exponential of a scalar multiple of a mapped rational matrix, via Mathlib's
`IsNilpotent.exp`. This is the shared body of the raising and lowering pinning exponentials
(`TauCeti.DynkinType.pinnedExp` and `TauCeti.DynkinType.pinnedExpNeg`), which differ only in
the generator fed in. -/
private def pinnedExpAux (X : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (R : Type*) [CommRing R] [Algebra ℚ R] (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  IsNilpotent.exp (u • (X.map (algebraMap ℚ R)))

/-- The uniform exponential of the `i`-th simple raising generator: `exp(u • e_i)` as a
matrix over any `ℚ`-algebra. This is Mathlib's `IsNilpotent.exp` applied to the scalar
multiple of the generator mapped along `algebraMap ℚ R`; nilpotency
(`TauCeti.DynkinType.isNilpotent_coe_lieBasis_e`) makes the exponential a finite sum,
hence a polynomial map. -/
def pinnedExp (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  t.pinnedExpAux ht ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) R u

/-- The exponential at `u = 0` is the identity matrix, by `IsNilpotent.exp_zero`. -/
theorem pinnedExp_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExp ht R i 0 = 1 := by
  simp [pinnedExp, pinnedExpAux]

/-- The uniform lowering exponential `u ↦ exp(u • f_i)`, as `IsNilpotent.exp` of the scalar
multiple of the mapped lowering generator. -/
def pinnedExpNeg (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  t.pinnedExpAux ht ((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) R u

/-- The lowering exponential at `u = 0` is the identity matrix, by `IsNilpotent.exp_zero`. -/
theorem pinnedExpNeg_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExpNeg ht R i 0 = 1 := by
  simp [pinnedExpNeg, pinnedExpAux]

/-! ## Commutator relations -/

/-- If the simple raising generators commute as matrices, their uniform exponentials commute.
This is the group-level reflection of a vanishing Lie bracket: when `⁅e_i, e_j⁆ = 0`, the
corresponding root subgroups commute. The proof is `IsNilpotent.exp_add_of_commute`: the
mapped generators commute (mapping `hcomm` along `algebraMap ℚ R`), hence so do their
scalar multiples, and `exp` turns the sum into the product both ways. -/
theorem pinnedExp_comm_of_matrix_comm (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (u v : R)
    (hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  have hcomm' : Commute
      ((((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)).map
        (algebraMap ℚ R))
      ((((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)).map
        (algebraMap ℚ R)) := by
    -- Map the commutativity along `algebraMap ℚ R` via Mathlib's `Commute.map`
    -- (`Commute` is definitionally the equation, so `hcomm` serves directly).
    simpa using Commute.map (show Commute _ _ from hcomm) (algebraMap ℚ R).mapMatrix
  have hC : Commute
      (u • ((((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)).map
        (algebraMap ℚ R)))
      (v • ((((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)).map
        (algebraMap ℚ R))) :=
    (hcomm'.smul_left u).smul_right v
  have h1 := t.isNilpotent_smul_map ht
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (t.isNilpotent_coe_lieBasis_e ht i) R u
  have h2 := t.isNilpotent_smul_map ht
    ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (t.isNilpotent_coe_lieBasis_e ht j) R v
  unfold pinnedExp pinnedExpAux
  rw [← IsNilpotent.exp_add_of_commute hC h1 h2,
    ← IsNilpotent.exp_add_of_commute hC.symm h2 h1, add_comm]

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
commuting matrices, via `commute_iff_lie_eq`. -/
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
  rw [hbracket, ZeroMemClass.coe_zero] at hcoe
  exact (commute_iff_lie_eq.mpr hcoe.symm).eq

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

/-! ## Exponential inverse -/

/-- The uniform exponential is inverted by negating the parameter:
`exp(u • e_i) * exp(-u • e_i) = 1`, by `IsNilpotent.exp_mul_exp_neg_self`. -/
theorem pinnedExp_mul_pinnedExp_neg (R : Type*) [CommRing R] [Algebra ℚ R]
    (i : Fin t.rank) (u : R) :
    t.pinnedExp ht R i u * t.pinnedExp ht R i (-u) = 1 := by
  have h := t.isNilpotent_smul_map ht
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (t.isNilpotent_coe_lieBasis_e ht i) R u
  unfold pinnedExp pinnedExpAux
  rw [neg_smul]
  exact IsNilpotent.exp_mul_exp_neg_self h

end

end TauCeti.DynkinType
