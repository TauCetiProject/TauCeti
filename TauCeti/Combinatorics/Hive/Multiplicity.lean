/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Schur
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Combinatorics.Hive.GelfandTsetlin
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.LittlewoodRichardson
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.FDRep.DirectSum

/-!
# Tensor-product multiplicities, Schur expansions, and invariants via integer hives

Combining the object-level hive-to-Littlewood–Richardson equivalence of
`TauCeti.Combinatorics.Hive.LittlewoodRichardson` with Stembridge's Littlewood–Richardson rule for
Schur polynomials (`TauCeti.diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau`) and the
rational Weyl-module decomposition (`TauCeti.nonempty_equiv_tprod_rationalWeylRep`), this file
identifies integer hive counts with tensor-product multiplicities and invariant dimensions of
`GL n ℂ`, and specializes the finite-alphabet Schur expansion
(`TauCeti.Hive.diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount` in
`TauCeti.Combinatorics.Hive.Schur`):

* **Schur-polynomial expansion transport and sharpness**: coefficient-ring transport, evaluation
  transport, rank-lowering specialization along `Fin.snoc · 0`, and sharpness of the `N ≤ n`
  variable bound (`TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`), since the rank-`n`
  hive model suppresses shapes with more than `n` rows.
* **Intertwiner multiplicity** (`TauCeti.Hive.finrank_hom_eq_hiveCount`): for arbitrary signed
  dominant weights `λ, μ, γ` of `GL n ℂ`, the complex dimension of the intertwiner space
  `rationalWeylFDRep ℂ n γ ⟶ rationalWeylFDRep ℂ n λ ⊗ rationalWeylFDRep ℂ n μ` in
  `FDRep ℂ (GL (Fin n) ℂ)` equals `hiveCount (productBoundary λ μ γ)`.
* **Trilinear invariants** (`TauCeti.Hive.finrank_invariants_eq_hiveCount`): for arbitrary signed
  dominant weights `λ, μ, ν` of `GL n ℂ`, the invariant dimension
  `dim_ℂ Hom(𝟙_, V_λ ⊗ V_μ ⊗ V_ν)` equals the cyclic hive count `hiveCount ![λ.val, μ.val, ν.val]`.

## Main results

* `TauCeti.Hive.finrank_hom_eq_hiveCount`: Hom-space dimension between rational Weyl modules equals
  `hiveCount (productBoundary lam μ γ)`.
* `TauCeti.Hive.finrank_invariants_eq_hiveCount`: dimension of `GL n ℂ`-invariants in
  `V_lam ⊗ V_μ ⊗ V_ν` equals `hiveCount ![lam.val, μ.val, ν.val]`.
* `TauCeti.Hive.finrank_hom_two_std_std`, `TauCeti.Hive.finrank_invariants_two_std_checks`,
  `TauCeti.Hive.finrank_hom_rank_one`, `TauCeti.Hive.finrank_hom_rank_zero`,
  `TauCeti.Hive.finrank_invariants_rank_zero`, and
  `TauCeti.Hive.schur_mul_two_vars_ne_finsum_hiveCount_one`: concrete rank-`0`, rank-`1`, and
  rank-`2` representation-theoretic and sharpness checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of `GL_n(ℂ)` tensor products I: Proof of the
  saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Theorem 4 and Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), Research Paper 61, Theorem 1.
-/

public section

open CategoryTheory MonoidalCategory Matrix MvPolynomial YoungDiagram

namespace TauCeti.Hive

/-! ### Finite-alphabet Schur-polynomial expansion -/

private theorem finite_support_hiveCount_smul_diagramSchurPoly {n : ℕ} {R : Type*}
    [CommSemiring R] (lam μ : DominantWeight n) :
    (Function.support fun γ : DominantWeight n =>
      (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly n R γ.shape).Finite := by
  refine (finite_support_hiveCount_productBoundary lam μ).subset fun γ hγ => ?_
  rw [Function.mem_support] at hγ
  refine Nat.pos_of_ne_zero fun h0 => hγ ?_
  simp [h0]

/-- Coefficient-ring transport for the hive-indexed Schur sum along any semiring homomorphism
`f : R →+* S`. -/
theorem map_finsum_hiveCount_smul_diagramSchurPoly {n : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (lam μ : DominantWeight n) :
    MvPolynomial.map f
        (∑ᶠ γ : DominantWeight n,
          (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly n R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        (hiveCount (productBoundary lam μ γ) : S) • diagramSchurPoly n S γ.shape := by
  rw [map_finsum (MvPolynomial.map f)
    (finite_support_hiveCount_smul_diagramSchurPoly lam μ)]
  refine finsum_congr fun γ => ?_
  rw [smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_natCast, map_diagramSchurPoly,
    ← smul_eq_C_mul]

/-- Evaluation transport for the hive-indexed Schur sum along any semiring homomorphism
`f : R →+* S` and point `x : Fin n → S`. -/
theorem eval₂_finsum_hiveCount_smul_diagramSchurPoly {n : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : Fin n → S) (lam μ : DominantWeight n) :
    eval₂ f x
        (∑ᶠ γ : DominantWeight n,
          (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly n R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        (hiveCount (productBoundary lam μ γ) : S) • eval x (diagramSchurPoly n S γ.shape) := by
  rw [← MvPolynomial.eval_map, map_finsum_hiveCount_smul_diagramSchurPoly,
    map_finsum (eval x) (finite_support_hiveCount_smul_diagramSchurPoly lam μ)]
  refine finsum_congr fun γ => ?_
  rw [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]

/-- Setting the last variable to `0` transports the `(n + 1)`-variable hive-indexed Schur
expansion for polynomial weights of at most `n` rows to the `n`-variable expansion, where the
surviving hive coefficients match across ranks by
`TauCeti.Hive.hiveCount_productBoundary_eq_of_shape_eq`. -/
theorem aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly {n : ℕ} {R : Type*}
    [CommSemiring R] {lam μ : DominantWeight (n + 1)}
    (hl : lam.IsPolynomial) (hm : μ.IsPolynomial)
    (hln : lam.shape.colLen 0 ≤ n) (hmn : μ.shape.colLen 0 ≤ n) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0)
        (∑ᶠ γ : DominantWeight (n + 1),
          (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly (n + 1) R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        (hiveCount (productBoundary (weightOfShape n lam.shape) (weightOfShape n μ.shape) γ) :
          R) • diagramSchurPoly n R γ.shape := by
  simp_rw [Nat.cast_smul_eq_nsmul]
  rw [← diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount le_rfl hl hm, map_mul,
    aeval_snoc_zero_diagramSchurPoly, aeval_snoc_zero_diagramSchurPoly,
    ← shape_weightOfShape hln, ← shape_weightOfShape hmn,
    diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount le_rfl
      (isPolynomial_weightOfShape _ _) (isPolynomial_weightOfShape _ _),
    shape_weightOfShape hln, shape_weightOfShape hmn]

/-- Setting the last variable to `0` annihilates the `(n + 1)`-variable hive-indexed Schur
expansion when either polynomial input weight has `n + 1` rows. -/
theorem aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly_eq_zero {n : ℕ} {R : Type*}
    [CommSemiring R] {lam μ : DominantWeight (n + 1)}
    (hl : lam.IsPolynomial) (hm : μ.IsPolynomial)
    (hlt : n < lam.shape.colLen 0 ∨ n < μ.shape.colLen 0) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0)
        (∑ᶠ γ : DominantWeight (n + 1),
          (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly (n + 1) R γ.shape) = 0 := by
  simp_rw [Nat.cast_smul_eq_nsmul]
  rw [← diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount le_rfl hl hm, map_mul,
    aeval_snoc_zero_diagramSchurPoly, aeval_snoc_zero_diagramSchurPoly]
  rcases hlt with h | h
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen h, zero_mul]
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen h, mul_zero]

/-- Lifting rank-`n` polynomial weights to rank `n + 1` via `TauCeti.weightOfShape (n + 1)` and
setting the last variable to `0` recovers the rank-`n` hive-indexed Schur expansion. -/
theorem aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly_weightOfShape {n : ℕ}
    {R : Type*} [CommSemiring R] (lam μ : DominantWeight n)
    (hl : lam.IsPolynomial) (hm : μ.IsPolynomial) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0)
        (∑ᶠ γ : DominantWeight (n + 1),
          (hiveCount (productBoundary (weightOfShape (n + 1) lam.shape)
            (weightOfShape (n + 1) μ.shape) γ) : R) •
            diagramSchurPoly (n + 1) R γ.shape) =
      ∑ᶠ γ : DominantWeight n,
        (hiveCount (productBoundary lam μ γ) : R) • diagramSchurPoly n R γ.shape := by
  have hln : (weightOfShape (n + 1) lam.shape).shape.colLen 0 ≤ n := by
    rw [shape_weightOfShape ((DominantWeight.colLen_zero_shape_le lam).trans (Nat.le_succ n))]
    exact DominantWeight.colLen_zero_shape_le lam
  have hmn : (weightOfShape (n + 1) μ.shape).shape.colLen 0 ≤ n := by
    rw [shape_weightOfShape ((DominantWeight.colLen_zero_shape_le μ).trans (Nat.le_succ n))]
    exact DominantWeight.colLen_zero_shape_le μ
  rw [aeval_snoc_zero_finsum_hiveCount_smul_diagramSchurPoly
      (isPolynomial_weightOfShape _ _) (isPolynomial_weightOfShape _ _) hln hmn,
    shape_weightOfShape ((DominantWeight.colLen_zero_shape_le lam).trans (Nat.le_succ n)),
    shape_weightOfShape ((DominantWeight.colLen_zero_shape_le μ).trans (Nat.le_succ n)),
    weightOfShape_shape hl, weightOfShape_shape hm]

/-! ### Hom-space multiplicities and invariants on rational Weyl modules -/

open scoped Classical in
/-- Partition-indexed multiplicity sum matching `hiveCount (productBoundary lam μ γ)`. -/
private theorem sum_natCard_lrTableau_shift_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    (∑ ν : {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
        (ofPartition ν).colLen 0 ≤ n},
      if γ = (weightOfShape n (ofPartition ν.val)).shift (lam.detShift + μ.detShift) then
        Nat.card (LRTableau lam.detShiftShape (ofPartition ν.val) μ.detShiftShape)
      else 0) = hiveCount (productBoundary lam μ γ) := by
  let Sub := {ν : (lam.detShiftShape.card + μ.detShiftShape.card).Partition //
    (ofPartition ν).colLen 0 ≤ n}
  rw [hiveCount_productBoundary]
  split_ifs with hdet
  · set γ' := γ.shift (-(lam.detShift + μ.detShift))
    have hγ' : γ'.IsPolynomial := DominantWeight.isPolynomial_shift_neg_of_le_detShift hdet
    have heq_iff (ν : Sub) :
        γ = (weightOfShape n (ofPartition ν.val)).shift (lam.detShift + μ.detShift) ↔
          γ'.shape = ofPartition ν.val :=
      ⟨fun h => by
        have h' : γ' = weightOfShape n (ofPartition ν.val) := by simp [γ', h]
        rw [h', shape_weightOfShape ν.property],
      fun h => by
        have h' : weightOfShape n (ofPartition ν.val) = γ' := by rw [← h, weightOfShape_shape hγ']
        simp [h', γ']⟩
    have hsummand (ν : Sub) :
        (if γ = (weightOfShape n (ofPartition ν.val)).shift (lam.detShift + μ.detShift) then
          Nat.card (LRTableau lam.detShiftShape (ofPartition ν.val) μ.detShiftShape)
        else 0) =
          if γ'.shape = ofPartition ν.val then
            Nat.card (LRTableau lam.detShiftShape (ofPartition ν.val) μ.detShiftShape)
          else 0 :=
      if_congr (heq_iff ν) rfl rfl
    rw [Finset.sum_congr rfl fun ν _ => hsummand ν]
    by_cases hcard : γ'.shape.card = lam.detShiftShape.card + μ.detShiftShape.card
    · let ν₀ : Sub := ⟨γ'.shape.toPartition hcard, by simp⟩
      have hν₀ (ν : Sub) : γ'.shape = ofPartition ν.val ↔ ν = ν₀ :=
        ⟨fun h => Subtype.ext <| YoungDiagram.ofPartition_injective <| by
          rw [← h, YoungDiagram.ofPartition_toPartition],
        fun h => by rw [h, YoungDiagram.ofPartition_toPartition]⟩
      rw [Finset.sum_congr rfl fun ν _ => if_congr (hν₀ ν) rfl rfl,
        Finset.sum_ite_eq' Finset.univ ν₀]
      simp [ν₀]
    · have hne (ν : Sub) : γ'.shape ≠ ofPartition ν.val := fun h =>
        hcard (by rw [h, YoungDiagram.card_ofPartition])
      simp [hne, isEmpty_lrTableau_of_card_ne hcard]
  · have hne (ν : Sub) :
        γ ≠ (weightOfShape n (ofPartition ν.val)).shift (lam.detShift + μ.detShift) := fun h =>
      hdet <| by
        cases n with
        | zero => simp
        | succ m =>
          refine DominantWeight.isPolynomial_shift_neg_iff_le_detShift.mp ?_
          simp [h]
    simp [hne]

/-- **The hive model of tensor-product multiplicities for `GL n ℂ`**: for all dominant weights
`λ, μ, γ` of `GL n ℂ`, the complex dimension of the space of intertwiners from `V_γ` to
`V_λ ⊗ V_μ` in `FDRep ℂ (GL (Fin n) ℂ)` is `hiveCount (productBoundary λ μ γ)`. -/
theorem finrank_hom_eq_hiveCount {n : ℕ} (lam μ γ : DominantWeight n) :
    Module.finrank ℂ (rationalWeylFDRep ℂ n γ ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) =
      hiveCount (productBoundary lam μ γ) := by
  classical
  obtain ⟨he⟩ := nonempty_equiv_tensor_rationalWeylFDRep lam μ
  rw [FDRep.finrank_hom_of_equiv_directSum _ _ _ he, Fintype.sum_sigma,
    ← sum_natCard_lrTableau_shift_eq_hiveCount lam μ γ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [finrank_hom_rationalWeylFDRep, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_boole, card_boundedYamanouchi_eq_natCard_lrTableau ν.property]

/-- Reduces `Hom(𝟙, V_λ ⊗ V_μ ⊗ V_ν)` to `Hom(V_{ν*}, V_λ ⊗ V_μ)` by decomposing `V_λ ⊗ V_μ`
into irreducibles `⊕_p V_σ`, evaluating `dim Hom(𝟙, V_σ ⊗ V_ν) = δ_{ν*, σ} = dim Hom(V_{ν*}, V_σ)`
on each summand, and re-summing. -/
private theorem finrank_hom_tensorUnit_tensor_eq {n : ℕ} (lam μ ν : DominantWeight n) :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ ⊗
          rationalWeylFDRep ℂ n ν) =
      Module.finrank ℂ (rationalWeylFDRep ℂ n ν.dual ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) := by
  classical
  obtain ⟨i₀⟩ := nonempty_iso_tensorUnit_rationalWeylFDRep_zero ℂ n
  rw [(Linear.homCongr ℂ i₀ (α_ _ _ _).symm).finrank_eq]
  obtain ⟨he₁₂⟩ := nonempty_equiv_tensor_rationalWeylFDRep lam μ
  -- Decompose `V_λ ⊗ V_μ ⊗ V_ν ≅ ⊕_p V_{σ(p)} ⊗ V_ν`.
  have he₃ := (FDRep.tprodEquiv
      (rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ) (rationalWeylFDRep ℂ n ν)).trans <|
    (he₁₂.tprod (.refl _)).trans <| (Representation.tprodDirectSumLeftEquiv _ _).trans <|
      Representation.directSumEquivCongr fun p =>
        (FDRep.tprodEquiv (rationalWeylFDRep ℂ n
          ((weightOfShape n (ofPartition p.fst.val)).shift (lam.detShift + μ.detShift)))
          (rationalWeylFDRep ℂ n ν)).symm
  -- Each summand satisfies `dim Hom(𝟙, V_σ ⊗ V_ν) = δ_{ν*, σ} = dim Hom(V_{ν*}, V_σ)`,
  -- which re-sums to `dim Hom(V_{ν*}, V_λ ⊗ V_μ)`.
  have hrot (σ : DominantWeight n) :
      hiveCount (productBoundary σ ν 0) = if ν.dual = σ then 1 else 0 := by
    have hb : productBoundary σ ν 0 = fun s => productBoundary 0 σ ν.dual (s + 1) := by
      ext s i; fin_cases s <;> simp
    rw [hb, hiveCount_rotate, hiveCount_productBoundary_zero_left]
  have hterm (σ : DominantWeight n) :
      Module.finrank ℂ (rationalWeylFDRep ℂ n 0 ⟶
          rationalWeylFDRep ℂ n σ ⊗ rationalWeylFDRep ℂ n ν) =
        Module.finrank ℂ (rationalWeylFDRep ℂ n ν.dual ⟶ rationalWeylFDRep ℂ n σ) := by
    rw [finrank_hom_eq_hiveCount, hrot σ, finrank_hom_rationalWeylFDRep]
  rw [FDRep.finrank_hom_of_equiv_directSum _ _ _ he₃]
  refine (Finset.sum_congr rfl fun p _ => hterm _).trans ?_
  exact (FDRep.finrank_hom_of_equiv_directSum _ _ _ he₁₂).symm

/-- **The invariant form of the hive model for `GL n ℂ`**: for all dominant weights `λ, μ, ν` of
`GL n ℂ`, the complex dimension of the space of `GL n ℂ`-invariants
`𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ⟶ V_λ ⊗ V_μ ⊗ V_ν` equals the number of integer hives with cyclic
boundary `![λ.val, μ.val, ν.val]`. -/
theorem finrank_invariants_eq_hiveCount {n : ℕ} (lam μ ν : DominantWeight n) :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin n) ℂ)) ⟶
        rationalWeylFDRep ℂ n lam ⊗ rationalWeylFDRep ℂ n μ ⊗
          rationalWeylFDRep ℂ n ν) =
      hiveCount ![lam.val, μ.val, ν.val] := by
  have hdual : productBoundary lam μ ν.dual = ![lam.val, μ.val, ν.val] := by
    ext s i; fin_cases s <;> simp
  rw [finrank_hom_tensorUnit_tensor_eq, finrank_hom_eq_hiveCount, hdual]

/-! ### Concrete representation-theoretic and finite-alphabet checks -/

/-- Rank-`0` check: on `GL 0 ℂ`, every intertwiner space `V_γ ⟶ V_λ ⊗ V_μ` is one-dimensional,
matching the unique empty hive. -/
theorem finrank_hom_rank_zero (lam μ γ : DominantWeight 0) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 0 γ ⟶
        rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ) = 1 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_rank_zero]

/-- Rank-`0` invariant check: on `GL 0 ℂ`, every trilinear invariant space
`𝟙_ ⟶ V_λ ⊗ V_μ ⊗ V_ν` is one-dimensional, matching the unique empty hive. -/
theorem finrank_invariants_rank_zero (lam μ ν : DominantWeight 0) :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 0) ℂ)) ⟶
        rationalWeylFDRep ℂ 0 lam ⊗ rationalWeylFDRep ℂ 0 μ ⊗
          rationalWeylFDRep ℂ 0 ν) = 1 := by
  rw [finrank_invariants_eq_hiveCount, hiveCount_rank_zero]

open scoped Classical in
/-- Rank-`1` check: on `GL 1 ℂ`, `Hom(V_g, V_a ⊗ V_b)` has dimension `1` when `g = a + b` and `0`
otherwise. -/
theorem finrank_hom_rank_one (a b g : DominantWeight 1) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 1 g ⟶
        rationalWeylFDRep ℂ 1 a ⊗ rationalWeylFDRep ℂ 1 b) =
      if g = a + b then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_one_productBoundary]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · ext i; rw [Fin.fin_one_eq_zero i]; simp [← h]
  · subst h; rfl

/-- Rank-`2` tensor-product check: in `FDRep ℂ (GL (Fin 2) ℂ)`, `V_{(1, 0)} ⊗ V_{(1, 0)}` contains
`V_{(2, 0)}` and `V_{(1, 1)}` each with multiplicity `1` and every other `V_γ` with multiplicity
`0`. -/
theorem finrank_hom_two_std_std (γ : DominantWeight 2) :
    Module.finrank ℂ (rationalWeylFDRep ℂ 2 γ ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩) =
      if γ = ⟨![2, 0], by decide⟩ ∨ γ = ⟨![1, 1], by decide⟩ then 1 else 0 := by
  rw [finrank_hom_eq_hiveCount, hiveCount_two_std_std_eq]

/-- Rank-`2` trilinear invariant check: `dim_ℂ (V_{(1, 0)} ⊗ V_{(1, 0)} ⊗ V_{(-1, -1)})^{GL 2 ℂ} =
1` (via `det⁻¹`), whereas `dim_ℂ (V_{(1, 0)} ⊗ V_{(1, 0)} ⊗ V_{(0, 0)})^{GL 2 ℂ} = 0` (nonzero
total degree). -/
theorem finrank_invariants_two_std_checks :
    Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 2) ℂ)) ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![-1, -1], by decide⟩) = 1 ∧
      Module.finrank ℂ (𝟙_ (FDRep ℂ (GL (Fin 2) ℂ)) ⟶
        rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![1, 0], by decide⟩ ⊗
          rationalWeylFDRep ℂ 2 ⟨![0, 0], by decide⟩) = 0 := by
  rw [finrank_invariants_eq_hiveCount, finrank_invariants_eq_hiveCount]
  constructor
  · have hb : ![(⟨![1, 0], by decide⟩ : DominantWeight 2).val,
        (⟨![1, 0], by decide⟩ : DominantWeight 2).val,
        (⟨![-1, -1], by decide⟩ : DominantWeight 2).val] =
        productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
      ext s i; fin_cases s <;> fin_cases i <;> simp
    rw [hb]
    exact hiveCount_two_std_std_det
  · refine hiveCount_eq_zero_of_sum_ne_zero ?_
    simp [Fin.sum_univ_three, Fin.sum_univ_two]

private theorem shape_eq_of_one_two (w₁ : DominantWeight 1) (w₂ : DominantWeight 2)
    (h0 : w₁.val 0 = w₂.val 0) (h1 : w₂.val 1 = 0) : w₁.shape = w₂.shape := by
  refine YoungDiagram.rowLen_injective (funext fun i => ?_)
  match i with
  | 0 =>
    have a := w₁.rowLen_shape 0; have b := w₂.rowLen_shape 0
    simp only [Fin.val_zero, h0] at a b; omega
  | 1 =>
    have b := w₂.rowLen_shape 1
    rw [w₁.rowLen_shape_eq_zero_of_le le_rfl]; simp only [Fin.val_one, h1] at b; omega
  | i + 2 =>
    rw [w₁.rowLen_shape_eq_zero_of_le (by omega), w₂.rowLen_shape_eq_zero_of_le (by omega)]

/-- Sharpness of the `N ≤ n` alphabet bound in
`diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount`: for rank `1` weights
`λ = μ = (1)` evaluated in `2` variables, `s_{(1)}² = s_{(2)} + s_{(1, 1)}`, whereas the rank-`1`
hive sum produces only `s_{(2)}` and omits the nonzero term `s_{(1, 1)}`. -/
theorem schur_mul_two_vars_ne_finsum_hiveCount_one :
    let ω : DominantWeight 1 := ⟨![1], by decide⟩
    diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape ≠
      ∑ᶠ γ : DominantWeight 1,
        (hiveCount (productBoundary ω ω γ) : ℤ) • diagramSchurPoly 2 ℤ γ.shape := by
  intro ω heq
  let std₂ : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let sym₂ : DominantWeight 2 := ⟨![2, 0], by decide⟩
  let det₂ : DominantWeight 2 := ⟨![1, 1], by decide⟩
  have hstd₂ : std₂.IsPolynomial := by rw [DominantWeight.isPolynomial_def]; decide
  have hrhs₁ : (∑ᶠ γ : DominantWeight 1,
      (hiveCount (productBoundary ω ω γ) : ℤ) • diagramSchurPoly 2 ℤ γ.shape) =
      diagramSchurPoly 2 ℤ sym₂.shape := by
    rw [finsum_eq_single _ (ω + ω)]
    · rw [shape_eq_of_one_two (ω + ω) sym₂ rfl rfl]
      simp [hiveCount_one_productBoundary]
    · intro γ hγ
      have hne : ω.val 0 + ω.val 0 ≠ γ.val 0 := fun h => hγ <| by
        ext i; rw [Fin.fin_one_eq_zero i]; simp [← h]
      simp [hiveCount_one_productBoundary, hne]
  have hsupp₂ : Function.support
      (fun δ : DominantWeight 2 =>
        (hiveCount (productBoundary std₂ std₂ δ) : ℤ) • diagramSchurPoly 2 ℤ δ.shape) ⊆
      ({sym₂, det₂} : Finset (DominantWeight 2)) := by
    intro δ hδ
    rw [Function.mem_support] at hδ
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hnot
    dsimp only [sym₂, det₂] at hnot
    rw [hiveCount_two_std_std_eq] at hδ
    simp only [hnot, ↓reduceIte, CharP.cast_eq_zero, zero_smul] at hδ
    exact hδ rfl
  have hlhs₂ : diagramSchurPoly 2 ℤ ω.shape * diagramSchurPoly 2 ℤ ω.shape =
      diagramSchurPoly 2 ℤ sym₂.shape + diagramSchurPoly 2 ℤ det₂.shape := by
    simp_rw [Nat.cast_smul_eq_nsmul] at hsupp₂ ⊢
    rw [shape_eq_of_one_two ω std₂ rfl rfl,
      diagramSchurPoly_mul_diagramSchurPoly_eq_finsum_hiveCount le_rfl hstd₂ hstd₂,
      finsum_eq_sum_of_support_subset _ hsupp₂, Finset.sum_pair (by decide : sym₂ ≠ det₂),
      hiveCount_two_std_std_eq, hiveCount_two_std_std_eq]
    simp [sym₂, det₂]
  rw [hlhs₂, hrhs₁] at heq
  exact diagramSchurPoly_ne_zero det₂.colLen_zero_shape_le (add_eq_left.mp heq)

end TauCeti.Hive
