/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Relative
public import TauCeti.Algebra.Lie.Unitary
public import TauCeti.Analysis.Complex.TateLine
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Lie.Cohomology.SymmetricPair
import TauCeti.Data.Matrix.Block
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.LinearAlgebra.Matrix.Trace.Alternating
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# The relative trace representative of the Borel class

The representative in Burgos Gil, Proposition 9.25, is the alternated trace of the ordered
product of the Hermitian sums `X + Xᴴ`, multiplied by
`(-1)^k k! / (2k + 1)!`. Its degree is `2k + 1`, and its weight is `k + 1`.

## References

* J. I. Burgos Gil, *The Regulators of Beilinson and Borel*, CRM Monograph 15 (2002),
  §9.7, Proposition 9.25, p. 87.
-/

public section

noncomputable section

open Matrix ComplexConjugate CategoryTheory TauCeti.LieModule.Cohomology

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.BorelRegulator

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The sum of a matrix and its adjoint used in the relative Borel representative. -/
private def hermitianSum : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ :=
  LinearMap.id + (Matrix.conjTransposeLinearEquiv ι ι ℝ ℂ).toLinearMap

omit [Fintype ι] [DecidableEq ι] in
@[simp]
private theorem hermitianSum_apply (X : Matrix ι ι ℂ) : hermitianSum ι X = X + Xᴴ := by rfl

/-- The relative Borel trace form of weight `k + 1`, with the suspended Chern normalization
of Burgos Gil, Proposition 9.25. -/
def borelRelativeForm (k : ℕ) : Matrix ι ι ℂ [⋀^Fin (2 * k + 1)]→ₗ[ℝ] ℂ :=
  (((-1 : ℝ) ^ k * k.factorial / (2 * k + 1).factorial) •
    Matrix.alternatingTrace ℝ ι ℂ (2 * k + 1)).compLinearMap (hermitianSum ι)

/-- The exact formula for the relative representative, including its normalization. -/
theorem borelRelativeForm_apply (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    borelRelativeForm ι k v = ((-1 : ℝ) ^ k * k.factorial / (2 * k + 1).factorial) •
      ∑ σ : Equiv.Perm (Fin (2 * k + 1)), Equiv.Perm.sign σ •
        Matrix.trace (List.ofFn fun i ↦ v (σ i) + (v (σ i))ᴴ).prod := by
  simp [borelRelativeForm, Matrix.alternatingTrace_apply]

/-- The representative vanishes whenever an argument belongs to the unitary Lie algebra. -/
theorem borelRelativeForm_eq_zero_of_mem_unitaryLieAlgebra (k : ℕ)
    (v : Fin (2 * k + 1) → Matrix ι ι ℂ) (i : Fin (2 * k + 1))
    (hi : v i ∈ unitaryLieAlgebra ι) : borelRelativeForm ι k v = 0 := by
  rw [borelRelativeForm, AlternatingMap.compLinearMap_apply]
  apply AlternatingMap.map_coord_zero _ i
  simp [mem_unitaryLieAlgebra_iff.mp hi]

/-- Taking the Hermitian sum intertwines the adjoint action of the unitary Lie algebra. -/
private theorem hermitianSum_lie {Y : Matrix ι ι ℂ} (hY : Y ∈ unitaryLieAlgebra ι)
    (X : Matrix ι ι ℂ) : hermitianSum ι ⁅Y, X⁆ = ⁅Y, hermitianSum ι X⁆ := by
  simp only [hermitianSum_apply, Ring.lie_def, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, mem_unitaryLieAlgebra_iff.mp hY]
  noncomm_ring

/-- Complex conjugation multiplies the relative form by the Tate sign `(-1)^k`. -/
theorem star_borelRelativeForm (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    star (borelRelativeForm ι k v) = (-1 : ℝ) ^ k • borelRelativeForm ι k v := by
  have hsign : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2 * k + 1))) =
      (-1 : ℤˣ) ^ k := by
    rw [Fin.sign_revPerm, Nat.neg_one_pow_choose_two]
    congr 1
    omega
  have hherm : (fun i ↦ (hermitianSum ι (v i))ᴴ) = fun i ↦ hermitianSum ι (v i) := by
    ext i
    simp [hermitianSum_apply, add_comm]
  simp only [borelRelativeForm, AlternatingMap.compLinearMap_apply, smul_apply,
    star_smul, star_trivial, Matrix.star_alternatingTrace, hsign, hherm]
  rw [smul_comm]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.coe_neg_one,
    ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Every value lies in the exact real Tate line `(2πi)^k ℝ`. -/
theorem borelRelativeForm_mem_tateLine (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    borelRelativeForm ι k v ∈ Complex.realTateLine k := by
  rw [Complex.mem_realTateLine_iff_conj_eq]
  simpa [Complex.real_smul] using star_borelRelativeForm ι k v

/-- The relative trace form with coefficients in the native trivial Lie module used by the
Chevalley–Eilenberg complex. -/
def borelRelativeCochain (k : ℕ) :
    Matrix ι ι ℂ [⋀^Fin (2 * k + 1)]→ₗ[ℝ]
      TrivialLieModule ℝ (Matrix ι ι ℂ) (Complex.realTateLine k) :=
  ((TrivialLieModule.equiv ℝ (Matrix ι ι ℂ)
    (Complex.realTateLine k)).symm.toLinearMap).compAlternatingMap
      ((borelRelativeForm ι k).codRestrict (Complex.realTateLine k)
        (borelRelativeForm_mem_tateLine ι k))

@[simp]
theorem borelRelativeCochain_apply (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    (TrivialLieModule.equiv ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)
      (borelRelativeCochain ι k v) : ℂ) =
      borelRelativeForm ι k v := by
  simp [borelRelativeCochain]

/-- The Borel representative is annihilated by all unitary Lie derivatives. -/
@[simp]
theorem lie_borelRelativeCochain (k : ℕ) {Y : Matrix ι ι ℂ}
    (hY : Y ∈ unitaryLieAlgebra ι) : ⁅Y, borelRelativeCochain ι k⁆ = 0 := by
  ext v
  apply (TrivialLieModule.equiv ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)).injective
  apply Subtype.ext
  simp only [AlternatingMap.lie_apply, LieModule.IsTrivial.trivial,
    map_zero, zero_apply, zero_sub]
  simp only [map_neg, map_sum, Submodule.coe_neg, Submodule.coe_sum,
    borelRelativeCochain_apply, Submodule.coe_zero]
  rw [neg_eq_zero]
  simp only [borelRelativeForm, AlternatingMap.compLinearMap_apply,
    smul_apply, ← Finset.smul_sum]
  have hupdate (i : Fin (2 * k + 1)) :
      (fun j ↦ hermitianSum ι (Function.update v i ⁅Y, v i⁆ j)) =
        Function.update (fun j ↦ hermitianSum ι (v j)) i ⁅Y, hermitianSum ι (v i)⁆ := by
    simpa only [Function.comp_def, hermitianSum_lie ι hY] using
      Function.comp_update (hermitianSum ι) v i ⁅Y, v i⁆
  simp only [hupdate, Matrix.sum_alternatingTrace_update_lie, smul_zero]

/-- The exact Borel cochain belongs to the relative Chevalley–Eilenberg cochains of
`(𝔤𝔩(ℂ), 𝔲)`, with both horizontality and infinitesimal invariance proved. -/
theorem borelRelativeCochain_mem (k : ℕ) :
    borelRelativeCochain ι k ∈ LieModule.Cohomology.relativeCochains ℝ
      (TrivialLieModule ℝ (Matrix ι ι ℂ) (Complex.realTateLine k))
      (unitaryLieAlgebra ι) (2 * k + 1) := by
  refine LieModule.Cohomology.mem_relativeCochains_iff.mpr ⟨?_, fun Y hY ↦
    lie_borelRelativeCochain ι k hY⟩
  intro v i hi
  apply (TrivialLieModule.equiv ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)).injective
  apply Subtype.ext
  simpa using borelRelativeForm_eq_zero_of_mem_unitaryLieAlgebra ι k v i hi

/-- The relative Borel representative is a cocycle for the actual Chevalley–Eilenberg
differential. The Hermitian complement has skew-Hermitian commutators. -/
@[simp]
theorem d_borelRelativeCochain (k : ℕ) :
    LieModule.Cohomology.d ℝ (Matrix ι ι ℂ)
      (TrivialLieModule ℝ (Matrix ι ι ℂ) (Complex.realTateLine k))
      (2 * k + 1) (borelRelativeCochain ι k) = 0 := by
  have hsup : (unitaryLieAlgebra ι).toSubmodule ⊔
      selfAdjoint.submodule ℝ (Matrix ι ι ℂ) = ⊤ := by
    apply eq_top_iff.mpr
    intro X _
    rw [Submodule.mem_sup]
    refine ⟨skewAdjointPart ℝ X, ?_, selfAdjointPart ℝ X,
      (selfAdjointPart ℝ X).property, ?_⟩
    · exact mem_unitaryLieAlgebra_iff.mpr (skewAdjointPart ℝ X).property
    · rw [add_comm]
      exact StarModule.selfAdjointPart_add_skewAdjointPart ℝ X
  have hbracket (X : Matrix ι ι ℂ) (hX : X ∈ selfAdjoint.submodule ℝ (Matrix ι ι ℂ))
      (Y : Matrix ι ι ℂ) (hY : Y ∈ selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
      ⁅X, Y⁆ ∈ unitaryLieAlgebra ι := by
    rw [mem_unitaryLieAlgebra_iff]
    -- Express membership in the self-adjoint submodule as a conjugate-transpose equation.
    change Xᴴ = X at hX
    change Yᴴ = Y at hY
    simp only [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX, hY]
    noncomm_ring
  exact LieModule.Cohomology.d_eq_zero_of_mem_relativeCochains hsup hbracket
    (borelRelativeCochain_mem ι k)

/-- Taking the Hermitian sum commutes with unitary conjugation. -/
private theorem hermitianSum_unitaryConjugation (U : unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    hermitianSum ι (unitaryConjugation ι U X) =
      unitaryConjugation ι U (hermitianSum ι X) := by
  simp [hermitianSum_apply, unitaryConjugation_apply, Matrix.star_eq_conjTranspose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The Borel trace form is invariant under the unitary group. -/
theorem borelRelativeForm_unitaryConjugation (k : ℕ) (U : unitaryGroup ι ℂ)
    (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    borelRelativeForm ι k (fun i ↦ unitaryConjugation ι U (v i)) =
      borelRelativeForm ι k v := by
  simp only [borelRelativeForm, AlternatingMap.compLinearMap_apply, smul_apply,
    hermitianSum_unitaryConjugation, Matrix.alternatingTrace_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hprod := map_list_prod (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U)
    (List.ofFn fun i ↦ hermitianSum ι (v (σ i)))
  simp only [List.map_ofFn, Function.comp_def, Unitary.conjStarAlgAut_apply] at hprod
  simp only [unitaryConjugation_apply, ← hprod]
  simpa only [unitaryConjugation_apply] using
    trace_unitaryConjugation U (List.ofFn fun i ↦ hermitianSum ι (v (σ i))).prod

/-- The representative lies in the native relative cochain space with the unitary group
equivariance condition, using trivial coefficients. -/
theorem borelRelativeCochain_mem_equivariant (k : ℕ) :
    borelRelativeCochain ι k ∈ LieModule.Cohomology.equivariantRelativeCochains ℝ
      (TrivialLieModule ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)) (unitaryConjugation ι)
      (fun _ ↦ LinearMap.id) (unitaryLieAlgebra ι) (2 * k + 1) := by
  refine LieModule.Cohomology.mem_equivariantRelativeCochains_iff.mpr
    ⟨borelRelativeCochain_mem ι k, fun U v ↦ ?_⟩
  apply (TrivialLieModule.equiv ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)).injective
  apply Subtype.ext
  simpa only [borelRelativeCochain_apply, LinearMap.id_apply] using
    borelRelativeForm_unitaryConjugation ι k U v

/-- Simultaneously conjugating the matrix entries and coefficients preserves the Borel
representative. -/
theorem borelRelativeForm_conj (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    borelRelativeForm ι k (fun i ↦ (v i).map (starRingEnd ℂ)) =
      star (borelRelativeForm ι k v) := by
  rw [borelRelativeForm_apply, borelRelativeForm_apply]
  simp only [star_smul, star_trivial, star_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  have hsign : star (Equiv.Perm.sign σ) = Equiv.Perm.sign σ := by
    apply Units.ext
    simp
  rw [hsign]
  congr 1
  have hsum (X : Matrix ι ι ℂ) :
      X.map (starRingEnd ℂ) + (X.map (starRingEnd ℂ))ᴴ =
        (X + Xᴴ).map (starRingEnd ℂ) := by
    ext a b
    simp
  simpa only [hsum, List.map_ofFn, Function.comp_def, RingHom.mapMatrix_apply,
    starRingEnd_apply] using
    Matrix.trace_list_prod_map_mapMatrix (starRingEnd ℂ)
      (List.ofFn fun i ↦ v (σ i) + (v (σ i))ᴴ)

/-- A zero block in the additional coordinates preserves the positive-degree Borel
representative. This is the derivative of the trailing-identity group inclusion. -/
theorem borelRelativeForm_fromBlocks_zero (κ : Type*) [Fintype κ] [DecidableEq κ]
    (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    borelRelativeForm (ι ⊕ κ) k
      (fun i ↦ Matrix.fromBlocks (v i) 0 0 (0 : Matrix κ κ ℂ)) =
        borelRelativeForm ι k v := by
  rw [borelRelativeForm_apply, borelRelativeForm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hsum (X : Matrix ι ι ℂ) :
      Matrix.fromBlocks X 0 0 (0 : Matrix κ κ ℂ) +
          (Matrix.fromBlocks X 0 0 (0 : Matrix κ κ ℂ))ᴴ =
        Matrix.fromBlocks (X + Xᴴ) 0 0 (0 : Matrix κ κ ℂ) := by
    rw [Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [Matrix.fromBlocks_add]
    simp
  simp only [hsum]
  have hprod := (List.ofFn fun i ↦ v (σ i) + (v (σ i))ᴴ).prod_hom_nonempty
    (Matrix.fromBlocks₁₁NonUnitalStarAlgHom ℝ ℂ ι κ) (by simp)
  simp only [List.map_ofFn, Function.comp_def,
    Matrix.fromBlocks₁₁NonUnitalStarAlgHom_apply] at hprod
  rw [hprod, Matrix.trace_fromBlocks, Matrix.trace_zero, add_zero]

/-- Stabilization preserves the representative as a value of the actual Tate line. -/
theorem borelRelativeCochain_fromBlocks_zero (κ : Type*) [Fintype κ] [DecidableEq κ]
    (k : ℕ) (v : Fin (2 * k + 1) → Matrix ι ι ℂ) :
    TrivialLieModule.equiv ℝ (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (Complex.realTateLine k)
        (borelRelativeCochain (ι ⊕ κ) k
          (fun i ↦ Matrix.fromBlocks (v i) 0 0 (0 : Matrix κ κ ℂ))) =
      TrivialLieModule.equiv ℝ (Matrix ι ι ℂ) (Complex.realTateLine k)
        (borelRelativeCochain ι k v) := by
  apply Subtype.ext
  simpa only [borelRelativeCochain_apply] using borelRelativeForm_fromBlocks_zero ι κ k v

/-- The relative Chevalley–Eilenberg complex of the real Lie algebra of `GL(ℂ)` and its unitary
subgroup, with the trivial coefficient module `ℝ(k)`. -/
abbrev borelRelativeComplex (k : ℕ) : CochainComplex (ModuleCat ℝ) ℕ :=
  equivariantRelativeCochainComplex ℝ
    (TrivialLieModule ℝ (Matrix ι ι ℂ) (Complex.realTateLine k))
    (unitaryConjugation ι) (fun _ ↦ LinearMap.id) (unitaryLieAlgebra ι) (fun _ _ _ ↦ rfl)

private theorem borelRelativeComplex_d (k : ℕ) :
    (borelRelativeComplex ι k).d (2 * k + 1) (2 * k + 1 + 1)
      ⟨borelRelativeCochain ι k, borelRelativeCochain_mem_equivariant ι k⟩ = 0 := by
  rw [cochainSubcomplex_d_succ]
  exact Subtype.ext ((coe_cochainSubcomplexD _ _ _).trans (d_borelRelativeCochain ι k))

/-- The normalized weight `k + 1` Borel representative as a cycle of the unitary-equivariant
relative Chevalley–Eilenberg complex. -/
def borelRelativeCocycle (k : ℕ) : (borelRelativeComplex ι k).cycles (2 * k + 1) :=
  (borelRelativeComplex ι k).moduleCatCyclesMk
    ⟨borelRelativeCochain ι k, borelRelativeCochain_mem_equivariant ι k⟩
    (2 * k + 1 + 1) (CochainComplex.next ℕ _) (borelRelativeComplex_d ι k)

/-- The underlying cochain of the relative Borel cycle is the Tate-valued trace form. -/
@[simp]
theorem iCycles_borelRelativeCocycle (k : ℕ) :
    (borelRelativeComplex ι k).iCycles (2 * k + 1) (borelRelativeCocycle ι k) =
      ⟨borelRelativeCochain ι k, borelRelativeCochain_mem_equivariant ι k⟩ := by
  unfold borelRelativeCocycle
  exact (borelRelativeComplex ι k).iCycles_moduleCatCyclesMk
    (n := 2 * k + 1) ⟨borelRelativeCochain ι k, borelRelativeCochain_mem_equivariant ι k⟩
    _ (CochainComplex.next ℕ _) (borelRelativeComplex_d ι k)

/-- The weight `k + 1` relative Borel class with Tate coefficients, represented by the
normalized trace cocycle. -/
def borelRelativeClass (k : ℕ) : (borelRelativeComplex ι k).homology (2 * k + 1) :=
  (borelRelativeComplex ι k).homologyπ _ (borelRelativeCocycle ι k)

/-- The relative Borel class is the quotient class of the specified cocycle. -/
theorem borelRelativeClass_def (k : ℕ) :
    borelRelativeClass ι k =
      (borelRelativeComplex ι k).homologyπ (2 * k + 1) (borelRelativeCocycle ι k) :=
  (rfl)

end TauCeti.BorelRegulator
