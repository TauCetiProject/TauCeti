/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Rational
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.D4SpinIndex
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.RootBasis
import TauCeti.Data.Finset.Basic
import TauCeti.RepresentationTheory.Spin.Dimension
import TauCeti.RepresentationTheory.Spin.HalfSpin.Weight

/-!
# The exterior half-spin basis in the tripled type-D4 representation

The exterior basis of the split spin representation is indexed by subsets of four polarization
coordinates. The last sixteen coordinates of the tripled type-`D₄` minuscule table carry the
same weights. This file compares the two bases with all signs fixed.

At a chain node, a root operator contracts one coordinate and creates the adjacent one. At the
fork node it creates or contracts the adjacent final pair. In both cases the two exterior shuffle
signs are equal, hence their product is `1`. Thus the standard exterior basis already agrees with
the unsigned Chevalley basis of the tripled table; no diagonal sign correction is required.

## Main declarations

* `SpinPolarizationData.d4SpinPlusBlockEquiv` and `d4SpinMinusBlockEquiv`: the even and odd
  half-spin modules, identified with their separate eight-dimensional table blocks.
* The associated `serreE`, `serreF`, and `serreH` theorems intertwine all three Chevalley
  generators with the corresponding restricted tripled matrices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open scoped Matrix

namespace TauCeti.SpinPolarizationData

open CliffordAlgebra
open TauCeti.DynkinType

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) ℚ P.W)

private theorem odd_card_typeDSpinReflection_iff (i : Fin 4) (s : Finset (Fin 4)) :
    Odd (typeDSpinReflection i s).card ↔ Odd s.card := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
  exact not_congr (even_card_typeDSpinReflection_iff (n := 4) (by omega) i s)

private theorem W_ne_bot (b : Module.Basis (Fin 4) ℚ P.W) : P.W ≠ ⊥ := by
  intro hW
  have hb : (b 0 : V) = 0 := by
    have : (b 0 : V) ∈ (⊥ : Submodule ℚ V) := by
      rw [← hW]
      exact (b 0).property
    simpa using this
  exact b.ne_zero 0 (Subtype.ext hb)

/-- An even exterior-basis vector, regarded as an element of the even half-spin module. -/
noncomputable def d4SpinPlusExteriorBasis
    (s : {s : Finset (Fin 4) // Even s.card}) : spinPlus Q P :=
  ⟨b.ExteriorAlgebra s, (TauCeti.basis_mem_spinPlus_iff P b s).2 s.2⟩

private theorem d4SpinPlusBasisVector_linearIndependent :
    LinearIndependent ℚ (P.d4SpinPlusExteriorBasis b) := by
  apply LinearIndependent.of_comp (spinPlus Q P).subtype
  -- Coercing the half-spin subtype exposes the underlying exterior-basis family.
  change LinearIndependent ℚ (fun s : {s : Finset (Fin 4) // Even s.card} ↦
    b.ExteriorAlgebra s.1)
  exact b.ExteriorAlgebra.linearIndependent.comp Subtype.val Subtype.val_injective

private noncomputable def d4SpinPlusBasis :
    Module.Basis {s : Finset (Fin 4) // Even s.card} ℚ (spinPlus Q P) :=
  letI : FiniteDimensional ℚ P.W := b.finiteDimensional_of_finite
  letI : FiniteDimensional ℚ (ExteriorAlgebra ℚ P.W) :=
    b.ExteriorAlgebra.finiteDimensional_of_finite
  letI : FiniteDimensional ℚ (spinPlus Q P) :=
    FiniteDimensional.of_injective (spinPlus Q P).subtype (Submodule.injective_subtype _)
  basisOfLinearIndependentOfCardEqFinrank' (P.d4SpinPlusExteriorBasis b)
    (P.d4SpinPlusBasisVector_linearIndependent b) (by
      rw [Fintype.card_eq_nat_card, TauCeti.card_even_card_finset, Nat.card_fin,
        TauCeti.finrank_spinPlus P (P.W_ne_bot b), Module.finrank_eq_card_basis b]
      norm_num)

/-- An odd exterior-basis vector, regarded as an element of the odd half-spin module. -/
noncomputable def d4SpinMinusExteriorBasis
    (s : {s : Finset (Fin 4) // Odd s.card}) : spinMinus Q P :=
  ⟨b.ExteriorAlgebra s, (TauCeti.basis_mem_spinMinus_iff P b s).2 s.2⟩

private theorem d4SpinMinusBasisVector_linearIndependent :
    LinearIndependent ℚ (P.d4SpinMinusExteriorBasis b) := by
  apply LinearIndependent.of_comp (spinMinus Q P).subtype
  -- Coercing the half-spin subtype exposes the underlying exterior-basis family.
  change LinearIndependent ℚ (fun s : {s : Finset (Fin 4) // Odd s.card} ↦
    b.ExteriorAlgebra s.1)
  exact b.ExteriorAlgebra.linearIndependent.comp Subtype.val Subtype.val_injective

private noncomputable def d4SpinMinusBasis :
    Module.Basis {s : Finset (Fin 4) // Odd s.card} ℚ (spinMinus Q P) :=
  letI : FiniteDimensional ℚ P.W := b.finiteDimensional_of_finite
  letI : FiniteDimensional ℚ (ExteriorAlgebra ℚ P.W) :=
    b.ExteriorAlgebra.finiteDimensional_of_finite
  letI : FiniteDimensional ℚ (spinMinus Q P) :=
    FiniteDimensional.of_injective (spinMinus Q P).subtype (Submodule.injective_subtype _)
  basisOfLinearIndependentOfCardEqFinrank' (P.d4SpinMinusExteriorBasis b)
    (P.d4SpinMinusBasisVector_linearIndependent b) (by
      rw [Fintype.card_eq_nat_card, TauCeti.card_odd_card_finset, Nat.card_fin,
        TauCeti.finrank_spinMinus P (P.W_ne_bot b), Module.finrank_eq_card_basis b]
      norm_num)

private noncomputable def d4SpinPlusIndex (s : {s : Finset (Fin 4) // Even s.card}) :
    {a : Fin 24 // d4TripledSummand a = 2} :=
  ⟨d4SpinIndex s, by simp [s.2]⟩

private theorem d4SpinPlusIndex_bijective : Function.Bijective d4SpinPlusIndex := by
  constructor
  · intro s t h
    exact Subtype.ext (d4SpinIndex_injective (congrArg Subtype.val h))
  · intro a
    let a' : {a : Fin 24 // d4TripledSummand a ≠ 0} := ⟨a, by omega⟩
    obtain ⟨s, hs⟩ := d4SpinIndexEquiv.surjective a'
    have hsum : d4TripledSummand (d4SpinIndex s) = 2 := by
      rw [← coe_d4SpinIndexEquiv]
      simpa [hs] using a.2
    have heven : Even s.card := by
      by_contra h
      simp [d4TripledSummand_d4SpinIndex, h] at hsum
    refine ⟨⟨s, heven⟩, ?_⟩
    apply Subtype.ext
    simpa [d4SpinPlusIndex] using congrArg Subtype.val hs

private noncomputable def d4SpinMinusIndex (s : {s : Finset (Fin 4) // Odd s.card}) :
    {a : Fin 24 // d4TripledSummand a = 1} :=
  ⟨d4SpinIndex s, by simp [Nat.not_even_iff_odd.2 s.2]⟩

private theorem d4SpinMinusIndex_bijective : Function.Bijective d4SpinMinusIndex := by
  constructor
  · intro s t h
    exact Subtype.ext (d4SpinIndex_injective (congrArg Subtype.val h))
  · intro a
    let a' : {a : Fin 24 // d4TripledSummand a ≠ 0} := ⟨a, by omega⟩
    obtain ⟨s, hs⟩ := d4SpinIndexEquiv.surjective a'
    have hsum : d4TripledSummand (d4SpinIndex s) = 1 := by
      rw [← coe_d4SpinIndexEquiv]
      simpa [hs] using a.2
    have hodd : Odd s.card := by
      rw [← Nat.not_even_iff_odd]
      intro h
      simp [d4TripledSummand_d4SpinIndex, h] at hsum
    refine ⟨⟨s, hodd⟩, ?_⟩
    apply Subtype.ext
    simpa [d4SpinMinusIndex] using congrArg Subtype.val hs

/-- Even exterior subsets are exactly the indices of the `V(ϖ₄)` block in the tripled table. -/
noncomputable def d4SpinPlusIndexEquiv :
    {s : Finset (Fin 4) // Even s.card} ≃ {a : Fin 24 // d4TripledSummand a = 2} :=
  Equiv.ofBijective d4SpinPlusIndex d4SpinPlusIndex_bijective

/-- Odd exterior subsets are exactly the indices of the `V(ϖ₃)` block in the tripled table. -/
noncomputable def d4SpinMinusIndexEquiv :
    {s : Finset (Fin 4) // Odd s.card} ≃ {a : Fin 24 // d4TripledSummand a = 1} :=
  Equiv.ofBijective d4SpinMinusIndex d4SpinMinusIndex_bijective

/-- The underlying tripled-table index of an even exterior subset is `d4SpinIndex`. -/
@[simp]
theorem coe_d4SpinPlusIndexEquiv (s : {s : Finset (Fin 4) // Even s.card}) :
    (d4SpinPlusIndexEquiv s : Fin 24) = d4SpinIndex s := by
  simp [d4SpinPlusIndexEquiv, d4SpinPlusIndex]

/-- The underlying tripled-table index of an odd exterior subset is `d4SpinIndex`. -/
@[simp]
theorem coe_d4SpinMinusIndexEquiv (s : {s : Finset (Fin 4) // Odd s.card}) :
    (d4SpinMinusIndexEquiv s : Fin 24) = d4SpinIndex s := by
  simp [d4SpinMinusIndexEquiv, d4SpinMinusIndex]

/-- The even half-spin module in four polarization coordinates, written in the coordinates of
the `V(ϖ₄)` block of the tripled type-`D₄` weight table. -/
noncomputable def d4SpinPlusBlockEquiv :
    spinPlus Q P ≃ₗ[ℚ] ({a : Fin 24 // d4TripledSummand a = 2} → ℚ) :=
  (P.d4SpinPlusBasis b).equivFun.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ ↦ ℚ) d4SpinPlusIndexEquiv)

/-- The odd half-spin module in four polarization coordinates, written in the coordinates of
the `V(ϖ₃)` block of the tripled type-`D₄` weight table. -/
noncomputable def d4SpinMinusBlockEquiv :
    spinMinus Q P ≃ₗ[ℚ] ({a : Fin 24 // d4TripledSummand a = 1} → ℚ) :=
  (P.d4SpinMinusBasis b).equivFun.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ ↦ ℚ) d4SpinMinusIndexEquiv)

/-- The even half-spin coordinate equivalence sends an exterior-basis vector to the standard
coordinate carrying the same spin weight. -/
@[simp]
theorem d4SpinPlusBlockEquiv_exteriorBasis
    (s : {s : Finset (Fin 4) // Even s.card}) :
    P.d4SpinPlusBlockEquiv b (P.d4SpinPlusExteriorBasis b s) =
      Pi.single (d4SpinPlusIndexEquiv s) 1 := by
  classical
  have hbasis : P.d4SpinPlusBasis b s = P.d4SpinPlusExteriorBasis b s := by
    simp [d4SpinPlusBasis]
  rw [← hbasis]
  ext a
  simp only [d4SpinPlusBlockEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrLeft'_apply, Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : a = d4SpinPlusIndexEquiv s
  · subst a
    simp
  · have h' : s ≠ d4SpinPlusIndexEquiv.symm a := by
      intro hs
      apply h
      calc
        a = d4SpinPlusIndexEquiv (d4SpinPlusIndexEquiv.symm a) :=
          (d4SpinPlusIndexEquiv.apply_symm_apply a).symm
        _ = d4SpinPlusIndexEquiv s := congrArg d4SpinPlusIndexEquiv hs.symm
    simp [h, h']

/-- The inverse even half-spin coordinate equivalence sends a standard coordinate to the
exterior-basis vector carrying the same spin weight. -/
@[simp]
theorem d4SpinPlusBlockEquiv_symm_single
    (a : {a : Fin 24 // d4TripledSummand a = 2}) :
    (P.d4SpinPlusBlockEquiv b).symm (Pi.single a 1) =
      P.d4SpinPlusExteriorBasis b (d4SpinPlusIndexEquiv.symm a) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  simp

/-- The odd half-spin coordinate equivalence sends an exterior-basis vector to the standard
coordinate carrying the same spin weight. -/
@[simp]
theorem d4SpinMinusBlockEquiv_exteriorBasis
    (s : {s : Finset (Fin 4) // Odd s.card}) :
    P.d4SpinMinusBlockEquiv b (P.d4SpinMinusExteriorBasis b s) =
      Pi.single (d4SpinMinusIndexEquiv s) 1 := by
  classical
  have hbasis : P.d4SpinMinusBasis b s = P.d4SpinMinusExteriorBasis b s := by
    simp [d4SpinMinusBasis]
  rw [← hbasis]
  ext a
  simp only [d4SpinMinusBlockEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrLeft'_apply, Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : a = d4SpinMinusIndexEquiv s
  · subst a
    simp
  · have h' : s ≠ d4SpinMinusIndexEquiv.symm a := by
      intro hs
      apply h
      calc
        a = d4SpinMinusIndexEquiv (d4SpinMinusIndexEquiv.symm a) :=
          (d4SpinMinusIndexEquiv.apply_symm_apply a).symm
        _ = d4SpinMinusIndexEquiv s := congrArg d4SpinMinusIndexEquiv hs.symm
    simp [h, h']

/-- The inverse odd half-spin coordinate equivalence sends a standard coordinate to the
exterior-basis vector carrying the same spin weight. -/
@[simp]
theorem d4SpinMinusBlockEquiv_symm_single
    (a : {a : Fin 24 // d4TripledSummand a = 1}) :
    (P.d4SpinMinusBlockEquiv b).symm (Pi.single a 1) =
      P.d4SpinMinusExteriorBasis b (d4SpinMinusIndexEquiv.symm a) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  simp

private theorem d4SpinPlusBlockEquiv_intertwines (f : Module.End ℚ (spinPlus Q P))
    (M : Matrix {a : Fin 24 // d4TripledSummand a = 2}
      {a : Fin 24 // d4TripledSummand a = 2} ℚ)
    (hbasis : ∀ s, P.d4SpinPlusBlockEquiv b (f (P.d4SpinPlusExteriorBasis b s)) =
      M *ᵥ P.d4SpinPlusBlockEquiv b (P.d4SpinPlusExteriorBasis b s))
    (x : spinPlus Q P) :
    P.d4SpinPlusBlockEquiv b (f x) = M *ᵥ P.d4SpinPlusBlockEquiv b x := by
  have hmap :
      (P.d4SpinPlusBlockEquiv b).toLinearMap.comp f =
        (Matrix.mulVecLin M).comp (P.d4SpinPlusBlockEquiv b).toLinearMap := by
    apply (P.d4SpinPlusBasis b).ext
    intro s
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Matrix.mulVecLin_apply, d4SpinPlusBasis, coe_basisOfLinearIndependentOfCardEqFinrank']
      using hbasis s
  exact LinearMap.congr_fun hmap x

private theorem d4SpinPlusBlockEquiv_serreE_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Even s.card}) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
          (P.d4SpinPlusExteriorBasis b s)) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b (P.d4SpinPlusExteriorBasis b s) := by
  classical
  by_cases hs : typeDSpinWeight s i = -1
  · let t : {s : Finset (Fin 4) // Even s.card} :=
      ⟨typeDSpinReflection i s, (even_card_typeDSpinReflection_iff (by omega) i s).2 s.2⟩
    have hact :
        P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
            (P.d4SpinPlusExteriorBasis b s) = P.d4SpinPlusExteriorBasis b t := by
      apply Subtype.ext
      simp only [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inl i)]
      rw [← P.typeDSpinRep_serreE_eq_spinAction b (by omega) i]
      simpa [d4SpinPlusExteriorBasis, t] using
        P.typeDSpinRep_serreE_exteriorBasis b (by omega) i s hs
    rw [hact, P.d4SpinPlusBlockEquiv_exteriorBasis,
      P.d4SpinPlusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the transported basis vector and the raising matrix at one block coordinate.
    change (Pi.single (d4SpinPlusIndexEquiv t) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 2} → ℚ) a =
      D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24)
        (d4SpinPlusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinPlusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
    have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
        a = d4SpinPlusIndexEquiv t := by
      constructor
      · intro h
        apply Subtype.ext
        simpa [t, d4SpinIndex_typeDSpinReflection] using h
      · intro h
        simp [h, t, d4SpinIndex_typeDSpinReflection]
    rw [D4Tripled.weightTable_reflection]
    exact if_congr hindex.symm rfl rfl
  · have hact :
        P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
            (P.d4SpinPlusExteriorBasis b s) = 0 := by
      apply Subtype.ext
      simp only [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inl i), ZeroMemClass.coe_zero]
      rw [← P.typeDSpinRep_serreE_eq_spinAction b (by omega) i]
      simpa [d4SpinPlusExteriorBasis] using
        P.typeDSpinRep_serreE_exteriorBasis_eq_zero b (by omega) i s hs
    rw [hact, map_zero, P.d4SpinPlusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the zero vector and the raising matrix at one block coordinate.
    change 0 = D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24)
      (d4SpinPlusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinPlusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]

private theorem d4SpinPlusBlockEquiv_serreF_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Even s.card}) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
          (P.d4SpinPlusExteriorBasis b s)) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b (P.d4SpinPlusExteriorBasis b s) := by
  classical
  by_cases hs : typeDSpinWeight s i = 1
  · let t : {s : Finset (Fin 4) // Even s.card} :=
      ⟨typeDSpinReflection i s, (even_card_typeDSpinReflection_iff (by omega) i s).2 s.2⟩
    have hact :
        P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
            (P.d4SpinPlusExteriorBasis b s) = P.d4SpinPlusExteriorBasis b t := by
      apply Subtype.ext
      simp only [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inr i)]
      rw [← P.typeDSpinRep_serreF_eq_spinAction b (by omega) i]
      simpa [d4SpinPlusExteriorBasis, t] using
        P.typeDSpinRep_serreF_exteriorBasis b (by omega) i s hs
    rw [hact, P.d4SpinPlusBlockEquiv_exteriorBasis,
      P.d4SpinPlusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the transported basis vector and the lowering matrix at one block coordinate.
    change (Pi.single (d4SpinPlusIndexEquiv t) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 2} → ℚ) a =
      D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24)
        (d4SpinPlusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinPlusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
    have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
        a = d4SpinPlusIndexEquiv t := by
      constructor
      · intro h
        apply Subtype.ext
        simpa [t, d4SpinIndex_typeDSpinReflection] using h
      · intro h
        simp [h, t, d4SpinIndex_typeDSpinReflection]
    rw [D4Tripled.weightTable_reflection]
    exact if_congr hindex.symm rfl rfl
  · have hact :
        P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
            (P.d4SpinPlusExteriorBasis b s) = 0 := by
      apply Subtype.ext
      simp only [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inr i), ZeroMemClass.coe_zero]
      rw [← P.typeDSpinRep_serreF_eq_spinAction b (by omega) i]
      simpa [d4SpinPlusExteriorBasis] using
        P.typeDSpinRep_serreF_exteriorBasis_eq_zero b (by omega) i s hs
    rw [hact, map_zero, P.d4SpinPlusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the zero vector and the lowering matrix at one block coordinate.
    change 0 = D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24)
      (d4SpinPlusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinPlusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]


/-- The even half-spin coordinate equivalence intertwines each positive simple-root operator with
the raising matrix on the `V(ϖ₄)` block of the tripled table. -/
@[simp]
theorem d4SpinPlusBlockEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b x := by
  apply P.d4SpinPlusBlockEquiv_intertwines b
  exact P.d4SpinPlusBlockEquiv_serreE_exteriorBasis b hline i

/-- The even half-spin coordinate equivalence intertwines each negative simple-root operator with
the lowering matrix on the `V(ϖ₄)` block of the tripled table. -/
@[simp]
theorem d4SpinPlusBlockEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b x := by
  apply P.d4SpinPlusBlockEquiv_intertwines b
  exact P.d4SpinPlusBlockEquiv_serreF_exteriorBasis b hline i

private theorem d4SpinPlusBlockEquiv_serreH_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Even s.card}) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i)
          (P.d4SpinPlusExteriorBasis b s)) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b (P.d4SpinPlusExteriorBasis b s) := by
  classical
  have hact :
      P.typeDSpinPlusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i)
          (P.d4SpinPlusExteriorBasis b s) =
        (typeDSpinWeight s i : ℚ) • P.d4SpinPlusExteriorBasis b s := by
    apply Subtype.ext
    simp only [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply,
      P.typeDQuadraticEquiv_cartanGenerator b (by omega) hline i, SetLike.val_smul]
    simpa [d4SpinPlusExteriorBasis] using
      P.spinAction_typeDSimpleCorootBivector_basis b (by omega) i s
  rw [hact, map_smul, P.d4SpinPlusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
  ext a
  -- Evaluate scalar multiplication and the diagonal matrix at one block coordinate.
  change (typeDSpinWeight s i : ℚ) *
      ((Pi.single (d4SpinPlusIndexEquiv s) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 2} → ℚ) a) =
    D4Tripled.weightTable.cartanGeneratorMatrixQ i (a : Fin 24)
      (d4SpinPlusIndexEquiv s : Fin 24)
  rw [TauCeti.MinusculeWeightTable.cartanGeneratorMatrixQ_apply]
  simp only [D4Tripled.weightTable_weight, coe_d4SpinPlusIndexEquiv,
    d4TripledWeight_d4SpinIndex, Pi.single_apply]
  by_cases h : a = d4SpinPlusIndexEquiv s
  · subst a
    simp
  · have hval : (a : Fin 24) ≠ d4SpinIndex s := by
      simpa only [← coe_d4SpinPlusIndexEquiv] using fun h' ↦ h (Subtype.ext h')
    simp [h, hval]

/-- The even half-spin coordinate equivalence intertwines each Cartan generator with the diagonal
weight matrix on the `V(ϖ₄)` block of the tripled table. -/
@[simp]
theorem d4SpinPlusBlockEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusBlockEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinPlusBlockEquiv b x := by
  apply P.d4SpinPlusBlockEquiv_intertwines b
  exact P.d4SpinPlusBlockEquiv_serreH_exteriorBasis b hline i

private theorem d4SpinMinusBlockEquiv_intertwines (f : Module.End ℚ (spinMinus Q P))
    (M : Matrix {a : Fin 24 // d4TripledSummand a = 1}
      {a : Fin 24 // d4TripledSummand a = 1} ℚ)
    (hbasis : ∀ s, P.d4SpinMinusBlockEquiv b (f (P.d4SpinMinusExteriorBasis b s)) =
      M *ᵥ P.d4SpinMinusBlockEquiv b (P.d4SpinMinusExteriorBasis b s))
    (x : spinMinus Q P) :
    P.d4SpinMinusBlockEquiv b (f x) = M *ᵥ P.d4SpinMinusBlockEquiv b x := by
  have hmap :
      (P.d4SpinMinusBlockEquiv b).toLinearMap.comp f =
        (Matrix.mulVecLin M).comp (P.d4SpinMinusBlockEquiv b).toLinearMap := by
    apply (P.d4SpinMinusBasis b).ext
    intro s
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Matrix.mulVecLin_apply, d4SpinMinusBasis, coe_basisOfLinearIndependentOfCardEqFinrank']
      using hbasis s
  exact LinearMap.congr_fun hmap x

private theorem d4SpinMinusBlockEquiv_serreE_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Odd s.card}) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
          (P.d4SpinMinusExteriorBasis b s)) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b (P.d4SpinMinusExteriorBasis b s) := by
  classical
  by_cases hs : typeDSpinWeight s i = -1
  · let t : {s : Finset (Fin 4) // Odd s.card} :=
      ⟨typeDSpinReflection i s, (odd_card_typeDSpinReflection_iff i s).2 s.2⟩
    have hact :
        P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
            (P.d4SpinMinusExteriorBasis b s) = P.d4SpinMinusExteriorBasis b t := by
      apply Subtype.ext
      simp only [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inl i)]
      rw [← P.typeDSpinRep_serreE_eq_spinAction b (by omega) i]
      simpa [d4SpinMinusExteriorBasis, t] using
        P.typeDSpinRep_serreE_exteriorBasis b (by omega) i s hs
    rw [hact, P.d4SpinMinusBlockEquiv_exteriorBasis,
      P.d4SpinMinusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the transported basis vector and the raising matrix at one block coordinate.
    change (Pi.single (d4SpinMinusIndexEquiv t) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 1} → ℚ) a =
      D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24)
        (d4SpinMinusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinMinusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
    have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
        a = d4SpinMinusIndexEquiv t := by
      constructor
      · intro h
        apply Subtype.ext
        simpa [t, d4SpinIndex_typeDSpinReflection] using h
      · intro h
        simp [h, t, d4SpinIndex_typeDSpinReflection]
    rw [D4Tripled.weightTable_reflection]
    exact if_congr hindex.symm rfl rfl
  · have hact :
        P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i))
            (P.d4SpinMinusExteriorBasis b s) = 0 := by
      apply Subtype.ext
      simp only [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inl i), ZeroMemClass.coe_zero]
      rw [← P.typeDSpinRep_serreE_eq_spinAction b (by omega) i]
      simpa [d4SpinMinusExteriorBasis] using
        P.typeDSpinRep_serreE_exteriorBasis_eq_zero b (by omega) i s hs
    rw [hact, map_zero, P.d4SpinMinusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the zero vector and the raising matrix at one block coordinate.
    change 0 = D4Tripled.weightTable.raisingMatrixQ i (a : Fin 24)
      (d4SpinMinusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.raisingMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinMinusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]

private theorem d4SpinMinusBlockEquiv_serreF_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Odd s.card}) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
          (P.d4SpinMinusExteriorBasis b s)) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b (P.d4SpinMinusExteriorBasis b s) := by
  classical
  by_cases hs : typeDSpinWeight s i = 1
  · let t : {s : Finset (Fin 4) // Odd s.card} :=
      ⟨typeDSpinReflection i s, (odd_card_typeDSpinReflection_iff i s).2 s.2⟩
    have hact :
        P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
            (P.d4SpinMinusExteriorBasis b s) = P.d4SpinMinusExteriorBasis b t := by
      apply Subtype.ext
      simp only [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inr i)]
      rw [← P.typeDSpinRep_serreF_eq_spinAction b (by omega) i]
      simpa [d4SpinMinusExteriorBasis, t] using
        P.typeDSpinRep_serreF_exteriorBasis b (by omega) i s hs
    rw [hact, P.d4SpinMinusBlockEquiv_exteriorBasis,
      P.d4SpinMinusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the transported basis vector and the lowering matrix at one block coordinate.
    change (Pi.single (d4SpinMinusIndexEquiv t) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 1} → ℚ) a =
      D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24)
        (d4SpinMinusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinMinusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, true_and, Pi.single_apply]
    have hindex : (a : Fin 24) = d4TripledReflection i (d4SpinIndex s) ↔
        a = d4SpinMinusIndexEquiv t := by
      constructor
      · intro h
        apply Subtype.ext
        simpa [t, d4SpinIndex_typeDSpinReflection] using h
      · intro h
        simp [h, t, d4SpinIndex_typeDSpinReflection]
    rw [D4Tripled.weightTable_reflection]
    exact if_congr hindex.symm rfl rfl
  · have hact :
        P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i))
            (P.d4SpinMinusExteriorBasis b s) = 0 := by
      apply Subtype.ext
      simp only [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply,
        P.typeDQuadraticEquiv_rootGenerator b (by omega) hline (.inr i), ZeroMemClass.coe_zero]
      rw [← P.typeDSpinRep_serreF_eq_spinAction b (by omega) i]
      simpa [d4SpinMinusExteriorBasis] using
        P.typeDSpinRep_serreF_exteriorBasis_eq_zero b (by omega) i s hs
    rw [hact, map_zero, P.d4SpinMinusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
    ext a
    -- Evaluate the zero vector and the lowering matrix at one block coordinate.
    change 0 = D4Tripled.weightTable.loweringMatrixQ i (a : Fin 24)
      (d4SpinMinusIndexEquiv s : Fin 24)
    rw [TauCeti.MinusculeWeightTable.loweringMatrixQ_apply]
    simp only [D4Tripled.weightTable_weight, coe_d4SpinMinusIndexEquiv,
      d4TripledWeight_d4SpinIndex, hs, false_and, ↓reduceIte]

/-- The odd half-spin coordinate equivalence intertwines each positive simple-root operator with
the raising matrix on the `V(ϖ₃)` block of the tripled table. -/
@[simp]
theorem d4SpinMinusBlockEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b x := by
  apply P.d4SpinMinusBlockEquiv_intertwines b
  exact P.d4SpinMinusBlockEquiv_serreE_exteriorBasis b hline i

/-- The odd half-spin coordinate equivalence intertwines each negative simple-root operator with
the lowering matrix on the `V(ϖ₃)` block of the tripled table. -/
@[simp]
theorem d4SpinMinusBlockEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b x := by
  apply P.d4SpinMinusBlockEquiv_intertwines b
  exact P.d4SpinMinusBlockEquiv_serreF_exteriorBasis b hline i

private theorem d4SpinMinusBlockEquiv_serreH_exteriorBasis (hline : P.line = ⊥)
    (i : Fin 4) (s : {s : Finset (Fin 4) // Odd s.card}) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i)
          (P.d4SpinMinusExteriorBasis b s)) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b (P.d4SpinMinusExteriorBasis b s) := by
  classical
  have hact :
      P.typeDSpinMinusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i)
          (P.d4SpinMinusExteriorBasis b s) =
        (typeDSpinWeight s i : ℚ) • P.d4SpinMinusExteriorBasis b s := by
    apply Subtype.ext
    simp only [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply,
      P.typeDQuadraticEquiv_cartanGenerator b (by omega) hline i, SetLike.val_smul]
    simpa [d4SpinMinusExteriorBasis] using
      P.spinAction_typeDSimpleCorootBivector_basis b (by omega) i s
  rw [hact, map_smul, P.d4SpinMinusBlockEquiv_exteriorBasis, Matrix.mulVec_single_one]
  ext a
  -- Evaluate scalar multiplication and the diagonal matrix at one block coordinate.
  change (typeDSpinWeight s i : ℚ) *
      ((Pi.single (d4SpinMinusIndexEquiv s) (1 : ℚ) :
        {a : Fin 24 // d4TripledSummand a = 1} → ℚ) a) =
    D4Tripled.weightTable.cartanGeneratorMatrixQ i (a : Fin 24)
      (d4SpinMinusIndexEquiv s : Fin 24)
  rw [TauCeti.MinusculeWeightTable.cartanGeneratorMatrixQ_apply]
  simp only [D4Tripled.weightTable_weight, coe_d4SpinMinusIndexEquiv,
    d4TripledWeight_d4SpinIndex, Pi.single_apply]
  by_cases h : a = d4SpinMinusIndexEquiv s
  · subst a
    simp
  · have hval : (a : Fin 24) ≠ d4SpinIndex s := by
      simpa only [← coe_d4SpinMinusIndexEquiv] using fun h' ↦ h (Subtype.ext h')
    simp [h, hval]

/-- The odd half-spin coordinate equivalence intertwines each Cartan generator with the diagonal
weight matrix on the `V(ϖ₃)` block of the tripled table. -/
@[simp]
theorem d4SpinMinusBlockEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusBlockEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ
        P.d4SpinMinusBlockEquiv b x := by
  apply P.d4SpinMinusBlockEquiv_intertwines b
  exact P.d4SpinMinusBlockEquiv_serreH_exteriorBasis b hline i

end TauCeti.SpinPolarizationData
