/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Cancelling two blocks of a four-term cochain complex

Suppose a complex has terms `Q`, `A ⊞ (U ⊞ Q)`, `U ⊞ B`, and `Z` in degrees
`-3`, `-2`, `-1`, and `0`. In these coordinates its differentials are

`(α, 0, -id)`, `((f,g), (-id,δ), α ≫ (f,g))`, and `(δ ≫ ε, ε)`.

The two negative identity blocks cancel, leaving the three-term complex
`A ⟶ B ⟶ Z`, with differentials `f ≫ δ + g` and `ε`. The corrected projection
is `(id,0,α)` in degree `-2` and `(δ,id)` in degree `-1`; the corrected inclusion
is `(id,f,0)` in degree `-2` and the second inclusion in degree `-1`. The homotopy
is minus the projection to `Q` and minus the map from the first `U` to the second.

The off-diagonal maps need not vanish. This is the two-block form of algebraic
Gaussian elimination, packaged in the existing `Contraction` interface.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace TauCeti.Contraction

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  (K L : CochainComplex C ℤ) (A U Q B Z : C)

/-- Four-term coordinates with two negative identity blocks and a specified surviving complex. -/
structure FourTermCancellationData where
  /-- The lowest source term. -/
  minusThreeIso : K.X (-3) ≅ Q
  /-- The source term containing the surviving and both cancellable summands. -/
  minusTwoIso : K.X (-2) ≅ A ⊞ (U ⊞ Q)
  /-- The next source term, containing the second copy of `U`. -/
  minusOneIso : K.X (-1) ≅ U ⊞ B
  /-- The highest source term. -/
  zeroIso : K.X 0 ≅ Z
  /-- The lowest surviving target term. -/
  targetMinusTwoIso : L.X (-2) ≅ A
  /-- The middle surviving target term. -/
  targetMinusOneIso : L.X (-1) ≅ B
  /-- The highest surviving target term. -/
  targetZeroIso : L.X 0 ≅ Z
  /-- The source is supported in these four consecutive degrees. -/
  vanish : ∀ n, n ≠ -3 → n ≠ -2 → n ≠ -1 → n ≠ 0 → IsZero (K.X n)
  /-- The target is supported in the three surviving degrees. -/
  targetVanish : ∀ n, n ≠ -2 → n ≠ -1 → n ≠ 0 → IsZero (L.X n)
  /-- The surviving component of the lowest differential. -/
  alpha : Q ⟶ A
  /-- The first component of the middle differential on `A`. -/
  first : A ⟶ U
  /-- The second component of the middle differential on `A`. -/
  second : A ⟶ B
  /-- The second component of the middle differential on `U`. -/
  delta : U ⟶ B
  /-- The differential out of the surviving `B`. -/
  epsilon : B ⟶ Z
  /-- The lowest differential has a negative identity in its `Q` component. -/
  d_minusThree : K.d (-3) (-2) ≫ minusTwoIso.hom =
    minusThreeIso.hom ≫ biprod.lift alpha (biprod.lift 0 (-𝟙 Q))
  /-- The middle differential has a negative identity in its `U` component. -/
  d_minusTwo : K.d (-2) (-1) ≫ minusOneIso.hom =
    minusTwoIso.hom ≫ biprod.desc (biprod.lift first second)
      (biprod.desc (biprod.lift (-𝟙 U) delta) (alpha ≫ biprod.lift first second))
  /-- The highest source differential is compatible with the surviving `B` projection. -/
  d_minusOne : K.d (-1) 0 ≫ zeroIso.hom =
    minusOneIso.hom ≫ biprod.desc (delta ≫ epsilon) epsilon
  /-- The surviving differential includes the correction through the cancellable `U`. -/
  target_d_minusTwo : L.d (-2) (-1) ≫ targetMinusOneIso.hom =
    targetMinusTwoIso.hom ≫ (first ≫ delta + second)
  /-- The last surviving differential. -/
  target_d_minusOne : L.d (-1) 0 ≫ targetZeroIso.hom =
    targetMinusOneIso.hom ≫ epsilon

namespace FourTermCancellationData
variable {K L A U Q B Z} (h : FourTermCancellationData K L A U Q B Z)

private abbrev pQ : A ⊞ (U ⊞ Q) ⟶ Q := biprod.snd ≫ biprod.snd
private abbrev iU : U ⟶ A ⊞ (U ⊞ Q) := biprod.inl ≫ biprod.inr
private def d3 : Q ⟶ A ⊞ (U ⊞ Q) := biprod.lift h.alpha (biprod.lift 0 (-𝟙 Q))
private def d2 : A ⊞ (U ⊞ Q) ⟶ U ⊞ B :=
  biprod.desc (biprod.lift h.first h.second)
    (biprod.desc (biprod.lift (-𝟙 U) h.delta) (h.alpha ≫ biprod.lift h.first h.second))
private def d1 : U ⊞ B ⟶ Z := biprod.desc (h.delta ≫ h.epsilon) h.epsilon
private def p2 : A ⊞ (U ⊞ Q) ⟶ A := biprod.fst + pQ ≫ h.alpha
private def j2 : A ⟶ A ⊞ (U ⊞ Q) := biprod.inl + h.first ≫ iU
private def p1 : U ⊞ B ⟶ B := biprod.desc h.delta (𝟙 B)

private theorem d3_p2 : d3 h ≫ p2 h = 0 := by simp [d3, p2, pQ, Category.assoc]
private theorem d2_p1 : d2 h ≫ p1 h = p2 h ≫ (h.first ≫ h.delta + h.second) := by
  ext <;> simp [d2, p1, p2, pQ, Category.assoc]
private theorem j2_d2 : j2 h ≫ d2 h = (h.first ≫ h.delta + h.second) ≫ biprod.inr := by
  ext <;> simp [j2, iU, d2, Category.assoc]
  abel
private theorem p1_epsilon : p1 h ≫ h.epsilon = d1 h := by
  ext <;> simp [p1, d1]
@[reassoc]
private theorem j2_p2 : j2 h ≫ p2 h = 𝟙 A := by simp [j2, iU, p2, pQ, Category.assoc]
@[reassoc]
private theorem inr_p1 : (biprod.inr : B ⟶ U ⊞ B) ≫ p1 h = 𝟙 B := by simp [p1]

private theorem bottom_contract : d3 h ≫ (-pQ) = 𝟙 Q := by simp [d3, pQ]
private theorem lower_contract :
    d2 h ≫ (-biprod.fst ≫ iU) + (-pQ) ≫ d3 h + p2 h ≫ j2 h =
      𝟙 (A ⊞ (U ⊞ Q)) := by
  ext <;> simp [d2, d3, p2, j2, iU, pQ, Category.assoc]
private theorem upper_contract :
    (-biprod.fst ≫ iU) ≫ d2 h + p1 h ≫ biprod.inr = 𝟙 (U ⊞ B) := by
  ext <;> simp [d2, p1, iU, Category.assoc]

@[reassoc]
private theorem source_d3 : K.d (-3) (-2) ≫ h.minusTwoIso.hom =
    h.minusThreeIso.hom ≫ d3 h := h.d_minusThree
@[reassoc]
private theorem source_d2 : K.d (-2) (-1) ≫ h.minusOneIso.hom =
    h.minusTwoIso.hom ≫ d2 h := h.d_minusTwo
@[reassoc]
private theorem source_d1 : K.d (-1) 0 ≫ h.zeroIso.hom =
    h.minusOneIso.hom ≫ d1 h := h.d_minusOne
@[reassoc]
private theorem target_d2 : L.d (-2) (-1) ≫ h.targetMinusOneIso.hom =
    h.targetMinusTwoIso.hom ≫ (h.first ≫ h.delta + h.second) := h.target_d_minusTwo
@[reassoc]
private theorem target_d1 : L.d (-1) 0 ≫ h.targetZeroIso.hom =
    h.targetMinusOneIso.hom ≫ h.epsilon := h.target_d_minusOne

private def projectionMinusTwo : K.X (-2) ⟶ L.X (-2) :=
  h.minusTwoIso.hom ≫ p2 h ≫ h.targetMinusTwoIso.inv
private def projectionMinusOne : K.X (-1) ⟶ L.X (-1) :=
  h.minusOneIso.hom ≫ p1 h ≫ h.targetMinusOneIso.inv
private def projectionZero : K.X 0 ⟶ L.X 0 := h.zeroIso.hom ≫ h.targetZeroIso.inv
private def inclusionMinusTwo : L.X (-2) ⟶ K.X (-2) :=
  h.targetMinusTwoIso.hom ≫ j2 h ≫ h.minusTwoIso.inv
private def inclusionMinusOne : L.X (-1) ⟶ K.X (-1) :=
  h.targetMinusOneIso.hom ≫ biprod.inr ≫ h.minusOneIso.inv
private def inclusionZero : L.X 0 ⟶ K.X 0 := h.targetZeroIso.hom ≫ h.zeroIso.inv

private theorem d3_projection : K.d (-3) (-2) ≫ projectionMinusTwo h = 0 := by
  simp only [projectionMinusTwo, ← Category.assoc]
  rw [source_d3, Category.assoc h.minusThreeIso.hom, d3_p2]
  simp
private theorem projection_d2 :
    projectionMinusTwo h ≫ L.d (-2) (-1) = K.d (-2) (-1) ≫ projectionMinusOne h := by
  rw [← cancel_mono h.targetMinusOneIso.hom]
  simp only [projectionMinusTwo, projectionMinusOne, Category.assoc, target_d2,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, source_d2_assoc]
  exact congrArg (h.minusTwoIso.hom ≫ ·) (d2_p1 h).symm
private theorem projection_d1 :
    projectionMinusOne h ≫ L.d (-1) 0 = K.d (-1) 0 ≫ projectionZero h := by
  rw [← cancel_mono h.targetZeroIso.hom]
  simp only [projectionMinusOne, projectionZero, Category.assoc, target_d1,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, source_d1]
  exact congrArg (h.minusOneIso.hom ≫ ·) (p1_epsilon h)
private theorem inclusion_d2 :
    inclusionMinusTwo h ≫ K.d (-2) (-1) = L.d (-2) (-1) ≫ inclusionMinusOne h := by
  rw [← cancel_mono h.minusOneIso.hom]
  simp only [inclusionMinusTwo, inclusionMinusOne, Category.assoc, source_d2,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, target_d2_assoc]
  exact congrArg (h.targetMinusTwoIso.hom ≫ ·) (j2_d2 h)
private theorem inclusion_d1 :
    inclusionMinusOne h ≫ K.d (-1) 0 = L.d (-1) 0 ≫ inclusionZero h := by
  rw [← cancel_mono h.zeroIso.hom]
  simp [inclusionMinusOne, inclusionZero, Category.assoc, source_d1, target_d1, d1]

private def projectionFamily (n : ℤ) : K.X n ⟶ L.X n := by
  by_cases h₂ : n = -2
  · subst n; exact projectionMinusTwo h
  · by_cases h₁ : n = -1
    · subst n; exact projectionMinusOne h
    · by_cases h₀ : n = 0
      · subst n; exact projectionZero h
      · exact 0
private def inclusionFamily (n : ℤ) : L.X n ⟶ K.X n := by
  by_cases h₂ : n = -2
  · subst n; exact inclusionMinusTwo h
  · by_cases h₁ : n = -1
    · subst n; exact inclusionMinusOne h
    · by_cases h₀ : n = 0
      · subst n; exact inclusionZero h
      · exact 0

private def projection : K ⟶ L where
  f := projectionFamily h
  comm' i j hij := by
    -- The cochain shape fixes the next degree; all other source degrees vanish.
    rw [ComplexShape.up_Rel] at hij
    by_cases h₃ : i = -3
    · subst i
      have hj : j = -2 := by omega
      subst j
      simpa [projectionFamily] using (d3_projection h).symm
    · by_cases h₂ : i = -2
      · subst i
        have hj : j = -1 := by omega
        subst j
        simpa [projectionFamily] using projection_d2 h
      · by_cases h₁ : i = -1
        · subst i
          have hj : j = 0 := by omega
          subst j
          simpa [projectionFamily] using projection_d1 h
        · by_cases h₀ : i = 0
          · exact (h.targetVanish j (by omega) (by omega) (by omega)).eq_of_tgt _ _
          · exact (h.vanish i h₃ h₂ h₁ h₀).eq_of_src _ _
private def inclusion : L ⟶ K where
  f := inclusionFamily h
  comm' i j hij := by
    rw [ComplexShape.up_Rel] at hij
    by_cases h₂ : i = -2
    · subst i
      have hj : j = -1 := by omega
      subst j
      simpa [inclusionFamily] using inclusion_d2 h
    · by_cases h₁ : i = -1
      · subst i
        have hj : j = 0 := by omega
        subst j
        simpa [inclusionFamily] using inclusion_d1 h
      · by_cases h₀ : i = 0
        · exact (h.vanish j (by omega) (by omega) (by omega) (by omega)).eq_of_tgt _ _
        · exact (h.targetVanish i h₂ h₁ h₀).eq_of_src _ _

private theorem inclusion_projection : inclusion h ≫ projection h = 𝟙 L := by
  ext n
  by_cases h₂ : n = -2
  · subst n
    simp [inclusion, projection, inclusionFamily, projectionFamily,
      inclusionMinusTwo, projectionMinusTwo, Category.assoc, j2_p2_assoc]
  · by_cases h₁ : n = -1
    · subst n
      simp [inclusion, projection, inclusionFamily, projectionFamily,
        inclusionMinusOne, projectionMinusOne, Category.assoc, inr_p1_assoc]
    · by_cases h₀ : n = 0
      · subst n
        simp [inclusion, projection, inclusionFamily, projectionFamily,
          inclusionZero, projectionZero]
      · exact (h.targetVanish n h₂ h₁ h₀).eq_of_src _ _

private def s2 : K.X (-2) ⟶ K.X (-3) :=
  h.minusTwoIso.hom ≫ (-pQ) ≫ h.minusThreeIso.inv
private def s1 : K.X (-1) ⟶ K.X (-2) :=
  h.minusOneIso.hom ≫ (-biprod.fst ≫ iU) ≫ h.minusTwoIso.inv

private theorem source_bottom_contract : K.d (-3) (-2) ≫ s2 h = 𝟙 _ := by
  rw [← cancel_mono h.minusThreeIso.hom]
  simp only [s2, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.id_comp, source_d3_assoc]
  exact (congrArg (h.minusThreeIso.hom ≫ ·) (bottom_contract h)).trans (by simp)
private theorem source_lower_contract :
    K.d (-2) (-1) ≫ s1 h + s2 h ≫ K.d (-3) (-2) +
      projectionMinusTwo h ≫ inclusionMinusTwo h = 𝟙 _ := by
  rw [← cancel_mono h.minusTwoIso.hom]
  simp only [Preadditive.add_comp, s1, s2, projectionMinusTwo, inclusionMinusTwo,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    Category.id_comp, source_d3, source_d2_assoc]
  simpa only [Preadditive.comp_add, Category.assoc, Category.comp_id] using
    congrArg (h.minusTwoIso.hom ≫ ·) (lower_contract h)
private theorem source_upper_contract :
    s1 h ≫ K.d (-2) (-1) + projectionMinusOne h ≫ inclusionMinusOne h = 𝟙 _ := by
  rw [← cancel_mono h.minusOneIso.hom]
  simp only [Preadditive.add_comp, s1, projectionMinusOne, inclusionMinusOne,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    Category.id_comp, source_d2]
  simpa only [Preadditive.comp_add, Category.assoc, Category.comp_id] using
    congrArg (h.minusOneIso.hom ≫ ·) (upper_contract h)

private def homFamily (i j : ℤ) : K.X i ⟶ K.X j := by
  by_cases h₂ : i = -2
  · subst i
    by_cases h₃ : j = -3
    · subst j; exact s2 h
    · exact 0
  · by_cases h₁ : i = -1
    · subst i
      by_cases h₂' : j = -2
      · subst j; exact s1 h
      · exact 0
    · exact 0
private def contraction : Homotopy (𝟙 K) (projection h ≫ inclusion h) where
  hom := homFamily h
  zero i j hn := by
    by_cases h₂ : i = -2
    · subst i
      by_cases h₃ : j = -3
      · subst j; exact (hn (by simp)).elim
      · simp [homFamily, h₃]
    · by_cases h₁ : i = -1
      · subst i
        by_cases h₂' : j = -2
        · subst j; exact (hn (by simp)).elim
        · simp [homFamily, h₂']
      · simp [homFamily, h₂, h₁]
  comm i := by
    by_cases h₃ : i = -3
    · subst i
      rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel (-3) (-2)),
        prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-4) (-3))]
      simpa [homFamily, projection, projectionFamily] using (source_bottom_contract h).symm
    · by_cases h₂ : i = -2
      · subst i
        rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel (-2) (-1)),
          prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-3) (-2))]
        simpa [homFamily, projection, inclusion, projectionFamily, inclusionFamily] using
          (source_lower_contract h).symm
      · by_cases h₁ : i = -1
        · subst i
          rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel (-1) 0),
            prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-2) (-1))]
          simpa [homFamily, projection, inclusion, projectionFamily, inclusionFamily] using
            (source_upper_contract h).symm
        · by_cases h₀ : i = 0
          · subst i
            rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel 0 1),
              prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-1) 0)]
            simp [homFamily, projection, inclusion, projectionFamily, inclusionFamily,
              projectionZero, inclusionZero]
          · exact (h.vanish i h₃ h₂ h₁ h₀).eq_of_src _ _

/-- Cancel the two negative identity blocks and retract onto the surviving three-term complex. -/
def toContraction : TauCeti.Contraction K L where
  proj := projection h
  incl := inclusion h
  incl_comp_proj := inclusion_projection h
  homotopy := Cochain.ofHomotopy (contraction h)
  δ_homotopy := by
    rw [Cochain.ofHom_sub]
    exact δ_ofHomotopy (contraction h)

/-- The lowest projection includes the correction through the eliminated `Q`. -/
@[simp]
theorem toContraction_proj_f_minusTwo :
    h.toContraction.proj.f (-2) ≫ h.targetMinusTwoIso.hom =
      h.minusTwoIso.hom ≫ (biprod.fst + (biprod.snd ≫ biprod.snd) ≫ h.alpha) := by
  simp [toContraction, projection, projectionFamily, projectionMinusTwo, p2, pQ]
/-- The middle projection includes the correction through the eliminated `U`. -/
@[simp]
theorem toContraction_proj_f_minusOne :
    h.toContraction.proj.f (-1) ≫ h.targetMinusOneIso.hom =
      h.minusOneIso.hom ≫ biprod.desc h.delta (𝟙 B) := by
  simp [toContraction, projection, projectionFamily, projectionMinusOne, p1]
/-- The lowest inclusion includes the correction into the eliminated `U`. -/
@[simp]
theorem toContraction_incl_f_minusTwo :
    h.targetMinusTwoIso.inv ≫ h.toContraction.incl.f (-2) =
      (biprod.inl + h.first ≫ (biprod.inl ≫ biprod.inr)) ≫ h.minusTwoIso.inv := by
  simp [toContraction, inclusion, inclusionFamily, inclusionMinusTwo, j2, iU]
/-- The middle inclusion is the second biproduct inclusion in source coordinates. -/
@[simp]
theorem toContraction_incl_f_minusOne :
    h.targetMinusOneIso.inv ≫ h.toContraction.incl.f (-1) =
      biprod.inr ≫ h.minusOneIso.inv := by
  simp [toContraction, inclusion, inclusionFamily, inclusionMinusOne]

end FourTermCancellationData
end TauCeti.Contraction
