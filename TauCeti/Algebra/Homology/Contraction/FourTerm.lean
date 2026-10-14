/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Conj

/-!
# Cancelling two blocks of a four-term cochain complex

Suppose a complex has terms `Q`, `A ⊞ (U ⊞ Q)`, `U ⊞ B`, and `Z` in degrees
`-3`, `-2`, `-1`, and `0`. In these coordinates its differentials are

`(α, β, -id)`, `((f,g), (-id,δ), (qU,qB))`,
and `(zU, ε)`.

The square-zero identity forces `qU = α ≫ f - β`, `qB = α ≫ g + β ≫ δ`,
and `zU = δ ≫ ε`; these are conclusions rather than additional hypotheses.
In `TauCeti.Contraction.FourTermCancellationData` the components `α`, `β`, `f`, `g`, `δ`,
`qU`, `qB`, `zU` and `ε` are the fields `alpha`, `beta`, `first`, `second`, `delta`,
`qFirst`, `qSecond`, `zFirst` and `epsilon`, and the three identities are its theorems
`qFirst_eq`, `qSecond_eq` and `zFirst_eq`.

The two negative identity blocks cancel, leaving the three-term complex
`A ⟶ B ⟶ Z`, with differentials `f ≫ δ + g` and `ε`. The corrected projection
is `(id,0,α)` in degree `-2` and `(δ,id)` in degree `-1`; the corrected inclusion
is `(id,f,0)` in degree `-2` and the second inclusion in degree `-1`. The homotopy
is minus the projection to `Q` and minus the map from the second `U` (degree `-1`)
to the first `U` (degree `-2`).

The off-diagonal maps need not vanish. This is the two-block form of algebraic
Gaussian elimination, and its result is a `Contraction K L`. When the two blocks
are invertible, the caller supplies coordinate isomorphisms bringing them into
the displayed negative-identity form.

## References

* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications
  16 (2007), 243--255, Lemma 4.2, https://arxiv.org/abs/math/0606318.
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
  /-- The component of the lowest differential into the cancellable `U`. -/
  beta : Q ⟶ U
  /-- The first component of the middle differential on `A`. -/
  first : A ⟶ U
  /-- The second component of the middle differential on `A`. -/
  second : A ⟶ B
  /-- The first component of the middle differential on `Q`. -/
  qFirst : Q ⟶ U
  /-- The second component of the middle differential on `Q`. -/
  qSecond : Q ⟶ B
  /-- The second component of the middle differential on `U`. -/
  delta : U ⟶ B
  /-- The differential out of the cancellable `U`. -/
  zFirst : U ⟶ Z
  /-- The differential out of the surviving `B`. -/
  epsilon : B ⟶ Z
  /-- The lowest differential has a negative identity in its `Q` component. -/
  d_minusThree : K.d (-3) (-2) ≫ minusTwoIso.hom =
    minusThreeIso.hom ≫ biprod.lift alpha (biprod.lift beta (-𝟙 Q))
  /-- The middle differential has a negative identity in its `U` component. -/
  d_minusTwo : K.d (-2) (-1) ≫ minusOneIso.hom =
    minusTwoIso.hom ≫ biprod.desc (biprod.lift first second)
      (biprod.desc (biprod.lift (-𝟙 U) delta) (biprod.lift qFirst qSecond))
  /-- The highest source differential in the specified coordinates. -/
  d_minusOne : K.d (-1) 0 ≫ zeroIso.hom =
    minusOneIso.hom ≫ biprod.desc zFirst epsilon
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
private def d3 : Q ⟶ A ⊞ (U ⊞ Q) := biprod.lift h.alpha (biprod.lift h.beta (-𝟙 Q))
private def rawD2 : A ⊞ (U ⊞ Q) ⟶ U ⊞ B :=
  biprod.desc (biprod.lift h.first h.second)
    (biprod.desc (biprod.lift (-𝟙 U) h.delta) (biprod.lift h.qFirst h.qSecond))

private theorem raw_square_zero : d3 h ≫ rawD2 h = 0 := by
  apply (cancel_epi h.minusThreeIso.hom).1
  have hz : K.d (-3) (-2) ≫ K.d (-2) (-1) ≫ h.minusOneIso.hom = 0 := by
    rw [← Category.assoc, K.d_comp_d, zero_comp]
  rw [h.d_minusTwo, ← Category.assoc, h.d_minusThree] at hz
  simpa only [Category.assoc, d3, rawD2, comp_zero] using hz

/-- Square-zero determines the component from `Q` to the next `U`. -/
@[reassoc]
theorem qFirst_eq : h.qFirst = h.alpha ≫ h.first - h.beta := by
  have hz : (d3 h ≫ rawD2 h) ≫ (biprod.fst : U ⊞ B ⟶ U) = 0 := by
    rw [raw_square_zero, zero_comp]
  have he : h.alpha ≫ h.first - h.beta - h.qFirst = 0 := by
    simpa [d3, rawD2, Category.assoc, sub_eq_add_neg, add_assoc] using hz
  exact (sub_eq_zero.mp he).symm

/-- Square-zero determines the component from `Q` to the surviving `B`. -/
@[reassoc]
theorem qSecond_eq : h.qSecond = h.alpha ≫ h.second + h.beta ≫ h.delta := by
  have hz : (d3 h ≫ rawD2 h) ≫ (biprod.snd : U ⊞ B ⟶ B) = 0 := by
    rw [raw_square_zero, zero_comp]
  have he : h.alpha ≫ h.second + h.beta ≫ h.delta - h.qSecond = 0 := by
    simpa [d3, rawD2, Category.assoc, sub_eq_add_neg, add_assoc] using hz
  exact (sub_eq_zero.mp he).symm

private def rawD1 : U ⊞ B ⟶ Z := biprod.desc h.zFirst h.epsilon

private theorem raw_last_square_zero : rawD2 h ≫ rawD1 h = 0 := by
  apply (cancel_epi h.minusTwoIso.hom).1
  have hz : K.d (-2) (-1) ≫ K.d (-1) 0 ≫ h.zeroIso.hom = 0 := by
    rw [← Category.assoc, K.d_comp_d, zero_comp]
  rw [h.d_minusOne, ← Category.assoc, h.d_minusTwo] at hz
  simpa only [Category.assoc, rawD2, rawD1, comp_zero] using hz

/-- Square-zero determines the last differential on the cancellable `U`. -/
@[reassoc]
theorem zFirst_eq : h.zFirst = h.delta ≫ h.epsilon := by
  have hz : (biprod.inl ≫ biprod.inr : U ⟶ A ⊞ (U ⊞ Q)) ≫ rawD2 h ≫ rawD1 h = 0 := by
    rw [raw_last_square_zero, comp_zero]
  have he : -h.zFirst + h.delta ≫ h.epsilon = 0 := by
    simpa [rawD2, rawD1, Category.assoc] using hz
  exact (sub_eq_zero.mp ((neg_add_eq_sub _ _).symm.trans he)).symm

private def d2 : A ⊞ (U ⊞ Q) ⟶ U ⊞ B :=
  biprod.desc (biprod.lift h.first h.second)
    (biprod.desc (biprod.lift (-𝟙 U) h.delta) (biprod.lift (h.alpha ≫ h.first - h.beta)
      (h.alpha ≫ h.second + h.beta ≫ h.delta)))
private def d1 : U ⊞ B ⟶ Z := biprod.desc (h.delta ≫ h.epsilon) h.epsilon
private def p2 : A ⊞ (U ⊞ Q) ⟶ A := biprod.fst + pQ ≫ h.alpha
private def j2 : A ⟶ A ⊞ (U ⊞ Q) := biprod.inl + h.first ≫ iU
private def p1 : U ⊞ B ⟶ B := biprod.desc h.delta (𝟙 B)

private theorem d3_p2 : d3 h ≫ p2 h = 0 := by simp [d3, p2, pQ, Category.assoc]
@[reassoc]
private theorem d2_p1 : d2 h ≫ p1 h = p2 h ≫ (h.first ≫ h.delta + h.second) := by
  ext <;> simp [d2, p1, p2, pQ, Category.assoc, Preadditive.sub_comp]
@[reassoc]
private theorem j2_d2 : j2 h ≫ d2 h = (h.first ≫ h.delta + h.second) ≫ biprod.inr := by
  ext <;> simp [j2, iU, d2, Category.assoc]
  · -- The component into B adds the direct and through-U maps.
    abel
@[reassoc]
private theorem p1_epsilon : p1 h ≫ h.epsilon = d1 h := by
  ext <;> simp [p1, d1]
@[reassoc]
private theorem j2_p2 : j2 h ≫ p2 h = 𝟙 A := by simp [j2, iU, p2, pQ, Category.assoc]
@[reassoc]
private theorem inr_p1 : (biprod.inr : B ⟶ U ⊞ B) ≫ p1 h = 𝟙 B := by simp [p1]

@[reassoc]
private theorem bottom_contract : d3 h ≫ (-pQ) = 𝟙 Q := by simp [d3, pQ]
@[reassoc]
private theorem lower_contract :
    d2 h ≫ (-biprod.fst ≫ iU) + (-pQ) ≫ d3 h + p2 h ≫ j2 h =
      𝟙 (A ⊞ (U ⊞ Q)) := by
  ext <;> simp [d2, d3, p2, j2, iU, pQ, Category.assoc]
  · -- The Q-to-U component cancels the two off-diagonal contributions.
    abel
@[reassoc]
private theorem upper_contract :
    (-biprod.fst ≫ iU) ≫ d2 h + p1 h ≫ biprod.inr = 𝟙 (U ⊞ B) := by
  ext <;> simp [d2, p1, iU, Category.assoc]

@[reassoc]
private theorem source_d3 : K.d (-3) (-2) ≫ h.minusTwoIso.hom =
    h.minusThreeIso.hom ≫ d3 h := h.d_minusThree
@[reassoc]
private theorem source_d2 : K.d (-2) (-1) ≫ h.minusOneIso.hom =
    h.minusTwoIso.hom ≫ d2 h := by
  simpa only [d2, qFirst_eq, qSecond_eq] using h.d_minusTwo
private theorem source_d3_eq : K.d (-3) (-2) =
    h.minusThreeIso.hom ≫ d3 h ≫ h.minusTwoIso.inv := by
  simpa only [Category.assoc] using (h.minusTwoIso.eq_comp_inv).2 (source_d3 h)
private theorem source_d2_eq : K.d (-2) (-1) =
    h.minusTwoIso.hom ≫ d2 h ≫ h.minusOneIso.inv := by
  simpa only [Category.assoc] using (h.minusOneIso.eq_comp_inv).2 (source_d2 h)
@[reassoc]
private theorem source_d1 : K.d (-1) 0 ≫ h.zeroIso.hom =
    h.minusOneIso.hom ≫ d1 h := by
  simpa only [d1, zFirst_eq] using h.d_minusOne
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
  simp [projectionMinusTwo, projectionMinusOne, Category.assoc, source_d2_assoc,
    target_d2, d2_p1]
private theorem projection_d1 :
    projectionMinusOne h ≫ L.d (-1) 0 = K.d (-1) 0 ≫ projectionZero h := by
  rw [← cancel_mono h.targetZeroIso.hom]
  simp [projectionMinusOne, projectionZero, Category.assoc, source_d1,
    target_d1, p1_epsilon]
private theorem inclusion_d2 :
    inclusionMinusTwo h ≫ K.d (-2) (-1) = L.d (-2) (-1) ≫ inclusionMinusOne h := by
  rw [← cancel_mono h.minusOneIso.hom]
  simp [inclusionMinusTwo, inclusionMinusOne, Category.assoc, source_d2,
    target_d2_assoc, j2_d2]
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

@[simp]
private theorem projectionFamily_minusTwo : projectionFamily h (-2) = projectionMinusTwo h := by
  simp [projectionFamily]

@[simp]
private theorem projectionFamily_minusOne : projectionFamily h (-1) = projectionMinusOne h := by
  simp [projectionFamily]

@[simp]
private theorem projectionFamily_zero : projectionFamily h 0 = projectionZero h := by
  simp [projectionFamily]

@[simp]
private theorem projectionFamily_eq_zero (n : ℤ) (h₂ : n ≠ -2) (h₁ : n ≠ -1)
    (h₀ : n ≠ 0) : projectionFamily h n = 0 := by
  simp [projectionFamily, h₂, h₁, h₀]

@[simp]
private theorem inclusionFamily_minusTwo : inclusionFamily h (-2) = inclusionMinusTwo h := by
  simp [inclusionFamily]

@[simp]
private theorem inclusionFamily_minusOne : inclusionFamily h (-1) = inclusionMinusOne h := by
  simp [inclusionFamily]

@[simp]
private theorem inclusionFamily_zero : inclusionFamily h 0 = inclusionZero h := by
  simp [inclusionFamily]

@[simp]
private theorem inclusionFamily_eq_zero (n : ℤ) (h₂ : n ≠ -2) (h₁ : n ≠ -1)
    (h₀ : n ≠ 0) : inclusionFamily h n = 0 := by
  simp [inclusionFamily, h₂, h₁, h₀]

private def projection : K ⟶ L where
  f := projectionFamily h
  comm' i j hij := by
    -- The cochain shape fixes the next degree; all other source degrees vanish.
    rw [ComplexShape.up_Rel] at hij
    by_cases h₃ : i = -3
    · subst i
      have hj : j = -2 := by omega
      subst j
      simpa using (d3_projection h).symm
    · by_cases h₂ : i = -2
      · subst i
        have hj : j = -1 := by omega
        subst j
        simpa using projection_d2 h
      · by_cases h₁ : i = -1
        · subst i
          have hj : j = 0 := by omega
          subst j
          simpa using projection_d1 h
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
      simpa using inclusion_d2 h
    · by_cases h₁ : i = -1
      · subst i
        have hj : j = 0 := by omega
        subst j
        simpa using inclusion_d1 h
      · by_cases h₀ : i = 0
        · exact (h.vanish j (by omega) (by omega) (by omega) (by omega)).eq_of_tgt _ _
        · exact (h.targetVanish i h₂ h₁ h₀).eq_of_src _ _

private theorem inclusion_projection : inclusion h ≫ projection h = 𝟙 L := by
  ext n
  by_cases h₂ : n = -2
  · subst n
    simp [inclusion, projection,
      inclusionMinusTwo, projectionMinusTwo, Category.assoc, j2_p2_assoc]
  · by_cases h₁ : n = -1
    · subst n
      simp [inclusion, projection,
        inclusionMinusOne, projectionMinusOne, Category.assoc, inr_p1_assoc]
    · by_cases h₀ : n = 0
      · subst n
        simp [inclusion, projection,
          inclusionZero, projectionZero]
      · exact (h.targetVanish n h₂ h₁ h₀).eq_of_src _ _

private def s2 : K.X (-2) ⟶ K.X (-3) :=
  h.minusTwoIso.hom ≫ (-pQ) ≫ h.minusThreeIso.inv
private def s1 : K.X (-1) ⟶ K.X (-2) :=
  h.minusOneIso.hom ≫ (-biprod.fst ≫ iU) ≫ h.minusTwoIso.inv

private theorem source_bottom_contract : K.d (-3) (-2) ≫ s2 h = 𝟙 _ := by
  calc
    _ = h.minusThreeIso.symm.conj (d3 h ≫ (-pQ)) := by
      simp [Iso.conj_apply_asHom, s2, source_d3_eq h, Category.assoc]
    _ = 𝟙 _ := by rw [bottom_contract, Iso.conj_id]
private theorem source_lower_contract :
    K.d (-2) (-1) ≫ s1 h + s2 h ≫ K.d (-3) (-2) +
      projectionMinusTwo h ≫ inclusionMinusTwo h = 𝟙 _ := by
  calc
    _ = h.minusTwoIso.symm.conj
        ((d2 h ≫ (-biprod.fst ≫ iU) + (-pQ) ≫ d3 h + p2 h ≫ j2 h) :
          A ⊞ (U ⊞ Q) ⟶ A ⊞ (U ⊞ Q)) := by
      simp [Iso.conj_apply_asHom, s1, s2, projectionMinusTwo, inclusionMinusTwo,
        source_d3_eq h, source_d2_eq h, Preadditive.comp_add,
        Preadditive.add_comp, Category.assoc]
    _ = 𝟙 _ := by rw [lower_contract, Iso.conj_id]
private theorem source_upper_contract :
    s1 h ≫ K.d (-2) (-1) + projectionMinusOne h ≫ inclusionMinusOne h = 𝟙 _ := by
  calc
    _ = h.minusOneIso.symm.conj
        (((-biprod.fst ≫ iU) ≫ d2 h + p1 h ≫ biprod.inr) : U ⊞ B ⟶ U ⊞ B) := by
      simp [Iso.conj_apply_asHom, s1, projectionMinusOne, inclusionMinusOne,
        source_d2_eq h, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    _ = 𝟙 _ := by rw [upper_contract, Iso.conj_id]

private theorem δ_singles :
    δ (-1) 0 (Cochain.single (s2 h) (-1) + Cochain.single (s1 h) (-1)) =
      Cochain.ofHom (𝟙 K - projection h ≫ inclusion h) := by
  ext p
  rw [δ_v (-1) 0 (by norm_num) _ p p (by omega) (p - 1) (p + 1) (by omega) rfl,
    Cochain.ofHom_v]
  simp only [Cochain.add_v, Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
    projection, inclusion]
  by_cases h₃ : p = -3
  · subst p
    simpa [Cochain.single_v_eq_zero] using source_bottom_contract h
  · by_cases h₂ : p = -2
    · subst p
      simpa [Cochain.single_v_eq_zero, add_comm] using
        eq_sub_iff_add_eq.2 (source_lower_contract h)
    · by_cases h₁ : p = -1
      · subst p
        simpa [Cochain.single_v_eq_zero] using eq_sub_iff_add_eq.2 (source_upper_contract h)
      · by_cases h₀ : p = 0
        · subst p
          simp [Cochain.single_v_eq_zero, projectionZero, inclusionZero]
        · exact (h.vanish p h₃ h₂ h₁ h₀).eq_of_src _ _

/-- Cancel the two negative identity blocks and retract onto the surviving three-term complex. -/
def toContraction : TauCeti.Contraction K L where
  proj := projection h
  incl := inclusion h
  incl_comp_proj := inclusion_projection h
  homotopy := Cochain.single (s2 h) (-1) + Cochain.single (s1 h) (-1)
  δ_homotopy := δ_singles h

/-- The lowest projection includes the correction through the eliminated `Q`. -/
@[reassoc (attr := simp)]
theorem toContraction_proj_f_minusTwo :
    h.toContraction.proj.f (-2) ≫ h.targetMinusTwoIso.hom =
      h.minusTwoIso.hom ≫ (biprod.fst + (biprod.snd ≫ biprod.snd) ≫ h.alpha) := by
  simp [toContraction, projection, projectionMinusTwo, p2, pQ]
/-- The middle projection includes the correction through the eliminated `U`. -/
@[reassoc (attr := simp)]
theorem toContraction_proj_f_minusOne :
    h.toContraction.proj.f (-1) ≫ h.targetMinusOneIso.hom =
      h.minusOneIso.hom ≫ biprod.desc h.delta (𝟙 B) := by
  simp [toContraction, projection, projectionMinusOne, p1]
/-- The lowest inclusion includes the correction into the eliminated `U`. -/
@[reassoc (attr := simp)]
theorem toContraction_incl_f_minusTwo :
    h.targetMinusTwoIso.inv ≫ h.toContraction.incl.f (-2) =
      (biprod.inl + h.first ≫ (biprod.inl ≫ biprod.inr)) ≫ h.minusTwoIso.inv := by
  simp [toContraction, inclusion, inclusionMinusTwo, j2, iU]
/-- The middle inclusion is the second biproduct inclusion in source coordinates. -/
@[reassoc (attr := simp)]
theorem toContraction_incl_f_minusOne :
    h.targetMinusOneIso.inv ≫ h.toContraction.incl.f (-1) =
      biprod.inr ≫ h.minusOneIso.inv := by
  simp [toContraction, inclusion, inclusionMinusOne]

/-- The degree-zero projection is the specified coordinate identification. -/
@[reassoc (attr := simp)]
theorem toContraction_proj_f_zero :
    h.toContraction.proj.f 0 ≫ h.targetZeroIso.hom = h.zeroIso.hom := by
  simp [toContraction, projection, projectionZero]

/-- The degree-zero inclusion is the inverse coordinate identification. -/
@[reassoc (attr := simp)]
theorem toContraction_incl_f_zero :
    h.targetZeroIso.inv ≫ h.toContraction.incl.f 0 = h.zeroIso.inv := by
  simp [toContraction, inclusion, inclusionZero]

/-- The lower homotopy is minus the projection onto the eliminated `Q`. -/
@[reassoc (attr := simp)]
theorem toContraction_homotopy_v_minusTwo :
    h.toContraction.homotopy.v (-2) (-3) (by decide) ≫ h.minusThreeIso.hom =
      h.minusTwoIso.hom ≫ (-(biprod.snd ≫ biprod.snd)) := by
  simp [toContraction, Cochain.single_v_eq_zero, s2, pQ, Category.assoc]

/-- The upper homotopy sends the second `U` to minus its first copy. -/
@[reassoc (attr := simp)]
theorem toContraction_homotopy_v_minusOne :
    h.toContraction.homotopy.v (-1) (-2) (by decide) ≫ h.minusTwoIso.hom =
      h.minusOneIso.hom ≫ (-(biprod.fst ≫ biprod.inl ≫ biprod.inr)) := by
  simp [toContraction, Cochain.single_v_eq_zero, s1, iU, Category.assoc]

/-- All homotopy components outside the two cancelled pairs vanish. -/
@[simp]
theorem toContraction_homotopy_v_eq_zero (i j : ℤ) (hij : i + (-1) = j)
    (h₂ : i ≠ -2) (h₁ : i ≠ -1) : h.toContraction.homotopy.v i j hij = 0 := by
  simp [toContraction, Cochain.single_v_eq_zero, h₂, h₁]

end FourTermCancellationData
end TauCeti.Contraction
