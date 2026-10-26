/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Idempotents.Karoubi
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Retract

/-!
# The idempotent completion of an exact category

Let `E` be an exact structure on an additive category `C`. Its idempotent completion
`Karoubi C` carries an exact structure whose conflations are the retracts, in the category of
short complexes, of the images of conflations of `E` under `toKaroubi`.

## Main definitions

* `TauCeti.ExactStructure.karoubi`: the exact structure on `Karoubi C` induced by `E`.

## Main results

* `TauCeti.ExactStructure.karoubi_isInflation_iff`,
  `TauCeti.ExactStructure.karoubi_isDeflation_iff`: the inflations (deflations) of `E.karoubi`
  are the retracts, in the arrow category, of images of inflations (deflations) of `E`.
* `TauCeti.ExactStructure.isConflationExact_toKaroubi`: the embedding `toKaroubi` is exact.

## Implementation notes

A retract of the image of an inflation `a` is an inflation: its cokernel is the image of the
idempotent induced on the cokernel of `a`. Composition uses
`CategoryTheory.Idempotents.Karoubi.exists_retractArrow_comp_of_retracts`, and (co)base change
uses `CategoryTheory.IsPushout.nonempty_retractArrow_of_retract` and
`CategoryTheory.IsPushout.hasPushout_of_retract` with their pullback duals. No complements of
short complexes are formed.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 6,
  Proposition 6.13, for the exact structure on the idempotent completion.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u

variable {C : Type u} [Category.{v} C]


variable [Preadditive C]

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

variable (E : ExactStructure C)

/-- The conflation class on the idempotent completion: the retracts, in the category of short
complexes, of the images of conflations of `E` under `toKaroubi`. -/
private def karoubiConflations : ConflationClass (Karoubi C) where
  Conflation S := ∃ T : ShortComplex C, E.Conflation T ∧ Nonempty (Retract S (T.map (toKaroubi C)))
  isKernelCokernelPair _ := fun ⟨_, hT, ⟨e⟩⟩ ↦
    ((E.isKernelCokernelPair _ hT).map (toKaroubi C)).of_retract e
  isClosedUnderIsomorphisms := ⟨fun e ⟨T, hT, ⟨r⟩⟩ ↦
    ⟨T, hT, ⟨⟨e.inv ≫ r.i, r.r ≫ e.hom, by simp⟩⟩⟩⟩

/-- The image of a conflation of `E` is a conflation of the idempotent completion. -/
private theorem karoubiConflations_map_toKaroubi {T : ShortComplex C} (hT : E.Conflation T) :
    E.karoubiConflations.Conflation (T.map (toKaroubi C)) :=
  ⟨T, hT, ⟨⟨𝟙 _, 𝟙 _, by simp⟩⟩⟩

/-- A retract of the image of an inflation of `E` is an inflation of the idempotent completion.
The cokernel is the image of the idempotent induced on the cokernel of the inflation of `E`. -/
private theorem karoubiConflations_isInflation_of_retract {P Q : Karoubi C} {f : P ⟶ Q} {A B : C}
    {a : A ⟶ B} (ha : E.IsInflation a) (h : RetractArrow f ((toKaroubi C).map a)) :
    E.karoubiConflations.IsInflation f := by
  obtain ⟨D, d, zero, hT⟩ := (ConflationClass.isInflation_iff _ a).mp ha
  have hK := (E.isKernelCokernelPair _ hT).map (toKaroubi C)
  have : Epi ((toKaroubi C).map d) := hK.epi_g
  have wi : f ≫ h.i.right = h.i.left ≫ (toKaroubi C).map a := h.i_w.symm
  have wr : (toKaroubi C).map a ≫ h.r.right = h.r.left ≫ f := h.r_w.symm
  have hd : (toKaroubi C).map a ≫ h.r.right ≫ h.i.right ≫ (toKaroubi C).map d = 0 := by
    rw [reassoc_of% wr, reassoc_of% wi, ← Functor.map_comp, zero, Functor.map_zero, comp_zero,
      comp_zero]
  let eD : (toKaroubi C).obj D ⟶ (toKaroubi C).obj D := hK.desc _ hd
  have heD : (toKaroubi C).map d ≫ eD = h.r.right ≫ h.i.right ≫ (toKaroubi C).map d :=
    hK.g_desc _ hd
  have hidem : eD ≫ eD = eD := by
    rw [← cancel_epi ((toKaroubi C).map d), reassoc_of% heD, heD]
    simp
  obtain ⟨R, iR, rR, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ eD hidem
  have zero' : f ≫ h.i.right ≫ (toKaroubi C).map d ≫ rR = 0 := by
    rw [reassoc_of% wi, ← Functor.map_comp_assoc, zero, Functor.map_zero, zero_comp, comp_zero]
  refine (ConflationClass.isInflation_iff _ f).mpr
    ⟨R, _, zero', ShortComplex.mk a d zero, hT, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · exact
      { τ₁ := h.i.left
        τ₂ := h.i.right
        τ₃ := iR
        comm₁₂ := wi.symm
        comm₂₃ := by
          simp only [ShortComplex.map_g, Category.assoc, h₂]
          rw [heD]
          simp }
  · exact
      { τ₁ := h.r.left
        τ₂ := h.r.right
        τ₃ := rR
        comm₁₂ := wr.symm
        comm₂₃ := by
          simp only [ShortComplex.map_g]
          rw [← reassoc_of% heD, ← h₂, Category.assoc, h₁, Category.comp_id] }
  · ext <;> simp [h₁]

/-- An inflation of the idempotent completion is a retract of the image of an inflation of `E`. -/
private theorem karoubiConflations_isInflation_iff {P Q : Karoubi C} (f : P ⟶ Q) :
    E.karoubiConflations.IsInflation f ↔ ∃ (A B : C) (a : A ⟶ B),
      E.IsInflation a ∧ Nonempty (RetractArrow f ((toKaroubi C).map a)) := by
  constructor
  · intro hf
    obtain ⟨_, _, _, T, hT, ⟨e⟩⟩ := (ConflationClass.isInflation_iff _ f).mp hf
    exact ⟨_, _, T.f, E.isInflation_f hT, ⟨e.map ShortComplex.fFunctor⟩⟩
  · rintro ⟨_, _, _, ha, ⟨h⟩⟩
    exact E.karoubiConflations_isInflation_of_retract ha h

/-- A retract of the image of a deflation of `E` is a deflation of the idempotent completion.
The kernel is the image of the idempotent induced on the kernel of the deflation of `E`. -/
private theorem karoubiConflations_isDeflation_of_retract {Q R : Karoubi C} {g : Q ⟶ R} {B D : C}
    {d : B ⟶ D} (hd : E.IsDeflation d) (h : RetractArrow g ((toKaroubi C).map d)) :
    E.karoubiConflations.IsDeflation g := by
  obtain ⟨A, a, zero, hT⟩ := (ConflationClass.isDeflation_iff _ d).mp hd
  have hK := (E.isKernelCokernelPair _ hT).map (toKaroubi C)
  have : Mono ((toKaroubi C).map a) := hK.mono_f
  have wi : g ≫ h.i.right = h.i.left ≫ (toKaroubi C).map d := h.i_w.symm
  have wr : (toKaroubi C).map d ≫ h.r.right = h.r.left ≫ g := h.r_w.symm
  have ha : ((toKaroubi C).map a ≫ h.r.left ≫ h.i.left) ≫ (toKaroubi C).map d = 0 := by
    rw [Category.assoc, Category.assoc, ← wi, ← reassoc_of% wr, ← Functor.map_comp_assoc, zero,
      Functor.map_zero, zero_comp]
  let eA : (toKaroubi C).obj A ⟶ (toKaroubi C).obj A := hK.lift _ ha
  have heA : eA ≫ (toKaroubi C).map a = (toKaroubi C).map a ≫ h.r.left ≫ h.i.left :=
    hK.lift_f _ ha
  have hidem : eA ≫ eA = eA := by
    rw [← cancel_mono ((toKaroubi C).map a), Category.assoc, heA, reassoc_of% heA]
    simp
  obtain ⟨K, iK, rK, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split _ eA hidem
  have zero' : (iK ≫ (toKaroubi C).map a ≫ h.r.left) ≫ g = 0 := by
    rw [Category.assoc, Category.assoc, ← wr, ← Functor.map_comp_assoc, zero, Functor.map_zero,
      zero_comp, comp_zero]
  refine (ConflationClass.isDeflation_iff _ g).mpr
    ⟨K, _, zero', ShortComplex.mk a d zero, hT, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · exact
      { τ₁ := iK
        τ₂ := h.i.left
        τ₃ := h.i.right
        comm₁₂ := by
          simp only [ShortComplex.map_f, Category.assoc]
          rw [← heA, ← h₂]
          simp [reassoc_of% h₁]
        comm₂₃ := wi.symm }
  · exact
      { τ₁ := rK
        τ₂ := h.r.left
        τ₃ := h.r.right
        comm₁₂ := by
          simp only [ShortComplex.map_f]
          rw [reassoc_of% h₂, reassoc_of% heA]
          simp
        comm₂₃ := wr.symm }
  · ext <;> simp [h₁]

/-- A deflation of the idempotent completion is a retract of the image of a deflation of `E`. -/
private theorem karoubiConflations_isDeflation_iff {Q R : Karoubi C} (g : Q ⟶ R) :
    E.karoubiConflations.IsDeflation g ↔ ∃ (B D : C) (d : B ⟶ D),
      E.IsDeflation d ∧ Nonempty (RetractArrow g ((toKaroubi C).map d)) := by
  constructor
  · intro hg
    obtain ⟨_, _, _, T, hT, ⟨e⟩⟩ := (ConflationClass.isDeflation_iff _ g).mp hg
    exact ⟨_, _, T.g, E.isDeflation_g hT, ⟨e.map ShortComplex.gFunctor⟩⟩
  · rintro ⟨_, _, _, hd, ⟨h⟩⟩
    exact E.karoubiConflations_isDeflation_of_retract hd h

/-- Identities are inflations of the idempotent completion: `𝟙 P` is a retract of `𝟙 P.X`. -/
private theorem karoubiConflations_isInflation_id (P : Karoubi C) :
    E.karoubiConflations.IsInflation (𝟙 P) :=
  E.karoubiConflations_isInflation_of_retract (E.isInflation_id P.X)
    ⟨Arrow.homMk (Karoubi.decompId_i P) (Karoubi.decompId_i P),
      Arrow.homMk (Karoubi.decompId_p P) (Karoubi.decompId_p P),
      by ext <;> simp⟩

/-- Identities are deflations of the idempotent completion: `𝟙 P` is a retract of `𝟙 P.X`. -/
private theorem karoubiConflations_isDeflation_id (P : Karoubi C) :
    E.karoubiConflations.IsDeflation (𝟙 P) :=
  E.karoubiConflations_isDeflation_of_retract (E.isDeflation_id P.X)
    ⟨Arrow.homMk (Karoubi.decompId_i P) (Karoubi.decompId_i P),
      Arrow.homMk (Karoubi.decompId_p P) (Karoubi.decompId_p P),
      by ext <;> simp⟩

/-- Inflations of the idempotent completion are closed under composition. -/
private theorem karoubiConflations_isInflation_comp {P Q R : Karoubi C} {i : P ⟶ Q} {j : Q ⟶ R}
    (hi : E.karoubiConflations.IsInflation i) (hj : E.karoubiConflations.IsInflation j) :
    E.karoubiConflations.IsInflation (i ≫ j) := by
  obtain ⟨_, B, _, ha, ⟨hi⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  obtain ⟨_, _, _, hb, ⟨hj⟩⟩ := (E.karoubiConflations_isInflation_iff j).mp hj
  obtain ⟨θ, _, ⟨h⟩⟩ := Karoubi.exists_retractArrow_comp_of_retracts i j _ _ _ _ _ _ _ _
    hi.retract_left hi.retract_right hj.retract_left hj.retract_right hi.i_w hi.r_w hj.i_w hj.r_w
  exact E.karoubiConflations_isInflation_of_retract
    (E.isInflation_comp _ _ (E.isInflation_biprod_id ha _)
      (E.isInflation_comp _ _ (E.inflations.of_isIso θ) (E.isInflation_id_biprod hb B))) h

/-- Deflations of the idempotent completion are closed under composition. -/
private theorem karoubiConflations_isDeflation_comp {P Q R : Karoubi C} {p : P ⟶ Q} {q : Q ⟶ R}
    (hp : E.karoubiConflations.IsDeflation p) (hq : E.karoubiConflations.IsDeflation q) :
    E.karoubiConflations.IsDeflation (p ≫ q) := by
  obtain ⟨_, B, _, hd, ⟨hp⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  obtain ⟨_, _, _, hd', ⟨hq⟩⟩ := (E.karoubiConflations_isDeflation_iff q).mp hq
  obtain ⟨θ, _, ⟨h⟩⟩ := Karoubi.exists_retractArrow_comp_of_retracts p q _ _ _ _ _ _ _ _
    hp.retract_left hp.retract_right hq.retract_left hq.retract_right hp.i_w hp.r_w hq.i_w hq.r_w
  exact E.karoubiConflations_isDeflation_of_retract
    (E.isDeflation_comp _ _ (E.isDeflation_biprod_id hd _)
      (E.isDeflation_comp _ _ (E.deflations.of_isIso θ) (E.isDeflation_id_biprod hd' B))) h

/-- Pushouts of inflations of the idempotent completion exist. If `i` is a retract of the image of
an inflation `a` of `E`, the span `(i, h)` is a retract of the image of a span `(a, k)`, whose
pushout in `C` exists by `E`. -/
private theorem karoubiConflations_hasPushout {P Q P' : Karoubi C} {i : P ⟶ Q}
    (hi : E.karoubiConflations.IsInflation i) (h : P ⟶ P') : HasPushout i h := by
  obtain ⟨A, B, a, ha, ⟨r⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  obtain ⟨k, wk, wk'⟩ := Karoubi.exists_span_retract r h
  have : HasPushout a k := E.hasPushouts_inflations.hasPushout k ha
  exact ((toKaroubi C).map_isPushout (IsPushout.of_hasPushout a k)).hasPushout_of_retract
    r.retract_right
    (Karoubi.decompId P').symm r.i_w.symm r.r_w.symm wk wk'

/-- Inflations of the idempotent completion are stable under cobase change. The cobase change of
`i` along `h` is a retract of the image of the cobase change in `C` of the corresponding
inflation of `E`. -/
private theorem karoubiConflations_isInflation_of_isPushout {P Q P' Z : Karoubi C} {i : P ⟶ Q}
    {h : P ⟶ P'} {h' : Q ⟶ Z} {i' : P' ⟶ Z} (sq : IsPushout h i i' h')
    (hi : E.karoubiConflations.IsInflation i) : E.karoubiConflations.IsInflation i' := by
  obtain ⟨A, B, a, ha, ⟨r⟩⟩ := (E.karoubiConflations_isInflation_iff i).mp hi
  obtain ⟨k, wk, wk'⟩ := Karoubi.exists_span_retract r h
  have : HasPushout a k := E.hasPushouts_inflations.hasPushout k ha
  have hpo := IsPushout.of_hasPushout a k
  obtain ⟨r'⟩ := sq.flip.nonempty_retractArrow_of_retract ((toKaroubi C).map_isPushout hpo)
    r.retract_right
    (Karoubi.decompId P').symm r.i_w.symm r.r_w.symm wk wk'
  exact E.karoubiConflations_isInflation_of_retract
    (E.isStableUnderCobaseChange_inflations.of_isPushout hpo.flip ha) r'

/-- Pullbacks of deflations of the idempotent completion exist; dual to
`karoubiConflations_hasPushout`. -/
private theorem karoubiConflations_hasPullback {Q P P' : Karoubi C} {p : Q ⟶ P}
    (hp : E.karoubiConflations.IsDeflation p) (h : P' ⟶ P) : HasPullback p h := by
  obtain ⟨B, D, d, hd, ⟨r⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  obtain ⟨k, wk, wk'⟩ := Karoubi.exists_cospan_retract r h
  have : HasPullback d k := E.hasPullbacks_deflations.hasPullback k hd
  exact ((toKaroubi C).map_isPullback (IsPullback.of_hasPullback d k)).hasPullback_of_retract
    r.retract_left
    (Karoubi.decompId P').symm r.i_w r.r_w wk wk'

/-- Deflations of the idempotent completion are stable under base change; dual to
`karoubiConflations_isInflation_of_isPushout`. -/
private theorem karoubiConflations_isDeflation_of_isPullback {Q P P' Z : Karoubi C} {p : Q ⟶ P}
    {h : P' ⟶ P} {h' : Z ⟶ Q} {p' : Z ⟶ P'} (sq : IsPullback h' p' p h)
    (hp : E.karoubiConflations.IsDeflation p) : E.karoubiConflations.IsDeflation p' := by
  obtain ⟨B, D, d, hd, ⟨r⟩⟩ := (E.karoubiConflations_isDeflation_iff p).mp hp
  obtain ⟨k, wk, wk'⟩ := Karoubi.exists_cospan_retract r h
  have : HasPullback d k := E.hasPullbacks_deflations.hasPullback k hd
  have hpb := IsPullback.of_hasPullback d k
  obtain ⟨r'⟩ := sq.nonempty_retractArrow_of_retract ((toKaroubi C).map_isPullback hpb)
    r.retract_left
    (Karoubi.decompId P').symm r.i_w r.r_w wk wk'
  exact E.karoubiConflations_isDeflation_of_retract
    (E.isStableUnderBaseChange_deflations.of_isPullback hpb hd) r'

/-- The exact structure on the idempotent completion (Bühler, Proposition 6.13). Its conflations
are the retracts, in the category of short complexes, of images of conflations of `E`. -/
def karoubi : ExactStructure (Karoubi C) where
  toConflationClass := E.karoubiConflations
  isInflation_id := E.karoubiConflations_isInflation_id
  isDeflation_id := E.karoubiConflations_isDeflation_id
  isInflation_comp _ _ := E.karoubiConflations_isInflation_comp
  isDeflation_comp _ _ := E.karoubiConflations_isDeflation_comp
  hasPushouts_inflations := ⟨fun g hf ↦ E.karoubiConflations_hasPushout hf g⟩
  isStableUnderCobaseChange_inflations :=
    ⟨fun sq hf ↦ E.karoubiConflations_isInflation_of_isPushout sq hf⟩
  hasPullbacks_deflations := ⟨fun g hf ↦ E.karoubiConflations_hasPullback hf g⟩
  isStableUnderBaseChange_deflations :=
    ⟨fun sq hg ↦ E.karoubiConflations_isDeflation_of_isPullback sq hg⟩

/-- The conflations of `E.karoubi` are the retracts of images of conflations of `E`. -/
theorem karoubi_conflation_iff (S : ShortComplex (Karoubi C)) :
    E.karoubi.Conflation S ↔
      ∃ T : ShortComplex C, E.Conflation T ∧ Nonempty (Retract S (T.map (toKaroubi C))) :=
  Iff.rfl

/-- The inflations of `E.karoubi` are the retracts of images of inflations of `E`. -/
theorem karoubi_isInflation_iff {P Q : Karoubi C} (f : P ⟶ Q) :
    E.karoubi.IsInflation f ↔ ∃ (A B : C) (a : A ⟶ B),
      E.IsInflation a ∧ Nonempty (RetractArrow f ((toKaroubi C).map a)) :=
  E.karoubiConflations_isInflation_iff f

/-- The deflations of `E.karoubi` are the retracts of images of deflations of `E`. -/
theorem karoubi_isDeflation_iff {Q R : Karoubi C} (g : Q ⟶ R) :
    E.karoubi.IsDeflation g ↔ ∃ (B D : C) (d : B ⟶ D),
      E.IsDeflation d ∧ Nonempty (RetractArrow g ((toKaroubi C).map d)) :=
  E.karoubiConflations_isDeflation_iff g

/-- The embedding of `C` into its idempotent completion is exact. -/
theorem isConflationExact_toKaroubi : E.IsConflationExact E.karoubi (toKaroubi C) where
  map_conflation hT := E.karoubiConflations_map_toKaroubi hT

end ExactStructure

end TauCeti
