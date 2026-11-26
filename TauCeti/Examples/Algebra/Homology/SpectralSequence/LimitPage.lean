/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Homology.HomologicalComplex.Double
public import TauCeti.Algebra.Homology.SpectralSequence.LimitPage
public import TauCeti.Examples.Algebra.Homology.SpectralObject.Tower.TimesTwo

/-!
# Stabilization and limit pages of spectral sequences: checks

Concrete examples exercising stabilization, regularity, coregularity, degeneration, rebasing,
and limit pages:

1. **Graded spectral sequence with zero differentials** (`TauCeti.Examples.LimitPage.graded`):
   a spectral sequence in any abelian category `C` with constant objects `X pq` and zero
   differentials degenerates at `r₀`, satisfies `Z_∞ = ⊤` and `B_∞ = ⊥`, and has canonical
   isomorphisms `X pq ≅ limitPage pq`; when `X = 0`, its limit pages vanish.
2. **A two-term `ℤ`-module spectral sequence `E₂^{0,1} = ℤ →(×2) E₂^{2,0} = ℤ`**
   (`TauCeti.Examples.LimitPage.timesTwoPage2`): does not stabilize at `(0, 1)` or `(2, 0)` on
   page `2`, does not degenerate at page `2`, degenerates at page `3`, has vanishing limit page at
   `(0, 1)`, and has nontrivial limit page `cokernel (×2) ≅ ℤ/2ℤ` at `(2, 0)`.
3. **The filtered complex `ℤ →(×2) ℤ`** (`TauCeti.Examples.TimesTwo.spectralObject`): at `(1, -1)`
   the limit cycles vanish (`Z_∞ = ⊥`), the object on page `3` vanishes, the spectral sequence
   stabilizes from page `3`, and `E_∞(1, -1) = 0`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian ZeroObject

namespace TauCeti.Examples.LimitPage

section Graded

variable {C κ : Type*} [Category* C] [Abelian C] (c : ℤ → ComplexShape κ) (r₀ : ℤ)

/-- The spectral sequence with constant terms `X pq` and zero differentials on every page. -/
def graded (X : κ → C) : SpectralSequence C c r₀ where
  page r _ := HomologicalComplex.graded (c r) X
  iso r _ pq _ _ :=
    ((HomologicalComplex.graded (c r) X).XIsoHomologyOfDEqZero pq (by simp) (by simp)).symm

lemma degeneratesAt_graded (X : κ → C) : (graded c r₀ X).DegeneratesAt r₀ where
  le := le_rfl
  d_eq_zero _ _ _ _ _ := rfl

instance hasLimitPage_graded (X : κ → C) (pq : κ) : (graded c r₀ X).HasLimitPage pq :=
  ((degeneratesAt_graded c r₀ X).stabilizesAt pq).hasLimitPage

lemma cyclesInf_graded (X : κ → C) (pq : κ) :
    (graded c r₀ X).cyclesInf pq = ⊤ := by
  rw [((degeneratesAt_graded c r₀ X).stabilizesAt pq).cyclesInf_eq]
  exact SpectralSequence.cyclesSubobject_self _ _

lemma boundariesSup_graded (X : κ → C) (pq : κ) :
    (graded c r₀ X).boundariesSup pq = ⊥ := by
  rw [((degeneratesAt_graded c r₀ X).stabilizesAt pq).boundariesSup_eq]
  exact SpectralSequence.boundariesSubobject_self _ _

/-- For a zero-differential spectral sequence, every object `X pq` is canonically isomorphic to
`E_∞(pq)`. -/
example (X : κ → C) (pq : κ) : Nonempty (X pq ≅ (graded c r₀ X).limitPage pq) :=
  ⟨((degeneratesAt_graded c r₀ X).stabilizesAt pq).limitPageIso r₀ le_rfl le_rfl⟩

/-- Rebased to any later page `s ≥ r₀`, the limit page is unchanged. -/
example (X : κ → C) (s : ℤ) (hs : r₀ ≤ s) (pq : κ) :
    Nonempty (((graded c r₀ X).fromPage s hs).limitPage pq ≅ (graded c r₀ X).limitPage pq) :=
  ⟨(graded c r₀ X).limitPageFromPageIso pq s hs⟩

/-- The zero spectral sequence has `IsZero (limitPage pq)`. -/
example (pq : κ) : IsZero ((graded c r₀ (fun _ : κ ↦ (0 : C))).limitPage pq) :=
  IsZero.of_iso (isZero_zero C)
    (((degeneratesAt_graded c r₀ (fun _ : κ ↦ (0 : C))).stabilizesAt pq).limitPageIso
      r₀ le_rfl le_rfl).symm

end Graded

section TimesTwoPage2

/-- First-quadrant cohomological complex shapes `c r` on `ℕ × ℕ`. -/
abbrev cohShape (r : ℤ) : ComplexShape (ℕ × ℕ) :=
  ComplexShape.spectralSequenceNat (r, 1 - r)

private lemma cohShape_rel_two : (cohShape 2).Rel (0, 1) (2, 0) := by
  simp [cohShape]

private lemma pair_ne : ((0 : ℕ), (1 : ℕ)) ≠ (2, 0) := by
  decide

/-- The free rank-one `ℤ`-module. -/
abbrev ZModZ : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Multiplication by `2` on `ℤ`. -/
abbrev mulTwo : ZModZ ⟶ ZModZ := 2 • 𝟙 ZModZ

private lemma mono_mulTwo : Mono mulTwo :=
  (ModuleCat.mono_iff_injective _).2 fun x y h ↦ by simpa [mulTwo] using h

/-- The cokernel `ℤ / 2ℤ` of multiplication by `2` on `ℤ`. -/
abbrev targetCok : ModuleCat ℤ := cokernel mulTwo

private abbrev page2 : HomologicalComplex (ModuleCat ℤ) (cohShape 2) :=
  HomologicalComplex.double mulTwo cohShape_rel_two

private def page3Obj (pq : ℕ × ℕ) : ModuleCat ℤ :=
  if pq = (2, 0) then targetCok else 0

private def page2HomologyIso (pq : ℕ × ℕ) : page2.homology pq ≅ page3Obj pq :=
  if h2 : pq = (2, 0) then
    eqToIso (by rw [h2]) ≪≫
      HomologicalComplex.doubleHomologyIso₁ pair_ne (cokernelIsCokernel mulTwo) ≪≫
      eqToIso (by simp [page3Obj, h2, targetCok])
  else if h1 : pq = (0, 1) then
    eqToIso (by rw [h1]) ≪≫
      (haveI := mono_mulTwo
      IsZero.iso
        ((isZero_kernel_of_mono mulTwo).of_iso
          (HomologicalComplex.doubleHomologyIso₀ pair_ne (limit.isLimit _)))
        (by dsimp only [page3Obj]; rw [ite_eq_right h2]; exact isZero_zero _))
  else
    IsZero.iso (HomologicalComplex.isZero_double_homology mulTwo cohShape_rel_two pq h1 h2)
      (by dsimp only [page3Obj]; rw [ite_eq_right h2]; exact isZero_zero _)

private def timesTwoPage (r : ℤ) : HomologicalComplex (ModuleCat ℤ) (cohShape r) :=
  if hr : r = 2 then hr ▸ page2 else HomologicalComplex.graded (cohShape r) page3Obj

@[simp]
private lemma timesTwoPage_two : timesTwoPage 2 = page2 := by
  simp [timesTwoPage]

private lemma timesTwoPage_of_ne {r : ℤ} (hr : r ≠ 2) :
    timesTwoPage r = HomologicalComplex.graded (cohShape r) page3Obj :=
  dite_eq_right hr

/-- Explicit `E₂`-spectral sequence with `E₂^{0,1} = ℤ →(×2) E₂^{2,0} = ℤ` and zero elsewhere,
degenerating at page `3`. -/
def timesTwoPage2 : SpectralSequence (ModuleCat ℤ) cohShape 2 where
  page r _ := timesTwoPage r
  iso r r' pq hrr' _ := by
    by_cases hr2 : r = 2
    · subst hr2
      have hr'3 : r' = 3 := by lia
      subst hr'3
      have h32 : (3 : ℤ) ≠ 2 := by norm_num
      exact eqToIso (congrArg (fun K ↦ K.homology pq) timesTwoPage_two) ≪≫
        page2HomologyIso pq ≪≫
        eqToIso (congrArg (fun K ↦ K.X pq) (timesTwoPage_of_ne h32).symm)
    · have hr'2 : r' ≠ 2 := by lia
      have h0 : (timesTwoPage r).d ((cohShape r).prev pq) pq = 0 := by
        rw [timesTwoPage_of_ne hr2]
      have h1 : (timesTwoPage r).d pq ((cohShape r).next pq) = 0 := by
        rw [timesTwoPage_of_ne hr2]
      refine (HomologicalComplex.XIsoHomologyOfDEqZero _ pq h0 h1).symm ≪≫ eqToIso ?_
      rw [timesTwoPage_of_ne hr2, timesTwoPage_of_ne hr'2]

lemma d_timesTwoPage2_two_ne_zero :
    (timesTwoPage2.page 2 le_rfl).d (0, 1) (2, 0) ≠ 0 := by
  intro h
  have h1 : (HomologicalComplex.doubleXIso₀ mulTwo cohShape_rel_two).hom ≫ mulTwo ≫
      (HomologicalComplex.doubleXIso₁ mulTwo cohShape_rel_two pair_ne).inv = 0 := by
    refine (HomologicalComplex.double_d mulTwo cohShape_rel_two pair_ne).symm.trans ?_
    exact h
  have h2 : mulTwo = 0 := by
    simpa using (cancel_epi (HomologicalComplex.doubleXIso₀ mulTwo cohShape_rel_two).hom).1
      ((cancel_mono (HomologicalComplex.doubleXIso₁ mulTwo cohShape_rel_two pair_ne).inv).1
        (by simpa using h1))
  have h3 := ConcreteCategory.congr_hom h2 (1 : ℤ)
  norm_num [mulTwo, ZModZ] at h3

lemma not_degeneratesAt_timesTwoPage2_two : ¬ timesTwoPage2.DegeneratesAt 2 := by
  intro h
  exact d_timesTwoPage2_two_ne_zero (h.d_eq_zero le_rfl le_rfl (0, 1) (2, 0))

lemma not_stabilizesAt_timesTwoPage2_zero_one : ¬ timesTwoPage2.StabilizesAt (0, 1) 2 := by
  intro h
  have hd : (timesTwoPage2.page 2 le_rfl).dFrom (0, 1) = 0 := h.dFrom_eq_zero le_rfl le_rfl
  exact d_timesTwoPage2_two_ne_zero (by
    rw [← (timesTwoPage2.page 2 le_rfl).dFrom_comp_xNextIso cohShape_rel_two, hd, zero_comp])

lemma not_stabilizesAt_timesTwoPage2_two_zero : ¬ timesTwoPage2.StabilizesAt (2, 0) 2 := by
  intro h
  have hd : (timesTwoPage2.page 2 le_rfl).dTo (2, 0) = 0 := h.dTo_eq_zero le_rfl le_rfl
  exact d_timesTwoPage2_two_ne_zero (by
    rw [← (timesTwoPage2.page 2 le_rfl).xPrevIso_comp_dTo cohShape_rel_two, hd, comp_zero])

lemma degeneratesAt_timesTwoPage2_three : timesTwoPage2.DegeneratesAt 3 where
  le := by norm_num
  d_eq_zero r _ h3r pq pq' := by
    have hne : r ≠ 2 := by lia
    have hd : ∀ (K : HomologicalComplex (ModuleCat ℤ) (cohShape r)),
        K = HomologicalComplex.graded (cohShape r) page3Obj → K.d pq pq' = 0 := by
      rintro _ rfl
      rfl
    exact hd _ (timesTwoPage_of_ne hne)

example : timesTwoPage2.IsRegularAt (0, 1) ∧ timesTwoPage2.IsCoregularAt (0, 1) :=
  ⟨(degeneratesAt_timesTwoPage2_three.stabilizesAt (0, 1)).isRegularAt,
    (degeneratesAt_timesTwoPage2_three.stabilizesAt (0, 1)).isCoregularAt⟩

example (r : ℤ) (h3r : 3 ≤ r) :
    Nonempty ((timesTwoPage2.page 3 (by norm_num)).X (2, 0) ≅
      (timesTwoPage2.page r (by lia)).X (2, 0)) :=
  ⟨(degeneratesAt_timesTwoPage2_three.stabilizesAt (2, 0)).pageXIso r (by lia) h3r⟩

instance hasLimitPage_timesTwoPage2 (pq : ℕ × ℕ) : timesTwoPage2.HasLimitPage pq :=
  (degeneratesAt_timesTwoPage2_three.stabilizesAt pq).hasLimitPage

lemma isZero_limitPage_timesTwoPage2_zero_one : IsZero (timesTwoPage2.limitPage (0, 1)) := by
  have hst := degeneratesAt_timesTwoPage2_three.stabilizesAt (0, 1)
  have h3 : IsZero ((timesTwoPage2.page 3 (by norm_num)).X (0, 1)) := by
    dsimp only [timesTwoPage2, timesTwoPage]
    split_ifs with h
    · exact absurd h (by norm_num)
    · dsimp only [HomologicalComplex.graded_X, page3Obj]
      rw [ite_eq_right (by decide)]
      exact isZero_zero _
  exact h3.of_iso (hst.limitPageIso 3 (by norm_num) le_rfl).symm

/-- At `(2, 0)`, the limit page of `timesTwoPage2` is isomorphic to `cokernel (×2)`. -/
def targetCokIsoLimitPage : targetCok ≅ timesTwoPage2.limitPage (2, 0) :=
  have hst := degeneratesAt_timesTwoPage2_three.stabilizesAt (2, 0)
  eqToIso (by simp [timesTwoPage2, timesTwoPage, page3Obj]) ≪≫
    hst.limitPageIso 3 (by norm_num) le_rfl

/-- At `(2, 0)`, the limit page of `timesTwoPage2` is nonzero. -/
lemma not_isZero_limitPage_timesTwoPage2_two_zero :
    ¬ IsZero (timesTwoPage2.limitPage (2, 0)) := by
  intro hz
  have hzCok : IsZero targetCok := hz.of_iso targetCokIsoLimitPage
  let φ : ZModZ ⟶ ModuleCat.of ℤ (ZMod 2) := ModuleCat.ofHom (Algebra.linearMap ℤ (ZMod 2))
  have hφ : mulTwo ≫ φ = 0 := by
    ext
    simp only [Linear.smul_comp, Category.id_comp, ModuleCat.hom_smul, LinearMap.smul_apply,
      nsmul_eq_mul, Nat.cast_ofNat, ModuleCat.hom_zero, LinearMap.zero_apply]
    decide
  have hzero : φ = 0 := by
    calc φ = cokernel.π mulTwo ≫ cokernel.desc mulTwo φ hφ := (cokernel.π_desc _ _ _).symm
      _ = 0 ≫ cokernel.desc mulTwo φ hφ := by rw [hzCok.eq_of_tgt (cokernel.π mulTwo) 0]
      _ = 0 := zero_comp
  have h1 := ConcreteCategory.congr_hom hzero (1 : ℤ)
  simp [φ, ZModZ] at h1

end TimesTwoPage2

section FilteredTimesTwo

/-- The spectral sequence of the filtered complex `ℤ →(×2) ℤ` from `TauCeti.Examples.TimesTwo`. -/
abbrev filteredTimesTwo :=
  TimesTwo.spectralObject.spectralSequence SpectralObject.coreE₂Cohomological

/-- At `(1, -1)`, `Z_3 = ⊥` implies `(filteredTimesTwo.page 3 _).X (1, -1)` is zero, so the
spectral sequence stabilizes at `(1, -1)` from page `3`, and has vanishing limit page
`E_∞(1, -1) = 0`. -/
example :
    IsZero ((filteredTimesTwo.page 3 (by norm_num)).X ((1 : ℤ), (-1 : ℤ))) ∧
      filteredTimesTwo.StabilizesAt ((1 : ℤ), (-1 : ℤ)) 3 ∧
      ∀ [filteredTimesTwo.HasLimitPage ((1 : ℤ), (-1 : ℤ))],
        IsZero (filteredTimesTwo.limitPage ((1 : ℤ), (-1 : ℤ))) := by
  have hZ : filteredTimesTwo.cyclesSubobject ((1 : ℤ), (-1 : ℤ)) 3 (by norm_num) = ⊥ :=
    TimesTwo.cyclesSubobject_three_eq_bot
  have hX : IsZero ((filteredTimesTwo.page 3 (by norm_num)).X ((1 : ℤ), (-1 : ℤ))) := by
    have hBZ := filteredTimesTwo.boundariesSubobject_le_cyclesSubobject ((1 : ℤ), (-1 : ℤ))
      3 3 (by norm_num) (by norm_num)
    rw [filteredTimesTwo.isZero_page_X_iff ((1 : ℤ), (-1 : ℤ)) 3 (by norm_num)]
    rw [hZ] at hBZ ⊢
    exact le_antisymm hBZ bot_le
  have hst : filteredTimesTwo.StabilizesAt ((1 : ℤ), (-1 : ℤ)) 3 :=
    SpectralSequence.stabilizesAt_of_isZero (by norm_num) hX
  refine ⟨hX, hst, fun {_} ↦ hX.of_iso (hst.limitPageIso 3 (by norm_num) le_rfl).symm⟩

end FilteredTimesTwo

end TauCeti.Examples.LimitPage
