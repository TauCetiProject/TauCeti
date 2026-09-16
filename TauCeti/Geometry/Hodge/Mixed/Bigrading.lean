/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Conjugation
import TauCeti.LinearAlgebra.Submodule.Compl
import TauCeti.Order.CompactlyGenerated

/-!
# Mixed Hodge structures from a bigrading

Deligne's theorem (`TauCeti.Hodge.MixedHodgeStructure.isInternal_deligneSplittingFamily`) says
that a mixed Hodge structure carries a bigrading `I^{p,q}` of its complex model from which both
filtrations are read off,

`W_k = ⨆_{p + q ≤ k} I^{p,q}`, `F^p = ⨆_{p' ≥ p} I^{p',q'}`,

and whose pieces are conjugate to each other modulo lower weight. This file proves the converse:
a rational weight filtration and a Hodge filtration admitting such a bigrading form a mixed Hodge
structure. The conjugation condition asked for is the weakest one that works,
`conj I^{p,q} ≤ I^{q,p} ⊔ W_{p+q-1}` — the images of `I^{p,q}` and `I^{q,p}` in `grᵂ_{p+q}` are
conjugate — and it need not be Deligne's own bigrading: no uniqueness is claimed or needed.

The converse is a way to recognise new mixed Hodge structures. Verifying purity of every graded
piece directly means computing induced filtrations on quotients, whereas exhibiting a bigrading is
a statement about subspaces of the ambient complex space alone. Together with Deligne's theorem it
characterises mixed Hodge structures among bounded pairs of filtrations
(`TauCeti.Hodge.MixedHodgeStructure.exists_isHodgeBigrading_iff`).

The argument takes place in the ambient space. On `grᵂ_k`, the images of `F^p` and of
`conj F^{k+1-p}` are complementary: modulo `W_{k-1}`, the first is spanned by the pieces
`I^{p',q'}` of total degree `k` with `p' ≥ p`, the second is contained in the span of those with
`q' ≥ k + 1 - p`, and independence of the bigrading separates the two sets of bidegrees, while
every piece of total degree `k` lies in one of the two spans.

## Main declarations

* `TauCeti.Hodge.IsHodgeBigrading`: a bigrading of the complex model adapted to a rational weight
  filtration and a Hodge filtration.
* `TauCeti.Hodge.IsHodgeBigrading.isCompl_complexGradedF`: the induced filtration on a complex
  graded piece is opposed to its conjugate.
* `TauCeti.Hodge.MixedHodgeStructure.ofIsHodgeBigrading`: the mixed Hodge structure defined by a
  bounded pair of filtrations with a bigrading.
* `TauCeti.Hodge.MixedHodgeStructure.isHodgeBigrading_deligneSplittingFamily`: Deligne's bigrading
  is such a bigrading.
* `TauCeti.Hodge.MixedHodgeStructure.exists_isHodgeBigrading_iff`: a bounded pair of filtrations
  satisfies the purity axiom exactly when it admits a bigrading.

## References

Deligne, *Théorie de Hodge II*, 1.2.8 and 1.2.10; Peters–Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4 and Ch. 3.1, where mixed Hodge structures are characterised by their
bigradings.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ) in
/-- A **Hodge bigrading** for a rational weight filtration `WQ` and a Hodge filtration `F`: an
independent family `I^{p,q}` of complex subspaces recovering the complexified weight filtration as
`W_k = ⨆_{p+q ≤ k} I^{p,q}` and the Hodge filtration as `F^p = ⨆_{p' ≥ p} I^{p',q'}`, whose pieces
are conjugate modulo lower weight: `conj I^{p,q} ≤ I^{q,p} ⊔ W_{p+q-1}`. -/
structure IsHodgeBigrading (WQ : ℤ → Submodule ℚ Vℚ) (F : ℤ → Submodule ℂ Vℂ)
    (I : ℤ × ℤ → Submodule ℂ Vℂ) : Prop where
  /-- The pieces of the bigrading are independent. -/
  iSupIndep : iSupIndep I
  /-- The complexified weight filtration is the sum of the pieces of bounded total degree. -/
  rationalToComplexSubmodule_eq_iSup (k : ℤ) :
    rationalToComplexSubmodule hℚ hℂ (WQ k) = ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k), I pq
  /-- The Hodge filtration is the sum of the pieces of bounded-below first index. -/
  F_eq_iSup (p : ℤ) : F p = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), I pq
  /-- Conjugation exchanges the pieces `I^{p,q}` and `I^{q,p}` modulo lower weight. -/
  map_latticeConj_le (pq : ℤ × ℤ) :
    (I pq).map (latticeConj hℂ) ≤
      I pq.swap ⊔ rationalToComplexSubmodule hℚ hℂ (WQ (pq.1 + pq.2 - 1))

namespace IsHodgeBigrading

variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {WQ : ℤ → Submodule ℚ Vℚ} {F : ℤ → Submodule ℂ Vℂ} {I : ℤ × ℤ → Submodule ℂ Vℂ}

/-- A piece of a Hodge bigrading lies in the weight step of its total degree. -/
theorem le_rationalToComplexSubmodule (h : IsHodgeBigrading hℚ hℂ WQ F I) {pq : ℤ × ℤ} {k : ℤ}
    (hk : pq.1 + pq.2 ≤ k) : I pq ≤ rationalToComplexSubmodule hℚ hℂ (WQ k) :=
  h.rationalToComplexSubmodule_eq_iSup k ▸ le_iSup₂_of_le pq hk le_rfl

/-- A piece of a Hodge bigrading lies in the Hodge step of its first index. -/
theorem le_F (h : IsHodgeBigrading hℚ hℂ WQ F I) {pq : ℤ × ℤ} {p : ℤ} (hp : p ≤ pq.1) :
    I pq ≤ F p :=
  h.F_eq_iSup p ▸ le_iSup₂_of_le pq hp le_rfl

/-- A weight filtration admitting a Hodge bigrading is increasing. -/
theorem monotone (h : IsHodgeBigrading hℚ hℂ WQ F I) : Monotone WQ := fun j k hjk ↦ by
  rw [← rationalToComplexSubmodule_le_iff hℚ hℂ, h.rationalToComplexSubmodule_eq_iSup j]
  exact iSup₂_le fun pq hpq ↦ h.le_rationalToComplexSubmodule (hpq.trans hjk)

/-- A Hodge filtration admitting a Hodge bigrading is decreasing. -/
theorem antitone (h : IsHodgeBigrading hℚ hℂ WQ F I) : Antitone F := fun p q hpq ↦ by
  rw [h.F_eq_iSup q]
  exact iSup₂_le fun pq hq ↦ h.le_F (hpq.trans hq)

/-- Every piece of a Hodge bigrading lies in the conjugate of the swapped piece, modulo lower
weight. -/
theorem le_map_latticeConj_sup (h : IsHodgeBigrading hℚ hℂ WQ F I) (pq : ℤ × ℤ) :
    I pq ≤ (I pq.swap).map (latticeConj hℂ) ⊔
      rationalToComplexSubmodule hℚ hℂ (WQ (pq.1 + pq.2 - 1)) := by
  intro x hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h.map_latticeConj_le pq ⟨x, hx, rfl⟩)
  refine Submodule.mem_sup.2 ⟨latticeConj hℂ y, ⟨y, hy, rfl⟩, latticeConj hℂ z, ?_, ?_⟩
  · rw [← rationalToComplexSubmodule_conj hℚ hℂ]
    exact ⟨z, hz, rfl⟩
  · rw [← map_add, hyz, latticeConj_involutive]

/-- A Hodge step meets a weight step in the sum of the pieces lying in both. -/
theorem F_inf_rationalToComplexSubmodule_eq_iSup (h : IsHodgeBigrading hℚ hℂ WQ F I)
    (p k : ℤ) :
    F p ⊓ rationalToComplexSubmodule hℚ hℂ (WQ k) =
      ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1 ∧ pq.1 + pq.2 ≤ k), I pq := by
  rw [h.F_eq_iSup p, h.rationalToComplexSubmodule_eq_iSup k]
  exact TauCeti.iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and h.iSupIndep _ _

/-- Inside `W_k`, the conjugate of the Hodge step `F^r` is spanned, modulo `W_{k-1}`, by pieces
whose second index is at least `r`. -/
theorem map_latticeConj_F_inf_rationalToComplexSubmodule_le_iSup
    (h : IsHodgeBigrading hℚ hℂ WQ F I) (r k : ℤ) :
    (F r).map (latticeConj hℂ) ⊓ rationalToComplexSubmodule hℚ hℂ (WQ k) ≤
      ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k - 1 ∨ r ≤ pq.2), I pq := by
  conv_lhs => rw [← rationalToComplexSubmodule_conj hℚ hℂ (WQ k),
    ← Submodule.map_inf _ (latticeConj_involutive hℂ).injective,
    h.F_inf_rationalToComplexSubmodule_eq_iSup r k]
  simp only [Submodule.map_iSup]
  refine iSup₂_le fun pq hpq ↦ (h.map_latticeConj_le pq).trans (sup_le ?_ ?_)
  · exact le_iSup₂_of_le pq.swap (Or.inr hpq.1) le_rfl
  · refine (rationalToComplexSubmodule_mono hℚ hℂ (h.monotone (by omega : _ ≤ k - 1))).trans ?_
    rw [h.rationalToComplexSubmodule_eq_iSup]
    exact biSup_mono fun _ ↦ Or.inl

/-- **The filtration induced on a complex graded piece is opposed to its conjugate.** On
`grᵂ_k`, the images of `F^p` and of `conj F^{k+1-p}` are complementary. -/
theorem isCompl_complexGradedF (h : IsHodgeBigrading hℚ hℂ WQ F I) (k p : ℤ) :
    IsCompl (complexGradedF (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j)) F k p)
      (complexGradedF (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j))
        (fun q ↦ (F q).map (latticeConj hℂ)) k (k + 1 - p)) := by
  set W := fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j) with hW
  have hWk : W (k - 1) ≤ W k := rationalToComplexSubmodule_mono hℚ hℂ (h.monotone (by omega))
  have hdef (G : ℤ → Submodule ℂ Vℂ) (q : ℤ) : complexGradedF W G k q =
      ((G q ⊓ W k).submoduleOf (W k)).map ((W (k - 1)).submoduleOf (W k)).mkQ := by
    ext x
    rw [mem_complexGradedF_iff]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ ⟨y, ⟨hy, y.2⟩, hyx⟩, fun ⟨y, hy, hyx⟩ ↦ ⟨y, hy.1, hyx⟩⟩
  rw [hdef, hdef, TauCeti.Submodule.isCompl_map_mkQ_iff,
    ← Submodule.map_le_map_iff_of_injective (W k).injective_subtype,
    ← (Submodule.map_injective_of_injective (W k).injective_subtype).eq_iff]
  simp only [Submodule.map_inf _ (W k).injective_subtype, Submodule.map_sup,
    Submodule.submoduleOf, Submodule.map_comap_subtype, Submodule.map_subtype_top,
    inf_of_le_right hWk, inf_of_le_right (inf_le_right : _ ⊓ W k ≤ W k)]
  constructor
  · -- Modulo `W_{k-1}`, the two images sit in the sums of pieces over disjoint sets of bidegrees.
    have hA : W (k - 1) ⊔ F p ⊓ W k ≤
        ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k - 1 ∨ p ≤ pq.1 ∧ pq.1 + pq.2 ≤ k), I pq := by
      simp only [hW]
      rw [h.rationalToComplexSubmodule_eq_iSup, h.F_inf_rationalToComplexSubmodule_eq_iSup]
      exact sup_le (biSup_mono fun _ ↦ Or.inl) (biSup_mono fun _ ↦ Or.inr)
    have hB : W (k - 1) ⊔ (F (k + 1 - p)).map (latticeConj hℂ) ⊓ W k ≤
        ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k - 1 ∨ k + 1 - p ≤ pq.2), I pq := by
      refine sup_le ?_ (h.map_latticeConj_F_inf_rationalToComplexSubmodule_le_iSup _ k)
      simp only [hW]
      rw [h.rationalToComplexSubmodule_eq_iSup]
      exact biSup_mono fun _ ↦ Or.inl
    refine (inf_le_inf hA hB).trans ?_
    simp only [hW]
    rw [TauCeti.iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and h.iSupIndep,
      h.rationalToComplexSubmodule_eq_iSup]
    exact biSup_mono fun _ ↦ by omega
  · -- Every piece of total degree at most `k` lies in `W_{k-1}` or in one of the two images.
    refine le_antisymm (sup_le hWk (sup_le inf_le_right inf_le_right)) ?_
    conv_lhs => simp only [hW]; rw [h.rationalToComplexSubmodule_eq_iSup]
    refine iSup₂_le fun pq hpq ↦ ?_
    rcases lt_or_eq_of_le hpq with hlt | heq
    · exact le_sup_of_le_left (h.le_rationalToComplexSubmodule (by omega))
    by_cases hp : p ≤ pq.1
    · exact le_sup_of_le_right (le_sup_of_le_left
        (le_inf (h.le_F hp) (h.le_rationalToComplexSubmodule hpq)))
    refine (h.le_map_latticeConj_sup pq).trans (sup_le ?_ ?_)
    · refine le_sup_of_le_right (le_sup_of_le_right (le_inf (Submodule.map_mono
        (h.le_F (by simp; omega))) ?_))
      simp only [hW]
      rw [← rationalToComplexSubmodule_conj hℚ hℂ (WQ k)]
      exact Submodule.map_mono (h.le_rationalToComplexSubmodule (by simp; omega))
    · rw [heq]
      exact le_sup_left

/-- **Purity of the graded pieces.** If a Hodge filtration with a Hodge bigrading is exhaustive,
then on every rational graded piece `grᵂ_k` the induced filtration is the Hodge filtration of a
pure Hodge structure of weight `k`: this is the purity axiom of a mixed Hodge structure. -/
theorem exists_hodgeStructure_F_eq_gradedF (h : IsHodgeBigrading hℚ hℂ WQ F I)
    (hF : ∃ p, F p = ⊤) (k : ℤ) :
    ∃ hs : HodgeStructure (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k)) k,
      hs.F = gradedF hℚ hℂ WQ h.monotone F k := by
  -- The pure structure is first built on the complex graded piece, then transported.
  let hsC : HodgeStructureOn
      (weightGradedComplex (fun j ↦ rationalToComplexSubmodule hℚ hℂ (WQ j)) k)
      (gradedComplexConjugation hℚ hℂ WQ k) k :=
    { F := complexGradedF _ F k
      F_antitone := complexGradedF_antitone _ F h.antitone k
      F_top := hF.imp fun _ hp ↦ complexGradedF_of_eq_top _ F hp
      opposed := fun p ↦ by
        rw [map_gradedComplexConjugation_complexGradedF]
        exact h.isCompl_complexGradedF k p }
  refine ⟨hsC.comap (gradedComplexEquiv hℚ hℂ WQ h.monotone k) fun x ↦ ?_, ?_⟩
  · rw [latticeConjugation_toEquiv_apply]
    exact gradedComplexEquiv_latticeConj hℚ hℂ WQ h.monotone k x
  · ext p x
    rw [HodgeStructureOn.comap_F, Submodule.mem_comap, mem_gradedF_iff]
    exact mem_complexGradedF_iff _ F k p _

end IsHodgeBigrading

namespace MixedHodgeStructure

variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {WQ : ℤ → Submodule ℚ Vℚ} {F : ℤ → Submodule ℂ Vℂ} {I : ℤ × ℤ → Submodule ℂ Vℂ}

/-- **The mixed Hodge structure defined by a bigrading.** A bounded rational weight filtration and
a bounded Hodge filtration admitting a Hodge bigrading form a mixed Hodge structure. -/
noncomputable def ofIsHodgeBigrading (h : IsHodgeBigrading hℚ hℂ WQ F I)
    (hW_top : ∃ k, WQ k = ⊤) (hW_bot : ∃ k, WQ k = ⊥) (hF_top : ∃ p, F p = ⊤)
    (hF_bot : ∃ p, F p = ⊥) : MixedHodgeStructure hℚ hℂ where
  WQ := WQ
  WQ_monotone := h.monotone
  WQ_top := hW_top
  WQ_bot := hW_bot
  F := F
  F_antitone := h.antitone
  F_top := hF_top
  F_bot := hF_bot
  graded_pure := h.exists_hodgeStructure_F_eq_gradedF hF_top

@[simp]
theorem ofIsHodgeBigrading_WQ (h : IsHodgeBigrading hℚ hℂ WQ F I) (hW_top : ∃ k, WQ k = ⊤)
    (hW_bot : ∃ k, WQ k = ⊥) (hF_top : ∃ p, F p = ⊤) (hF_bot : ∃ p, F p = ⊥) :
    (ofIsHodgeBigrading h hW_top hW_bot hF_top hF_bot).WQ = WQ :=
  (rfl)

@[simp]
theorem ofIsHodgeBigrading_F (h : IsHodgeBigrading hℚ hℂ WQ F I) (hW_top : ∃ k, WQ k = ⊤)
    (hW_bot : ∃ k, WQ k = ⊥) (hF_top : ∃ p, F p = ⊤) (hF_bot : ∃ p, F p = ⊥) :
    (ofIsHodgeBigrading h hW_top hW_bot hF_top hF_bot).F = F :=
  (rfl)

/-- **Deligne's bigrading is a Hodge bigrading** of the filtrations of a mixed Hodge structure. -/
theorem isHodgeBigrading_deligneSplittingFamily (mhs : MixedHodgeStructure hℚ hℂ) :
    IsHodgeBigrading hℚ hℂ mhs.WQ mhs.F mhs.deligneSplittingFamily where
  iSupIndep := mhs.iSupIndep_deligneSplittingFamily
  rationalToComplexSubmodule_eq_iSup k := by
    simpa only [deligneSplittingFamily_apply] using mhs.WC_eq_iSup_deligneSplitting k
  F_eq_iSup p := by
    simpa only [deligneSplittingFamily_apply] using mhs.F_eq_iSup_deligneSplitting p
  map_latticeConj_le pq := by
    simp only [deligneSplittingFamily_apply, Prod.fst_swap, Prod.snd_swap]
    exact (mhs.map_latticeConj_deligneSplitting_le_sup_WC pq.1 pq.2).trans
      (sup_le_sup_left (mhs.WC_monotone (by omega)) _)

/-- Rebuilding a mixed Hodge structure from Deligne's bigrading returns it. -/
@[simp]
theorem ofIsHodgeBigrading_deligneSplittingFamily (mhs : MixedHodgeStructure hℚ hℂ) :
    ofIsHodgeBigrading mhs.isHodgeBigrading_deligneSplittingFamily mhs.WQ_top mhs.WQ_bot
      mhs.F_top mhs.F_bot = mhs :=
  (rfl)

/-- **A pair of bounded filtrations is a mixed Hodge structure exactly when it admits a Hodge
bigrading.** Precisely: the purity axiom holds for a bounded increasing rational weight filtration
and a bounded decreasing Hodge filtration if and only if the two filtrations have a Hodge
bigrading. -/
theorem exists_isHodgeBigrading_iff (hWQ : Monotone WQ) (hW_top : ∃ k, WQ k = ⊤)
    (hW_bot : ∃ k, WQ k = ⊥) (hF_anti : Antitone F) (hF_top : ∃ p, F p = ⊤)
    (hF_bot : ∃ p, F p = ⊥) :
    (∃ I, IsHodgeBigrading hℚ hℂ WQ F I) ↔
      ∀ k, ∃ hs : HodgeStructure (isBaseChange_ratTensorMap ℂ (weightGradedRat WQ k)) k,
        hs.F = gradedF hℚ hℂ WQ hWQ F k :=
  ⟨fun ⟨_, h⟩ ↦ h.exists_hodgeStructure_F_eq_gradedF hF_top, fun hpure ↦
    ⟨_, isHodgeBigrading_deligneSplittingFamily ⟨WQ, hWQ, hW_top, hW_bot, F, hF_anti, hF_top,
      hF_bot, hpure⟩⟩⟩

end MixedHodgeStructure

end TauCeti.Hodge
