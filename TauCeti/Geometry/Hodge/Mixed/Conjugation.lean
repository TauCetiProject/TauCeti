/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Decomposition
public import Mathlib.LinearAlgebra.SModEq.Basic

/-!
# Conjugation of Deligne's bigrading

For a mixed Hodge structure, complex conjugation exchanges the Deligne bigrading pieces up to
strictly lower bidegrees. This file first proves the coarser weight-filtered form

`conj I^{p,q} + W_{p+q-2} = I^{q,p} + W_{p+q-2}`.

The two-step weight bound follows directly from the current API. Deligne's closed formula puts a
vector of `conj I^{p,q}` in `F^q` modulo `W_{p+q-2}`, while it lies in `conj F^p` exactly. A
representative of the same class in `I^{q,p}` initially agrees only modulo `W_{p+q-1}`. On the
intervening graded piece, however, their difference lies in the opposed steps `F^q` and
`conj F^p` of a pure Hodge
structure of weight `p+q-1`, so it vanishes and the difference drops one step further.

The full relation then refines the error term to the sum of the pieces `I^{r,s}` with `r < q`
and `s < p`. The Hodge-filtration recovery theorem identifies every intersection `F^a ∩ W_b`
as the sum of the Deligne components satisfying both bounds. It follows that the tail in
Deligne's formula, after adjoining its leading filtration step, is precisely saturation by the
lower-bidegree components. Induction on total degree gives the same statement for the conjugate
tail. The two closed formulas then agree modulo the lower-bidegree sum by the modular law for
subspaces.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_le_sup_WC`: conjugating
  `I^{p,q}` lands in `I^{q,p} + W_{p+q-2}`.
* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_sup_WC`: the symmetric
  equality modulo `W_{p+q-2}`.
* `TauCeti.Hodge.MixedHodgeStructure.exists_mem_deligneSplitting_smodEq_latticeConj`: the
  elementwise modular-congruence form.
* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_sup_below`: the full
  Deligne relation, with the error supported in strictly lower bidegrees.
* `TauCeti.Hodge.MixedHodgeStructure.exists_mem_deligneSplitting_smodEq_latticeConj_below`:
  the elementwise form of the full relation.

## References

Deligne, *Théorie de Hodge II*, 1.2.10; Peters--Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace MixedHodgeStructure

variable (mhs : MixedHodgeStructure hℚ hℂ)

/-- The sum of the Deligne components strictly below `(p,q)` in both bidegrees. -/
noncomputable def deligneSplittingBelow (p q : ℤ) : Submodule ℂ Vℂ :=
  ⨆ r, ⨆ (_ : r < p), ⨆ s, ⨆ (_ : s < q), mhs.deligneSplitting r s

/-- The lower Deligne sum as a supremum over its two strict index bounds. -/
theorem deligneSplittingBelow_def (p q : ℤ) :
    mhs.deligneSplittingBelow p q =
      ⨆ r, ⨆ (_ : r < p), ⨆ s, ⨆ (_ : s < q), mhs.deligneSplitting r s :=
  (rfl)

/-- A Deligne component strictly below both bounds belongs to the lower Deligne sum. -/
theorem deligneSplitting_le_deligneSplittingBelow {r s p q : ℤ} (hr : r < p) (hs : s < q) :
    mhs.deligneSplitting r s ≤ mhs.deligneSplittingBelow p q :=
  le_iSup₂_of_le r hr (le_iSup₂_of_le s hs le_rfl)

/-- The lower-bidegree error below `(p,q)` lies at least two steps below total weight `p+q`. -/
theorem deligneSplittingBelow_le_WC (p q : ℤ) :
    mhs.deligneSplittingBelow p q ≤ mhs.WC (p + q - 2) := by
  refine iSup₂_le fun r hr ↦ iSup₂_le fun s hs ↦
    (mhs.deligneSplitting_le_WC r s).trans ?_
  exact mhs.WC_monotone (by omega)

/-- Enlarging either bound enlarges the sum of lower Deligne components. -/
theorem deligneSplittingBelow_mono {p q p' q' : ℤ} (hp : p ≤ p') (hq : q ≤ q') :
    mhs.deligneSplittingBelow p q ≤ mhs.deligneSplittingBelow p' q' := by
  rw [deligneSplittingBelow, deligneSplittingBelow]
  refine iSup₂_le fun r hr ↦ iSup₂_le fun s hs ↦ ?_
  exact le_iSup₂_of_le r (hr.trans_le hp)
    (le_iSup₂_of_le s (hs.trans_le hq) le_rfl)

/-- The part of Deligne's formula below its leading conjugate-filtration term. -/
private noncomputable def hodgeTail (p q : ℤ) : Submodule ℂ Vℂ :=
  ⨆ j : ℕ, mhs.F (q - (j : ℤ) - 1) ⊓ mhs.WC (p + q - (j : ℤ) - 2)

/-- The Hodge-filtration tail in Deligne's formula, after adjoining its leading filtration step,
is exactly saturation by the lower-bidegree components. -/
private theorem inf_sup_hodgeTail_eq_inf_sup_deligneSplittingBelow (p q : ℤ) :
    (mhs.F q ⊓ mhs.WC (p + q)) ⊔ mhs.hodgeTail p q =
      (mhs.F q ⊓ mhs.WC (p + q)) ⊔ mhs.deligneSplittingBelow q p := by
  apply le_antisymm
  · refine sup_le le_sup_left (iSup_le fun j ↦ ?_)
    rw [mhs.F_inf_WC_eq_iSup_deligneSplitting
      (q - (j : ℤ) - 1) (p + q - (j : ℤ) - 2)]
    refine iSup₂_le fun rs hrs ↦ ?_
    by_cases hr : q ≤ rs.1
    · exact le_sup_of_le_left (le_inf
        ((mhs.deligneSplitting_le_F rs.1 rs.2).trans (mhs.F_antitone hr))
        ((mhs.deligneSplitting_le_WC rs.1 rs.2).trans (mhs.WC_monotone (by omega))))
    · exact le_sup_of_le_right
        (le_iSup₂_of_le rs.1 (by omega) (le_iSup₂_of_le rs.2 (by omega) le_rfl))
  · refine sup_le le_sup_left (iSup₂_le fun r hr ↦ iSup₂_le fun s hs ↦ ?_)
    let j : ℕ := (q - r - 1).toNat
    have hj : (j : ℤ) = q - r - 1 := by
      rw [Int.toNat_of_nonneg]
      omega
    refine le_sup_of_le_right (le_iSup_of_le j ?_)
    rw [hj]
    have hFIndex : q - (q - r - 1) - 1 = r := by omega
    have hWIndex : p + q - (q - r - 1) - 2 = p + r - 1 := by omega
    rw [hFIndex, hWIndex]
    exact le_inf (mhs.deligneSplitting_le_F r s)
      ((mhs.deligneSplitting_le_WC r s).trans (mhs.WC_monotone (by omega)))

/-- An element of a weight step lying in opposed filtration steps modulo the preceding weight step
already lies in that preceding step. -/
private theorem mem_WC_sub_one_of_mem_F_sup_and_mem_conjF_sup (k p : ℤ) {x : Vℂ}
    (hxW : x ∈ mhs.WC k) (hxF : x ∈ mhs.F p ⊔ mhs.WC (k - 1))
    (hxConj : x ∈ mhs.conjF (k + 1 - p) ⊔ mhs.WC (k - 1)) :
    x ∈ mhs.WC (k - 1) := by
  obtain ⟨f, hf, wf, hwf, hfw⟩ := Submodule.mem_sup.1 hxF
  obtain ⟨c, hc, wc, hwc, hcw⟩ := Submodule.mem_sup.1 hxConj
  have hfW : f ∈ mhs.WC k := by
    have hfd : f = x - wf := by rw [← hfw]; abel
    rw [hfd]
    exact Submodule.sub_mem _ hxW (mhs.WC_monotone (by omega) hwf)
  have hcW : c ∈ mhs.WC k := by
    have hcd : c = x - wc := by rw [← hcw]; abel
    rw [hcd]
    exact Submodule.sub_mem _ hxW (mhs.WC_monotone (by omega) hwc)
  have hfc : f - c ∈ mhs.WC (k - 1) := by
    have hfc' : f - c = wc - wf := by
      calc
        f - c = (f + wf) - (c + wc) + (wc - wf) := by abel
        _ = wc - wf := by rw [hfw, hcw, sub_self, zero_add]
    rw [hfc']
    exact Submodule.sub_mem _ hwc hwf
  have hmk : (Submodule.Quotient.mk (⟨f, hfW⟩ : mhs.WC k) :
        weightGradedComplex mhs.WC k) = Submodule.Quotient.mk ⟨c, hcW⟩ :=
    (weightGradedComplex_mk_eq_mk_iff mhs.WC k _ _).2 hfc
  have hF := mhs.mk_mem_complexGradedHodgeStructure_F k p ⟨f, hfW⟩ hf
  have hConj := mhs.mk_mem_complexGradedHodgeStructure_conjF k (k + 1 - p) ⟨c, hcW⟩ hc
  rw [← hmk] at hConj
  have hzero := ((mhs.complexGradedHodgeStructure k).isCompl_F_conjF p).disjoint.le_bot
    ⟨hF, hConj⟩
  rw [Submodule.mem_bot] at hzero
  have hfLower : f ∈ mhs.WC (k - 1) :=
    (weightGradedComplex_mk_eq_zero_iff mhs.WC k ⟨f, hfW⟩).1 hzero
  rw [← hfw]
  exact Submodule.add_mem _ hfLower hwf

/-- Conjugating `I^{p,q}` lands in the swapped Deligne piece modulo `W_{p+q-2}`. -/
theorem map_latticeConj_deligneSplitting_le_sup_WC (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) ≤
      mhs.deligneSplitting q p ⊔ mhs.WC (p + q - 2) := by
  intro x hx
  rw [mhs.map_latticeConj_deligneSplitting p q] at hx
  obtain ⟨hxConj, hxW, hxSecond⟩ := by
    simpa only [Submodule.mem_inf, and_assoc] using hx
  obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hxSecond
  have htW : t ∈ mhs.WC (p + q - 2) := by
    exact (iSup_le fun j ↦ inf_le_right.trans (mhs.WC_monotone (by omega))) ht
  have haW : a ∈ mhs.WC (p + q) := ha.2
  have hxW' : x ∈ mhs.WC (p + q) := hxW
  have hclassA : Submodule.Quotient.mk (⟨a, haW⟩ : mhs.WC (p + q)) ∈
      (mhs.complexGradedHodgeStructure (p + q)).piece q := by
    refine mhs.mk_mem_complexGradedHodgeStructure_piece (p + q) q ⟨a, haW⟩ ha.1 ?_
    have hax : a = x - t := by rw [← hat]; abel
    have haConj : a ∈ mhs.conjF p ⊔ mhs.WC (p + q - 1) := by
      rw [hax]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxConj)
        (Submodule.mem_sup_right (mhs.WC_monotone (by omega) htW))
    have hindex : p + q - q = p := by ring
    simpa only [mhs.conjF_def, hindex] using haConj
  have hmap := mhs.map_deligneSplitting_eq_piece q p
  rw [add_comm q p] at hmap
  rw [← hmap] at hclassA
  obtain ⟨y, hyI, hyClass⟩ := hclassA
  have hyIAmbient : (y : Vℂ) ∈ mhs.deligneSplitting q p := hyI
  have hyW : (y : Vℂ) ∈ mhs.WC (p + q) := y.2
  have hyConj : (y : Vℂ) ∈ mhs.conjF p ⊔ mhs.WC (p + q - 2) := by
    have h := mhs.deligneSplitting_le_conjF_sup_WC q p hyIAmbient
    simpa only [add_comm q p] using h
  have hdiffW : x - (y : Vℂ) ∈ mhs.WC (p + q - 1) := by
    rw [Submodule.mkQ_apply] at hyClass
    have hxa : x - a = t := by rw [← hat]; abel
    have hxaW : x - a ∈ mhs.WC (p + q - 1) := by
      rw [hxa]
      exact mhs.WC_monotone (by omega) htW
    have hxy : (Submodule.Quotient.mk (⟨x, hxW'⟩ : mhs.WC (p + q)) :
          weightGradedComplex mhs.WC (p + q)) =
        Submodule.Quotient.mk ⟨(y : Vℂ), hyW⟩ := by
      have hxaClass : (Submodule.Quotient.mk (⟨x, hxW'⟩ : mhs.WC (p + q)) :
            weightGradedComplex mhs.WC (p + q)) = Submodule.Quotient.mk ⟨a, haW⟩ :=
        (weightGradedComplex_mk_eq_mk_iff mhs.WC (p + q) _ _).2 hxaW
      exact hxaClass.trans hyClass.symm
    exact (weightGradedComplex_mk_eq_mk_iff mhs.WC (p + q) ⟨x, hxW'⟩
      ⟨(y : Vℂ), hyW⟩).1 hxy
  have hdiffF : x - (y : Vℂ) ∈ mhs.F q ⊔ mhs.WC (p + q - 2) := by
    have hxmem : x ∈ mhs.F q ⊔ mhs.WC (p + q - 2) := by
      rw [← hat]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha.1) (Submodule.mem_sup_right htW)
    exact Submodule.sub_mem _ hxmem
      (Submodule.mem_sup_left (mhs.deligneSplitting_le_F q p hyIAmbient))
  have hdiffConj : x - (y : Vℂ) ∈ mhs.conjF p ⊔ mhs.WC (p + q - 2) :=
    Submodule.sub_mem _ (Submodule.mem_sup_left hxConj) hyConj
  have hdrop : x - (y : Vℂ) ∈ mhs.WC (p + q - 2) := by
    have hstep : p + q - 1 - 1 = p + q - 2 := by ring
    have hconjIndex : p + q - 1 + 1 - q = p := by ring
    simpa only [hstep] using mhs.mem_WC_sub_one_of_mem_F_sup_and_mem_conjF_sup
      (p + q - 1) q hdiffW (by simpa only [hstep] using hdiffF)
        (by simpa only [hstep, hconjIndex] using hdiffConj)
  convert Submodule.add_mem_sup hyIAmbient hdrop using 1
  all_goals abel

/-- The swapped Deligne piece lands in the conjugate of `I^{p,q}` modulo `W_{p+q-2}`.

This is the reverse containment to
`TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_le_sup_WC`. It follows by
applying that containment with the indices exchanged and conjugating once more. -/
theorem deligneSplitting_le_map_latticeConj_sup_WC (p q : ℤ) :
    mhs.deligneSplitting q p ≤
      (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔ mhs.WC (p + q - 2) := by
  intro x hx
  have hxMap : latticeConj hℂ x ∈ (mhs.deligneSplitting q p).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem hx
  have hswap := mhs.map_latticeConj_deligneSplitting_le_sup_WC q p hxMap
  have h : latticeConj hℂ x ∈ mhs.deligneSplitting p q ⊔ mhs.WC (p + q - 2) := by
    simpa only [add_comm q p] using hswap
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  have hconjA : latticeConj hℂ a ∈
      (mhs.deligneSplitting p q).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem ha
  have hconjB : latticeConj hℂ b ∈ mhs.WC (p + q - 2) := by
    rw [← mhs.WC_conj (p + q - 2)]
    exact Submodule.mem_map_of_mem hb
  have hsum : latticeConj hℂ a + latticeConj hℂ b = x := by
    rw [← map_add, hab, latticeConj_apply_apply]
  rw [← hsum]
  exact Submodule.add_mem_sup hconjA hconjB

/-- **Conjugation exchanges Deligne's bigrading modulo two lower weight steps:**

`conj I^{p,q} + W_{p+q-2} = I^{q,p} + W_{p+q-2}`.

The two containments are symmetric because lattice conjugation is an involution and preserves the
weight filtration. -/
theorem map_latticeConj_deligneSplitting_sup_WC (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔ mhs.WC (p + q - 2) =
      mhs.deligneSplitting q p ⊔ mhs.WC (p + q - 2) := by
  apply le_antisymm
  · exact sup_le (mhs.map_latticeConj_deligneSplitting_le_sup_WC p q) le_sup_right
  · exact sup_le (mhs.deligneSplitting_le_map_latticeConj_sup_WC p q) le_sup_right

/-- If the weight filtration already vanishes two steps below `p+q`, conjugation exchanges the
Deligne pieces `I^{p,q}` and `I^{q,p}` exactly. -/
theorem map_latticeConj_deligneSplitting_eq_of_WC_eq_bot {p q : ℤ}
    (hW : mhs.WC (p + q - 2) = ⊥) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) = mhs.deligneSplitting q p := by
  simpa only [hW, sup_bot_eq] using mhs.map_latticeConj_deligneSplitting_sup_WC p q

/-- The images of `conj I^{p,q}` and `I^{q,p}` in the quotient by `W_{p+q-2}` agree. -/
theorem map_mkQ_map_latticeConj_deligneSplitting_eq (p q : ℤ) :
    ((mhs.deligneSplitting p q).map (latticeConj hℂ)).map
        (mhs.WC (p + q - 2)).mkQ =
      (mhs.deligneSplitting q p).map (mhs.WC (p + q - 2)).mkQ := by
  apply Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ]
  simpa only [sup_comm] using mhs.map_latticeConj_deligneSplitting_sup_WC p q

/-- Elementwise form of conjugation symmetry modulo `W_{p+q-2}`: every vector in `I^{p,q}` has
a conjugate congruent to a vector in `I^{q,p}`. -/
theorem exists_mem_deligneSplitting_smodEq_latticeConj (p q : ℤ) {x : Vℂ}
    (hx : x ∈ mhs.deligneSplitting p q) :
    ∃ y ∈ mhs.deligneSplitting q p,
      latticeConj hℂ x ≡ y [SMOD (mhs.WC (p + q - 2))] := by
  have hxMap : latticeConj hℂ x ∈
      (mhs.deligneSplitting p q).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem hx
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Submodule.mem_sup.1 (mhs.map_latticeConj_deligneSplitting_le_sup_WC p q hxMap)
  refine ⟨y, hy, SModEq.sub_mem.2 ?_⟩
  have hdiff : latticeConj hℂ x - y = z := by rw [← hyz]; abel
  rwa [hdiff]

/-! ### The fine lower-bidegree relation -/

private abbrev FineConjugationAt (p q : ℤ) : Prop :=
  (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔
      mhs.deligneSplittingBelow q p =
    mhs.deligneSplitting q p ⊔ mhs.deligneSplittingBelow q p

/-- Conjugating the Hodge-filtration tail in Deligne's formula replaces `F` by `conj F`. -/
private theorem map_hodgeTail (p q : ℤ) :
    (mhs.hodgeTail p q).map (latticeConj hℂ) =
      ⨆ j : ℕ, mhs.conjF (q - (j : ℤ) - 1) ⊓
        mhs.WC (p + q - (j : ℤ) - 2) := by
  have hinj : Function.Injective (latticeConj hℂ) := (latticeConj_involutive hℂ).injective
  simp only [hodgeTail, Submodule.map_iSup, Submodule.map_inf _ hinj, ← conjF_def, WC_conj]

/-- If the fine conjugation relation is known in every smaller total degree, conjugation exchanges
the corresponding lower-bidegree sums. -/
private theorem map_deligneSplittingBelow_eq_of_fine (p q : ℤ)
    (ih : ∀ r s : ℤ, r + s < p + q → mhs.FineConjugationAt r s) :
    (mhs.deligneSplittingBelow p q).map (latticeConj hℂ) =
      mhs.deligneSplittingBelow q p := by
  have hforward : ∀ a b : ℤ, a + b = p + q →
      (mhs.deligneSplittingBelow a b).map (latticeConj hℂ) ≤
        mhs.deligneSplittingBelow b a := by
    intro a b hab
    simp only [deligneSplittingBelow, Submodule.map_iSup]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    calc
      (mhs.deligneSplitting r s).map (latticeConj hℂ) ≤
          (mhs.deligneSplitting r s).map (latticeConj hℂ) ⊔
            mhs.deligneSplittingBelow s r := le_sup_left
      _ = mhs.deligneSplitting s r ⊔
            mhs.deligneSplittingBelow s r := ih r s (by omega)
      _ ≤ mhs.deligneSplittingBelow b a := sup_le
        (le_iSup₂_of_le s hs (le_iSup₂_of_le r hr le_rfl))
        (mhs.deligneSplittingBelow_mono hs.le hr.le)
  refine le_antisymm (hforward p q rfl) ?_
  have hmap :
      ((mhs.deligneSplittingBelow q p).map (latticeConj hℂ)).map (latticeConj hℂ) ≤
        (mhs.deligneSplittingBelow p q).map (latticeConj hℂ) :=
    Submodule.map_mono (hforward q p (by omega))
  simpa only [← latticeConjugation_toLinearMap, Conjugation.map_map_eq_self] using hmap

/-- Under the fine relation in smaller total degree, the conjugate-filtration tail is saturated by
the same lower-bidegree sum as the Hodge-filtration tail. -/
private theorem inf_sup_conjTail_eq_inf_sup_deligneSplittingBelow (p q : ℤ)
    (ih : ∀ r s : ℤ, r + s < p + q → mhs.FineConjugationAt r s) :
    (mhs.conjF p ⊓ mhs.WC (p + q)) ⊔
        (⨆ j : ℕ, mhs.conjF (p - (j : ℤ) - 1) ⊓
          mhs.WC (p + q - (j : ℤ) - 2)) =
      (mhs.conjF p ⊓ mhs.WC (p + q)) ⊔ mhs.deligneSplittingBelow q p := by
  have hinj : Function.Injective (latticeConj hℂ) := (latticeConj_involutive hℂ).injective
  have h := congrArg (Submodule.map (latticeConj hℂ))
    (mhs.inf_sup_hodgeTail_eq_inf_sup_deligneSplittingBelow q p)
  have hbelow := mhs.map_deligneSplittingBelow_eq_of_fine p q ih
  simpa only [Submodule.map_sup, Submodule.map_inf _ hinj, ← conjF_def, WC_conj,
    mhs.map_hodgeTail, add_comm p q, hbelow] using h

/-- The fine conjugation relation in a given bidegree follows from the relation in all smaller
total degrees. Deligne's two tails become the same lower-bidegree sum, and the remaining equality
is the modular law for subspaces. -/
private theorem map_latticeConj_deligneSplitting_sup_below_of_lower (p q : ℤ)
    (ih : ∀ r s : ℤ, r + s < p + q → mhs.FineConjugationAt r s) :
    mhs.FineConjugationAt p q := by
  unfold FineConjugationAt
  rw [mhs.map_latticeConj_deligneSplitting p q, mhs.deligneSplitting_def q p]
  rw [add_comm q p]
  -- Fold the explicit first tail back to `hodgeTail`; the two saturation lemmas are stated
  -- against that name, while the second tail deliberately remains visible for its conjugate form.
  change
    ((mhs.conjF p ⊓ mhs.WC (p + q)) ⊓
        ((mhs.F q ⊓ mhs.WC (p + q)) ⊔ mhs.hodgeTail p q)) ⊔
          mhs.deligneSplittingBelow q p =
      ((mhs.F q ⊓ mhs.WC (p + q)) ⊓
        ((mhs.conjF p ⊓ mhs.WC (p + q)) ⊔
          (⨆ j : ℕ, mhs.conjF (p - (j : ℤ) - 1) ⊓
            mhs.WC (p + q - (j : ℤ) - 2)))) ⊔ mhs.deligneSplittingBelow q p
  rw [mhs.inf_sup_hodgeTail_eq_inf_sup_deligneSplittingBelow p q,
    mhs.inf_sup_conjTail_eq_inf_sup_deligneSplittingBelow p q ih]
  let C := mhs.conjF p ⊓ mhs.WC (p + q)
  let F := mhs.F q ⊓ mhs.WC (p + q)
  let E := mhs.deligneSplittingBelow q p
  change (C ⊓ (F ⊔ E)) ⊔ E = (F ⊓ (C ⊔ E)) ⊔ E
  calc
    (C ⊓ (F ⊔ E)) ⊔ E = E ⊔ (C ⊓ (F ⊔ E)) := sup_comm _ _
    _ = (E ⊔ C) ⊓ (F ⊔ E) := (sup_inf_assoc_of_le C le_sup_right).symm
    _ = (E ⊔ F) ⊓ (C ⊔ E) := by ac_rfl
    _ = E ⊔ (F ⊓ (C ⊔ E)) := sup_inf_assoc_of_le F le_sup_right
    _ = (F ⊓ (C ⊔ E)) ⊔ E := sup_comm _ _

/-- **Deligne's fine conjugation relation.** Conjugation exchanges `I^{p,q}` and `I^{q,p}`
modulo the sum of the components `I^{r,s}` with `r < q` and `s < p`. -/
theorem map_latticeConj_deligneSplitting_sup_below (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔
        mhs.deligneSplittingBelow q p =
      mhs.deligneSplitting q p ⊔ mhs.deligneSplittingBelow q p := by
  obtain ⟨k₀, hk₀⟩ := mhs.WC_bot
  have key : ∀ k : ℤ, k₀ ≤ k → ∀ p q : ℤ, p + q ≤ k →
      mhs.FineConjugationAt p q := by
    refine Int.leInduction ?_ ?_
    · intro p q hpq
      unfold FineConjugationAt
      have hpq' : q + p ≤ k₀ := by omega
      have hI := mhs.deligneSplitting_eq_bot_of_WC_eq_bot hk₀ hpq
      have hIswap := mhs.deligneSplitting_eq_bot_of_WC_eq_bot hk₀ hpq'
      have hbelow : mhs.deligneSplittingBelow q p = ⊥ := le_bot_iff.1
        ((mhs.deligneSplittingBelow_le_WC q p).trans
          ((mhs.WC_monotone (by omega)).trans_eq hk₀))
      simp only [hI, hIswap, hbelow, Submodule.map_bot, sup_bot_eq]
    · intro k hk₀k ih p q hpq
      rcases lt_or_eq_of_le hpq with hpq' | hpq'
      · exact ih p q (by omega)
      · exact mhs.map_latticeConj_deligneSplitting_sup_below_of_lower p q
          (fun r s hrs ↦ ih r s (by omega))
  exact key (max k₀ (p + q)) (le_max_left _ _) p q (le_max_right _ _)

/-- Elementwise form of Deligne's fine conjugation relation. -/
theorem exists_mem_deligneSplitting_smodEq_latticeConj_below (p q : ℤ) {x : Vℂ}
    (hx : x ∈ mhs.deligneSplitting p q) :
    ∃ y ∈ mhs.deligneSplitting q p,
      latticeConj hℂ x ≡ y [SMOD (mhs.deligneSplittingBelow q p)] := by
  have hxMap : latticeConj hℂ x ∈
      (mhs.deligneSplitting p q).map (latticeConj hℂ) := Submodule.mem_map_of_mem hx
  have hxSup : latticeConj hℂ x ∈
      mhs.deligneSplitting q p ⊔ mhs.deligneSplittingBelow q p := by
    rw [← mhs.map_latticeConj_deligneSplitting_sup_below p q]
    exact Submodule.mem_sup_left hxMap
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
    hxSup
  refine ⟨y, hy, SModEq.sub_mem.2 ?_⟩
  have hdiff : latticeConj hℂ x - y = z := by rw [← hyz]; abel
  rwa [hdiff]

end MixedHodgeStructure

end TauCeti.Hodge
