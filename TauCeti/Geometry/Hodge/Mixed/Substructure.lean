/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Strictness
import TauCeti.Algebra.DirectSum.Internal

/-!
# Sub-mixed Hodge structures

A rational subspace of the ambient space of a mixed Hodge structure is a **sub-mixed Hodge
structure** when its complexification is spanned by its intersections with the pieces `I^{p,q}` of
Deligne's bigrading. This is the mixed counterpart of the condition defining
`TauCeti.Hodge.HodgeStructureOn.IsSubstructure` in the pure theory, where the Hodge components
take the place of the bigrading pieces; conjugation stability, a separate requirement there, is
automatic here because the subspace is rational.

The condition is what makes the *intersection* filtrations behave: since both filtrations of a
mixed Hodge structure are suprema of bigrading pieces over a set of bidegrees, intersecting either
of them with such a subspace gives the supremum of the corresponding pieces of the subspace
(`TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.WC_inf_eq_iSup_inf_deligneSplitting` and
`…F_inf_eq_iSup_inf_deligneSplitting`).

Sums and intersections of sub-mixed Hodge structures are again such. Examples are recorded: the
zero subspace and the whole space, the steps of the weight filtration,
and — this is the point — the kernel and the image of a morphism. For the kernel the
argument is that the complexified kernel is the kernel of the complexified map
(`TauCeti.Hodge.MixedHodgeStructure.Hom.ker_toLinearMap`), that the bigrading of the source spans
and that of the target is independent, so a vector killed by the map has each of its bigraded
parts killed as well. For the image it is that the image is the sum of the images of the
bigrading pieces, each of which already sits in the piece of the same bidegree.

Equipping such a subspace with the induced filtrations as a mixed Hodge structure in its own
right is not done here: `TauCeti.Hodge.MixedHodgeStructure` bundles base-change models for the
subspace, which have to be built first.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure`: a rational subspace whose complexification
  is spanned by its intersections with Deligne's bigrading.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.WC_inf_eq_iSup_inf_deligneSplitting` and
  `…F_inf_eq_iSup_inf_deligneSplitting`: the weight and Hodge steps traced on a sub-mixed Hodge
  structure are bigraded.
* `TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.sup` and `…inf`: sub-mixed Hodge structures
  are closed under sums and intersections.
* `TauCeti.Hodge.MixedHodgeStructure.isSubstructure_WQ`: the steps of the weight filtration are
  sub-mixed Hodge structures.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.isSubstructure_ker` and `…isSubstructure_range`: the
  kernel and the image of a morphism are sub-mixed Hodge structures.

## References

Deligne, *Théorie de Hodge II*, 1.2.10 and 2.3.5; Peters–Steenbrink, *Mixed Hodge Structures*,
Ch. 3, where the bigrading criterion is how subobjects of the mixed theory are recognised.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

namespace MixedHodgeStructure

section Substructure

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

/-- A **sub-mixed Hodge structure** of `mhs`: a rational subspace whose complexification is
spanned by its intersections with the pieces of Deligne's bigrading.

The reverse inequality holds for any rational subspace, so the single field is the whole of the
spanning condition; see
`TauCeti.Hodge.MixedHodgeStructure.IsSubstructure.eq_iSup_inf_deligneSplittingFamily`. -/
structure IsSubstructure (mhs : MixedHodgeStructure hℚ hℂ) (U : Submodule ℚ Vℚ) : Prop where
  /-- The complexification of the subspace is spanned by its intersections with the pieces of
  Deligne's bigrading. -/
  le_iSup_inf_deligneSplittingFamily :
    rationalToComplexSubmodule hℚ hℂ U ≤
      ⨆ pq : ℤ × ℤ, rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplittingFamily pq

variable {mhs : MixedHodgeStructure hℚ hℂ} {U U' : Submodule ℚ Vℚ}

namespace IsSubstructure

/-- The complexification of a sub-mixed Hodge structure is the sum of its intersections with the
pieces of Deligne's bigrading. -/
theorem eq_iSup_inf_deligneSplittingFamily (h : mhs.IsSubstructure U) :
    rationalToComplexSubmodule hℚ hℂ U =
      ⨆ pq : ℤ × ℤ, rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplittingFamily pq :=
  le_antisymm h.le_iSup_inf_deligneSplittingFamily (iSup_le fun _ ↦ inf_le_left)

/-- **A sum of bigrading pieces traces on a sub-mixed Hodge structure in the corresponding sum of
their traces.** Both filtrations of a mixed Hodge structure are such sums, so this carries the two
statements below. -/
theorem iSup₂_deligneSplittingFamily_inf (h : mhs.IsSubstructure U) (P : ℤ × ℤ → Prop) :
    (⨆ (pq : ℤ × ℤ) (_ : P pq), mhs.deligneSplittingFamily pq) ⊓
        rationalToComplexSubmodule hℚ hℂ U =
      ⨆ (pq : ℤ × ℤ) (_ : P pq),
        rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplittingFamily pq := by
  have key := TauCeti.iSupIndep.iSup₂_inf_iSup_eq_iSup₂
    (A := mhs.deligneSplittingFamily)
    (B := fun pq ↦ rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplittingFamily pq)
    mhs.iSupIndep_deligneSplittingFamily (fun _ ↦ inf_le_right) P
  rwa [← h.eq_iSup_inf_deligneSplittingFamily] at key

/-- **The weight filtration traced on a sub-mixed Hodge structure is bigraded**: its `k`-th step
is the sum of the traces of the bigrading pieces of total degree at most `k`. -/
theorem WC_inf_eq_iSup_inf_deligneSplitting (h : mhs.IsSubstructure U) (k : ℤ) :
    mhs.WC k ⊓ rationalToComplexSubmodule hℚ hℂ U =
      ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k),
        rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplitting pq.1 pq.2 := by
  simpa only [deligneSplittingFamily_apply, ← mhs.WC_eq_iSup_deligneSplitting k] using
    h.iSup₂_deligneSplittingFamily_inf fun pq ↦ pq.1 + pq.2 ≤ k

/-- **The Hodge filtration traced on a sub-mixed Hodge structure is bigraded**: its `p`-th step is
the sum of the traces of the bigrading pieces of first index at least `p`. -/
theorem F_inf_eq_iSup_inf_deligneSplitting (h : mhs.IsSubstructure U) (p : ℤ) :
    mhs.F p ⊓ rationalToComplexSubmodule hℚ hℂ U =
      ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1),
        rationalToComplexSubmodule hℚ hℂ U ⊓ mhs.deligneSplitting pq.1 pq.2 := by
  simpa only [deligneSplittingFamily_apply, ← mhs.F_eq_iSup_deligneSplitting p] using
    h.iSup₂_deligneSplittingFamily_inf fun pq ↦ p ≤ pq.1

/-- Sub-mixed Hodge structures are closed under sums. -/
theorem sup (h : mhs.IsSubstructure U) (h' : mhs.IsSubstructure U') :
    mhs.IsSubstructure (U ⊔ U') where
  le_iSup_inf_deligneSplittingFamily := by
    have hU : rationalToComplexSubmodule hℚ hℂ U ≤ rationalToComplexSubmodule hℚ hℂ (U ⊔ U') :=
      rationalToComplexSubmodule_mono hℚ hℂ le_sup_left
    have hU' : rationalToComplexSubmodule hℚ hℂ U' ≤ rationalToComplexSubmodule hℚ hℂ (U ⊔ U') :=
      rationalToComplexSubmodule_mono hℚ hℂ le_sup_right
    refine (rationalToComplexSubmodule_sup hℚ hℂ U U').le.trans (sup_le ?_ ?_)
    · exact h.le_iSup_inf_deligneSplittingFamily.trans
        (iSup_mono fun _ ↦ inf_le_inf_right _ hU)
    · exact h'.le_iSup_inf_deligneSplittingFamily.trans
        (iSup_mono fun _ ↦ inf_le_inf_right _ hU')

/-- Sub-mixed Hodge structures are closed under intersections. -/
theorem inf (h : mhs.IsSubstructure U) (h' : mhs.IsSubstructure U') :
    mhs.IsSubstructure (U ⊓ U') where
  le_iSup_inf_deligneSplittingFamily := by
    classical
    rw [rationalToComplexSubmodule_inf]
    rintro x ⟨hx, hx'⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1
      (h.le_iSup_inf_deligneSplittingFamily hx)
    obtain ⟨c, hc, hcb⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1
      (h'.le_iSup_inf_deligneSplittingFamily hx')
    have hbc : b = c := by
      have hsum : ∑ pq ∈ (b - c).support, (b - c) pq = 0 := by
        have := Finsupp.sum_sub_index (f := b) (g := c) (h := fun _ v ↦ v) fun _ _ _ ↦ rfl
        simp only [Finsupp.sum] at this hcb
        rw [this, hcb, sub_self]
      have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1
        mhs.iSupIndep_deligneSplittingFamily _ _
        (fun pq _ ↦ Submodule.sub_mem _ (hb pq).2 (hc pq).2) hsum
      rw [← sub_eq_zero, ← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
      exact fun pq hpq ↦ Finsupp.mem_support_iff.1 hpq (hzero pq hpq)
    subst hbc
    exact Submodule.sum_mem _ fun pq _ ↦
      Submodule.mem_iSup_of_mem pq ⟨⟨(hb pq).1, (hc pq).1⟩, (hb pq).2⟩

end IsSubstructure

/-- The zero subspace is a sub-mixed Hodge structure. -/
theorem isSubstructure_bot : mhs.IsSubstructure ⊥ where
  le_iSup_inf_deligneSplittingFamily := by simp

/-- The whole space is a sub-mixed Hodge structure: Deligne's bigrading spans. -/
theorem isSubstructure_top : mhs.IsSubstructure ⊤ where
  le_iSup_inf_deligneSplittingFamily := by
    simp only [rationalToComplexSubmodule_top, top_inf_eq]
    exact mhs.iSup_deligneSplittingFamily_eq_top.ge

/-- **Every step of the weight filtration is a sub-mixed Hodge structure**: it is the sum of the
bigrading pieces of total degree at most `k`, each of which it contains. -/
theorem isSubstructure_WQ (k : ℤ) : mhs.IsSubstructure (mhs.WQ k) where
  le_iSup_inf_deligneSplittingFamily := by
    rw [← WC_def mhs k]
    exact (mhs.WC_eq_iSup_deligneSplitting k).le.trans <| iSup₂_le fun rs hrs ↦
      le_iSup_of_le rs (le_inf ((mhs.deligneSplitting_le_WC rs.1 rs.2).trans
        (mhs.WC_monotone hrs)) (mhs.deligneSplittingFamily_apply rs).ge)

end Substructure

namespace Hom

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ} {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}

/-- **The kernel of a morphism of mixed Hodge structures is a sub-mixed Hodge structure.** -/
theorem isSubstructure_ker (f : Hom source target) :
    source.IsSubstructure (LinearMap.ker f.toRatLinearMap) where
  le_iSup_inf_deligneSplittingFamily := by
    rw [← f.ker_toLinearMap]
    exact (f.toLinearMap.ker_eq_iSup_inf_of_map_le source.iSup_deligneSplittingFamily_eq_top
      target.iSupIndep_deligneSplittingFamily fun pq ↦ by
        simpa only [deligneSplittingFamily_apply] using
          f.map_deligneSplitting_le pq.1 pq.2).le

/-- **The image of a morphism of mixed Hodge structures is a sub-mixed Hodge structure.** -/
theorem isSubstructure_range (f : Hom source target) :
    target.IsSubstructure (LinearMap.range f.toRatLinearMap) where
  le_iSup_inf_deligneSplittingFamily := by
    rw [← f.range_toLinearMap]
    conv_lhs => rw [f.range_eq_iSup_map_deligneSplittingFamily]
    refine iSup_le fun pq ↦ le_iSup_of_le pq (le_inf LinearMap.map_le_range ?_)
    simpa only [deligneSplittingFamily_apply] using f.map_deligneSplitting_le pq.1 pq.2

end Hom

end MixedHodgeStructure

end TauCeti.Hodge
