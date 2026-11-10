/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Mayer–Vietoris induction on quasi-compact quasi-separated opens

A property of scheme opens holds on every quasi-compact quasi-separated open if it holds on
affine opens and passes from two quasi-compact opens and their intersection to their union.
Only the open under consideration needs to be quasi-separated; the ambient scheme need not be.

This form of induction applies to cohomological properties propagated by a Mayer–Vietoris
sequence. Intersections of affine opens need not be affine, so the proof first handles
quasi-compact subopens of a single affine open.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- To prove a property on a quasi-compact quasi-separated open, it suffices to prove it on
affine opens and to propagate it from two quasi-compact opens and their intersection to their
quasi-separated union. -/
@[elab_as_elim]
theorem induction_on_isCompact_isQuasiSeparated {X : Scheme.{u}} {P : X.Opens → Prop}
    (U : X.Opens) (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (h_aff : ∀ V, IsAffineOpen V → P V)
    (h_sup : ∀ (V W : X.Opens), IsCompact (V : Set X) → IsCompact (W : Set X) →
      IsQuasiSeparated (V ⊔ W : Set X) → P V → P W → P (V ⊓ W) → P (V ⊔ W)) : P U := by
  classical
  have hfin {V : X.Opens} (hV : IsAffineOpen V) {ι : Type u} (s : Finset ι)
      (f : ι → Γ(X, V)) :
      IsCompact ((s.sup fun i ↦ X.basicOpen (f i) : X.Opens) : Set X) ∧
        P (s.sup fun i ↦ X.basicOpen (f i)) := by
    induction s using Finset.induction_on generalizing f with
    | empty => exact ⟨isCompact_empty, h_aff _ (isAffineOpen_bot X)⟩
    | insert a s _ ih =>
      rw [Finset.sup_insert]
      obtain ⟨hc, hs⟩ := ih f
      have ha := hV.basicOpen (f a)
      refine ⟨ha.isCompact.union hc,
        h_sup _ _ ha.isCompact hc (hV.isQuasiSeparated.of_subset ?_)
          (h_aff _ ha) hs ?_⟩
      · exact sup_le (X.basicOpen_le _) (Finset.sup_le fun i _ ↦ X.basicOpen_le _)
      · rw [Finset.sup_inf_distrib_left]
        simpa only [Scheme.basicOpen_mul] using (ih fun i ↦ f a * f i).2
  have hcpt {V : X.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hWV : W ≤ V)
      (hW : IsCompact (W : Set X)) : P W := by
    obtain ⟨s, hsW⟩ := hV.exists_finset_sup_basicOpen_eq hW hWV
    rw [← hsW]
    exact (hfin hV s fun i ↦ i.1).2
  revert hU'
  refine compact_open_induction_on
    (P := fun V ↦ IsQuasiSeparated (V : Set X) → P V) U hU
    (fun _ ↦ h_aff _ (isAffineOpen_bot X)) ?_
  intro V hV W ih hVW
  refine h_sup V W hV W.2.isCompact hVW
    (ih (hVW.of_subset Set.subset_union_left)) (h_aff _ W.2) (hcpt W.2 inf_le_right ?_)
  exact hVW _ _ Set.subset_union_left V.isOpen hV
    Set.subset_union_right W.1.isOpen W.2.isCompact

end AlgebraicGeometry.Scheme
