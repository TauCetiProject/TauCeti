/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.Order.SupClosed

/-!
# Mayer–Vietoris induction on quasi-compact quasi-separated opens

A property of scheme opens holds on every quasi-compact quasi-separated open if it holds on
affine opens and passes from two quasi-compact opens and their intersection to their union.
Only the open under consideration needs to be quasi-separated; the ambient scheme need not be.

This form of induction applies to cohomological properties propagated by a Mayer–Vietoris
sequence. Intersections of affine opens need not be affine, so the proof first handles
quasi-compact subopens of a single affine open.

## References

* Stacks Project, [Section 30.4, tag 01XH](https://stacks.math.columbia.edu/tag/01XH).
  The two-stage induction is extracted from the cohomology localization proof in
  `TauCeti.AlgebraicGeometry.Cohomology.Localization`.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Opens

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
      (f : ι → Γ(X, V)) : P (s.sup fun i ↦ X.basicOpen (f i)) := by
    let Q (W : X.Opens) := W ≤ V ∧ IsCompact (W : Set X) ∧ P W
    have hQ : Q ((s.image fun i ↦ X.basicOpen (f i)).sup id) := by
      apply TauCeti.finset_sup_of_inf_closed Q
        (fun _ hU _ hW ↦ Scheme.inf_mem_range_basicOpen _ hU _ hW)
      · exact ⟨bot_le, isCompact_empty, h_aff _ (isAffineOpen_bot X)⟩
      · rintro _ ⟨g, rfl⟩
        exact ⟨X.basicOpen_le g, (hV.basicOpen g).isCompact, h_aff _ (hV.basicOpen g)⟩
      · intro W Z hW hZ hWZ
        exact ⟨sup_le hW.1 hZ.1, hW.2.1.union hZ.2.1,
          h_sup W Z hW.2.1 hZ.2.1 (hV.isQuasiSeparated.of_subset (sup_le hW.1 hZ.1))
            hW.2.2 hZ.2.2 hWZ.2.2⟩
      · intro W hW
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
        exact ⟨f i, rfl⟩
    simpa only [Q, Finset.sup_image, Function.comp_def, id_eq] using hQ.2.2
  have hcpt {V : X.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hWV : W ≤ V)
      (hW : IsCompact (W : Set X)) : P W := by
    obtain ⟨s, hsW⟩ := hV.exists_finset_sup_basicOpen_eq hW hWV
    rw [← hsW]
    exact hfin hV s fun i ↦ i.1
  revert hU'
  refine compact_open_induction_on
    (P := fun V ↦ IsQuasiSeparated (V : Set X) → P V) U hU
    (fun _ ↦ h_aff _ (isAffineOpen_bot X)) ?_
  intro V hV W ih hVW
  refine h_sup V W hV W.2.isCompact hVW
    (ih (hVW.of_subset Set.subset_union_left)) (h_aff _ W.2) (hcpt W.2 inf_le_right ?_)
  exact hVW _ _ Set.subset_union_left V.isOpen hV
    Set.subset_union_right W.1.isOpen W.2.isCompact

end AlgebraicGeometry.Scheme.Opens
