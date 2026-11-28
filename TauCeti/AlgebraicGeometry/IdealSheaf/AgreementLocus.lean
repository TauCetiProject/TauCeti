/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.IdealSheaf.WeilRestriction

/-!
# Agreement of morphisms out of a finite locally free family

For a finite locally free morphism `g : X ⟶ S`, the condition that two maps from `X` to a
separated target agree on the whole family is represented by a closed subscheme of `S`.
The ideal `Scheme.Hom.agreementLocus` is obtained by pulling back Mathlib's relative diagonal
`pullback.diagonal` along the pair of maps and applying Tau Ceti's
`Scheme.IdealSheafData.weilRestriction`. The criterion
`Scheme.Hom.agreementLocus_le_ker_iff` tests equality of morphisms after pulling back the
family, not just equality on points. The theorem
`Scheme.Hom.existsUnique_agreementLocus_subschemeι_iff` gives the unique factorization through the
closed locus. Its defining ideal commutes with arbitrary base change by
`Scheme.Hom.comap_agreementLocus`.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §7.6, for Weil restriction.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y S B : Scheme.{u}} (g : X ⟶ S)
  [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
  {p : Y ⟶ B} {a b : X ⟶ Y} (h : a ≫ p = b ≫ p)

/-- The ideal on `S` obtained by Weil restriction of the inverse image of the diagonal of
`p` along the pair `(a, b)`. If `p` is separated, its closed subscheme represents agreement
of the two maps on the base change of the finite locally free family `g`. -/
noncomputable def agreementLocus : S.IdealSheafData :=
  ((pullback.diagonal p).ker.comap (pullback.lift a b h)).weilRestriction g

/-- The agreement ideal is the Weil restriction of the inverse image of the diagonal ideal. -/
theorem agreementLocus_eq_weilRestriction :
    g.agreementLocus h =
      ((pullback.diagonal p).ker.comap (pullback.lift a b h)).weilRestriction g :=
  (rfl)

variable {g} in
/-- In any pullback square for the finite locally free family, the base map factors through the
agreement locus exactly when the maps to the separated target agree on the pulled-back family.

This lemma is not `@[simp]` because the pullback witness is not in its conclusion. The canonical
pullback variant `Scheme.Hom.agreementLocus_le_ker_iff` is a simp lemma. -/
theorem _root_.CategoryTheory.IsPullback.agreementLocus_le_ker_iff [IsSeparated p]
    {T X' : Scheme.{u}} {t : T ⟶ S} {g' : X' ⟶ T} {i : X' ⟶ X}
    (H : IsPullback g' i t g) (h : a ≫ p = b ≫ p) :
    g.agreementLocus h ≤ t.ker ↔ i ≫ a = i ≫ b := by
  rw [g.agreementLocus_eq_weilRestriction h, IdealSheafData.weilRestriction_le_ker_iff_of_isPullback
    _ H, ← IdealSheafData.le_map_iff_comap_le, IdealSheafData.map_ker]
  refine ⟨fun hk ↦ ?_, fun he ↦ ?_⟩
  · let l := IsClosedImmersion.lift (pullback.diagonal p) (i ≫ pullback.lift a b h) hk
    have hl : l ≫ pullback.diagonal p = i ≫ pullback.lift a b h :=
      IsClosedImmersion.lift_fac _ _ _
    calc
      i ≫ a = l := by
        simpa only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
          using (congrArg (fun k ↦ k ≫ pullback.fst p p) hl).symm
      _ = i ≫ b := by
        simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
          using congrArg (fun k ↦ k ≫ pullback.snd p p) hl
  · have heq : i ≫ pullback.lift a b h = (i ≫ a) ≫ pullback.diagonal p := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, he]
    rw [heq]
    exact (i ≫ a).le_ker_comp _

variable {g} in
/-- A morphism `t : T ⟶ S` factors through the agreement locus exactly when the two maps to
the separated target agree on the pullback of the finite locally free family to `T`. -/
@[simp]
theorem agreementLocus_le_ker_iff [IsSeparated p] {T : Scheme.{u}} {t : T ⟶ S} :
    g.agreementLocus h ≤ t.ker ↔ pullback.snd t g ≫ a = pullback.snd t g ≫ b :=
  (IsPullback.of_hasPullback t g).agreementLocus_le_ker_iff h

variable {g} in
/-- Agreement on the pulled-back family is represented by the closed subscheme of
`g.agreementLocus h`: a map from the test scheme to the base factors uniquely through it. -/
@[simp]
theorem existsUnique_agreementLocus_subschemeι_iff [IsSeparated p] {T : Scheme.{u}} {t : T ⟶ S} :
    (∃! u : T ⟶ (g.agreementLocus h).subscheme, u ≫ (g.agreementLocus h).subschemeι = t) ↔
      pullback.snd t g ≫ a = pullback.snd t g ≫ b := by
  rw [← agreementLocus_le_ker_iff (g := g) (t := t) h]
  let I := g.agreementLocus h
  have hk : I.subschemeι.ker = I := I.ker_subschemeι
  constructor
  · intro hfactor
    obtain ⟨u, hu⟩ := hfactor.exists
    exact hk.ge.trans (hu ▸ u.le_ker_comp I.subschemeι)
  · intro ht
    let u := IsClosedImmersion.lift I.subschemeι t (hk.le.trans ht)
    have hu : u ≫ I.subschemeι = t := IsClosedImmersion.lift_fac _ _ _
    exact ExistsUnique.intro u hu fun v hv ↦ (cancel_mono I.subschemeι).mp (hv.trans hu.symm)

/-- The agreement ideal is zero precisely when the two maps agree before base change. -/
@[simp]
theorem agreementLocus_eq_bot_iff [IsSeparated p] : g.agreementLocus h = ⊥ ↔ a = b := by
  simpa only [← le_bot_iff, Scheme.Hom.ker_eq_bot_of_isIso, Category.id_comp] using
    (IsPullback.id_horiz g |>.flip).agreementLocus_le_ker_iff h

/-- After pulling back the finite locally free family along `t`, the agreement ideal of the
precomposed maps is the inverse image of the original agreement ideal. -/
theorem comap_agreementLocus {T : Scheme.{u}} (t : T ⟶ S) :
    (g.agreementLocus h).comap t =
      (pullback.fst t g).agreementLocus
        (p := p) (a := pullback.snd t g ≫ a) (b := pullback.snd t g ≫ b)
        (by simp only [Category.assoc, h]) := by
  rw [agreementLocus_eq_weilRestriction, agreementLocus_eq_weilRestriction,
    ← IdealSheafData.weilRestriction_comap, ← IdealSheafData.comap_comp]
  congr 2
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

end AlgebraicGeometry.Scheme.Hom
