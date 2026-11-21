/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Homology.SpectralObject.Abutment

/-!
# The spectral sequence of a homological functor on a t-structure

Let `t` be a t-structure on a triangulated category `C`, let `X` be an object of `C` and let
`H : C ⥤ A` be a homological functor to an abelian category, with its shift sequence
`n ↦ H.shift n`, `(H.shift n).obj Y ≅ H.obj (Y⟦n⟧)` (`H.isoShift n`). The truncations of `X`
form Mathlib's spectral object `t.spectralObject X` in `C`, and applying `H` gives the spectral
object `(t.spectralObject X).mapHomologicalFunctor H` in `A`, whose value `H^n(a ≤ b)` is
`(H.shift n).obj (τ_{≥a} τ_{<b} X)`. Its abutment is `H^n(⊥ ≤ ⊤) ≅ (H.shift n).obj X`
(`abutmentMapHomologicalFunctorSpectralObjectIso`), because `τ_{≥⊥} τ_{<⊤}` is the identity
(`ω₁_obj_bot_top`), and the objects of the first page of its `E₂` spectral sequence are the
values `(H.shift (p + q)).obj (τ_{≥q} τ_{<q+1} X)` of `H` on the `t`-cohomology objects of `X`.
For the canonical t-structure on a derived category this is the hypercohomology spectral
sequence `E₂^{p,q} = Hᵖ(Hᵠ(X)) ⇒ H^{p+q}(X)` (see
`TauCeti.Algebra.Homology.DerivedCategory.SpectralObject`); applied to the derived pushforward
`X = Rf_* F` of a sheaf and to the represented functor `Hom(Z, -)` with `Z` the constant sheaf
`ℤ` placed in degree `0`, which computes global sections, it gives the Leray spectral sequence.

The spectral object is first quadrant in the sense of Mathlib's `IsFirstQuadrant`
(`isFirstQuadrant_mapHomologicalFunctor_spectralObject`) as soon as `X` is `≥ 0` and `H` vanishes
on the objects `≥ 1`: then `τ_{<b} X = 0` for `b ≤ 0`, and
`(H.shift n).obj (τ_{≥a} Y) ≅ H.obj ((τ_{≥a} Y)⟦n⟧)` vanishes for `n < a`
(`isZero_shift_obj_of_isGE`, which more generally allows `H` vanishing on the objects `≥ b` and
`n + b ≤ a`). The filtration of its abutment is then finite in each degree, with
`F_q H^n = 0` for `q ≤ 0` and `F_q H^n = H^n` for `q > n` (Tau Ceti's
`CategoryTheory.Abelian.SpectralObject.isZero_abutmentFiltration` and
`CategoryTheory.Abelian.SpectralObject.isIso_abutmentFiltrationι`), and the pages stabilize to
its graded pieces (`CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoEInfty`). The
vanishing condition holds for the represented functor `H = Hom(Z, -)` when `Z` is `≤ 0`, since
`Hom(Z, -)` vanishes on the objects `≥ q` when `Z` is `≤ p` for some `p < q`
(`isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE`), and the spectral object is then first
quadrant by an instance.

## Main results

* `CategoryTheory.Triangulated.TStructure.isZero_shift_obj_of_isGE`: a functor vanishing on the
  objects `≥ b` has `H.shift n` vanishing on the objects `≥ a` for `n + b ≤ a`.
* `CategoryTheory.Triangulated.TStructure.isFirstQuadrant_mapHomologicalFunctor_spectralObject`:
  the spectral object of `X ≥ 0` under a homological functor vanishing on the objects `≥ 1` is
  first quadrant.
* `CategoryTheory.Triangulated.TStructure.abutmentMapHomologicalFunctorSpectralObjectIso`: its
  abutment is `(H.shift n).obj X`.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
* [The Stacks Project, Section 21.14](https://stacks.math.columbia.edu/tag/072X), for the Leray
  spectral sequence.
-/

public section

namespace CategoryTheory.Triangulated.TStructure

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- If a functor `H` with a shift sequence vanishes on the objects `≥ b` of a t-structure, its
shift `H.shift n` vanishes on the objects `≥ a` for `n + b ≤ a`. -/
lemma isZero_shift_obj_of_isGE {A : Type*} [Category* A] (H : C ⥤ A) [H.ShiftSequence ℤ] {b : ℤ}
    (hH : ∀ Y : C, t.IsGE Y b → IsZero (H.obj Y)) (Y : C) {n a : ℤ} (hna : n + b ≤ a)
    [t.IsGE Y a] : IsZero ((H.shift n).obj Y) :=
  have := t.isGE_of_ge Y (n + b) a
  (hH _ (t.isGE_shift Y (n + b) n b)).of_iso ((H.isoShift n).app Y).symm

/-- The functor `Hom(Z, -)` vanishes on the objects `≥ q` when `Z` is `≤ p` for some `p < q`. -/
lemma isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE (Z Y : C) {p q : ℤ} (hpq : p < q)
    [t.IsLE Z p] [t.IsGE Y q] : IsZero ((preadditiveCoyoneda.obj (Opposite.op Z)).obj Y) :=
  have : Subsingleton (Z ⟶ Y) := ⟨fun f g ↦ (t.zero f p q).trans (t.zero g p q).symm⟩
  @AddCommGrpCat.isZero_of_subsingleton _ this

/-- The truncation functor `τ_{≥⊥} τ_{<⊤}` of the whole interval `⊥ ≤ ⊤` is the identity. -/
lemma ω₁_obj_bot_top :
    t.ω₁.obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) = 𝟭 C := by
  simp [eTruncLT_obj_top, eTruncGE_obj_bot, Functor.id_comp]

variable [IsTriangulated C] {A : Type*} [Category* A] [Abelian A] (H : C ⥤ A) [H.IsHomological]
  [H.ShiftSequence ℤ]

/-- The spectral object of the truncations of an object `X ≥ 0` under a homological functor
vanishing on the objects `≥ 1` is first quadrant. -/
lemma isFirstQuadrant_mapHomologicalFunctor_spectralObject
    (hH : ∀ Y : C, t.IsGE Y 1 → IsZero (H.obj Y)) (X : C) [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsFirstQuadrant where
  isZero₁ i j hij hj n :=
    (H.shift n).map_isZero ((t.eTruncGE.obj i).map_isZero (t.isZero_eTruncLT_obj_obj X 0 j hj))
  isZero₂ i j hij n hi := by
    induction i using WithBotTop.rec with
    | bot => simp at hi
    | coe a =>
      have : t.IsGE ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj j).obj X)) a :=
        t.isGE_eTruncGE_obj_obj a a le_rfl _
      exact t.isZero_shift_obj_of_isGE H hH ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj j).obj X))
        (by simp at hi; lia : n + 1 ≤ a)
    | top => exact (H.shift n).map_isZero (Functor.zero_obj _)

/-- The spectral object of the truncations of an object `X ≥ 0` under the functor `Hom(Z, -)`,
for `Z ≤ 0`, is first quadrant. -/
instance (Z X : C) [t.IsLE Z 0] [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor
      (preadditiveCoyoneda.obj (Opposite.op Z))).IsFirstQuadrant :=
  t.isFirstQuadrant_mapHomologicalFunctor_spectralObject _
    (fun Y (_ : t.IsGE Y 1) ↦ t.isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE Z Y zero_lt_one) X

/-- The abutment `H^n(⊥ ≤ ⊤)` of the spectral object of the truncations of `X` under a
homological functor `H` is `(H.shift n).obj X`: the truncations `τ_{<⊤}` and `τ_{≥⊥}` are the
identity (`ω₁_obj_bot_top`). -/
noncomputable def abutmentMapHomologicalFunctorSpectralObjectIso (X : C) (n : ℤ) :
    ((t.spectralObject X).mapHomologicalFunctor H).abutment n ≅ (H.shift n).obj X :=
  (H.shift n).mapIso (eqToIso (Functor.congr_obj t.ω₁_obj_bot_top X))

end CategoryTheory.Triangulated.TStructure
