/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
public import TauCeti.CategoryTheory.Monoidal.Mod.Faithful
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.GrpObj
public import TauCeti.CategoryTheory.Sites.Over

/-!
# Torsors under a group scheme

Let `G` be a group scheme over a scheme `S`, that is, a group object of `Over S`. Its functor of
points is a sheaf of groups `h_G` on the big fppf site `(Sch/S)_fppf`, whose underlying category is
`Over S` with the topology `Scheme.fppfTopology.over S`. A scheme `X` over `S` with an action of
`G` is a `G`-torsor, `(Scheme.fppfTopology.over S).IsTorsor G X`, when `(g, x) ↦ (g • x, x)` is an
isomorphism `G ×_S X ≅ X ×_S X` and `X` has sections fppf-locally on `S`. Its functor of points is
then a torsor under `h_G` (`CategoryTheory.GrothendieckTopology.IsTorsor.toTorsor`), whose class
lies in `CategoryTheory.Sheaf.NonabelianH1` of the sheaf of points; with the sheaf of points
valued in groups of the universe `u + 1` these classes are functorial in `G`. The comparison
between geometric torsors and torsors of sheaves, which is fully faithful, is developed for an
arbitrary subcanonical site in `TauCeti.CategoryTheory.Sites.NonabelianCohomology.GrpObj`.

This file supplies the scheme-theoretic input. A pseudo-torsor `X` whose structure morphism is
flat, surjective and locally of finite presentation is a torsor: it trivialises over the fppf
covering `X ⟶ S` itself, along the tautological section. Conversely, the structure morphism of a
torsor inherits from that of `G` every property that is stable under base change and descends
along fppf coverings: over an fppf covering `Z ⟶ S` on which `X` has a section, `X ×_S Z` is
isomorphic to `G ×_S Z`. So for `G` flat and locally of finite presentation, the torsors are
exactly the pseudo-torsors which are flat, surjective and locally of finite presentation over `S`.
Torsors are stable under base change, a torsor is trivial exactly when its structure morphism has
a section, and the empty scheme over a nonempty base is never a torsor.

## Main declarations

* `TauCeti.GroupScheme.isTorsor_of_isIso_leftSMul`: a pseudo-torsor which is flat, surjective and
  locally of finite presentation over `S` is a torsor.
* `CategoryTheory.MorphismProperty.of_isTorsor`: a property of the structure morphism of `G`
  which is stable under base change and descends along fppf coverings passes to every `G`-torsor;
  in particular `flat_of_isTorsor`, `surjective_of_isTorsor` and
  `locallyOfFinitePresentation_of_isTorsor`.
* `TauCeti.GroupScheme.isTorsor_iff`: for `G` flat and locally of finite presentation, the
  torsors are the flat, surjective pseudo-torsors locally of finite presentation over `S`.
* `TauCeti.GroupScheme.isTorsor_pullback_obj`: the base change of a torsor is a torsor under the
  base change of `G`.
* `TauCeti.GroupScheme.mk_toTorsor_eq_one_iff`: a torsor has the trivial class if and only if its
  structure morphism has a section.
* `TauCeti.GroupScheme.not_isTorsor_of_isEmpty`: the empty scheme over a nonempty base is not a
  torsor.

## References

* [The Stacks project, Definition 78.9.3 (04TY)](https://stacks.math.columbia.edu/tag/04TY).
* B. Poonen, *Rational points on varieties*, Section 5.12 and Section 6.5.
-/

public section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped MonObj

universe w u

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}}

variable {G : Grp (Over S)} {X : Over S} [ModObj G.X X]

/-- A scheme `X` over `S` with an action of `G` for which `(g, x) ↦ (g • x, x)` is an isomorphism
`G ×_S X ≅ X ×_S X`, and whose structure morphism is flat, surjective and locally of finite
presentation, is a `G`-torsor for the fppf topology: it has a section over the fppf covering
`X ⟶ S`. -/
theorem isTorsor_of_isIso_leftSMul (h : IsIso (ModObj.leftSMul G.X X)) [Flat X.hom]
    [Surjective X.hom] [LocallyOfFinitePresentation X.hom] :
    (Scheme.fppfTopology.over S).IsTorsor G X where
  isIso_leftSMul := h
  coversTop := (Scheme.fppfTopology.coversTop_over_iff X).2
    (Precoverage.generate_mem_toGrothendieck X.hom.singleton_mem_fppfPrecoverage)

/-- A `G`-torsor `X` over `S` has the trivial class if and only if its structure morphism has a
section (Stacks, Lemma 21.4.2 (03AI)). -/
theorem mk_toTorsor_eq_one_iff (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    Sheaf.NonabelianH1.mk (GrothendieckTopology.IsTorsor.toTorsor.{w} h) = 1 ↔
      ∃ s : S ⟶ X.left, s ≫ X.hom = 𝟙 S := by
  rw [GrothendieckTopology.IsTorsor.mk_toTorsor_eq_one_iff]
  exact ⟨fun ⟨s⟩ ↦ ⟨s.left, Over.w s⟩, fun ⟨s, hs⟩ ↦ ⟨Over.homMk s hs⟩⟩

/-- The local sections of a torsor `X`, as a covering family of the fppf precoverage of `S`
each of whose members `Z ⟶ S` lifts to `X`. -/
private lemma exists_mem_fppfPrecoverage
    (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    ∃ R ∈ Scheme.fppfPrecoverage S, ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ S), R f →
      ∃ x : Z ⟶ X.left, x ≫ X.hom = f := by
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  obtain ⟨R, hR, hRS⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.1
    ((Scheme.fppfTopology.coversTop_over_iff X).1 h.coversTop)
  refine ⟨R, hR, fun Z f hf ↦ ?_⟩
  obtain ⟨_, x, _, ⟨⟩, hx⟩ := hRS _ f hf
  exact ⟨x, hx⟩

/-- The empty scheme over a nonempty base is not a `G`-torsor for any action: it has no section
fppf-locally on `S`. -/
theorem not_isTorsor_of_isEmpty [Nonempty S] [IsEmpty X.left] :
    ¬ (Scheme.fppfTopology.over S).IsTorsor G X := by
  intro h
  obtain ⟨R, hR, hRX⟩ := exists_mem_fppfPrecoverage h
  obtain ⟨Z, f, hf, z, -⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hR.1 (Classical.arbitrary S)
  obtain ⟨x, -⟩ := hRX f hf
  exact isEmptyElim (x z)

/-- A torsor `X` has a section over a single fppf covering `q : Z ⟶ S`: the coproduct of members
of a covering family through which the points of `S` are reached. -/
private lemma exists_cover_section
    (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S) (x : Z ⟶ X.left), Flat q ∧ Surjective q ∧
      LocallyOfFinitePresentation q ∧ x ≫ X.hom = q := by
  obtain ⟨R, hR, hRX⟩ := exists_mem_fppfPrecoverage h
  choose Y f hf hs using (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hR.1
  choose x hx using fun s ↦ hRX (f s) (hf s)
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  refine ⟨∐ Y, Limits.Sigma.desc f, Limits.Sigma.desc x,
    IsZariskiLocalAtSource.sigmaDesc fun s ↦ (hR.2 (hf s)).1,
    Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun s ↦
      Set.mem_iUnion.2 ⟨s, hs s⟩),
    IsZariskiLocalAtSource.sigmaDesc fun s ↦ (hR.2 (hf s)).2, ?_⟩
  ext1 s
  simp [hx]

end TauCeti.GroupScheme

namespace CategoryTheory.MorphismProperty

variable {S : Scheme.{u}} {G : Grp (Over S)} {X : Over S} [ModObj G.X X]

/-- Let `P` be a property of morphisms of schemes which is stable under base change and descends
along flat, surjective morphisms locally of finite presentation. If the structure morphism of the
group scheme `G` has `P`, so does that of every `G`-torsor `X`: over an fppf covering
`q : Z ⟶ S` on which `X` has a section, `X ×_S Z` is isomorphic to `G ×_S Z`. -/
theorem of_isTorsor (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)] (hG : P G.X.hom)
    (h : (Scheme.fppfTopology.over S).IsTorsor G X) : P X.hom := by
  obtain ⟨Z, q, x, _, _, _, hx⟩ := TauCeti.GroupScheme.exists_cover_section h
  have : P.RespectsIso := IsStableUnderBaseChange.respectsIso
  have := h.isIso_leftSMul
  -- The trivialisation `(g, z) ↦ (g • x z, z)` of `X ×_S Z` over `Z`.
  have := TauCeti.isIso_lift_smul_snd_of_isIso_leftSMul (G := G.X)
    (CategoryTheory.Over.homMk x hx : CategoryTheory.Over.mk q ⟶ X)
  refine of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ?_
  rw [← P.cancel_left_of_respectsIso
    (lift (fst G.X (CategoryTheory.Over.mk q) •
      (snd G.X (CategoryTheory.Over.mk q) ≫ CategoryTheory.Over.homMk x hx))
        (snd G.X (CategoryTheory.Over.mk q))).left]
  simpa using P.pullback_snd _ q hG

end CategoryTheory.MorphismProperty

namespace TauCeti.GroupScheme

variable {S : Scheme.{u}} {G : Grp (Over S)} {X : Over S} [ModObj G.X X]

/-- The structure morphism of a torsor is surjective. -/
theorem surjective_of_isTorsor (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    Surjective X.hom := by
  have := MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
    @Surjective.{u}
  -- The unit section shows that the structure morphism of `G` is surjective.
  have : Surjective (η[G.X].left ≫ G.X.hom) := by
    rw [Over.w]
    exact inferInstanceAs (Surjective (𝟙 S))
  exact MorphismProperty.of_isTorsor @Surjective (Surjective.of_comp η[G.X].left G.X.hom) h

/-- A torsor under a flat group scheme is flat over the base. -/
theorem flat_of_isTorsor [Flat G.X.hom]
    (h : (Scheme.fppfTopology.over S).IsTorsor G X) : Flat X.hom := by
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @Flat.{u} (Q := @RingHom.Flat)
  have := MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
    @Flat.{u}
  exact MorphismProperty.of_isTorsor @Flat ‹_› h

/-- A torsor under a group scheme locally of finite presentation is locally of finite
presentation over the base. -/
theorem locallyOfFinitePresentation_of_isTorsor
    [LocallyOfFinitePresentation G.X.hom] (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    LocallyOfFinitePresentation X.hom := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u}
      (Q := @RingHom.FinitePresentation)
  have := MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
    @LocallyOfFinitePresentation.{u}
  exact MorphismProperty.of_isTorsor @LocallyOfFinitePresentation ‹_› h

/-- For a group scheme `G` flat and locally of finite presentation over `S`, a scheme `X` over `S`
with an action of `G` is a `G`-torsor for the fppf topology if and only if
`(g, x) ↦ (g • x, x)` is an isomorphism `G ×_S X ≅ X ×_S X` and `X` is flat, surjective and
locally of finite presentation over `S`. -/
theorem isTorsor_iff [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    (Scheme.fppfTopology.over S).IsTorsor G X ↔ IsIso (ModObj.leftSMul G.X X) ∧ Flat X.hom ∧
      Surjective X.hom ∧ LocallyOfFinitePresentation X.hom := by
  refine ⟨fun h ↦ ⟨h.isIso_leftSMul, flat_of_isTorsor h, surjective_of_isTorsor h,
    locallyOfFinitePresentation_of_isTorsor h⟩, fun ⟨h, _, _, _⟩ ↦ ?_⟩
  exact isTorsor_of_isIso_leftSMul h

open scoped Obj in
/-- The base change `X ×_S S'` of a `G`-torsor `X` along a morphism `p : S' ⟶ S` is a torsor under
the base change `G ×_S S'`, acting by the base change of the action. -/
theorem isTorsor_pullback_obj {S' : Scheme.{u}} (p : S' ⟶ S)
    (h : (Scheme.fppfTopology.over S).IsTorsor G X) :
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
      (Over.pullback p).modObjObj G.X X
    (Scheme.fppfTopology.over S').IsTorsor ((Over.pullback p).mapGrp.obj G)
      ((Over.pullback p).obj X) := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  refine ⟨?_, ?_⟩
  · -- The image of `(g, x) ↦ (g • x, x)` is the base-changed morphism up to the tensorators.
    have := h.isIso_leftSMul
    have hmap : IsIso ((Over.pullback p).map (ModObj.leftSMul G.X X)) := inferInstance
    rw [ModObj.leftSMul, Functor.map_lift_smul_snd, isIso_comp_left_iff,
      isIso_comp_right_iff] at hmap
    exact hmap
  · -- A morphism `Z ⟶ S'` whose composite with `p` factors through `X` factors through
    -- `X ×_S S'`, so the covering sieve generated by `X ⟶ S` pulls back into the sieve generated
    -- by `X ×_S S' ⟶ S'`.
    rw [GrothendieckTopology.coversTop_over_iff]
    refine Scheme.fppfTopology.superset_covering ?_ (Scheme.fppfTopology.pullback_stable p
      ((Scheme.fppfTopology.coversTop_over_iff X).1 h.coversTop))
    rintro Z g ⟨_, x, _, ⟨⟩, hx⟩
    exact ⟨_, Limits.pullback.lift x g hx, _, Presieve.singleton.mk, by simp⟩

end TauCeti.GroupScheme
