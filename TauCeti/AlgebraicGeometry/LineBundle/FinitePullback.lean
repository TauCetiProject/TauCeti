/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.AlgebraicGeometry.Fibers.Composition
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.Morphisms.Affine.QuasiAffine

/-!
# Finiteness from an ample pullback

A proper morphism is finite if the pullback of some line bundle on its target is ample.
On each scheme-theoretic fibre the pulled-back class is trivial because it comes from the
residue field. Ampleness of the trivial class makes the fibre quasi-affine, and properness
then makes the fibre finite.

This is the geometric step that turns ampleness of the pullback along a multiplication map of an
abelian variety into finiteness. See [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
for that application and [Tag 02LS](https://stacks.math.columbia.edu/tag/02LS) for the proper
finite-fibre criterion.
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry (LineBundleClass)

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A proper scheme morphism whose pullback of a line-bundle class is ample is finite. -/
theorem isFinite_of_isAmple_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {L : LineBundleClass Y} (hL : (LineBundleClass.pullback f L).IsAmple) : IsFinite f := by
  refine (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, ?_⟩
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro y
  have hpoint : IsAffineHom (Y.fromSpecResidueField y) :=
    ⟨fun _ _ ↦ .of_subsingleton Set.subsingleton_of_subsingleton⟩
  have : IsAffineHom (f.fiberι y) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f _).flip hpoint
  have htriv : LineBundleClass.pullback (Y.fromSpecResidueField y) L = 1 :=
    Subsingleton.elim _ _
  have hAmple := hL.pullback (f.fiberι y)
  rw [LineBundleClass.pullback_comp, f.fiber_fac y, ← LineBundleClass.pullback_comp,
    htriv, LineBundleClass.pullback_one] at hAmple
  have : (f.fiber y).IsQuasiAffine := LineBundleClass.isAmple_one_iff.mp hAmple
  have := IsAffineHom.of_universallyClosed_of_isQuasiAffine (f.fiberToSpecResidueField y)
  have : IsFinite (f.fiberToSpecResidueField y) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  infer_instance

end AlgebraicGeometry.Scheme.Hom
