/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
public import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat base change of conductor ideal sheaves

The conductor of a finite morphism commutes with flat base change. This is equality of
ideal sheaves, not just of their supports, so the conductor closed subscheme also commutes
with flat base change. In particular, conductor calculations for finite normalization
morphisms can be transported to étale charts.

On affine charts this is the flat base-change formula for the annihilator of the finite
module `B / A`. No injectivity of `A → B`, reducedness, or Noetherian hypothesis is needed.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter IV, §1 (conductors).
* The Stacks Project, Lemma 10.40.4, Tag 07T8 (annihilators and flat base change).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsFinite f] [IsFinite f'] [Flat g]

/-- The affine conductor calculation in a cartesian square. -/
private theorem conductor_ideal_of_isPullback (H : IsPullback g' f' f g)
    (U : Y.affineOpens) (V : Y'.affineOpens) (hVU : V.1 ≤ g ⁻¹ᵁ U.1) :
    f'.conductor.ideal V = (f.conductor.ideal U).map (g.appLE U V hVU).hom := by
  have hpre : f' ⁻¹ᵁ V.1 = g' ⁻¹ᵁ (f ⁻¹ᵁ U.1) ⊓ f' ⁻¹ᵁ V.1 := by
    apply (inf_eq_right.mpr ?_).symm
    exact (f'.preimage_mono hVU).trans_eq (by simp only [← Scheme.Hom.comp_preimage, H.w])
  have hpush := (isIso_pushoutSection_iff H hVU le_rfl hpre).mp
    (isIso_pushoutSection_of_isAffineOpen H hVU le_rfl hpre U.2 V.2 (U.2.preimage f))
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U.1)
  let A' := Γ(Y', V)
  let B' := Γ(X', f' ⁻¹ᵁ V.1)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Algebra A A' := (g.appLE U V hVU).hom.toAlgebra
  let : Algebra A' B' := (f'.app V).hom.toAlgebra
  let : Algebra B B' := (g'.appLE (f ⁻¹ᵁ U.1) (f' ⁻¹ᵁ V.1)
    (hpre ▸ inf_le_left)).hom.toAlgebra
  let : Algebra A B' := ((f'.app V).hom.comp (g.appLE U V hVU).hom).toAlgebra
  have : IsScalarTower A A' B' := .of_algebraMap_eq' rfl
  have : IsScalarTower A B B' := .of_algebraMap_eq' (by
    simpa only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_eq_app] using congrArg CommRingCat.Hom.hom hpush.w.symm)
  have : Algebra.IsPushout A A' B B' :=
    CommRingCat.isPushout_iff_isPushout.mp (by
      simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
        Scheme.Hom.appLE_eq_app] using hpush.flip)
  have : Module.Flat A A' := g.flat_appLE U.2 V.2 hVU
  have : Module.Finite A B := IsFinite.finite_app f U U.2
  rw [conductor_ideal, conductor_ideal]
  exact TauCeti.Algebra.conductor_eq_map_of_flat A (B := B) A' B'

/-- The conductor ideal sheaf of a finite morphism commutes with flat base change.
The square may be any chosen pullback square. -/
theorem conductor_of_isPullback (H : IsPullback g' f' f g) :
    f'.conductor = f.conductor.comap g := by
  have charts (y : Y') : ∃ (U : Y.Opens) (V : Y'.Opens), IsAffineOpen U ∧
      IsAffineOpen V ∧ y ∈ V ∧ V ≤ g ⁻¹ᵁ U := by
    obtain ⟨U, hU, hyU, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (U := ⊤) (x := g y) (by simp)
    obtain ⟨V, hV, hyV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
        (U := g ⁻¹ᵁ U) (x := y) hyU
    exact ⟨U, V, hU, hV, hyV, hVU⟩
  choose U V hU hV hy hVU using charts
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y ↦ Spec Γ(Y', V y))
    (fun y ↦ (hV y).fromSpec) (fun y ↦ ⟨y, by
      have hmem : y ∈ Set.range (hV y).fromSpec := (hV y).range_fromSpec.symm ▸ hy y
      simpa only [Set.mem_range] using hmem⟩)
  apply Scheme.IdealSheafData.ext_of_comap_openCover 𝒰
  intro y
  -- The cover projections are the chosen affine chart maps; make these dependent
  -- projections explicit before using the affine ideal-sheaf comparisons.
  change f'.conductor.comap (hV y).fromSpec =
    (f.conductor.comap g).comap (hV y).fromSpec
  rw [Scheme.IdealSheafData.comap_fromSpec_eq_ofIdealTop,
    Scheme.IdealSheafData.comap_comap_fromSpec_eq_ofIdealTop _ g (hU y) (hV y) (hVU y),
    conductor_ideal_of_isPullback H ⟨U y, hU y⟩ ⟨V y, hV y⟩ (hVU y)]

/-- The conductor of the base change of a finite morphism is the pullback of its
conductor ideal sheaf along a flat morphism. -/
@[simp]
theorem conductor_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsFinite f] [Flat g] :
    (Limits.pullback.snd f g).conductor = f.conductor.comap g :=
  conductor_of_isPullback (IsPullback.of_hasPullback f g)

end AlgebraicGeometry.Scheme.Hom
