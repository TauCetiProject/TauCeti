/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# Separated families at a finite stage

A quasi-compact quasi-separated family that becomes separated over an affine-transition
inverse limit is separated at a finite stage. Apply closed-immersion descent to the diagonal,
using Mathlib's canonical base-change identification.

References: The Stacks Project, Tag 01ZQ.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Limits.IsLimit

/-- A quasi-compact quasi-separated family that is separated over the inverse limit becomes
separated after passage to a finite stage. -/
theorem exists_isSeparated_pullback_snd
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    {D : Iᵒᵖ ⥤ Scheme.{u}}
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    {c : Cone D} (hc : IsLimit c) {i₀ : I} {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ D.obj (Opposite.op i₀)) [QuasiCompact p]
    [IsSeparated (pullback.snd p (c.π.app (Opposite.op i₀)))] :
    ∃ (i : I) (hi : i₀ ≤ i), IsSeparated (pullback.snd p (D.map (homOfLE hi).op)) := by
  have : IsSeparated (pullback.fst (c.π.app (Opposite.op i₀)) p) := by
    rw [← pullbackSymmetry_hom_comp_snd (c.π.app (Opposite.op i₀)) p]
    infer_instance
  let γ : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p)
  have : LocallyOfFiniteType γ.left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.diagonal p))
  have : CompactSpace (Over.mk p : Over (D.obj (Opposite.op i₀))).left := ‹CompactSpace X›
  have : QuasiSeparatedSpace (Over.mk p : Over (D.obj (Opposite.op i₀))).left :=
    ‹QuasiSeparatedSpace X›
  have : CompactSpace (Over.mk (pullback.snd p p ≫ p) : Over (D.obj (Opposite.op i₀))).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace
      (Over.mk (pullback.snd p p ≫ p) : Over (D.obj (Opposite.op i₀))).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  have hγ : IsClosedImmersion ((Over.pullback (c.π.app (Opposite.op i₀))).map γ).left :=
    (isClosedImmersion_overPullback_diagonal_iff _ p).mpr inferInstance
  obtain ⟨i, hi, hstage⟩ := Functor.exists_isClosedImmersion_baseChange_of_isLimit
    D c hc i₀ _ _ γ hγ
  have : IsSeparated (pullback.fst (D.map (homOfLE hi).op) p) :=
    (isClosedImmersion_overPullback_diagonal_iff _ p).mp hstage
  refine ⟨i, hi, ?_⟩
  rw [← pullbackSymmetry_hom_comp_fst p (D.map (homOfLE hi).op)]
  infer_instance

end CategoryTheory.Limits.IsLimit
