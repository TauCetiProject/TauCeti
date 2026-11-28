/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Finite.Basic
public import TauCeti.AlgebraicGeometry.Limits.Finite.Presentation

import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Closed immersions at a finite stage

A finite type morphism of quasi-compact quasi-separated schemes that becomes a closed
immersion over an affine-transition inverse limit is a closed immersion at a finite stage.
The proof combines finite-stage finiteness and monomorphism inheritance. This is the
closed-immersion clause of the Stacks Project, Tag 01ZP.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Functor

/-- A finite type stage morphism that is a closed immersion over the inverse limit is a
closed immersion after passage to a later stage. -/
theorem exists_isClosedImmersion_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hf : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsClosedImmersion ((Over.pullback (D.map (homOfLE hi).op)).map f₀).left := by
  have : Nonempty I := ⟨i₀⟩
  have := hf
  obtain ⟨i, hi, hfinite⟩ := exists_isFinite_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀
    inferInstance
  obtain ⟨j, hj, hmono⟩ := hc.exists_mono_overPullback f₀
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j.unop
  refine ⟨k, hi.trans hik, (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨?_, ?_⟩⟩
  · have H := MorphismProperty.overPullbackMap_comp (@IsFinite)
      (D.map (homOfLE hik).op) (D.map (homOfLE hi).op) f₀ hfinite
    have he : D.map (homOfLE hik).op ≫ D.map (homOfLE hi).op =
        D.map (homOfLE (hi.trans hik)).op := by rw [← D.map_comp]; rfl
    rw [← he]
    exact H
  · have H := MorphismProperty.overPullbackMap_comp (MorphismProperty.monomorphisms Scheme.{u})
      (D.map (homOfLE hjk).op) (D.map hj) f₀ hmono
    have he : D.map (homOfLE hjk).op ≫ D.map hj =
        D.map (homOfLE (hi.trans hik)).op := by rw [← D.map_comp]; rfl
    rw [← he]
    exact H

end CategoryTheory.Functor
