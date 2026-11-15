/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic

import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain

/-!
# Isotopies of homeomorphisms of compact manifolds are ambient

An isotopy (`TauCeti.Isotopy`) only asks every time slice to be a topological embedding, while an
ambient isotopy (`TauCeti.AmbientIsotopy`) is a motion of the whole space by homeomorphisms. Every
ambient isotopy `Φ` of `Y` moves a homeomorphism `f₀ : X ≃ₜ Y` by the isotopy
`t ↦ Φ_t ∘ f₀` (`TauCeti.AmbientIsotopy.isotopic`). This file proves the converse when `Y` is a
compact connected topological manifold without boundary: every isotopy starting at `f₀` is of that
form (`TauCeti.isotopic_iff_ambientIsotopic`). So for self-homeomorphisms of such a
manifold, for instance of the torus `S¹ × S¹`, isotopy in the general sense of `TauCeti.Isotopic`
is isotopy through homeomorphisms.

There are two steps.

* **Point-set topology.** If `Y` is compact Hausdorff and every time slice of an isotopy `F`
  starting at `f₀` is onto, then `(t, y) ↦ F (t, f₀⁻¹ y)` is an ambient isotopy of `Y`
  (`TauCeti.AmbientIsotopy.ofIsotopy`): its level-preserving total map is a continuous bijection of
  the compact Hausdorff space `[0, 1] × Y`, hence a homeomorphism.
* **Invariance of domain.** If `Y` is moreover a connected manifold, every time slice is onto
  (`TauCeti.Isotopy.surjective_apply`): read through `f₀`, it is a continuous injection of `Y` into
  itself, which is onto by invariance of domain (`Continuous.surjective_of_injective`).

## Main definitions

* `TauCeti.AmbientIsotopy.ofIsotopy`: the ambient isotopy traced by an isotopy of a homeomorphism
  onto a compact Hausdorff space whose time slices are onto.

## Main results

* `TauCeti.AmbientIsotopy.final_ofIsotopy_apply`: it moves the initial homeomorphism to the end of
  the isotopy.
* `TauCeti.Isotopy.surjective_apply`: an isotopy of a homeomorphism onto a compact connected
  manifold is onto at every time.
* `TauCeti.isotopic_iff_ambientIsotopic`: a map is isotopic to a homeomorphism `f₀` onto a
  compact connected manifold exactly when it is ambient isotopic to `f₀`, that is, it is
  `Φ₁ ∘ f₀` for an ambient isotopy `Φ`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, Section 1 (isotopies and ambient isotopies).
-/

public section

noncomputable section

open Function Module Set unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace AmbientIsotopy

variable [CompactSpace Y] [T2Space Y] (f₀ : X ≃ₜ Y) {f₁ : C(X, Y)}
  (F : Isotopy (f₀ : C(X, Y)) f₁) (hF : ∀ t, Surjective fun x ↦ F (t, x))

/-- The **ambient isotopy traced by an isotopy** `F` starting at a homeomorphism `f₀ : X ≃ₜ Y` onto
a compact Hausdorff space, all of whose time slices are onto: it is `(t, y) ↦ F (t, f₀⁻¹ y)`. Its
level-preserving total map is a continuous bijection of the compact Hausdorff space `[0, 1] × Y`,
hence a homeomorphism. It carries `f₀` to the end `f₁` of the isotopy
(`TauCeti.AmbientIsotopy.final_ofIsotopy_apply`). -/
def ofIsotopy : AmbientIsotopy Y where
  toFun p := F (p.1, f₀.symm p.2)
  continuous_toFun := F.continuous.comp (by fun_prop)
  isHomeomorph_total' := by
    refine isHomeomorph_iff_continuous_bijective.2
      ⟨(continuous_fst.prodMk (F.continuous.comp (by fun_prop))), ?_, ?_⟩
    · rintro ⟨t, y⟩ ⟨t', y'⟩ h
      obtain ⟨rfl, h⟩ := Prod.mk.inj h
      exact Prod.ext rfl (f₀.symm.injective ((F.isEmbedding_apply t).injective h))
    · rintro ⟨t, z⟩
      obtain ⟨x, hx⟩ := hF t z
      exact ⟨(t, f₀ x), by simpa using hx⟩
  map_zero_left' y := by simp

@[simp]
theorem ofIsotopy_apply (p : I × Y) :
    (ofIsotopy f₀ F hF).toContinuousMap p = F (p.1, f₀.symm p.2) :=
  (rfl)

/-- The ambient isotopy traced by an isotopy `F` from `f₀` to `f₁` carries `f₀` to `f₁`. -/
theorem final_ofIsotopy_apply (x : X) : (ofIsotopy f₀ F hF).final (f₀ x) = f₁ x := by
  simp

end AmbientIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E Y] [CompactSpace Y] [T2Space Y] [ConnectedSpace Y]

include E

/-- **An isotopy of a homeomorphism onto a compact connected manifold is onto at every time.** If
`Y` is a compact connected topological manifold without boundary, every time slice of an isotopy
starting at a homeomorphism `f₀ : X ≃ₜ Y` is surjective: composed with `f₀⁻¹`, it is a continuous
injection of `Y` into itself, which is onto by invariance of domain. -/
theorem Isotopy.surjective_apply (f₀ : X ≃ₜ Y) {f₁ : C(X, Y)} (F : Isotopy (f₀ : C(X, Y)) f₁)
    (t : I) : Surjective fun x ↦ F (t, x) := by
  have hg : Surjective fun y ↦ F (t, f₀.symm y) :=
    Continuous.surjective_of_injective (E := E) (F := E) (F.continuous.comp (by fun_prop))
      ((F.isEmbedding_apply t).injective.comp f₀.symm.injective) rfl
  exact fun z ↦ let ⟨y, hy⟩ := hg z; ⟨f₀.symm y, hy⟩

/-- **Isotopy of a homeomorphism of a compact connected manifold is ambient.** If `Y` is a compact
connected topological manifold without boundary, a map `f₁ : C(X, Y)` is isotopic to a
homeomorphism `f₀ : X ≃ₜ Y` exactly when it is ambient isotopic to `f₀`, that is `f₁ = Φ₁ ∘ f₀`
for some ambient isotopy `Φ` of `Y`. -/
theorem isotopic_iff_ambientIsotopic (f₀ : X ≃ₜ Y) (f₁ : C(X, Y)) :
    Isotopic (f₀ : C(X, Y)) f₁ ↔ AmbientIsotopic (f₀ : C(X, Y)) f₁ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.isotopic f₀.isEmbedding⟩
  obtain ⟨F⟩ := isotopic_def.1 h
  refine ambientIsotopic_def.2 ⟨AmbientIsotopy.ofIsotopy f₀ F (F.surjective_apply (E := E) f₀), ?_⟩
  ext x
  exact AmbientIsotopy.final_ofIsotopy_apply f₀ F _ x

end TauCeti
