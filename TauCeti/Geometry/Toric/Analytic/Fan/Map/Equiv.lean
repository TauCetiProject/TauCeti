/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Holomorphic

/-!
# Equivalences of fans induce biholomorphisms of analytic realizations

An equivalence of regular fans `e : FanEquiv Φ Ψ` has an underlying fan morphism in each
direction, `e.toFanHom` and `e.symm.toFanHom`. By functoriality of the induced maps of analytic
realizations (`TauCeti.Toric.FanHom.analyticMap_id` and `TauCeti.Toric.FanHom.analyticMap_comp`)
the two induced maps are mutually inverse, so `e` induces an isomorphism of analytic
realizations, whose inverse is induced by the inverse fan equivalence. Both maps are holomorphic
(`TauCeti.Toric.FanHom.contMDiff_analyticMap`), so this isomorphism is a biholomorphism for the
complex manifold structures of the two realizations. The construction respects identities,
composition and inverses of fan equivalences, and carries the affine chart of each cone `σ` onto the
affine chart of the corresponding cone `e.coneEquiv σ`.

## Main declarations

* `TauCeti.Toric.FanEquiv.analyticIso`: the isomorphism of analytic realizations induced by an
  equivalence of regular fans.
* `TauCeti.Toric.FanEquiv.analyticDiffeomorph`: the same map as a biholomorphism of complex
  manifolds.
* `TauCeti.Toric.FanEquiv.analyticDiffeomorph_symm`: its inverse is the biholomorphism induced by
  the inverse fan equivalence.
* `TauCeti.Toric.FanEquiv.image_analyticMap_range_analyticAffineChartι`: the affine chart of a cone
  is carried onto the affine chart of the corresponding cone.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti.Toric.FanEquiv

universe u

variable {N N' N'' V V' V'' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''} {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''}
  (e : FanEquiv Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-! ### The isomorphism of analytic realizations -/

/-- The isomorphism between the analytic realizations of two regular fans induced by a fan
equivalence. Its inverse is induced by the inverse fan equivalence. -/
noncomputable def analyticIso : Φ.analyticRealization hΦ ≅ Ψ.analyticRealization hΨ where
  hom := e.toFanHom.analyticMap hΦ hΨ
  inv := e.symm.toFanHom.analyticMap hΨ hΦ
  hom_inv_id := by simp [← FanHom.analyticMap_comp, ← toFanHom_trans]
  inv_hom_id := by simp [← FanHom.analyticMap_comp, ← toFanHom_trans]

/-- The isomorphism induced by a fan equivalence is the map induced by its underlying fan
morphism. -/
@[simp]
theorem analyticIso_hom : (e.analyticIso hΦ hΨ).hom = e.toFanHom.analyticMap hΦ hΨ := (rfl)

/-- The inverse of the isomorphism induced by a fan equivalence is the map induced by the inverse
fan equivalence. -/
@[simp]
theorem analyticIso_inv : (e.analyticIso hΦ hΨ).inv = e.symm.toFanHom.analyticMap hΨ hΦ := (rfl)

/-- The inverse of the isomorphism induced by a fan equivalence is the isomorphism induced by the
inverse fan equivalence. -/
@[simp]
theorem analyticIso_symm : (e.analyticIso hΦ hΨ).symm = e.symm.analyticIso hΨ hΦ :=
  Iso.ext (rfl)

/-- The identity fan equivalence induces the identity isomorphism. -/
@[simp]
theorem analyticIso_refl : (FanEquiv.refl Φ).analyticIso hΦ hΦ = Iso.refl _ :=
  Iso.ext (by simp)

/-- A composite of fan equivalences induces the composite isomorphism. -/
theorem analyticIso_trans (e' : FanEquiv Ψ Ω) (hΩ : Ω.IsRegular) :
    (e.trans e').analyticIso hΦ hΩ = e.analyticIso hΦ hΨ ≪≫ e'.analyticIso hΨ hΩ :=
  Iso.ext (by simp [e.toFanHom.analyticMap_comp hΦ hΨ])

/-- The map induced by a fan equivalence carries the affine chart of a cone `σ` into the affine
chart of the corresponding cone `e.coneEquiv σ`. -/
private theorem image_analyticMap_range_subset (σ : Φ.cones) :
    e.toFanHom.analyticMap hΦ hΨ '' range (Φ.analyticAffineChartι hΦ σ) ⊆
      range (Ψ.analyticAffineChartι hΨ (e.coneEquiv σ)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have h := e.toFanHom.mapsTo_leastCone σ.2
  rw [toFanHom_leastCone] at h
  exact ⟨_, (e.toFanHom.analyticMap_analyticAffineChartι_of_mapsTo hΦ hΨ h x).symm⟩

/-- The map induced by a fan equivalence carries the affine chart of a cone `σ` onto the affine
chart of the corresponding cone `e.coneEquiv σ`. -/
theorem image_analyticMap_range_analyticAffineChartι (σ : Φ.cones) :
    e.toFanHom.analyticMap hΦ hΨ '' range (Φ.analyticAffineChartι hΦ σ) =
      range (Ψ.analyticAffineChartι hΨ (e.coneEquiv σ)) := by
  refine (e.image_analyticMap_range_subset hΦ hΨ σ).antisymm fun y hy ↦ ?_
  -- The inverse fan equivalence carries the chart of `e.coneEquiv σ` back into the chart of `σ`.
  have hinv := e.symm.image_analyticMap_range_subset hΨ hΦ (e.coneEquiv σ) (mem_image_of_mem _ hy)
  rw [← coneEquiv_symm, OrderIso.symm_apply_apply] at hinv
  refine ⟨_, hinv, ?_⟩
  rw [← analyticIso_hom, ← analyticIso_inv]
  exact (e.analyticIso hΦ hΨ).inv_hom_id_apply y

/-! ### The biholomorphism of analytic realizations -/

/-- The biholomorphism between the analytic realizations of two regular fans induced by a fan
equivalence, for their complex manifold structures modelled on `ℂ ^ r` and `ℂ ^ r'`, where
`r = Module.finrank ℤ N` and `r' = Module.finrank ℤ N'` are the ranks of the two lattices. The
argument `n` is the differentiability order: the map and its inverse are both `C^n`. -/
noncomputable def analyticDiffeomorph (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    Diffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ)
      (Φ.analyticRealization hΦ) (Ψ.analyticRealization hΨ) n :=
  letI := Φ.analyticChartedSpace hΦ
  letI := Ψ.analyticChartedSpace hΨ
  { toEquiv := (TopCat.homeoOfIso (e.analyticIso hΦ hΨ)).toEquiv
    contMDiff_toFun := e.toFanHom.contMDiff_analyticMap hΦ hΨ n
    contMDiff_invFun := e.symm.toFanHom.contMDiff_analyticMap hΨ hΦ n }

/-- The biholomorphism induced by a fan equivalence is the map induced by its underlying fan
morphism. -/
@[simp]
theorem coe_analyticDiffeomorph (n : ℕ∞ω) :
    ⇑(e.analyticDiffeomorph hΦ hΨ n) = e.toFanHom.analyticMap hΦ hΨ := (rfl)

/-- The inverse of the biholomorphism induced by a fan equivalence is the biholomorphism induced by
the inverse fan equivalence. -/
@[simp]
theorem analyticDiffeomorph_symm (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    (e.analyticDiffeomorph hΦ hΨ n).symm = e.symm.analyticDiffeomorph hΨ hΦ n :=
  letI := Φ.analyticChartedSpace hΦ
  letI := Ψ.analyticChartedSpace hΨ
  -- The right-hand side is a right inverse of `e.analyticDiffeomorph hΦ hΨ n`, by `inv_hom_id`.
  Diffeomorph.ext fun y ↦ (e.analyticDiffeomorph hΦ hΨ n).symm_apply_eq.2 <| by
    simpa using ((e.analyticIso hΦ hΨ).inv_hom_id_apply y).symm

/-- The identity fan equivalence induces the identity biholomorphism. -/
@[simp]
theorem analyticDiffeomorph_refl (n : ℕ∞ω) :
    (FanEquiv.refl Φ).analyticDiffeomorph hΦ hΦ n =
      letI := Φ.analyticChartedSpace hΦ
      Diffeomorph.refl 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) (Φ.analyticRealization hΦ) n :=
  letI := Φ.analyticChartedSpace hΦ
  Diffeomorph.ext fun x ↦ by simp

/-- A composite of fan equivalences induces the composite biholomorphism. -/
theorem analyticDiffeomorph_trans (e' : FanEquiv Ψ Ω) (hΩ : Ω.IsRegular) (n : ℕ∞ω) :
    (e.trans e').analyticDiffeomorph hΦ hΩ n =
      letI := Φ.analyticChartedSpace hΦ
      letI := Ψ.analyticChartedSpace hΨ
      letI := Ω.analyticChartedSpace hΩ
      (e.analyticDiffeomorph hΦ hΨ n).trans (e'.analyticDiffeomorph hΨ hΩ n) :=
  letI := Φ.analyticChartedSpace hΦ
  letI := Ψ.analyticChartedSpace hΨ
  letI := Ω.analyticChartedSpace hΩ
  Diffeomorph.ext fun x ↦ by simp [e.toFanHom.analyticMap_comp hΦ hΨ]

end TauCeti.Toric.FanEquiv
