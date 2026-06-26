/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Transporting symplectic forms along linear equivalences

A real-linear isomorphism `e : V ≃ₗ[ℝ] W` carries a symplectic form `ω` on `V` to one on `W` by
pushing the arguments back along `e.symm`: `(ω.transport e)(v, w) = ω(e.symm v, e.symm w)`. This
is the symplectic companion of `TauCeti.AlmostComplexStructure.transport`
(in `TauCeti.Geometry.Symplectic.Transport`): together they make `e` simultaneously a
symplectomorphism and a complex-linear isomorphism, so every compatibility relation between `ω`
and an almost complex structure `J` is preserved when both are transported along `e`.

This is the pointwise linear algebra that the smooth layer of the analytic Heegaard Floer roadmap
needs before stating bundle-level naturality: a symplectic form on a vector bundle is given
fiberwise, and a change of trivialization acts on each fiber by exactly this transport. Stating
the compatibility transport now keeps the invariance statements naturality-ready, as the roadmap
asks. The underlying form transport reuses Mathlib's `LinearMap.BilinForm.congr` and
`LinearMap.BilinForm.Nondegenerate.congr`.

## Main declarations

* `TauCeti.SymplecticForm.transport`: the symplectic form `ω.transport e` on `W` obtained by
  transporting `ω` along `e : V ≃ₗ[ℝ] W`.
* `TauCeti.SymplecticForm.transport_refl` / `transport_trans` / `transport_symm_transport` /
  `transport_transport_symm`: functoriality of transport in the linear equivalence.
* `TauCeti.SymplecticForm.transport_apply_apply`: `e` is a symplectomorphism onto the transported
  form, `(ω.transport e)(e v, e w) = ω(v, w)`.
* `TauCeti.SymplecticForm.Invariant.transport`, `Tames.transport`, `Compatible.transport`:
  invariance, tameness, and compatibility of a pair `(ω, J)` transport along `e` to the pair
  `(ω.transport e, J.transport e)`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1, where a symplectomorphism carries a compatible triple to a compatible triple.
-/

@[expose] public section

namespace TauCeti

namespace SymplecticForm

variable {V W X : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup X] [Module ℝ X]

/-- Transport a symplectic form along a real-linear equivalence `e : V ≃ₗ[ℝ] W` by pushing the
arguments back along `e.symm`.

The underlying bilinear form is `LinearMap.BilinForm.congr e` applied to `ω`, equivalently
`(v, w) ↦ ω(e.symm v, e.symm w)`; it stays alternating and nondegenerate because `e.symm` is a
linear bijection. -/
noncomputable def transport (ω : SymplecticForm V) (e : V ≃ₗ[ℝ] W) : SymplecticForm W where
  toBilinForm := LinearMap.BilinForm.congr e ω.toBilinForm
  isAlt := fun w => by
    rw [LinearMap.BilinForm.congr_apply]
    exact ω.isAlt.self_eq_zero (e.symm w)
  nondegenerate := ω.nondegenerate.congr e

@[simp]
lemma transport_toBilinForm (ω : SymplecticForm V) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e).toBilinForm = LinearMap.BilinForm.congr e ω.toBilinForm := rfl

@[simp]
lemma transport_apply (ω : SymplecticForm V) (e : V ≃ₗ[ℝ] W) (v w : W) :
    ω.transport e v w = ω (e.symm v) (e.symm w) := rfl

/-- Transporting along the identity equivalence does nothing. -/
@[simp]
lemma transport_refl (ω : SymplecticForm V) :
    ω.transport (LinearEquiv.refl ℝ V) = ω :=
  toBilinForm_injective (by simp [transport_toBilinForm])

/-- Transport is functorial: transporting along `e₁` then `e₂` is transporting along their
composite. -/
@[simp]
lemma transport_trans (ω : SymplecticForm V) (e₁ : V ≃ₗ[ℝ] W) (e₂ : W ≃ₗ[ℝ] X) :
    (ω.transport e₁).transport e₂ = ω.transport (e₁ ≪≫ₗ e₂) :=
  toBilinForm_injective <| by
    simp only [transport_toBilinForm]
    rw [LinearMap.BilinForm.congr_congr]

/-- Transporting forward along `e` and back along `e.symm` returns the original form. -/
@[simp]
lemma transport_symm_transport (ω : SymplecticForm V) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e).transport e.symm = ω := by
  rw [transport_trans, e.self_trans_symm, transport_refl]

/-- Transporting back along `e.symm` and forward along `e` returns the original form. -/
@[simp]
lemma transport_transport_symm (ω : SymplecticForm W) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e.symm).transport e = ω := by
  rw [transport_trans, e.symm_trans_self, transport_refl]

/-- `e` is a symplectomorphism onto the transported form: evaluating `ω.transport e` on images
under `e` recovers `ω`. -/
@[simp]
lemma transport_apply_apply (ω : SymplecticForm V) (e : V ≃ₗ[ℝ] W) (v w : V) :
    ω.transport e (e v) (e w) = ω v w := by
  rw [transport_apply, e.symm_apply_apply, e.symm_apply_apply]

section Compatible

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- Transport by a linear equivalence preserves and reflects `J`-invariance. -/
@[simp]
lemma invariant_transport_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (e : V ≃ₗ[ℝ] W) : (ω.transport e).Invariant (J.transport e) ↔ ω.Invariant J := by
  constructor
  · rw [invariant_iff, invariant_iff]
    intro hinv v w
    have h := hinv (e v) (e w)
    simpa [transport_apply, AlmostComplexStructure.transport_apply] using h
  · rw [invariant_iff, invariant_iff]
    intro hinv v w
    simp only [transport_apply, AlmostComplexStructure.transport_apply,
      LinearEquiv.symm_apply_apply]
    exact hinv (e.symm v) (e.symm w)

/-- `J`-invariance transports along a linear equivalence: if `ω` is `J`-invariant, then
`ω.transport e` is invariant under the transported almost complex structure `J.transport e`. -/
lemma Invariant.transport (hinv : ω.Invariant J) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e).Invariant (J.transport e) :=
  (invariant_transport_iff ω J e).mpr hinv

/-- Transport by a linear equivalence preserves and reflects tameness. -/
@[simp]
lemma tames_transport_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (e : V ≃ₗ[ℝ] W) : (ω.transport e).Tames (J.transport e) ↔ ω.Tames J := by
  constructor
  · intro htames v hv
    have h := htames (e v) (mt e.map_eq_zero_iff.mp hv)
    simpa [transport_apply, AlmostComplexStructure.transport_apply] using h
  · intro htames w hw
    rw [transport_apply]
    simp only [AlmostComplexStructure.transport_apply, LinearEquiv.symm_apply_apply]
    exact htames (e.symm w) (mt e.symm.map_eq_zero_iff.mp hw)

/-- Taming transports along a linear equivalence: if `ω` tames `J`, then `ω.transport e` tames
the transported almost complex structure `J.transport e`. -/
lemma Tames.transport (htames : ω.Tames J) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e).Tames (J.transport e) :=
  (tames_transport_iff ω J e).mpr htames

/-- Transport by a linear equivalence preserves and reflects compatibility. -/
@[simp]
lemma compatible_transport_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (e : V ≃ₗ[ℝ] W) : (ω.transport e).Compatible (J.transport e) ↔ ω.Compatible J := by
  rw [(ω.transport e).compatible_iff (J.transport e), ω.compatible_iff J,
    invariant_transport_iff, tames_transport_iff]

/-- Compatibility transports along a linear equivalence: if `ω` is compatible with `J`, then
`ω.transport e` is compatible with the transported almost complex structure `J.transport e`. This
expresses that `e` carries the compatible pair `(ω, J)` to the compatible pair
`(ω.transport e, J.transport e)`. -/
lemma Compatible.transport (h : ω.Compatible J) (e : V ≃ₗ[ℝ] W) :
    (ω.transport e).Compatible (J.transport e) :=
  (compatible_transport_iff ω J e).mpr h

end Compatible

end SymplecticForm

end TauCeti
