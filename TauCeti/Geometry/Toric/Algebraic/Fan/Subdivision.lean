/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Product

/-!
# Subdivisions of finite toric fans

A fan `Φ` subdivides a fan `Ψ` when they have the same support and every cone of `Φ` is
contained in a cone of `Ψ`. Every cone of `Ψ` is then covered by the cones of `Φ` which it
contains. This derived conewise form is needed to control affine cone charts and to apply support
criteria for toric maps.

A subdivision has the same support as the original fan and induces a fan morphism whose lattice
and real-linear maps are identities. Subdivisions are reflexive and transitive, and products of
subdivisions are subdivisions.

## Main declarations

* `TauCeti.Toric.Fan.IsSubdivision`: the conewise subdivision relation on finite fans.
* `TauCeti.Toric.Fan.IsSubdivision.support_eq`: a subdivision and the original fan have the same
  support.
* `TauCeti.Toric.Fan.IsSubdivision.toFanHom`: the fan morphism induced by a subdivision.
* `TauCeti.Toric.Fan.IsSubdivision.refl` and `TauCeti.Toric.Fan.IsSubdivision.trans`: subdivision
  is a preorder relation.
* `TauCeti.Toric.Fan.IsSubdivision.prod`: products preserve subdivisions.

## References

The definition is the standard one in §1.4 of W. Fulton, *Introduction to Toric
Varieties*, and §3.3 of D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

namespace Fan

/-- A fan `Φ` is a *subdivision* of a fan `Ψ` if both fans have the same support and every
cone of `Φ` lies in a cone of `Ψ`. -/
structure IsSubdivision (Φ Ψ : Fan i) : Prop where
  /-- Every cone of the subdividing fan lies in a cone of the original fan. -/
  exists_cone_le : ∀ ⦃σ⦄, σ ∈ Φ.cones → ∃ τ ∈ Ψ.cones, σ ≤ τ
  /-- The subdividing fan has the same support as the original fan. -/
  support_eq : Φ.support = Ψ.support

namespace IsSubdivision

variable {Φ Ψ Ω : Fan i} {σ τ : PointedCone ℝ V}

/-- Every point of an original cone lies in a subdividing cone contained in it. -/
theorem exists_mem_cone (h : Φ.IsSubdivision Ψ) (hτ : τ ∈ Ψ.cones) {x : V} (hx : x ∈ τ) :
    ∃ σ ∈ Φ.cones, σ ≤ τ ∧ x ∈ σ := by
  have hxΦ : x ∈ Φ.support := h.support_eq.symm ▸ Ψ.subset_support hτ hx
  obtain ⟨σ, hσ, hxσ⟩ := Φ.mem_support.1 hxΦ
  obtain ⟨υ, hυ, hσυ⟩ := h.exists_cone_le hσ
  have hface : (σ ⊓ τ).IsFaceOf σ := by
    have hinter := (Ψ.inf_isFaceOf_right hτ hυ).inf (PointedCone.IsFaceOf.refl σ)
    simpa only [inf_assoc, inf_comm, inf_left_comm, inf_eq_left.mpr hσυ] using hinter
  exact ⟨σ ⊓ τ, Φ.mem_of_isFaceOf hσ hface, inf_le_right, ⟨hxσ, hx⟩⟩

/-- Membership in a cone of the original fan is equivalent to membership in some subdividing
cone contained in it. -/
theorem mem_iff_exists (h : Φ.IsSubdivision Ψ) (hτ : τ ∈ Ψ.cones) {x : V} :
    x ∈ τ ↔ ∃ σ ∈ Φ.cones, σ ≤ τ ∧ x ∈ σ := by
  constructor
  · exact h.exists_mem_cone hτ
  · rintro ⟨σ, _, hστ, hx⟩
    exact hστ hx

/-- A subdivision is complete exactly when the original fan is complete. -/
theorem isComplete_iff (h : Φ.IsSubdivision Ψ) : Φ.IsComplete ↔ Ψ.IsComplete := by
  constructor
  · intro hΦ
    apply Ψ.isComplete_iff.2
    intro x
    obtain ⟨σ, hσ, hxσ⟩ := Φ.isComplete_iff.1 hΦ x
    obtain ⟨τ, hτ, hστ⟩ := h.exists_cone_le hσ
    exact ⟨τ, hτ, hστ hxσ⟩
  · intro hΨ
    apply Φ.isComplete_iff.2
    intro x
    obtain ⟨τ, hτ, hxτ⟩ := Ψ.isComplete_iff.1 hΨ x
    obtain ⟨σ, hσ, _, hxσ⟩ := h.exists_mem_cone hτ hxτ
    exact ⟨σ, hσ, hxσ⟩

/-- A subdivision induces the fan morphism which is the identity on the ambient lattice. -/
noncomputable def toFanHom (h : Φ.IsSubdivision Ψ) : FanHom Φ Ψ :=
  FanHom.ofLatticeMap Φ Ψ (AddMonoidHom.id N) fun σ hσ ↦ by
    obtain ⟨τ, hτ, hστ⟩ := h.exists_cone_le hσ
    rw [Φ.lattice.extend_id, PointedCone.map_id]
    exact ⟨τ, hτ, hστ⟩

/-- The integral map induced by a subdivision is the identity. -/
@[simp]
theorem toFanHom_latticeMap (h : Φ.IsSubdivision Ψ) :
    h.toFanHom.latticeMap = AddMonoidHom.id N := by
  rw [toFanHom, FanHom.ofLatticeMap_latticeMap]

/-- The real-linear map induced by a subdivision is the identity. -/
@[simp]
theorem toFanHom_realMap (h : Φ.IsSubdivision Ψ) : h.toFanHom.realMap = LinearMap.id :=
  by rw [toFanHom, FanHom.ofLatticeMap_realMap, Φ.lattice.extend_id]

/-- Every fan is a subdivision of itself. -/
protected theorem refl (Φ : Fan i) : Φ.IsSubdivision Φ where
  exists_cone_le _ hσ := ⟨_, hσ, le_rfl⟩
  support_eq := rfl

/-- Subdivision is transitive. -/
theorem trans (hΦΨ : Φ.IsSubdivision Ψ) (hΨΩ : Ψ.IsSubdivision Ω) :
    Φ.IsSubdivision Ω where
  exists_cone_le _ hσ := by
    obtain ⟨τ, hτ, hστ⟩ := hΦΨ.exists_cone_le hσ
    obtain ⟨υ, hυ, hτυ⟩ := hΨΩ.exists_cone_le hτ
    exact ⟨υ, hυ, hστ.trans hτυ⟩
  support_eq := hΦΨ.support_eq.trans hΨΩ.support_eq

/-- The identity morphism is the morphism induced by the reflexive subdivision. -/
@[simp]
theorem toFanHom_refl (Φ : Fan i) : (IsSubdivision.refl Φ).toFanHom = FanHom.id Φ :=
  FanHom.ext (by simp)

/-- The fan morphism of a composite subdivision is the composite of the induced morphisms. -/
@[simp]
theorem toFanHom_trans (hΦΨ : Φ.IsSubdivision Ψ) (hΨΩ : Ψ.IsSubdivision Ω) :
    (hΦΨ.trans hΨΩ).toFanHom = hΨΩ.toFanHom.comp hΦΨ.toFanHom :=
  FanHom.ext (by simp)

section Prod

variable {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V'] {i' : N' →+ V'}
  {Φ' Ψ' : Fan i'}

/-- The product of two subdivisions is a subdivision of the product fan. -/
theorem prod (h : Φ.IsSubdivision Ψ) (h' : Φ'.IsSubdivision Ψ') :
    (Φ.prod Φ').IsSubdivision (Ψ.prod Ψ') where
  exists_cone_le _ hξ := by
    obtain ⟨σ, hσ, σ', hσ', rfl⟩ := (Φ.mem_prod_cones Φ').1 hξ
    obtain ⟨τ, hτ, hστ⟩ := h.exists_cone_le hσ
    obtain ⟨τ', hτ', hστ'⟩ := h'.exists_cone_le hσ'
    exact ⟨τ.prod τ', (Ψ.mem_prod_cones Ψ').2 ⟨τ, hτ, τ', hτ', rfl⟩,
      fun _ hx ↦ ⟨hστ hx.1, hστ' hx.2⟩⟩
  support_eq := by
    rw [Fan.support_prod, Fan.support_prod, h.support_eq, h'.support_eq]

/-- The fan morphism of a product subdivision is the product of the induced morphisms. -/
@[simp]
theorem toFanHom_prod (h : Φ.IsSubdivision Ψ) (h' : Φ'.IsSubdivision Ψ') :
    (h.prod h').toFanHom = h.toFanHom.prodMap h'.toFanHom := by
  apply FanHom.ext
  simp only [toFanHom_latticeMap, FanHom.prodMap_latticeMap]
  ext x <;> rfl

end Prod

end IsSubdivision

end Fan

end TauCeti.Toric
