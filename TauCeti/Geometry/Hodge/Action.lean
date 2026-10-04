/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.PeriodDomain
public import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Lattice automorphisms act on Hodge structures and on period domains

A linear automorphism `g` of a lattice `V` extends to a complex-linear automorphism of the
complexification commuting with lattice conjugation, `TauCeti.Hodge.integralEquivToComplex`. Pushing
a Hodge filtration forward along it gives a Hodge structure of the same weight, and this is an
action of the group `V ≃ₗ[ℤ] V` on the weight-`n` Hodge structures on the complexification. The
action preserves the Hodge numbers, and it transports polarizations: `Q` polarizes `hs` exactly
when the transported form polarizes `g • hs`.

When `g` preserves a fixed integral form `Qint`, the transported form is `Qint` itself, so the
isometry group `Aut(V, Qint)` (`TauCeti.BilinForm.isometryGroup Qint`) acts on the points of the
period domain of `(V, Qint)` at every Hodge type. This is the sense in which `Aut(V, Qint)` is the
symmetry group of the period domain; classically, the period map of a variation of Hodge structure
whose monodromy lies in a subgroup `Γ ≤ Aut(V, Qint)` takes values in the quotient `Γ \ D` by this
action.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.instMulAction`: `V ≃ₗ[ℤ] V` acts on weight-`n` Hodge structures
  on the complexification of `V`, with `TauCeti.Hodge.HodgeStructureOn.smul_F` computing the Hodge
  filtration of `g • hs`.
* `TauCeti.Hodge.HodgeStructureOn.hodgeType_smul`: the action preserves the Hodge type.
* `TauCeti.Hodge.isPolarization_smul_iff`: `Q` polarizes `hs` exactly when the form transported
  along `g` polarizes `g • hs`.
* `TauCeti.Hodge.IsPolarization.smul_of_mem_isometryGroup`: an isometry of a polarizing form
  carries a Hodge structure it polarizes to another one.
* `TauCeti.Hodge.PeriodDomain.Point.instMulAction`: the isometry group `Aut(V, Qint)` acts on the
  period domain of `(V, Qint)`.

## References

* Griffiths, *Periods of integrals on algebraic manifolds II*, §1.
* Carlson–Müller-Stach–Peters, *Period Mappings and Period Domains*, Ch. 4.
-/

public section

namespace TauCeti.Hodge

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}

namespace HodgeStructureOn

/-- A linear automorphism `g` of the lattice moves a Hodge structure on the complexification: the
Hodge filtration of `g • hs` is the image of that of `hs` under the complexification of `g`
(`TauCeti.Hodge.HodgeStructureOn.smul_F`). -/
noncomputable instance instSMul : SMul (V ≃ₗ[ℤ] V) (HodgeStructure hℂ n) where
  smul g hs := hs.comap (integralEquivToComplex hℂ hℂ g).symm fun x ↦ by simp

/-- The Hodge filtration of `g • hs` is the image of that of `hs` under the complexification of
`g`. -/
@[simp]
theorem smul_F (g : V ≃ₗ[ℤ] V) (hs : HodgeStructure hℂ n) (p : ℤ) :
    (g • hs).F p = (hs.F p).map (integralEquivToComplex hℂ hℂ g).toLinearMap :=
  (comap_F _ _ hs p).trans (Submodule.comap_equiv_eq_map_symm _ _)

/-- The Hodge components of `g • hs` are the images of those of `hs` under the complexification of
`g`. -/
@[simp]
theorem smul_piece (g : V ≃ₗ[ℤ] V) (hs : HodgeStructure hℂ n) (p : ℤ) :
    (g • hs).piece p = (hs.piece p).map (integralEquivToComplex hℂ hℂ g).toLinearMap :=
  (comap_piece _ _ hs p).trans (Submodule.comap_equiv_eq_map_symm _ _)

/-- The lattice automorphisms act on the weight-`n` Hodge structures on the complexification. -/
noncomputable instance instMulAction : MulAction (V ≃ₗ[ℤ] V) (HodgeStructure hℂ n) where
  one_smul hs := HodgeStructureOn.ext <| funext fun p ↦ by
    simp [LinearEquiv.one_eq_refl]
  mul_smul g h hs := HodgeStructureOn.ext <| funext fun p ↦ by
    rw [smul_F, smul_F, smul_F, LinearEquiv.mul_eq_trans, integralEquivToComplex_trans hℂ hℂ hℂ,
      LinearEquiv.coe_trans, Submodule.map_comp]

/-- The action of a lattice automorphism preserves the Hodge numbers. -/
@[simp]
theorem hodgeNumber_smul (g : V ≃ₗ[ℤ] V) (hs : HodgeStructure hℂ n) (p : ℤ) :
    (g • hs).hodgeNumber p = hs.hodgeNumber p := by
  rw [hodgeNumber_def, hodgeNumber_def, smul_piece, LinearEquiv.finrank_map_eq]

/-- The action of a lattice automorphism preserves the Hodge type. -/
@[simp]
theorem hodgeType_smul (g : V ≃ₗ[ℤ] V) (hs : HodgeStructure hℂ n) :
    (g • hs).hodgeType = hs.hodgeType := by
  ext p <;> simp

end HodgeStructureOn

section Polarization

variable {hs : HodgeStructure hℂ n} {Q : LinearMap.BilinForm ℤ V}

/-- Transporting a Hodge structure and a polarization of it along the same lattice automorphism
gives a polarized Hodge structure: if `Q` polarizes `hs`, then `Q` transported along `g`
polarizes `g • hs`. -/
theorem IsPolarization.smul (h : IsPolarization hℂ hs Q) (g : V ≃ₗ[ℤ] V) :
    IsPolarization hℂ (g • hs) (LinearMap.BilinForm.congr g Q) where
  symm_weight x y := by
    simpa [LinearMap.BilinForm.congr_apply] using h.symm_weight (g.symm x) (g.symm y)
  nondegenerate := (LinearMap.BilinForm.nondegenerate_congr_iff g).2 h.nondegenerate
  orthogonal p x hx y hy := by
    rw [HodgeStructureOn.smul_F, Submodule.mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    simpa using h.orthogonal p x hx y hy
  positive p x hx hx0 := by
    rw [HodgeStructureOn.smul_piece, Submodule.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rw [LinearEquiv.coe_coe] at hx0 ⊢
    rw [← integralEquivToComplex_commutes_conj,
      integralFormBaseChange_congr_integralEquivToComplex]
    exact h.positive p x hx fun hx' ↦ hx0 (by rw [hx', map_zero])

/-- A form polarizes a Hodge structure exactly when its transport along a lattice automorphism `g`
polarizes the transported Hodge structure `g • hs`. -/
theorem isPolarization_smul_iff (g : V ≃ₗ[ℤ] V) :
    IsPolarization hℂ (g • hs) (LinearMap.BilinForm.congr g Q) ↔ IsPolarization hℂ hs Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul g⟩
  have key : LinearMap.BilinForm.congr g⁻¹ (LinearMap.BilinForm.congr g Q) = Q := by
    rw [LinearMap.BilinForm.congr_congr, ← LinearEquiv.mul_eq_trans, inv_mul_cancel,
      LinearEquiv.one_eq_refl, LinearMap.BilinForm.congr_refl, LinearEquiv.refl_apply]
  have h' := h.smul g⁻¹
  rwa [inv_smul_smul, key] at h'

/-- An isometry of a polarizing form carries a Hodge structure it polarizes to another Hodge
structure it polarizes. -/
theorem IsPolarization.smul_of_mem_isometryGroup (h : IsPolarization hℂ hs Q) {g : V ≃ₗ[ℤ] V}
    (hg : g ∈ BilinForm.isometryGroup Q) : IsPolarization hℂ (g • hs) Q := by
  have h' := h.smul g
  rwa [BilinForm.mem_isometryGroup_iff_congr_eq.1 hg] at h'

/-- The action of a lattice automorphism preserves polarizability. -/
@[simp]
theorem isPolarizable_smul_iff (g : V ≃ₗ[ℤ] V) :
    IsPolarizable hℂ (g • hs) ↔ IsPolarizable hℂ hs := by
  suffices ∀ (g : V ≃ₗ[ℤ] V) (hs : HodgeStructure hℂ n),
      IsPolarizable hℂ hs → IsPolarizable hℂ (g • hs) from
    ⟨fun h ↦ by simpa using this g⁻¹ _ h, this g hs⟩
  intro g hs h
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  exact Polarization.isPolarizable ⟨_, P.isPolarization.smul g⟩

end Polarization

namespace PeriodDomain.Point

variable [Module.Free ℤ V] [Module.Finite ℤ V] {Qint : LinearMap.BilinForm ℤ V}
  {htype : HodgeType}

/-- An isometry `g` of the fixed form moves a point of the period domain: `g • D` has the Hodge
structure `g • D.hs`, which `Qint` still polarizes and which has the same Hodge numbers. -/
noncomputable instance instSMul :
    SMul (BilinForm.isometryGroup Qint) (PeriodDomain.Point hℂ n Qint htype) where
  smul g D :=
    { hs := (g : V ≃ₗ[ℤ] V) • D.hs
      htype_weight := D.htype_weight
      pol := D.pol.smul_of_mem_isometryGroup g.2
      hodge_numbers p := by rw [HodgeStructureOn.hodgeNumber_smul, D.hodge_numbers] }

/-- The Hodge structure of `g • D` is `g • D.hs`. -/
@[simp]
theorem smul_hs (g : BilinForm.isometryGroup Qint) (D : PeriodDomain.Point hℂ n Qint htype) :
    (g • D).hs = (g : V ≃ₗ[ℤ] V) • D.hs :=
  (rfl)

/-- **The symmetry group of the period domain.** The isometry group `Aut(V, Qint)` of the fixed
form acts on the period domain of `(V, Qint)` at any Hodge type. -/
noncomputable instance instMulAction :
    MulAction (BilinForm.isometryGroup Qint) (PeriodDomain.Point hℂ n Qint htype) where
  one_smul D := ext <| by simp
  mul_smul g h D := ext <| by simp [mul_smul]

end PeriodDomain.Point

end TauCeti.Hodge
