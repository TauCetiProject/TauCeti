/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.LinearAlgebra.Submodule.Relation

/-!
# Composition of linear Lagrangian relations

A linear canonical relation from `(V, ω₁)` to `(W, ω₂)` is a Lagrangian subspace
of `V × W` for `ω₁ ⊖ ω₂`. Composition is ordinary relational composition of
submodules, with the intermediate vector eliminated. In finite dimension it is
again Lagrangian, even when the matching intersection is not transverse and the
projection is not injective. The diagonal and symplectic graphs are the identity
and invertible examples from `TauCeti.Geometry.Symplectic.Lagrangian.Constructions`.

This is the tangent-space calculation for geometric composition of smooth
Lagrangian correspondences. It does not supply smoothness or embeddedness of a
set-theoretic geometric composite.

The proof intersects the product relation with the matching subspace, then
eliminates its characteristic directions. Orthogonal complementation exchanges
intersection and sum, so no transversality or dimension-of-intersection assumption
is needed in this linear calculation.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

namespace TauCeti.SymplecticForm

variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]
  {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {ω₃ : SymplecticForm U}
  {L : Submodule ℝ (V × W)} {K : Submodule ℝ (W × U)}

/-- Composition of isotropic linear relations is isotropic. No finite-dimensionality
or transversality hypothesis is needed. -/
theorem IsIsotropic.relComp (hL : (ω₁.twistedProd ω₂).IsIsotropic L)
    (hK : (ω₂.twistedProd ω₃).IsIsotropic K) :
    (ω₁.twistedProd ω₃).IsIsotropic (L.relComp K) := by
  rw [isIsotropic_iff] at hL hK ⊢
  simp only [Submodule.mem_relComp]
  rintro x ⟨y, hxy, hyx⟩ z ⟨w, hzw, hwz⟩
  have h₁ := hL (x.1, y) hxy (z.1, w) hzw
  have h₂ := hK (y, x.2) hyx (w, z.2) hwz
  simp only [twistedProd_apply] at h₁ h₂ ⊢
  linarith

/-- Composition of finite-dimensional linear Lagrangian relations is Lagrangian,
including compositions with excess matching directions. -/
theorem IsLagrangian.relComp [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ U] (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    (ω₁.twistedProd ω₃).IsLagrangian (L.relComp K) := by
  let Ω := (ω₁.twistedProd ω₂).prod (ω₂.twistedProd ω₃)
  let C : Submodule ℝ ((V × W) × (W × U)) :=
    LinearMap.ker ((LinearMap.snd ℝ V W).comp (LinearMap.fst ℝ (V × W) (W × U)) -
      (LinearMap.fst ℝ W U).comp (LinearMap.snd ℝ (V × W) (W × U)))
  have memC (z : (V × W) × (W × U)) : z ∈ C ↔ z.1.2 = z.2.1 := by
    simp [C, sub_eq_zero]
  -- The characteristic directions of the matching subspace have zero outer coordinates.
  have orthC (z : (V × W) × (W × U)) (hz : z ∈ Ω.orthogonal C) :
      z.1.1 = 0 ∧ z.1.2 = z.2.1 ∧ z.2.2 = 0 := by
    rw [mem_orthogonal_iff] at hz
    have hv : z.1.1 = 0 := ω₁.separatingRight _ fun v ↦ by
      simpa [Ω] using hz ((v, 0), (0, 0)) ((memC _).mpr rfl)
    have hu : z.2.2 = 0 := ω₃.separatingRight _ fun u ↦ by
      have hu := hz ((0, 0), (0, u)) ((memC _).mpr rfl)
      simpa [Ω] using hu
    have hw : z.1.2 = z.2.1 := by
      apply sub_eq_zero.mp
      apply ω₂.separatingRight
      intro w
      have hw := hz ((0, w), (w, 0)) ((memC _).mpr rfl)
      simp [Ω] at hw
      simp only [map_sub]
      linarith
    exact ⟨hv, hw, hu⟩
  rw [isLagrangian_iff]
  refine ⟨hL.isIsotropic.relComp hK.isIsotropic, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  let z : (V × W) × (W × U) := ((x.1, 0), (0, x.2))
  have hz : z ∈ Ω.orthogonal (L.prod K ⊓ C) := by
    rw [mem_orthogonal_iff]
    intro y hy
    have hmatch := (memC y).mp hy.2
    have hcomp : (y.1.1, y.2.2) ∈ L.relComp K :=
      Submodule.mem_relComp.mpr ⟨y.1.2, hy.1.1, hmatch ▸ hy.1.2⟩
    have hzero := (mem_orthogonal_iff.mp hx) _ hcomp
    simpa [Ω, z, sub_eq_add_neg] using hzero
  -- Orthogonality puts the lift in the product relation plus a characteristic direction.
  have hprod : Ω.orthogonal (L.prod K) = L.prod K :=
    le_antisymm (isCoisotropic_iff_le.mp (hL.prod hK).isCoisotropic)
      (isIsotropic_iff_le.mp (hL.prod hK).isIsotropic)
  have hsplit : z ∈ L.prod K ⊔ Ω.orthogonal C := by
    rw [orthogonal_def, Ω.toBilinForm.orthogonal_inf Ω.nondegenerate Ω.isRefl,
      ← orthogonal_def, ← orthogonal_def, hprod] at hz
    exact hz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsplit
  obtain ⟨hbv, hbw, hbu⟩ := orthC b hb
  have hav : a.1.1 = x.1 := by
    simpa [z, hbv] using congrArg (fun p : (V × W) × (W × U) ↦ p.1.1) hab
  have hau : a.2.2 = x.2 := by
    simpa [z, hbu] using congrArg (fun p : (V × W) × (W × U) ↦ p.2.2) hab
  have haw : a.1.2 = a.2.1 := by
    have h₁ := congrArg (fun p : (V × W) × (W × U) ↦ p.1.2) hab
    have h₂ := congrArg (fun p : (V × W) × (W × U) ↦ p.2.1) hab
    dsimp [z] at h₁ h₂
    rw [← hbw] at h₂
    exact add_right_cancel (h₁.trans h₂.symm)
  apply Submodule.mem_relComp.mpr
  exact ⟨a.1.2, hav ▸ ha.1, hau ▸ haw ▸ ha.2⟩

end TauCeti.SymplecticForm
