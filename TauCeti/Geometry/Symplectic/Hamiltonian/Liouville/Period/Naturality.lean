/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.Lattice
import TauCeti.Geometry.Manifold.Flow.Related
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Naturality of the period lattice

Let `π : M → B` and `π₂ : M₂ → B₂` be regular Lagrangian torus fibrations
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`) for closed nondegenerate
two-forms `σ` and `σ₂`. Let `Ψ : M → M₂` be a smooth map with surjective differentials which pulls
`σ₂` back to `σ` and maps fibres to fibres, covering a map of the bases `g : B → B₂`:

`π₂ ∘ Ψ = g ∘ π`.

This file shows that `Ψ` intertwines the actions of the cotangent spaces on the fibres
(`IsLagrangianTorusFibration.fiberAction`): for a covector `α` at `g b` and a point `x` of the
fibre over `b`,

`Ψ ((α ∘ dg_b) +ᵥ x) = α +ᵥ Ψ x`

(`IsLagrangianTorusFibration.apply_fiberAction_comp_mfderiv`). Indeed, if `k` is a function on `B₂`
with `dk_(g b) = α`, then `k ∘ g` has differential `α ∘ dg_b` at `b`, and the pulled-back function
`(k ∘ g) ∘ π` is `(k ∘ π₂) ∘ Ψ`. Since `Ψ` pulls `σ₂` back to `σ`, it carries the Hamiltonian
vector field of `(k ∘ π₂) ∘ Ψ` to that of `k ∘ π₂`, so it conjugates their time-one maps. The map
of the bases is not assumed smooth: it is smooth because `π` is a surjective submersion.

Consequently `Ψ` relates the period lattices `Λ_b` and `Λ₂_(g b)`
(`IsLagrangianTorusFibration.periodLattice`) through the transpose of `dg_b`: if `α ∘ dg_b` lies in
`Λ_b`, then `α` lies in `Λ₂_(g b)`
(`IsLagrangianTorusFibration.mem_periodLattice_of_comp_mfderiv_mem`). When `Ψ` is injective on the
fibre over `b`, for instance when it is a symplectomorphism, the converse holds, and `Λ₂_(g b)` is
the preimage of `Λ_b` under precomposition with `dg_b`
(`IsLagrangianTorusFibration.comp_mfderiv_mem_periodLattice_iff`,
`IsLagrangianTorusFibration.periodLattice_eq_comap`). Injectivity cannot be dropped: the double
cover `(θ, I) ↦ (θ, I)` from `(ℝ / 2ℤ) × ℝ` to `(ℝ / ℤ) × ℝ`, with the form `dθ ∧ dI` and the
projections to `I`, has period lattices `2ℤ dI` and `ℤ dI`.

Over a common base, with `π₂ ∘ Ψ = π`, the map `Ψ` commutes with the actions of `T*_b B`
(`IsLagrangianTorusFibration.apply_fiberAction_of_comp_eq`), every period of the first fibration
is a period of the second (`IsLagrangianTorusFibration.periodLattice_le_of_comp_eq`), and a
fibrewise symplectomorphism preserves the period lattice
(`IsLagrangianTorusFibration.periodLattice_eq_of_comp_eq`). Thus the period lattice is an invariant
of a regular Lagrangian torus fibration up to fibrewise symplectomorphism.

All declarations are in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the action of `T*B` on the fibres and the period lattice).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B E₂ H₂ M₂ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [T2Space M₂] [BoundarylessManifold I₂ M₂] [I₂.Boundaryless]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}
  {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate}
  (h : hσ.IsLagrangianTorusFibration J π) (hσc : σ.IsClosed) (hσ₂c : σ₂.IsClosed)
  {Ψ : M → M₂} (hΨ : ContMDiff I I₂ ∞ Ψ) (hΨσ : SmoothForm.mpullback Ψ hΨ σ₂ = σ)
  (hΨs : ∀ x, Surjective (mfderiv I I₂ Ψ x))

section Base

variable {F₂ H₂' B₂ : Type*}
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂] [TopologicalSpace H₂']
  {J₂ : ModelWithCorners ℝ F₂ H₂'} [TopologicalSpace B₂] [ChartedSpace H₂' B₂]
  [IsManifold J₂ ∞ B₂] [T2Space B₂]
  {π₂ : M₂ → B₂} {g : B → B₂}

variable (hπ : π₂ ∘ Ψ = g ∘ π)
include hΨσ hΨs hπ

/-- **Fibre-preserving symplectic maps intertwine the fibre actions.** Let `Ψ` be a smooth map with
surjective differentials, pulling `σ₂` back to `σ`, which covers a map `g` of the bases. Then for a
covector `α` at `g b` and a point `x` of the fibre over `b`, the image under `Ψ` of the action of
`α ∘ dg_b` on `x` is the action of `α` on `Ψ x`. -/
theorem apply_fiberAction_comp_mfderiv (h₂ : hσ₂.IsLagrangianTorusFibration J₂ π₂) (b : B)
    (α : F₂ →L[ℝ] ℝ) (x : π ⁻¹' {b}) (y : π₂ ⁻¹' {g b}) (hxy : Ψ x = y) :
    Ψ (h.fiberAction hσc b (α.comp (mfderiv J J₂ g b)) x) = h₂.fiberAction hσ₂c (g b) α y := by
  -- The base map is smooth, since `g ∘ π = π₂ ∘ Ψ` and `π` is a surjective submersion.
  have hg : ContMDiff J J₂ ∞ g :=
    (h.isSubmersion.contMDiff_comp_iff h.surjective le_rfl).1 (hπ ▸ h₂.contMDiff.comp hΨ)
  -- A smooth function `k` on `B₂` with differential `α` at `g b`.
  obtain ⟨k, hk, -, -, -, hkα⟩ :=
    exists_contMDiff_hasCompactSupport_mvfderiv_eq (I := J₂) (g b) (0 : ℝ) α Filter.univ_mem
  have hk2 : ContMDiff J₂ 𝓘(ℝ) 2 k := hk.of_le (by simp)
  have hkg : ContMDiff J 𝓘(ℝ) 2 (k ∘ g) := hk2.comp (hg.of_le (by simp))
  have hkgα : mvfderiv J (k ∘ g) b = (α.comp (mfderiv J J₂ g b) : F →L[ℝ] ℝ) := by
    rw [mvfderiv_comp b ((hk (g b)).mdifferentiableAt (by simp))
      ((hg b).mdifferentiableAt (by simp)), hkα]
    -- The two sides differ only in reading the tangent spaces of `B` and `B₂` as their models.
    rfl
  have hcomp : (k ∘ g) ∘ π = (k ∘ π₂) ∘ Ψ := by rw [comp_assoc, ← hπ, comp_assoc]
  rw [h.coe_fiberAction_eq_flowOf hσc b hkg hkgα, h₂.coe_fiberAction_eq_flowOf hσ₂c (g b) hk2 hkα,
    ← hxy]
  -- `Ψ` carries the Hamiltonian vector field of `(k ∘ g) ∘ π = (k ∘ π₂) ∘ Ψ` to that of `k ∘ π₂`,
  -- so it conjugates their flows; the first field is complete since `π` is proper.
  have hX := h.isCompleteVectorField_hamiltonianVectorField_comp h.isProperMap hkg
  rw [hcomp] at hX ⊢
  exact (hΨ.mdifferentiable (by simp)).apply_flowOf
    (h₂.contMDiff_hamiltonianVectorField_comp hk2)
    (fun z ↦ hσ.mfderiv_hamiltonianVectorField_comp hσ₂ hΨ hΨσ (hΨs z)
      (((hk.comp h₂.contMDiff) (Ψ z)).mdifferentiableAt (by simp)))
    (hX.mem_flowDomain 1 x)

/-- **Fibre-preserving symplectic maps send periods to periods.** Under the hypotheses of
`apply_fiberAction_comp_mfderiv`, if `α ∘ dg_b` lies in the period lattice at `b`, then `α` lies in
the period lattice at `g b`. -/
theorem mem_periodLattice_of_comp_mfderiv_mem (h₂ : hσ₂.IsLagrangianTorusFibration J₂ π₂)
    {b : B} {α : F₂ →L[ℝ] ℝ}
    (hα : (α.comp (mfderiv J J₂ g b) : F →L[ℝ] ℝ) ∈ h.periodLattice hσc b) :
    α ∈ h₂.periodLattice hσ₂c (g b) := by
  obtain ⟨x⟩ := (h.isConnected_preimage_singleton b).nonempty.to_subtype
  let y : π₂ ⁻¹' {g b} := ⟨Ψ x, (congrFun hπ x).trans (congrArg g x.property)⟩
  rw [h₂.mem_periodLattice_iff_fiberAction_eq hσ₂c (g b) y, Subtype.ext_iff,
    ← h.apply_fiberAction_comp_mfderiv hσc hσ₂c hΨ hΨσ hΨs hπ h₂ b α x y rfl,
    (h.mem_periodLattice hσc b).1 hα x]

/-- **Fibre-preserving symplectomorphisms identify the period lattices.** Under the hypotheses of
`apply_fiberAction_comp_mfderiv`, if moreover `Ψ` is injective on the fibre over `b`, then
`α ∘ dg_b` lies in the period lattice at `b` exactly when `α` lies in the period lattice at
`g b`. -/
theorem comp_mfderiv_mem_periodLattice_iff (h₂ : hσ₂.IsLagrangianTorusFibration J₂ π₂) {b : B}
    (hΨb : InjOn Ψ (π ⁻¹' {b})) {α : F₂ →L[ℝ] ℝ} :
    (α.comp (mfderiv J J₂ g b) : F →L[ℝ] ℝ) ∈ h.periodLattice hσc b ↔
      α ∈ h₂.periodLattice hσ₂c (g b) := by
  refine ⟨h.mem_periodLattice_of_comp_mfderiv_mem hσc hσ₂c hΨ hΨσ hΨs hπ h₂, fun hα ↦ ?_⟩
  obtain ⟨x⟩ := (h.isConnected_preimage_singleton b).nonempty.to_subtype
  let y : π₂ ⁻¹' {g b} := ⟨Ψ x, (congrFun hπ x).trans (congrArg g x.property)⟩
  rw [h.mem_periodLattice_iff_fiberAction_eq hσc b x, Subtype.ext_iff]
  -- Both points of the fibre over `b` have the image `Ψ x`.
  refine hΨb (h.fiberAction hσc b _ x).property x.property ?_
  rw [h.apply_fiberAction_comp_mfderiv hσc hσ₂c hΨ hΨσ hΨs hπ h₂ b α x y rfl,
    (h₂.mem_periodLattice hσ₂c (g b)).1 hα y]

/-- **The period lattice is natural.** Under the hypotheses of `apply_fiberAction_comp_mfderiv`, if
moreover `Ψ` is injective on the fibre over `b`, then the period lattice at `g b` is the preimage of
the period lattice at `b` under precomposition with `dg_b`. -/
theorem periodLattice_eq_comap (h₂ : hσ₂.IsLagrangianTorusFibration J₂ π₂) {b : B}
    (hΨb : InjOn Ψ (π ⁻¹' {b})) :
    h₂.periodLattice hσ₂c (g b) =
      (h.periodLattice hσc b).comap
        ((ContinuousLinearMap.precomp ℝ (mfderiv J J₂ g b) : (F₂ →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ) :
          (F₂ →L[ℝ] ℝ) →+ F →L[ℝ] ℝ) :=
  AddSubgroup.ext fun _ ↦
    (h.comp_mfderiv_mem_periodLattice_iff hσc hσ₂c hΨ hΨσ hΨs hπ h₂ hΨb).symm

end Base

section SameBase

variable {π₂ : M₂ → B} (hπ : π₂ ∘ Ψ = π)
include hΨσ hΨs hπ

/-- **Fibrewise symplectic maps commute with the fibre actions.** Let `Ψ` be a smooth map with
surjective differentials, pulling `σ₂` back to `σ`, from one regular Lagrangian torus fibration to
another over the same base, `π₂ ∘ Ψ = π`. Then `Ψ` commutes with the actions of the covectors at
`b` on the fibres over `b`. -/
theorem apply_fiberAction_of_comp_eq (h₂ : hσ₂.IsLagrangianTorusFibration J π₂) (b : B)
    (α : F →L[ℝ] ℝ) (x : π ⁻¹' {b}) (y : π₂ ⁻¹' {b}) (hxy : Ψ x = y) :
    Ψ (h.fiberAction hσc b α x) = h₂.fiberAction hσ₂c b α y := by
  have := h.apply_fiberAction_comp_mfderiv hσc hσ₂c hΨ hΨσ hΨs (g := id) (by rwa [id_comp]) h₂ b
    α x y hxy
  -- `T_b B` is a type synonym of `F`, so `comp_id` applies to `α` after `mfderiv_id`.
  have hid : (α.comp (mfderiv J J id b) : F →L[ℝ] ℝ) = α := by
    rw [mfderiv_id]; exact α.comp_id
  rwa [hid] at this

/-- **Fibrewise symplectic maps send periods to periods.** Let `Ψ` be a smooth map with surjective
differentials, pulling `σ₂` back to `σ`, from one regular Lagrangian torus fibration to another over
the same base, `π₂ ∘ Ψ = π`. Then every period of the first fibration at `b` is a period of the
second. The inclusion can be strict when `Ψ` is not injective on the fibre, as for a fibrewise
double cover. -/
theorem periodLattice_le_of_comp_eq (h₂ : hσ₂.IsLagrangianTorusFibration J π₂) (b : B) :
    h.periodLattice hσc b ≤ h₂.periodLattice hσ₂c b := fun α hα ↦
  h.mem_periodLattice_of_comp_mfderiv_mem hσc hσ₂c hΨ hΨσ hΨs (g := id) (by rwa [id_comp]) h₂
    -- `T_b B` is a type synonym of `F`, so `comp_id` applies to `α` after `mfderiv_id`.
    (by rwa [show (α.comp (mfderiv J J id b) : F →L[ℝ] ℝ) = α by
      rw [mfderiv_id]; exact α.comp_id])

/-- **Fibrewise symplectomorphisms preserve the period lattice.** Let `Ψ` be a smooth map with
surjective differentials, pulling `σ₂` back to `σ`, from one regular Lagrangian torus fibration to
another over the same base, `π₂ ∘ Ψ = π`. If `Ψ` is injective on the fibre over `b`, for instance if
it is a symplectomorphism, the two fibrations have the same period lattice at `b`. -/
theorem periodLattice_eq_of_comp_eq (h₂ : hσ₂.IsLagrangianTorusFibration J π₂) {b : B}
    (hΨb : InjOn Ψ (π ⁻¹' {b})) :
    h₂.periodLattice hσ₂c b = h.periodLattice hσc b :=
  AddSubgroup.ext fun α ↦ by
    have := h.comp_mfderiv_mem_periodLattice_iff hσc hσ₂c hΨ hΨσ hΨs (g := id)
      (by rwa [id_comp]) h₂ hΨb (α := α)
    -- `T_b B` is a type synonym of `F`, so `comp_id` applies to `α` after `mfderiv_id`.
    have hid : (α.comp (mfderiv J J id b) : F →L[ℝ] ℝ) = α := by
      rw [mfderiv_id]; exact α.comp_id
    rw [hid] at this
    exact this.symm

end SameBase

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
