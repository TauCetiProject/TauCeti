/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.RingTheory.Idempotents.SquareRootOne

import TauCeti.LinearAlgebra.End.Basic

/-!
# The eigenspace projections of an involution

Let `g` be an involution of a module `Y` over a commutative ring `k` in which `2` is invertible,
and let `μ : k` with `μ * μ = 1`. Then `μ • g` squares to `1`, so `½ (1 + μ g)`
(`TauCeti.halfOneAdd k (μ • g)`) projects `Y` onto the `μ`-eigenspace of `g`. It fixes that
eigenspace and kills the `-μ`-eigenspace, and the projections for `μ` and `-μ` add up to the
identity.

## Main definitions

* `Module.End.eigenProjOfInvolutive`: the projection `½ (1 + μ g) : Y → Eig(g, μ)`.

## Main results

* `Module.End.coe_eigenProjOfInvolutive_apply`: the projection is `y ↦ ½ (y + μ g y)`.
* `Module.End.eigenProjOfInvolutive_apply_of_mem`: it fixes the `μ`-eigenspace.
* `Module.End.eigenProjOfInvolutive_apply_of_mem_neg`: it kills the `ν`-eigenspace for `μ ν = -1`.
* `Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg`: the projections for `μ` and
  `-μ` add up to the identity.
* `Module.End.disjoint_eigenspace_neg`: the `μ`- and `-μ`-eigenspaces of an endomorphism are
  disjoint when `2 * μ` acts injectively on the module.
* `Module.End.inf_eigenspace_sup_inf_eigenspace_neg`: an invariant submodule of an involution
  splits as the supremum of its intersections with the `μ`- and `-μ`-eigenspaces (`μ * μ = 1`).
-/

public section

noncomputable section

namespace Module.End

open TauCeti

variable {k Y : Type*} [CommRing k] [Invertible (2 : k)] [AddCommGroup Y] [Module k Y]
  {g : Module.End k Y}

/-- The projection `½ (1 + μ g)` of `Y` onto the `μ`-eigenspace of an involution `g`, for
`μ * μ = 1`. -/
def eigenProjOfInvolutive (hg : Function.Involutive g) {μ : k} (hμ : μ * μ = 1) :
    Y →ₗ[k] g.eigenspace μ :=
  LinearMap.codRestrict _ (halfOneAdd k (μ • g)) fun y ↦ by
    have h : g * halfOneAdd k (μ • g) = μ • halfOneAdd k (μ • g) := by
      conv_rhs => rw [← mul_halfOneAdd k (smul_mul_smul_self_eq_one hg hμ)]
      rw [smul_mul_assoc, smul_smul, hμ, one_smul]
    exact mem_eigenspace_iff.2 (LinearMap.congr_fun h y)

/-- The projection onto the `μ`-eigenspace of an involution is `y ↦ ½ (y + μ g y)`. -/
@[simp]
theorem coe_eigenProjOfInvolutive_apply (hg : Function.Involutive g) {μ : k} (hμ : μ * μ = 1)
    (y : Y) : (eigenProjOfInvolutive hg hμ y : Y) = (⅟2 : k) • (y + μ • g y) := by
  simp [eigenProjOfInvolutive, halfOneAdd_def]

/-- The projection onto the `μ`-eigenspace fixes the `μ`-eigenspace. -/
@[simp]
theorem eigenProjOfInvolutive_apply_of_mem (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) (y : g.eigenspace μ) : eigenProjOfInvolutive hg hμ y = y := by
  apply Subtype.ext
  rw [coe_eigenProjOfInvolutive_apply, mem_eigenspace_iff.1 y.property, smul_smul, hμ, one_smul,
    ← two_smul k, invOf_smul_smul]

/-- The projection onto the `μ`-eigenspace kills the `ν`-eigenspace when `μ ν = -1`, that is, when
`ν = -μ`. -/
@[simp]
theorem eigenProjOfInvolutive_apply_of_mem_neg (hg : Function.Involutive g) {μ ν : k}
    (hμ : μ * μ = 1) (hν : μ * ν = -1) (y : g.eigenspace ν) :
    eigenProjOfInvolutive hg hμ y = 0 := by
  apply Subtype.ext
  rw [coe_eigenProjOfInvolutive_apply, mem_eigenspace_iff.1 y.property, smul_smul, hν, neg_one_smul,
    add_neg_cancel, smul_zero, ZeroMemClass.coe_zero]

/-- The projections onto the `μ`- and `-μ`-eigenspaces of an involution add up to the identity. -/
theorem eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg (hg : Function.Involutive g) {μ : k}
    (hμ : μ * μ = 1) (hμ' : -μ * -μ = 1) (y : Y) :
    (eigenProjOfInvolutive hg hμ y : Y) + eigenProjOfInvolutive hg hμ' y = y := by
  have h := halfOneAdd_add_halfOneAdd_neg k (μ • g)
  rw [← neg_smul] at h
  exact LinearMap.congr_fun h y

variable (g) in
omit [Invertible (2 : k)] in
/-- The `μ`- and `-μ`-eigenspaces of an endomorphism are disjoint whenever `2 * μ` acts injectively
on `Y` (for instance when `2` and `μ` are units, as for `IsUnit (2 : k)` and `μ * μ = 1`). -/
theorem disjoint_eigenspace_neg {μ : k} (h : IsSMulRegular Y (2 * μ)) :
    Disjoint (g.eigenspace μ) (g.eigenspace (-μ)) :=
  Submodule.disjoint_def.mpr fun y hy₁ hy₂ ↦ h <| show (2 * μ) • y = (2 * μ) • 0 by
    rw [smul_zero, two_mul, add_smul]; nth_rw 1 [← mem_eigenspace_iff.mp hy₁]
    rw [mem_eigenspace_iff.mp hy₂, neg_smul, neg_add_cancel]

omit [Invertible (2 : k)] in
/-- An invariant submodule of an involution over a commutative ring in which `2` is a unit is the
supremum of its intersections with the `μ`- and `-μ`-eigenspaces (`μ * μ = 1`). -/
theorem inf_eigenspace_sup_inf_eigenspace_neg (h2 : IsUnit (2 : k)) (hg : Function.Involutive g)
    {μ : k} (hμ : μ * μ = 1) {N : Submodule k Y} (hN : ∀ y ∈ N, g y ∈ N) :
    (N ⊓ g.eigenspace μ) ⊔ (N ⊓ g.eigenspace (-μ)) = N := by
  let := h2.invertible
  have hmem {ν : k} (hν : ν * ν = 1) {y : Y} (hy : y ∈ N) :
      (g.eigenProjOfInvolutive hg hν y : Y) ∈ N := by
    rw [coe_eigenProjOfInvolutive_apply]; exact N.smul_mem _ (N.add_mem hy (N.smul_mem _ (hN y hy)))
  have hμ' : -μ * -μ = 1 := (neg_mul_neg μ μ).trans hμ
  exact le_antisymm (sup_le inf_le_left inf_le_left) fun y hy ↦ Submodule.mem_sup.mpr
    ⟨_, ⟨hmem hμ hy, (g.eigenProjOfInvolutive hg hμ y).property⟩,
      _, ⟨hmem hμ' hy, (g.eigenProjOfInvolutive hg hμ' y).property⟩,
      g.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg hg hμ hμ' y⟩

end Module.End
