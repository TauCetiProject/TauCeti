/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian

/-!
# Clifford multiplication between the half-spinors of an oriented four-space

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be
a finite-dimensional complex vector space with a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W`; write `c(v) = ρ (ι Q v)`. The chirality element `Γ`
(`CliffordAlgebra.chirality`) splits `W` into its `±1` eigenspaces `W⁺` and `W⁻`.

This file proves the facts about `Γ` and the generators that the linearized Seiberg–Witten
equations use. Each generator `c(v)` exchanges the two eigenspaces, and is injective for `v ≠ 0`
since `c(v)² = -‖v‖²`, so the eigenspaces have the same dimension. The main result: for a nonzero
`ψ` in one eigenspace, Clifford multiplication `v ↦ c(v) ψ` is a real-linear isomorphism of `V`
onto the other eigenspace when the eigenspaces have complex dimension two. It is injective
because `c(v) ψ = 0` forces `‖v‖² ψ = 0`, and both sides have real dimension four.

When `W` is moreover a Hermitian Clifford module, that is, a complex inner product space on which
the generators act skew-adjointly, `c(v)* = -c(v)`, the chirality `Γ` acts self-adjointly. On a
complex inner product space, a spinor `χ` of the opposite eigenspace with `Re ⟪c(v) ψ, χ⟫ = 0`
for every `v` vanishes. This is the pointwise step of the unique-continuation argument for the
cokernel of the linearized Seiberg–Witten map: the variations `a ↦ c(a) ψ` of the Dirac term force
such a cokernel element to vanish at every point where `ψ ≠ 0`.

The eigenspaces are stated for an arbitrary eigenvalue `ε`: `c(v)` maps the `ε`-eigenspace to
the `-ε`-eigenspace, and the case `ε = 1` is `W⁺ → W⁻`.

## Main definitions

* `TauCeti.SeibergWitten.cliffordMulEquiv`: for a nonzero `ψ` in a two-dimensional eigenspace of
  `Γ`, the real-linear isomorphism `v ↦ c(v) ψ` from `V` onto the opposite eigenspace.

## Main results

* `TauCeti.SeibergWitten.isSelfAdjoint_map_chirality`: `Γ* = Γ`.
* `TauCeti.SeibergWitten.map_ι_mem_eigenspace_chirality_neg`: `c(v)` maps the `ε`-eigenspace of
  `Γ` into the `-ε`-eigenspace.
* `TauCeti.SeibergWitten.finrank_eigenspace_chirality_neg`: the two eigenspaces have the same
  dimension.
* `TauCeti.SeibergWitten.eq_zero_of_forall_re_inner_map_ι_apply_eq_zero`: if
  `Re ⟪c(v) ψ, χ⟫ = 0` for all `v`, with `ψ ≠ 0` and `χ` in the opposite eigenspace, then `χ = 0`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1 and §5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Module.End
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The chirality element acts self-adjointly on a Hermitian Clifford module: `Γ* = Γ`. -/
theorem isSelfAdjoint_map_chirality {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsSelfAdjoint (ρ (chirality Q o)) := by
  rw [LinearMap.isSelfAdjoint_iff', adjoint_map_eq_map_star hρ, star_def, involute_chirality,
    reverse_chirality]

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- Clifford multiplication exchanges the eigenspaces of `Γ`: `c(v)` maps the `ε`-eigenspace into
the `-ε`-eigenspace. In particular it maps `W⁺` to `W⁻` and `W⁻` to `W⁺`. -/
theorem map_ι_mem_eigenspace_chirality_neg {ε : ℂ} {ψ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (v : V) :
    ρ (ι Q v) ψ ∈ eigenspace (ρ (chirality Q o)) (-ε) := by
  rw [mem_eigenspace_iff] at hψ ⊢
  rw [← Module.End.mul_apply, ← map_mul, chirality_mul_ι o hQ, map_neg, map_mul,
    LinearMap.neg_apply, Module.End.mul_apply, hψ, map_smul, neg_smul]

variable [FiniteDimensional ℂ W]

/-- Clifford multiplication by a nonzero vector embeds the `ε`-eigenspace of `Γ` into the
`-ε`-eigenspace. -/
private theorem finrank_eigenspace_chirality_le_neg (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (ε : ℂ) :
    finrank ℂ (eigenspace (ρ (chirality Q o)) ε) ≤
      finrank ℂ (eigenspace (ρ (chirality Q o)) (-ε)) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hinj := map_ι_injective ρ (v := v) (by simpa [hQ] using hv)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (ρ (ι Q v)).restrict fun _ hξ ↦ map_ι_mem_eigenspace_chirality_neg o hQ hξ v)
    fun ψ φ h ↦ Subtype.ext (hinj (congrArg Subtype.val h))

variable (ρ) in
/-- The two eigenspaces of `Γ` have the same dimension: `dim W⁻ = dim W⁺`. -/
theorem finrank_eigenspace_chirality_neg (ε : ℂ) :
    finrank ℂ (eigenspace (ρ (chirality Q o)) (-ε)) =
      finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  refine le_antisymm ?_ (finrank_eigenspace_chirality_le_neg o hQ ρ ε)
  have h := finrank_eigenspace_chirality_le_neg o hQ ρ (-ε)
  rwa [neg_neg] at h

/-- **Clifford multiplication by a nonzero spinor is a real isomorphism.** For a nonzero `ψ` in
the `ε`-eigenspace of `Γ`, when that eigenspace has complex dimension two, the real-linear map
`v ↦ c(v) ψ` is an isomorphism from `V` onto the `-ε`-eigenspace. For `ε = 1` this identifies
`V` with `W⁻`. -/
def cliffordMulEquiv {ε : ℂ} {ψ : W} (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (hψ₀ : ψ ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) :
    V ≃ₗ[ℝ] eigenspace (ρ (chirality Q o)) (-ε) :=
  LinearMap.linearEquivOfInjective
    { toFun v := ⟨ρ (ι Q v) ψ, map_ι_mem_eigenspace_chirality_neg o hQ hψ v⟩
      map_add' v w := by ext; simp
      map_smul' r v := by ext; simp }
    (fun v w h ↦ map_ι_apply_left_injective ρ (fun v hv ↦ by simpa [hQ] using hv) hψ₀
      (congrArg Subtype.val h))
    (by rw [finrank_real_of_complex, finrank_eigenspace_chirality_neg o hQ ρ, h₂,
      (Fact.out : finrank ℝ V = 4)])

/-- `cliffordMulEquiv` is Clifford multiplication: it sends `v` to `c(v) ψ`. -/
@[simp]
theorem coe_cliffordMulEquiv_apply {ε : ℂ} {ψ : W} (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε)
    (hψ₀ : ψ ≠ 0) (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (v : V) :
    (cliffordMulEquiv o hQ hψ hψ₀ h₂ v : W) = ρ (ι Q v) ψ :=
  (rfl)

end Module

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- If a spinor `χ` in the `-ε`-eigenspace of `Γ` is real-orthogonal to every Clifford multiple
`c(v) ψ` of a nonzero `ψ` in a two-dimensional `ε`-eigenspace, then `χ = 0`. For `ε = 1`: a
negative spinor with `Re ⟪c(v) ψ, χ⟫ = 0` for all `v` vanishes when the positive spinor `ψ` is
nonzero. -/
theorem eq_zero_of_forall_re_inner_map_ι_apply_eq_zero {ε : ℂ} {ψ χ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (hψ₀ : ψ ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (hχ : χ ∈ eigenspace (ρ (chirality Q o)) (-ε)) (h : ∀ v, (⟪ρ (ι Q v) ψ, χ⟫_ℂ).re = 0) :
    χ = 0 := by
  -- Write `χ = c(v) ψ` by surjectivity; then `‖χ‖² = Re ⟪χ, χ⟫ = 0`.
  set e := cliffordMulEquiv o hQ hψ hψ₀ h₂
  have hv := coe_cliffordMulEquiv_apply o hQ hψ hψ₀ h₂ (e.symm ⟨χ, hχ⟩)
  rw [LinearEquiv.apply_symm_apply] at hv
  have hχ₀ := h (e.symm ⟨χ, hχ⟩)
  rw [← hv, ← RCLike.re_to_complex, inner_self_eq_norm_sq] at hχ₀
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hχ₀)

end TauCeti.SeibergWitten
