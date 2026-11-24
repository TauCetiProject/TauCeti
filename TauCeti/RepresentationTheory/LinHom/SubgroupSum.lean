/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Sums of the conjugation action over a subgroup

Let `ρ` be a representation of a group `G` on `V`, let `σ = Representation.linHom ρ ρ` be the
conjugation action `σ g f = ρ g ∘ f ∘ ρ g⁻¹` of `G` on `End V`, and let `N` be a finite subgroup
of `G`. Every value of the sum `S = ∑ n ∈ N, σ n` commutes with the action of `N`. When the
`N`-equivariant endomorphisms of `V` form a line, as they do by Schur's lemma when `ρ` restricts
irreducibly to `N` over an algebraically closed field, every value of `S` is therefore a scalar,
and so is fixed by `σ g` for every `g ∈ G`, not only for `g ∈ N`
(`Representation.linHom_mul_sum_linHom_eq`).

This is the step in the proof of Gallagher's correspondence that computes the norm of a character
on a coset of `N`.
-/

public section

namespace Representation

open Module

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **Sums of the conjugation action over a subgroup are `G`-invariant under Schur's condition**:
if the `N`-equivariant endomorphisms of `V` form a line, then `σ g ∘ S = S` for every `g ∈ G`,
where `σ = Representation.linHom ρ ρ` and `S = ∑ n ∈ N, σ n`. -/
theorem linHom_mul_sum_linHom_eq (ρ : Representation k G V) (N : Subgroup G) [Fintype N]
    (hfin : finrank k (IntertwiningMap (ρ.comp N.subtype) (ρ.comp N.subtype)) = 1)
    (g : G) : linHom ρ ρ g * ∑ n : N, linHom ρ ρ n = ∑ n : N, linHom ρ ρ n := by
  let ρN : Representation k N V := ρ.comp N.subtype
  have hid : IntertwiningMap.id ρN ≠ 0 := fun h0 => by
    have : Subsingleton (IntertwiningMap ρN ρN) := ⟨fun φ ψ => by
      ext v
      have hv : v = 0 := by simpa using DFunLike.congr_fun h0 v
      simp [hv]⟩
    simp [finrank_zero_of_subsingleton] at hfin
  set σ := linHom ρ ρ
  set S : Module.End k (V →ₗ[k] V) := ∑ n : N, σ n
  refine LinearMap.ext fun f => ?_
  -- Every value of `S` commutes with `N`, since left multiplication by `m ∈ N` permutes `N`.
  have hinv (m : N) : σ m (S f) = S f := by
    simp only [S, LinearMap.sum_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft m) _ _ fun n => by
      rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, mul_apply_eq_comp]
  let φ : IntertwiningMap ρN ρN :=
    { toLinearMap := S f
      isIntertwining' := fun m => LinearMap.ext fun v => by
        simpa [σ, linHom_apply, ρN] using congr($(hinv m) (ρ m v)).symm }
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hid).mp hfin φ
  have hSf : S f = c • LinearMap.id := congr(($hc).toLinearMap).symm
  refine LinearMap.ext fun v => ?_
  simp [hSf, σ, linHom_apply]

end Representation
