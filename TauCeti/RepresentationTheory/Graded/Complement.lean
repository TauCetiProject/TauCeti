/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.DirectSum.Complement
public import TauCeti.RepresentationTheory.Invariants

/-!
# Homogeneous invariant complements

For a finite group of order invertible in a field, a homogeneous invariant subspace of a
representation graded by invariant pieces admits a homogeneous invariant complement.
Unlike applying Maschke's theorem to the whole representation, this splitting respects degree.
The representation and the set of degrees may both be infinite.

The construction averages a degree-preserving retraction using Mathlib's representation
`Representation.linHom` on linear maps and its averaging projection.
-/

public section

namespace Representation

variable {k G ι V : Type*} [Field k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)] [DecidableEq ι] [AddCommGroup V] [Module k V]

/-- A homogeneous invariant subspace has a homogeneous invariant complement when the finite
group order is invertible. All pieces of the grading must be invariant. -/
theorem exists_isCompl_isHomogeneous_of_invariant
    (ρ : Representation k G V) (𝒱 : ι → Submodule k V) [DirectSum.Decomposition 𝒱]
    (h𝒱 : ∀ g i, Set.MapsTo (ρ g) (𝒱 i) (𝒱 i))
    (U : Submodule k V) (hU : DirectSum.SetLike.IsHomogeneous 𝒱 U)
    (hρU : ∀ g, Set.MapsTo (ρ g) U U) :
    ∃ H : Submodule k V, IsCompl U H ∧ DirectSum.SetLike.IsHomogeneous 𝒱 H ∧
      ∀ g, Set.MapsTo (ρ g) H H := by
  obtain ⟨p, hp, hpdeg⟩ := U.exists_graded_retraction 𝒱 hU
  let q := U.subtype ∘ₗ p
  let P := (linHom ρ ρ).averageMap q
  have hP_apply (x : V) : P x =
      ⅟(Fintype.card G : k) • ∑ g : G, ρ g (q (ρ g⁻¹ x)) := by
    simp only [P, averageMap_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      linHom_apply, LinearMap.comp_apply]
  have hPmem (x : V) : P x ∈ U := by
    rw [hP_apply]
    exact U.smul_mem _ <| U.sum_mem fun g _ ↦ hρU g (p (ρ g⁻¹ x)).2
  have hPdeg : ∀ i, Set.MapsTo P (𝒱 i) (𝒱 i) := by
    intro i x hx
    rw [hP_apply]
    exact (𝒱 i).smul_mem _ <| (𝒱 i).sum_mem fun g _ ↦
      h𝒱 g i (hpdeg i _ (h𝒱 g⁻¹ i hx))
  have hPid (x : U) : P x = x := by
    have hq (g : G) : q (ρ g⁻¹ x) = ρ g⁻¹ x := by
      exact congrArg U.subtype (hp ⟨_, hρU g⁻¹ x.2⟩)
    rw [hP_apply]
    simp only [hq, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, invOf_mul_self, one_smul]
  have hcomm : IsIntertwiningMap ρ ρ P :=
    (mem_linHom_invariants_iff_isIntertwining P).1 ((linHom ρ ρ).averageMap_invariant q)
  let P' : V →ₗ[k] U := P.codRestrict U hPmem
  have hker : LinearMap.ker P' = LinearMap.ker P := LinearMap.ker_codRestrict U P hPmem
  refine ⟨LinearMap.ker P, ?_, P.isHomogeneous_ker_of_mapsTo 𝒱 hPdeg, ?_⟩
  · rw [← hker]
    exact LinearMap.isCompl_of_proj (fun x ↦ Subtype.ext (hPid x))
  · intro g x hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
    rw [hcomm.isIntertwining, hx, map_zero]

end Representation
