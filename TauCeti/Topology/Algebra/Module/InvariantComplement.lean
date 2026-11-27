/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Invariant topological complements

Let a finite group `G` act on a topological module `M` by continuous linear maps,
`ρ : G →* M →L[R] M`, and suppose that the order of `G` is invertible in `R`. This file proves the
topological form of the averaging step in Maschke's theorem (`LinearMap.equivariantProjection`, for
modules over the group algebra, which does not track continuity): a `G`-invariant submodule `p`
with a topological complement has a `G`-invariant topological complement
(`Submodule.ClosedComplemented.exists_isTopCompl_forall_mapsTo`). Starting from any continuous
projection `P` onto `p`, the average `(1 / |G|) ∑_g ρ g ∘ P ∘ ρ g⁻¹` is again a continuous
projection onto `p`, and it commutes with the action, so its kernel is invariant.

This is a linear input of an equivariant Lyapunov–Schmidt reduction: for a Fredholm operator
intertwining two such actions, it gives splittings of the domain and the codomain into invariant
summands.

## Main results

* `Submodule.ClosedComplemented.exists_isTopCompl_forall_mapsTo`: an invariant complemented
  submodule has an invariant topological complement.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42,
  Springer, 1977, §1.3 (the averaged projection).
-/

public section

open Set

namespace Submodule

section Average

variable {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [Group G] [Finite G]

/-- **Invariant topological complements.** Let a finite group `G`, whose order is invertible in
`R`, act on `M` by continuous linear maps. A `G`-invariant submodule with a topological complement
has a `G`-invariant topological complement. -/
theorem ClosedComplemented.exists_isTopCompl_forall_mapsTo (hG : IsUnit (Nat.card G : R))
    {p : Submodule R M} (ρ : G →* M →L[R] M) (hp : p.ClosedComplemented)
    (hρ : ∀ g, MapsTo (ρ g) p p) : ∃ q, IsTopCompl p q ∧ ∀ g, MapsTo (ρ g) q q := by
  have := Fintype.ofFinite G
  obtain ⟨P, hP⟩ := hp
  -- The averaged projection `x ↦ (1 / |G|) ∑_g ρ g (P (ρ g⁻¹ x))`, valued in `p`.
  let A : M →L[R] p := (↑hG.unit⁻¹ : R) •
    ∑ g, ((ρ g).restrict fun x hx ↦ hρ g hx).comp (P.comp (ρ g⁻¹))
  have hA (x : M) : (A x : M) = (↑hG.unit⁻¹ : R) • ∑ g, ρ g (P (ρ g⁻¹ x)) := by
    simp [A]
  have hinv (g : G) (x : M) : ρ g (ρ g⁻¹ x) = x := by
    simp [← mul_apply_eq_comp, ← map_mul]
  have hAp (x : p) : A x = x := by
    refine Subtype.ext ?_
    have hterm (g : G) : ρ g (P (ρ g⁻¹ x)) = x := by
      have hPx : P (ρ g⁻¹ x) = ⟨ρ g⁻¹ x, hρ g⁻¹ x.property⟩ := hP ⟨_, _⟩
      rw [hPx, hinv]
    simp [hA, hterm, ← Nat.cast_smul_eq_nsmul R, smul_smul]
  -- The averaged projection commutes with the action.
  have hAρ (h : G) (x : M) : (A (ρ h x) : M) = ρ h (A x) := by
    rw [hA, hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g ↦ ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, mul_apply_eq_comp, hinv]
  refine ⟨A.ker, A.isTopCompl_of_proj hAp, fun g x hx ↦ ?_⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  exact Subtype.ext (by rw [hAρ, hx, ZeroMemClass.coe_zero, map_zero])

end Average

end Submodule
