/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Coset sums of coinduced invariants

For a continuous representation `π` of `G` on `V`, Mathlib's coinduced representation
`π.coind₁` acts on `C(G, V)` by `(g • f) x = π g (f (g⁻¹ * x))`, so an invariant `f` satisfies
`π g (f x) = f (g * x)`. Evaluation at a point does not carry invariants of `π.coind₁` to
invariants of `π`, but a sum of evaluations over a transversal of a finite-index subgroup `U` does,
as soon as `f` is invariant under right translation by `U`: left multiplication by `g` permutes the
cosets of `U`, and right translation by `U` absorbs the change of representatives.

## Main results

* `ContRepresentation.sum_apply_out_mem_invariants`: summing an invariant element of the coinduced
  representation `C(G, V)` over a transversal of a finite-index subgroup stabilizing it under right
  translation gives an invariant element of `V`.
-/

public section

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [TopologicalSpace R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul R V]

/-- **Coset sums of coinduced invariants are invariant.** Let `f : C(G, V)` be invariant for the
coinduced representation `π.coind₁` and invariant under right translation by a finite-index
subgroup `U`. Then the sum of `f` over the transversal of `U` given by `Quotient.out` is invariant
for `π`. -/
theorem sum_apply_out_mem_invariants {π : ContRepresentation R G V} {f : C(G, V)}
    (hf : f ∈ π.coind₁.invariants) {U : Subgroup G} [Fintype (G ⧸ U)]
    (hU : U ≤ TauCeti.rightTranslationStabilizer f) :
    ∑ q : G ⧸ U, f q.out ∈ π.invariants := by
  intro g
  rw [map_sum]
  refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_
  -- invariance of `f` for `π.coind₁` moves `π g` inside: `π g (f y) = f (g * y)`
  have hπ : π g (f q.out) = f (g * q.out) := by
    simpa only [ContRepresentation.coind₁_apply_apply, inv_mul_cancel_left]
      using DFunLike.congr_fun (hf g) (g * q.out)
  -- `(g • q).out` and `g * q.out` differ by an element of `U` on the right
  obtain ⟨u, hu⟩ : ∃ u : U, g * q.out * u = (g • q).out :=
    ⟨⟨(g * q.out)⁻¹ * (g • q).out, QuotientGroup.eq.mp (QuotientGroup.mk_out_smul g q).symm⟩,
      by simp [mul_assoc]⟩
  rw [hπ, ← hu]
  exact ((TauCeti.mem_rightTranslationStabilizer.mp (hU u.2)) (g * q.out)).symm

end ContRepresentation
