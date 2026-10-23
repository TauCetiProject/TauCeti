/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import TauCeti.GroupTheory.Amenable.Basic

/-!
# Finite groups are amenable

On a finite topological group `G`, averaging over the group,

```text
m f = 𝔼 x, f x = (∑ x, f x) / |G|,
```

is a mean on `TauCeti.UCB G`. It is left invariant because `x ↦ g⁻¹ * x` permutes `G`, so every
finite topological group is amenable, whatever its topology.

Conversely, the uniform mean is the only left-invariant mean on a finite group: the sum
`∑ g, L_g f` of the left translates of `f` is the constant function `∑ x, f x`
(`TauCeti.UCB.sum_leftTranslation`), so a left-invariant mean `m` satisfies
`|G| * m f = ∑ x, f x`. In particular, on a group with one element the uniform
mean is evaluation at that element.

## Main definitions

* `TauCeti.Mean.uniform G`: the normalized counting mean `f ↦ 𝔼 x, f x` on a finite group.

## Main results

* `TauCeti.Mean.uniform_apply`, `TauCeti.Mean.uniform_apply_eq_sum_div_card`: the value of the
  uniform mean, for any choice of `Fintype` instance.
* `TauCeti.Mean.isLeftInvariant_uniform`: the uniform mean is left invariant.
* `TauCeti.Mean.isLeftInvariant_iff_eq_uniform`: it is the unique left-invariant mean.
* `TauCeti.Amenable.of_finite`: finite topological groups are amenable.

## References

* A. Garrido, *An introduction to amenable groups*, §1.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction BigOperators

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace Mean

section Uniform

variable [Finite G]

variable (G) in
/-- The normalized counting mean `f ↦ 𝔼 x, f x` on a finite topological group `G`. -/
def uniform : Mean G :=
  letI := Fintype.ofFinite G
  mk₀
    { toFun f := 𝔼 x, (f : G →ᵇ ℝ) x
      map_add' f f' := by simp [Finset.expect_add_distrib]
      map_smul' c f := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun x _ => UCB.le_def.1 hf x)
    (by simp)

/-- The uniform mean is the average over the group. The `Fintype` instance is arbitrary. -/
@[simp]
theorem uniform_apply [Fintype G] (f : UCB G) : uniform G f = 𝔼 x, (f : G →ᵇ ℝ) x := by
  simp only [uniform, mk₀_apply, LinearMap.coe_mk, AddHom.coe_mk]
  congr!

/-- The uniform mean is the sum over the group divided by its cardinality. The `Fintype` instance
is arbitrary. -/
theorem uniform_apply_eq_sum_div_card [Fintype G] (f : UCB G) :
    uniform G f = (∑ x, (f : G →ᵇ ℝ) x) / Fintype.card G := by
  rw [uniform_apply, Fintype.expect_eq_sum_div_card]

/-- The uniform mean is left invariant, since left multiplication permutes the group. -/
theorem isLeftInvariant_uniform : (uniform G).IsLeftInvariant := by
  have := Fintype.ofFinite G
  refine isLeftInvariant_iff.2 fun g f => ?_
  simp only [uniform_apply, UCB.leftTranslation_apply]
  exact Fintype.expect_equiv (Equiv.mulLeft g⁻¹) _ _ fun _ => rfl

/-- A left-invariant mean on a finite group is the uniform mean. -/
theorem IsLeftInvariant.eq_uniform {m : Mean G} (hm : m.IsLeftInvariant) : m = uniform G := by
  have := Fintype.ofFinite G
  refine ext fun f => ?_
  have h := congr(m $(UCB.sum_leftTranslation f))
  simp only [map_sum, hm.apply_leftTranslation, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, map_algebraMap] at h
  rw [uniform_apply_eq_sum_div_card, ← h, mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-- On a finite group, the uniform mean is the unique left-invariant mean. -/
theorem isLeftInvariant_iff_eq_uniform {m : Mean G} : m.IsLeftInvariant ↔ m = uniform G :=
  ⟨IsLeftInvariant.eq_uniform, fun h => h ▸ isLeftInvariant_uniform⟩

end Uniform

/-- On a group with one element, the uniform mean is evaluation at that element. -/
theorem uniform_eq_eval [Subsingleton G] (x : G) : uniform G = eval G x :=
  ext fun f => by
    have : Unique G := uniqueOfSubsingleton x
    rw [uniform_apply, Fintype.expect_eq_sum_div_card]
    simp [Unique.eq_default x]

end Mean

/-- A finite topological group is amenable, for any group topology. -/
instance (priority := 100) Amenable.of_finite [Finite G] : Amenable G :=
  ⟨⟨Mean.uniform G, Mean.isLeftInvariant_uniform⟩⟩

end TauCeti
