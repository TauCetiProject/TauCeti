/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Order.BigOperators.Expect
public import TauCeti.GroupTheory.Amenable.Multiplicative

/-!
# Finite averages; finite groups are amenable

For a finite nonempty subset `F` of a topological group `G`, averaging over `F`,

```text
m_F f = 𝔼 x ∈ F, f x = |F|⁻¹ ∑_{x ∈ F} f x,
```

is a mean on `TauCeti.UCB G`. On a finite group, the average over the whole group,

```text
m f = 𝔼 x, f x = (∑ x, f x) / |G|,
```

is the uniform mean. It is left invariant because `x ↦ g⁻¹ * x` permutes `G`, so every
finite topological group is amenable, whatever its topology.

Conversely, the uniform mean is the only left-invariant mean on a finite group: the sum
`∑ g, L_g f` of the left translates of `f` is the constant function `∑ x, f x`
(`TauCeti.UCB.sum_leftTranslation`), so a left-invariant mean `m` satisfies
`|G| * m f = ∑ x, f x`. In particular, on a group with one element the uniform
mean is evaluation at that element.

Additive counterparts are provided for `TauCeti.AddMean` and `TauCeti.AddAmenable`.

## Main definitions

* `TauCeti.Mean.average F hF`: the average over a finite nonempty set `F`, as a mean.
* `TauCeti.Mean.uniform G`: the normalized counting mean `f ↦ 𝔼 x, f x` on a finite group.
* `TauCeti.AddMean.average`, `TauCeti.AddMean.uniform`: additive counterparts.

## Main results

* `TauCeti.Mean.average_singleton`: the average over a singleton is point evaluation.
* `TauCeti.Mean.average_univ`: the average over the whole of a finite group is the uniform mean.
* `TauCeti.Mean.uniform_apply`, `TauCeti.Mean.uniform_apply_eq_sum_div_card`: the value of the
  uniform mean, for any choice of `Fintype` instance.
* `TauCeti.Mean.isLeftInvariant_uniform`: the uniform mean is left invariant.
* `TauCeti.Mean.isLeftInvariant_iff_eq_uniform`: it is the unique left-invariant mean.
* `TauCeti.Amenable.of_finite`: finite topological groups are amenable.
* Additive counterparts for `TauCeti.AddMean` and `TauCeti.AddAmenable.of_finite`.

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

/-- The average `f ↦ 𝔼 x ∈ F, f x` over a finite nonempty set `F ⊆ G`, as a mean on `UCB G`. -/
@[to_additive /-- The average `f ↦ 𝔼 x ∈ F, f x` over a finite nonempty `F ⊆ G`, on `AddUCB G`. -/]
def average (F : Finset G) (hF : F.Nonempty) : Mean G :=
  mk₀
    { toFun f := 𝔼 x ∈ F, (f : G →ᵇ ℝ) x
      map_add' f f' := by simp [Finset.expect_add_distrib]
      map_smul' c f := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun x _ => UCB.le_def.1 hf x)
    (by simp only [LinearMap.coe_mk, AddHom.coe_mk, ← eval_apply, map_one, Finset.expect_const hF])

section Average

variable {F : Finset G} (hF : F.Nonempty)

@[to_additive (attr := simp)]
theorem average_apply (f : UCB G) : average F hF f = 𝔼 x ∈ F, (f : G →ᵇ ℝ) x :=
  mk₀_apply _ _ _ f

/-- The average over `F` is the sum over `F` divided by the cardinality of `F`. -/
@[to_additive average_apply_eq_sum_div_card
/-- The average over `F` is the sum over `F` divided by the cardinality of `F`. -/]
theorem average_apply_eq_sum_div_card (f : UCB G) :
    average F hF f = (∑ x ∈ F, (f : G →ᵇ ℝ) x) / F.card := by
  rw [average_apply, Finset.expect_eq_sum_div_card]

/-- The average over a singleton `{x}` is evaluation at `x`. -/
@[to_additive (attr := simp) /-- The average over a singleton `{x}` is evaluation at `x`. -/]
theorem average_singleton (x : G) : average {x} (Finset.singleton_nonempty x) = eval G x :=
  ext fun f => by simp

end Average

section Uniform

variable [Finite G]

variable (G) in
/-- The normalized counting mean `f ↦ 𝔼 x, f x` on a finite topological group `G`. -/
@[to_additive /-- Normalized counting mean `f ↦ 𝔼 x, f x` on a finite additive group `G`. -/]
def uniform : Mean G :=
  letI := Fintype.ofFinite G
  average Finset.univ Finset.univ_nonempty

/-- The uniform mean is the average over the group. The `Fintype` instance is arbitrary. -/
@[to_additive (attr := simp) /-- Uniform mean on an additive group (`Fintype` is arbitrary). -/]
theorem uniform_apply [Fintype G] (f : UCB G) : uniform G f = 𝔼 x, (f : G →ᵇ ℝ) x := by
  simp only [uniform, average_apply]
  congr!

/-- On a finite group, the average over the whole group is the uniform mean. -/
@[to_additive (attr := simp) /-- Average over a finite additive group is the uniform mean. -/]
theorem average_univ [Fintype G] : average Finset.univ Finset.univ_nonempty = uniform G :=
  ext fun f => by simp

/-- The uniform mean is the sum over the group divided by its cardinality. The `Fintype` instance
is arbitrary. -/
@[to_additive uniform_apply_eq_sum_div_card
/-- Uniform mean as sum divided by cardinality (`Fintype` instance is arbitrary). -/]
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

end Uniform

end Mean

section Transport

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [Finite A]

/-- `Mean.multiplicativeEquiv` carries `Mean.uniform (Multiplicative A)` to `AddMean.uniform A`. -/
@[simp] theorem Mean.multiplicativeEquiv_uniform :
    Mean.multiplicativeEquiv A (Mean.uniform (Multiplicative A)) = AddMean.uniform A :=
  AddMean.ext fun f => by
    have := Fintype.ofFinite A
    simp only [multiplicativeEquiv_apply, uniform_apply, AddMean.uniform_apply,
      UCB.multiplicativeAlgEquiv_symm_apply]
    exact Fintype.expect_equiv Multiplicative.toAdd _ _ fun _ => rfl
/-- `(Mean.multiplicativeEquiv A).symm` carries `AddMean.uniform A` to `Mean.uniform`. -/
@[simp] theorem Mean.multiplicativeEquiv_symm_uniform :
    (Mean.multiplicativeEquiv A).symm (AddMean.uniform A) = Mean.uniform (Multiplicative A) :=
  (Mean.multiplicativeEquiv A).symm_apply_eq.2 Mean.multiplicativeEquiv_uniform.symm

/-- The uniform mean on a finite additive group is left invariant. -/
theorem AddMean.isLeftInvariant_uniform : (AddMean.uniform A).IsLeftInvariant := by
  rw [← Mean.multiplicativeEquiv_uniform]
  exact Mean.isLeftInvariant_multiplicativeEquiv_iff.2 Mean.isLeftInvariant_uniform
attribute [to_additive existing] Mean.isLeftInvariant_uniform

/-- A left-invariant mean on a finite additive group is the uniform mean. -/
theorem AddMean.IsLeftInvariant.eq_uniform {m : AddMean A} (hm : m.IsLeftInvariant) :
    m = AddMean.uniform A := by
  simpa using congrArg (Mean.multiplicativeEquiv A)
    (Mean.isLeftInvariant_multiplicativeEquiv_symm_iff.2 hm).eq_uniform
attribute [to_additive existing] Mean.IsLeftInvariant.eq_uniform

end Transport

namespace Mean

/-- On a finite group, the uniform mean is the unique left-invariant mean. -/
@[to_additive /-- On a finite additive group, the uniform mean is the only left-invariant mean. -/]
theorem isLeftInvariant_iff_eq_uniform [Finite G] {m : Mean G} :
    m.IsLeftInvariant ↔ m = uniform G :=
  ⟨IsLeftInvariant.eq_uniform, fun h => h ▸ isLeftInvariant_uniform⟩

/-- On a group with one element, the uniform mean is evaluation at that element. -/
@[to_additive /-- On a subsingleton additive group, the uniform mean is point evaluation. -/]
theorem uniform_eq_eval [Subsingleton G] (x : G) : uniform G = eval G x :=
  ext fun f => by
    have : Unique G := uniqueOfSubsingleton x
    rw [uniform_apply, Fintype.expect_eq_sum_div_card]
    simp [Unique.eq_default x]

end Mean

/-- A finite topological group is amenable, for any group topology. -/
@[to_additive /-- A finite additive topological group is amenable, for any additive group
topology. -/]
instance (priority := 100) Amenable.of_finite [Finite G] : Amenable G :=
  ⟨⟨Mean.uniform G, Mean.isLeftInvariant_uniform⟩⟩

/-- `AddMean.additiveEquiv` sends the uniform mean on `Additive G` to `Mean.uniform G`. -/
@[simp] theorem AddMean.additiveEquiv_uniform [Finite G] :
    AddMean.additiveEquiv G (AddMean.uniform (Additive G)) = Mean.uniform G :=
  (AddMean.isLeftInvariant_additiveEquiv_iff.2 AddMean.isLeftInvariant_uniform).eq_uniform

/-- `(AddMean.additiveEquiv G).symm` sends `Mean.uniform G` to the uniform mean on `Additive G`. -/
@[simp] theorem AddMean.additiveEquiv_symm_uniform [Finite G] :
    (AddMean.additiveEquiv G).symm (Mean.uniform G) = AddMean.uniform (Additive G) :=
  (AddMean.isLeftInvariant_additiveEquiv_symm_iff.2 Mean.isLeftInvariant_uniform).eq_uniform

end TauCeti
