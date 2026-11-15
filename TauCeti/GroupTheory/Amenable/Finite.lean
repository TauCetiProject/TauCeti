/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.Amenable.Basic

/-!
# Finite averages; finite groups and finite-index extensions are amenable

For a finite nonempty subset `F` of a topological group `G`, averaging over `F`,

```text
m_F f = 𝔼 x ∈ F, f x = |F|⁻¹ ∑_{x ∈ F} f x,
```

is a mean on `TauCeti.UCB G`. On a finite group, the average over the whole group,

```text
m f = 𝔼 x, f x = (∑ x, f x) / |G|,
```

is the uniform mean. It is left invariant because `x ↦ g⁻¹ * x` permutes `G`, so every
finite topological group is amenable, whatever its topology. More generally, if `H ≤ G` is an
amenable finite-index subgroup, averaging the pushforward of a left-invariant mean on `H` over the
finite set of left cosets `G ⧸ H` gives a left-invariant mean on `G`.

Conversely, the uniform mean is the only left-invariant mean on a finite group: the sum
`∑ g, L_g f` of the left translates of `f` is the constant function `∑ x, f x`
(`TauCeti.UCB.sum_leftTranslation`), so a left-invariant mean `m` satisfies
`|G| * m f = ∑ x, f x`. In particular, on a group with one element the uniform
mean is evaluation at that element.

## Main definitions

* `TauCeti.Mean.average F hF`: the average over a finite nonempty set `F`, as a mean.
* `TauCeti.Mean.uniform G`: the normalized counting mean `f ↦ 𝔼 x, f x` on a finite group.

## Main results

* `TauCeti.Mean.average_singleton`: the average over a singleton is point evaluation.
* `TauCeti.Mean.average_univ`: the average over the whole of a finite group is the uniform mean.
* `TauCeti.Mean.uniform_apply`, `TauCeti.Mean.uniform_apply_eq_sum_div_card`: the value of the
  uniform mean, for any choice of `Fintype` instance.
* `TauCeti.Mean.isLeftInvariant_uniform`: the uniform mean is left invariant.
* `TauCeti.Mean.isLeftInvariant_iff_eq_uniform`: it is the unique left-invariant mean.
* `TauCeti.Amenable.of_finite`: finite topological groups are amenable.
* `TauCeti.Amenable.of_finiteIndex`: a topological group with an amenable finite-index subgroup is
  amenable.

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
def average (F : Finset G) (hF : F.Nonempty) : Mean G :=
  mk₀
    { toFun f := 𝔼 x ∈ F, (f : G →ᵇ ℝ) x
      map_add' f f' := by simp [Finset.expect_add_distrib]
      map_smul' c f := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun x _ => UCB.le_def.1 hf x)
    (by simp [hF])

section Average

variable {F : Finset G} (hF : F.Nonempty)

@[simp]
theorem average_apply (f : UCB G) : average F hF f = 𝔼 x ∈ F, (f : G →ᵇ ℝ) x :=
  mk₀_apply _ _ _ f

/-- The average over `F` is the sum over `F` divided by the cardinality of `F`. -/
theorem average_apply_eq_sum_div_card (f : UCB G) :
    average F hF f = (∑ x ∈ F, (f : G →ᵇ ℝ) x) / F.card := by
  rw [average_apply, Finset.expect_eq_sum_div_card]

/-- The average over a singleton `{x}` is evaluation at `x`. -/
@[simp]
theorem average_singleton (x : G) : average {x} (Finset.singleton_nonempty x) = eval G x :=
  ext fun f => by simp

end Average

section Uniform

variable [Finite G]

variable (G) in
/-- The normalized counting mean `f ↦ 𝔼 x, f x` on a finite topological group `G`. -/
def uniform : Mean G :=
  letI := Fintype.ofFinite G
  average Finset.univ Finset.univ_nonempty

/-- The uniform mean is the average over the group. The `Fintype` instance is arbitrary. -/
@[simp]
theorem uniform_apply [Fintype G] (f : UCB G) : uniform G f = 𝔼 x, (f : G →ᵇ ℝ) x := by
  simp only [uniform, average_apply]
  congr!

/-- On a finite group, the average over the whole group is the uniform mean. -/
@[simp]
theorem average_univ [Fintype G] : average Finset.univ Finset.univ_nonempty = uniform G :=
  ext fun f => by simp

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

/-- A topological group with an amenable finite-index subgroup is amenable, for any group topology:
averaging the pushforward of a left-invariant mean on `H` over the finite set of left cosets
`G ⧸ H` gives a left-invariant mean on `G`. -/
theorem Amenable.of_finiteIndex (H : Subgroup G) [H.FiniteIndex] [Amenable H] : Amenable G := by
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (G ⧸ H)
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := H)
  let ι : H →ₜ* G := ⟨H.subtype, continuous_subtype_val⟩
  let trMean (t : G) : Mean G := Mean.mk₀
    { toFun f := m.map ι (UCB.leftTranslation t⁻¹ f)
      map_add' _ _ := by simp only [map_add]
      map_smul' _ _ := by simp only [map_smul, RingHom.id_apply] }
    (fun f hf => map_nonneg (m.map ι) <| by
      have h0 := UCB.leftTranslation_le_leftTranslation_iff (g := t⁻¹).mpr hf
      rwa [map_zero] at h0)
    (by rw [LinearMap.coe_mk, AddHom.coe_mk, UCB.leftTranslation_apply_one, Mean.map_one])
  have htr (t : G) (f : UCB G) : trMean t f = m.map ι (UCB.leftTranslation t⁻¹ f) :=
    Mean.mk₀_apply _ _ _ f
  let cosetMean (q : G ⧸ H) : Mean G :=
    Quotient.liftOn' q trMean fun a b hab => Mean.ext fun f => by
      let h : H := ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩
      have hmul : UCB.leftTranslation b⁻¹ f =
          UCB.leftTranslation (ι h⁻¹) (UCB.leftTranslation a⁻¹ f) := by
        apply Subtype.ext <| BoundedContinuousFunction.ext fun x => ?_
        have hι : (ι h⁻¹ : G) = (a⁻¹ * b)⁻¹ := rfl
        rw [UCB.leftTranslation_apply, UCB.leftTranslation_apply, UCB.leftTranslation_apply,
          inv_inv, inv_inv, hι, inv_inv]
        congr 1
        group
      rw [htr, htr, hmul, hm.map_apply_leftTranslation]
  let μ : Mean G := Mean.mk₀
    { toFun f := 𝔼 q : G ⧸ H, cosetMean q f
      map_add' f₁ f₂ := by simp [Finset.expect_add_distrib]
      map_smul' c f := by simp [Finset.mul_expect] }
    (fun f hf => Finset.expect_nonneg fun q _ => map_nonneg (cosetMean q) hf)
    (by simp)
  refine ⟨⟨μ, Mean.isLeftInvariant_iff.2 fun g f => ?_⟩⟩
  simp only [μ, Mean.mk₀_apply, LinearMap.coe_mk, AddHom.coe_mk]
  refine Fintype.expect_equiv (MulAction.toPerm g⁻¹) _ _ fun q =>
    Quotient.inductionOn' q fun t => ?_
  change trMean t (UCB.leftTranslation g f) = trMean (g⁻¹ * t) f
  rw [htr, htr]
  refine congrArg (m.map ι) <| Subtype.ext <| BoundedContinuousFunction.ext fun x => ?_
  rw [UCB.leftTranslation_apply, UCB.leftTranslation_apply, UCB.leftTranslation_apply,
    inv_inv, inv_inv]
  congr 1
  group

end TauCeti
