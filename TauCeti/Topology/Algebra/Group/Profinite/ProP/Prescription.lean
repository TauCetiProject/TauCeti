/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ZModTwist

/-!
# The prescription property of a character

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character, with twisted
coefficient modules `I(χ)/pⁱ = TauCeti.ZModTwist χ i`, on which `G` acts by `g • x = χ(g) x`. The
equivariant reductions `I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i` induce maps on continuous cohomology.

A character has the **prescription property** when every reduction
`H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective: every continuous crossed homomorphism to
`I(χ)/p` lifts, modulo principal ones, to a continuous crossed homomorphism to `I(χ)/pⁱ`. This is
Labute's condition on the orientation of a Demushkin group: such a group has exactly one continuous
character with the prescription property, its canonical character (Labute, Thm 4). Here the
property is defined, against the explicit model of continuous cohomology; it holds for every
continuous character of a free pro-`p` group
(`TauCeti.freeProP.hasPrescriptionProperty`, in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Prescription`). `I(χ)/p` is `ZModTwist χ 1`, the
module at `i = 1`, with carrier `ZMod (p ^ 1)`.

The property has two cohomological reformulations (Labute, Prop. 6), both read off the long exact
sequences of the short exact sequences `0 → I(χ)/pⁱ → I(χ)/pⁱ⁺¹ → I(χ)/p → 0`: it says that every
connecting map `δ¹ : H¹(G, I(χ)/p) → H²(G, I(χ)/pⁱ)` vanishes, and that multiplication by `p` is
injective on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹)` for every `i`. Once it holds, every reduction
`H¹(G, I(χ)/pⁿ) → H¹(G, I(χ)/pʲ)` between two levels is surjective, not only those onto the bottom
level, so that a class at one level lifts through the whole tower of coefficients; this is the form
in which compatible systems of crossed homomorphisms are built.

## Main definitions

* `TauCeti.HasPrescriptionProperty`: surjectivity of every `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`.

## Main results

* `TauCeti.HasPrescriptionProperty.surjective_explicitCoeff1_reduce`: every reduction
  `H¹(G, I(χ)/pⁿ) → H¹(G, I(χ)/pʲ)`, `j ≤ n`, is surjective.
* `TauCeti.hasPrescriptionProperty_iff_forall_explicitDelta1_eq_zero`: the property is the
  vanishing of the connecting maps `H¹(G, I(χ)/p) → H²(G, I(χ)/pⁱ)`.
* `TauCeti.hasPrescriptionProperty_iff_forall_injective_explicitCoeff2_mulPow`: the property is the
  injectivity of multiplication by `p` on `H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹)`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6 and Theorem 4.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-- **The prescription property** of a continuous character `χ : G →ₜ* ℤ_pˣ` (Labute's condition
on the orientation of a Demushkin group): every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`, for
`i ≥ 1`, is surjective. In cocycle terms, every continuous crossed homomorphism `G → I(χ)/p` is,
modulo principal ones, the reduction of a continuous crossed homomorphism `G → I(χ)/pⁱ`. -/
def HasPrescriptionProperty (χ : G →ₜ* ℤ_[p]ˣ) : Prop :=
  ∀ (i : ℕ) (hi : 1 ≤ i),
    Function.Surjective
      (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi) continuous_of_discreteTopology)

/-- The defining property of `HasPrescriptionProperty`, available to modules that only see the
declaration and not its body. -/
theorem hasPrescriptionProperty_iff (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ (i : ℕ) (hi : 1 ≤ i),
      Function.Surjective
        (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi)
          continuous_of_discreteTopology) :=
  Iff.rfl

/-! ### Lifting through the whole tower of coefficients

The defining property lifts classes from the bottom level `I(χ)/p`; by exactness at
`H¹(G, I(χ)/pʲ⁺¹)` of the sequence `0 → I(χ)/p → I(χ)/pʲ⁺¹ → I(χ)/pʲ → 0` and induction on `j`,
classes lift between any two levels. -/

namespace HasPrescriptionProperty

variable {χ : G →ₜ* ℤ_[p]ˣ} (hχ : HasPrescriptionProperty χ)
include hχ

/-- **Every reduction `H¹(G, I(χ)/pⁿ) → H¹(G, I(χ)/pʲ)` is surjective** under the prescription
property, not only the reductions onto the bottom level `I(χ)/p`. -/
theorem surjective_explicitCoeff1_reduce : ∀ {j n : ℕ} (h : j ≤ n),
    Function.Surjective
      (explicitCoeff1 G (ZModTwist χ n) (ZModTwist.reduce χ h) continuous_of_discreteTopology) := by
  intro j
  induction j with
  | zero => exact fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩
  | succ j ih =>
    intro n hn c
    -- lift the reduction of `c` to level `j` up to level `n`, and reduce the lift to level `j + 1`
    obtain ⟨c', hc'⟩ := ih (Nat.le_of_succ_le hn) (explicitCoeff1 G (ZModTwist χ (j + 1))
      (ZModTwist.reduce χ (Nat.le_succ j)) continuous_of_discreteTopology c)
    -- the difference from `c` dies at level `j`, so it is `pʲ` times a class at the bottom level
    have hker : c - explicitCoeff1 G (ZModTwist χ n) (ZModTwist.reduce χ hn)
        continuous_of_discreteTopology c' ∈
        (explicitCoeff1 G (ZModTwist χ (j + 1)) (ZModTwist.reduce χ (Nat.le_succ j))
          continuous_of_discreteTopology).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, ZModTwist.explicitCoeff1_reduce_explicitCoeff1_reduce,
        hc', sub_self]
    have hS := (ZModTwist.shortExact χ (Nat.add_comm 1 j)).explicitLongExact_H1B
    rw [ZModTwist.shortExact_inclDistribMulActionHom,
      ZModTwist.shortExact_projDistribMulActionHom] at hS
    rw [← hS] at hker
    obtain ⟨e, he⟩ := hker
    -- lift that bottom class to level `n - j` and multiply it back by `pʲ`
    have h1 : 1 ≤ n - j := by omega
    have hnj : n - j + j = n := Nat.sub_add_cancel (Nat.le_of_succ_le hn)
    obtain ⟨e', he'⟩ := hχ (n - j) h1 e
    refine ⟨c' + explicitCoeff1 G (ZModTwist χ (n - j)) (ZModTwist.mulPow χ hnj)
      continuous_of_discreteTopology e', ?_⟩
    rw [map_add, ZModTwist.explicitCoeff1_reduce_explicitCoeff1_mulPow χ hnj (Nat.add_comm 1 j) h1
      hn, he', he]
    abel

/-- Under the prescription property every connecting map
`δ¹ : H¹(G, I(χ)/pʲ) → H²(G, I(χ)/pⁱ)` of a sequence `0 → I(χ)/pⁱ → I(χ)/pⁱ⁺ʲ → I(χ)/pʲ → 0`
vanishes. -/
theorem explicitDelta1_shortExact_eq_zero [ContinuousMul G] {i j n : ℕ} (h : i + j = n) :
    (ZModTwist.shortExact χ h).explicitDelta1 = 0 := by
  have hS := (ZModTwist.shortExact χ h).explicitLongExact_H1C
  rw [ZModTwist.shortExact_projDistribMulActionHom] at hS
  rw [← AddMonoidHom.ker_eq_top_iff, ← hS, AddMonoidHom.range_eq_top]
  exact hχ.surjective_explicitCoeff1_reduce _

/-- Under the prescription property multiplication by `pʲ` is injective on
`H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺ʲ)`. -/
theorem injective_explicitCoeff2_mulPow [ContinuousMul G] {i j n : ℕ} (h : i + j = n) :
    Function.Injective (explicitCoeff2 G (ZModTwist χ i) (ZModTwist.mulPow χ h)
      continuous_of_discreteTopology) := by
  have hS := (ZModTwist.shortExact χ h).explicitLongExact_H2A
  rw [ZModTwist.shortExact_inclDistribMulActionHom] at hS
  rw [← AddMonoidHom.ker_eq_bot_iff, ← hS, AddMonoidHom.range_eq_bot_iff]
  exact hχ.explicitDelta1_shortExact_eq_zero h

end HasPrescriptionProperty

/-! ### The cohomological reformulations (Labute, Prop. 6) -/

/-- **The prescription property is the vanishing of the connecting maps**
`δ¹ : H¹(G, I(χ)/p) → H²(G, I(χ)/pⁱ)` of the sequences `0 → I(χ)/pⁱ → I(χ)/pⁱ⁺¹ → I(χ)/p → 0`, for
every `i` (Labute, Prop. 6). -/
theorem hasPrescriptionProperty_iff_forall_explicitDelta1_eq_zero [ContinuousMul G]
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔
      ∀ (i n : ℕ) (h : i + 1 = n), (ZModTwist.shortExact χ h).explicitDelta1 = 0 := by
  refine ⟨fun hχ i n h ↦ hχ.explicitDelta1_shortExact_eq_zero h, fun hδ n hn ↦ ?_⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hS := (ZModTwist.shortExact χ (rfl : i + 1 = i + 1)).explicitLongExact_H1C
  rw [ZModTwist.shortExact_projDistribMulActionHom, hδ i _ rfl, AddMonoidHom.ker_zero,
    AddMonoidHom.range_eq_top] at hS
  exact hS

/-- **The prescription property is the injectivity of multiplication by `p` on `H²`**,
`H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹)`, for every `i` (Labute, Prop. 6). -/
theorem hasPrescriptionProperty_iff_forall_injective_explicitCoeff2_mulPow [ContinuousMul G]
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ (i n : ℕ) (h : i + 1 = n),
      Function.Injective (explicitCoeff2 G (ZModTwist χ i) (ZModTwist.mulPow χ h)
        continuous_of_discreteTopology) := by
  rw [hasPrescriptionProperty_iff_forall_explicitDelta1_eq_zero]
  refine forall₃_congr fun i n h ↦ ?_
  rw [← AddMonoidHom.range_eq_bot_iff, (ZModTwist.shortExact χ h).explicitLongExact_H2A,
    ZModTwist.shortExact_inclDistribMulActionHom, AddMonoidHom.ker_eq_bot_iff]

end TauCeti
