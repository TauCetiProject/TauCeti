/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic

/-!
# The second cohomology of the twisted coefficients `I(χ)/pⁱ`

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character with the prescription
property (`TauCeti.HasPrescriptionProperty`), so that multiplication by `p` is injective on
`H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹)` for every `i`. Suppose moreover that `H²(G, -)` is right exact
on the tower of twisted coefficients, in the sense that every reduction
`H²(G, I(χ)/pⁱ⁺¹) → H²(G, I(χ)/p)` is surjective, and that `H²(G, I(χ)/p)` has order `p`. Then the
short exact sequences `0 → I(χ)/pⁱ → I(χ)/pⁱ⁺¹ → I(χ)/p → 0` give short exact sequences

```text
0 → H²(G, I(χ)/pⁱ) → H²(G, I(χ)/pⁱ⁺¹) → H²(G, I(χ)/p) → 0,
```

so `H²(G, I(χ)/pⁱ)` has order `pⁱ`; and a class of `H²(G, I(χ)/pⁱ⁺¹)` whose reduction to
`H²(G, I(χ)/p)` is nonzero has order `pⁱ⁺¹`, because `p` times it is the multiplication by `p` of
its reduction to level `i`. Hence `H²(G, I(χ)/pⁱ)` is cyclic of order `pⁱ`, and isomorphic to
`ℤ/pⁱ`.

The right exactness hypothesis holds when `G` is compact with `cd_p G ≤ 2`, because the connecting
map `H²(G, I(χ)/p) → H³(G, I(χ)/pⁱ)` then vanishes
(`TauCeti.ZModTwist.surjective_explicitCoeff2_reduce_of_cohomologicalDimensionAt_le_two`, in the
module `TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension`). The hypotheses are
met by the canonical character of an infinite Demushkin group, where the result is the finite-level
form of the statement that the dualizing module of such a group is `ℚ_p/ℤ_p` with `G` acting
through its orientation (Serre's exposé, §9); that specialization lives in
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.TwistedCoefficients`.

## Main results

* `TauCeti.HasPrescriptionProperty.natCard_H2_zModTwist`: `H²(G, I(χ)/pⁱ)` has order `pⁱ`.
* `TauCeti.HasPrescriptionProperty.addOrderOf_eq_pow_of_explicitCoeff2_reduce_ne_zero`: a class
  of `H²(G, I(χ)/pⁱ⁺¹)` with nonzero reduction to `H²(G, I(χ)/p)` has order `pⁱ⁺¹`.
* `TauCeti.HasPrescriptionProperty.isAddCyclic_H2_zModTwist`,
  `TauCeti.HasPrescriptionProperty.nonempty_addEquiv_H2_zModTwist_zmod`: `H²(G, I(χ)/pⁱ)` is
  cyclic, isomorphic to `ℤ/pⁱ`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] {χ : G →ₜ* ℤ_[p]ˣ}

/-! ### The order and cyclicity of `H²(G, I(χ)/pⁱ)` -/

namespace HasPrescriptionProperty

variable [ContinuousMul G] (hχ : HasPrescriptionProperty χ)
include hχ

/-- Under the prescription property, a class of `H²(G, I(χ)/pⁱ⁺¹)` whose reduction to
`H²(G, I(χ)/p)` is nonzero is not killed by `pⁱ`: `p` times the class is the multiplication by `p`
of its reduction to level `i`, which is injective, and the reduction has the same image at the
bottom level. -/
theorem pow_nsmul_ne_zero_of_explicitCoeff2_reduce_ne_zero (i : ℕ) :
    ∀ c : H2 G (ZModTwist χ (i + 1)),
      explicitCoeff2 G (ZModTwist χ (i + 1)) (ZModTwist.reduce χ (Nat.le_add_left 1 i))
        continuous_of_discreteTopology c ≠ 0 → p ^ i • c ≠ 0 := by
  induction i with
  | zero =>
    intro c hc h0
    rw [pow_zero, one_nsmul] at h0
    exact hc (by rw [h0, map_zero])
  | succ i ih =>
    intro c hc
    have hred := ih (explicitCoeff2 G (ZModTwist χ (i + 1 + 1))
      (ZModTwist.reduce χ (Nat.le_succ (i + 1))) continuous_of_discreteTopology c)
      (by rwa [ZModTwist.explicitCoeff2_reduce_explicitCoeff2_reduce])
    have hpc : p • c = explicitCoeff2 G (ZModTwist χ (i + 1))
        (ZModTwist.mulPow χ (rfl : i + 1 + 1 = i + 1 + 1)) continuous_of_discreteTopology
        (explicitCoeff2 G (ZModTwist χ (i + 1 + 1)) (ZModTwist.reduce χ (Nat.le_succ (i + 1)))
          continuous_of_discreteTopology c) := by
      rw [ZModTwist.explicitCoeff2_mulPow_explicitCoeff2_reduce, pow_one]
    rw [pow_succ', mul_nsmul, hpc, ← map_nsmul]
    exact fun h ↦ hred (hχ.injective_explicitCoeff2_mulPow rfl (h.trans (map_zero _).symm))

/-- Under the prescription property, a class of `H²(G, I(χ)/pⁱ⁺¹)` whose reduction to
`H²(G, I(χ)/p)` is nonzero has order exactly `pⁱ⁺¹`. -/
theorem addOrderOf_eq_pow_of_explicitCoeff2_reduce_ne_zero (i : ℕ) (c : H2 G (ZModTwist χ (i + 1)))
    (hc : explicitCoeff2 G (ZModTwist χ (i + 1)) (ZModTwist.reduce χ (Nat.le_add_left 1 i))
      continuous_of_discreteTopology c ≠ 0) :
    addOrderOf c = p ^ (i + 1) :=
  addOrderOf_eq_prime_pow (hχ.pow_nsmul_ne_zero_of_explicitCoeff2_reduce_ne_zero i c hc)
    (nsmul_H2_eq_zero (ZModTwist.pow_nsmul_eq_zero χ (i + 1)) c)

variable (hsurj : ∀ i : ℕ, Function.Surjective (explicitCoeff2 G (ZModTwist χ (i + 1))
    (ZModTwist.reduce χ (Nat.le_add_left 1 i)) continuous_of_discreteTopology))
  (hcard : Nat.card (H2 G (ZModTwist χ 1)) = p)
include hsurj hcard

/-- **The order of `H²(G, I(χ)/pⁱ)`.** Under the prescription property, if every reduction
`H²(G, I(χ)/pⁱ⁺¹) → H²(G, I(χ)/p)` is surjective and `H²(G, I(χ)/p)` has order `p`, then
`H²(G, I(χ)/pⁱ)` has order `pⁱ`. -/
theorem natCard_H2_zModTwist (i : ℕ) : Nat.card (H2 G (ZModTwist χ i)) = p ^ i := by
  induction i with
  | zero => rw [pow_zero, Nat.card_unique]
  | succ i ih =>
    -- the short exact sequence `0 → H²(I(χ)/pⁱ) → H²(I(χ)/pⁱ⁺¹) → H²(I(χ)/p) → 0`
    have hS := (ZModTwist.shortExact χ (rfl : i + 1 = i + 1)).explicitLongExact_H2B
    rw [ZModTwist.shortExact_inclDistribMulActionHom,
      ZModTwist.shortExact_projDistribMulActionHom] at hS
    rw [← AddSubgroup.card_ker_mul_card_of_surjective (hsurj i), ← hS,
      ← Nat.card_congr (AddMonoidHom.ofInjective (hχ.injective_explicitCoeff2_mulPow rfl)).toEquiv,
      ih, hcard, pow_succ]

/-- **`H²(G, I(χ)/pⁱ)` is cyclic.** Under the prescription property, if every reduction
`H²(G, I(χ)/pⁱ⁺¹) → H²(G, I(χ)/p)` is surjective and `H²(G, I(χ)/p)` has order `p`, then
`H²(G, I(χ)/pⁱ)` is cyclic: any lift of a nonzero class of `H²(G, I(χ)/p)` generates it. -/
theorem isAddCyclic_H2_zModTwist (i : ℕ) : IsAddCyclic (H2 G (ZModTwist χ i)) := by
  cases i with
  | zero => infer_instance
  | succ i =>
    have : Finite (H2 G (ZModTwist χ (i + 1))) :=
      Nat.finite_of_card_ne_zero ((hχ.natCard_H2_zModTwist hsurj hcard _).trans_ne
        (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
    have : Finite (H2 G (ZModTwist χ 1)) :=
      Nat.finite_of_card_ne_zero (hcard.trans_ne (Fact.out : p.Prime).ne_zero)
    have : Nontrivial (H2 G (ZModTwist χ 1)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact (Fact.out : p.Prime).one_lt)
    obtain ⟨y, hy⟩ := exists_ne (0 : H2 G (ZModTwist χ 1))
    obtain ⟨c, rfl⟩ := hsurj i y
    exact isAddCyclic_of_addOrderOf_eq_card c
      ((hχ.addOrderOf_eq_pow_of_explicitCoeff2_reduce_ne_zero i c hy).trans
        (hχ.natCard_H2_zModTwist hsurj hcard _).symm)

/-- **`H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ`.** Under the prescription property, if every reduction
`H²(G, I(χ)/pⁱ⁺¹) → H²(G, I(χ)/p)` is surjective and `H²(G, I(χ)/p)` has order `p`, then
`H²(G, I(χ)/pⁱ)` is isomorphic to `ℤ/pⁱ` as an additive group. -/
theorem nonempty_addEquiv_H2_zModTwist_zmod (i : ℕ) :
    Nonempty (H2 G (ZModTwist χ i) ≃+ ZMod (p ^ i)) :=
  have := hχ.isAddCyclic_H2_zModTwist hsurj hcard i
  ⟨addEquivOfAddCyclicCardEq
    ((hχ.natCard_H2_zModTwist hsurj hcard i).trans (Nat.card_zmod _).symm)⟩

end HasPrescriptionProperty

end TauCeti
