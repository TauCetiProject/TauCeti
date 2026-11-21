/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Order invariance, converse Möbius inversion and Weisner's theorem

The Möbius function is invariant under order isomorphisms (`OrderIso.mu_map`), and additive maps
preserving `1` carry it from one coefficient group to another (`IncidenceAlgebra.map_mu`).

Mathlib's `IncidenceAlgebra.moebius_inversion_bot` recovers `f` from its lower sums
`g x = ∑_{y ≤ x} f y` as `f x = ∑_{y ≤ x} μ(y, x) g y`. This file proves the converse direction:
summing the Möbius transform `x ↦ ∑_{z ≤ x} μ(z, x) g z` over the lower set of `x` gives back
`g x`.

It also proves Weisner's theorem: in a locally finite join-semilattice, the values `μ(c, x)`
summed over the elements `x ∈ [c, d]` whose join with a fixed `a` is `d` cancel, provided
`¬a ≤ c`. The coefficients only need an additive group with a `1`, the level at which `μ` is
defined: the statement is proved over `ℤ` and transported along `n ↦ n • 1`. In a finite
lattice, taking `c = ⊥`, `d = ⊤` and `a` an atom turns this into a recurrence for `μ(⊥, ⊤)` in
terms of the Möbius function on smaller intervals; this is how the Möbius function of the lattice
of noncrossing partitions is computed.

## Main results

* `IncidenceAlgebra.map_mu` — an additive map `f` with `f 1 = 1` satisfies
  `f (μ(a, b)) = μ(a, b)`.
* `IncidenceAlgebra.sum_Iic_sum_Iic_mu_mul` — `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`.
* `IncidenceAlgebra.sum_filter_sup_eq_mu_eq_zero` — *Weisner's theorem*: for `¬a ≤ c`,
  `∑_{x ∈ [c, d], x ⊔ a = d} μ(c, x) = 0`.

## References

* L. Weisner, *Abstract theory of inversion of finite series*, Trans. Amer. Math. Soc. 38 (1935),
  474–484.
* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2nd ed., Corollary 3.9.3.
-/

public section

open Finset IncidenceAlgebra

namespace OrderIso

variable {𝕜 α β : Type*} [AddCommGroup 𝕜] [One 𝕜]
  [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
  [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β]

/-- The Möbius function is invariant under order isomorphisms. -/
@[simp]
theorem mu_map (e : α ≃o β) (a b : α) : mu 𝕜 (e a) (e b) = mu 𝕜 a b := by
  induction hn : #(Icc a b) using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    by_cases hab : a = b
    · subst b
      simp
    rw [mu_eq_neg_sum_Ico_of_ne (e.injective.ne hab), mu_eq_neg_sum_Ico_of_ne hab, neg_inj]
    refine (sum_equiv e.toEquiv (fun x => by simp) fun x hx => ?_).symm
    obtain ⟨hax, hxb⟩ := mem_Ico.1 hx
    have hlt := card_lt_card (Icc_ssubset_Icc_right (hax.trans hxb.le) le_rfl hxb)
    exact (ih _ (hn ▸ hlt) x rfl).symm

end OrderIso

namespace IncidenceAlgebra

section MapMu

variable {𝕜 𝕝 α F : Type*} [AddCommGroup 𝕜] [One 𝕜] [AddCommGroup 𝕝] [One 𝕝]
  [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [FunLike F 𝕜 𝕝] [AddMonoidHomClass F 𝕜 𝕝]

/-- An additive map preserving `1` carries the Möbius function with coefficients in `𝕜` to the
Möbius function with coefficients in `𝕝`. -/
theorem map_mu (f : F) (hf : f 1 = 1) (a b : α) : f (mu 𝕜 a b) = mu 𝕝 a b := by
  induction hn : #(Icc a b) using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    rw [mu_apply, mu_apply (𝕜 := 𝕝)]
    split_ifs
    · exact hf
    rw [map_neg, map_sum]
    refine congrArg _ (sum_congr rfl fun x hx => ?_)
    obtain ⟨hax, hxb⟩ := mem_Ico.1 hx
    exact ih _ (hn ▸ card_lt_card (Icc_ssubset_Icc_right (hax.trans hxb.le) le_rfl hxb)) x rfl

end MapMu

section Converse

variable {𝕜 α : Type*} [NonAssocRing 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [LocallyFiniteOrderBot α] [DecidableEq α]

/-- *Converse Möbius inversion*: the lower sums of the Möbius transform
`y ↦ ∑_{z ≤ y} μ(z, y) g z` of `g` recover `g`, `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`. -/
theorem sum_Iic_sum_Iic_mu_mul (g : α → 𝕜) (x : α) :
    ∑ y ∈ Iic x, ∑ z ∈ Iic y, mu 𝕜 z y * g z = g x := by
  rw [sum_comm' (t' := Iic x) (s' := fun z => Icc z x) fun y z => by
    simp only [mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2, h.1⟩, h.2.trans h.1⟩, fun h => ⟨h.1.2, h.1.1⟩⟩]
  simp [← sum_mul, sum_Icc_mu_right]

end Converse

section Weisner

variable {𝕜 α : Type*} [AddCommGroup 𝕜] [One 𝕜] [SemilatticeSup α] [LocallyFiniteOrder α]
  [DecidableEq α]

/-- *Weisner's theorem*: in a locally finite join-semilattice, for an interval `[c, d]` and every
`a` with `¬a ≤ c`, the Möbius function `μ(c, x)` sums to zero over the `x ∈ [c, d]` with
`x ⊔ a = d`. In a finite lattice with `c = ⊥` and `d = ⊤` the hypothesis reads `a ≠ ⊥`. -/
theorem sum_filter_sup_eq_mu_eq_zero {a c d : α} (ha : ¬a ≤ c) :
    ∑ x ∈ Icc c d with x ⊔ a = d, mu 𝕜 c x = 0 := by
  -- It suffices to work over `ℤ`, since `n ↦ n • 1` carries `μ` over `ℤ` to `μ` over `𝕜`.
  suffices h : ∑ x ∈ Icc c d with x ⊔ a = d, mu ℤ c x = 0 by
    simp_rw [← map_mu (zmultiplesHom 𝕜 1) (one_zsmul 1), ← map_sum, h, map_zero]
  -- Detect `x ⊔ a = d` by `∑_{x ⊔ a ≤ y ≤ d} μ(y, d)`, then exchange the two sums: the inner sum
  -- `∑_{c ≤ x ≤ y} μ(c, x)` vanishes for every `y ≥ c ⊔ a`, since such `y` is not `c`.
  calc ∑ x ∈ Icc c d with x ⊔ a = d, mu ℤ c x
      = ∑ x ∈ Icc c d, ∑ y ∈ Icc (x ⊔ a) d, mu ℤ c x * mu ℤ y d := by
        refine (sum_filter _ _).trans (sum_congr rfl fun x _ => ?_)
        rw [← mul_sum, sum_Icc_mu_left, mul_ite, mul_one, mul_zero]
    _ = ∑ y ∈ Icc (c ⊔ a) d, ∑ x ∈ Icc c y, mu ℤ c x * mu ℤ y d := sum_comm' fun x y => by
        simp only [mem_Icc, sup_le_iff]
        exact ⟨fun ⟨⟨hcx, _⟩, ⟨hxy, hay⟩, hyd⟩ => ⟨⟨hcx, hxy⟩, ⟨hcx.trans hxy, hay⟩, hyd⟩,
          fun ⟨⟨hcx, hxy⟩, ⟨_, hay⟩, hyd⟩ => ⟨⟨hcx, hxy.trans hyd⟩, ⟨hxy, hay⟩, hyd⟩⟩
    _ = 0 := sum_eq_zero fun y hy => by
        have hcy : c ≠ y := fun h => ha ((le_sup_right.trans (mem_Icc.1 hy).1).trans_eq h.symm)
        rw [← sum_mul, sum_Icc_mu_right, ite_eq_right hcy, zero_mul]

end Weisner

end IncidenceAlgebra
