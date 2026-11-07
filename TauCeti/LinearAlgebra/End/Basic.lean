/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Basic facts about module endomorphisms

A nontrivial endomorphism semiring forces the underlying module to be nontrivial. Together with
Mathlib's converse instance, this identifies nontriviality on the two sides without assumptions on
the endomorphism semiring beyond nontriviality itself.

A vector on which every endomorphism of a list acts by the same scalar `z` is acted on by their
product through `z ^ l.length` (`Module.End.list_prod_apply_eq_pow_smul`).

An endomorphism of a torsion-free module over a domain some power of which is a scalar other than
one has no nonzero fixed vectors (`TauCeti.injective_one_sub_of_pow_eq_smul_one`).

Rescaling an involution by a scalar `μ` with `μ * μ = 1` gives an endomorphism squaring to `1`
(`Module.End.smul_mul_smul_self_eq_one`).

A finite nontrivial module has more than one endomorphism (`Module.End.one_lt_natCard`).
-/

public section

namespace TauCeti

/-- A module with nontrivial endomorphism semiring is nontrivial. -/
theorem nontrivial_of_nontrivial_end {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial (Module.End R M)] : Nontrivial M := by
  have : Nontrivial (M → M) := (DFunLike.coe_injective (F := Module.End R M)).nontrivial
  exact Function.nontrivial_of_nontrivial M M

/-- **`1 - φ` is injective when a power of `φ` is a scalar other than one**, for an endomorphism
of a torsion-free module over a domain. If `φ v = v` then `m • v = φ ^ n v = v`, so
`(1 - m) • v = 0` and `v = 0`. For the character map `φ` of a Steinberg endomorphism some power of
`φ` is `q • 1` with `q` a power of the characteristic. The hypothesis `m ≠ 1` cannot be dropped:
`φ = 1` satisfies `φ ^ 1 = 1 • 1`. -/
theorem injective_one_sub_of_pow_eq_smul_one {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M] {φ : Module.End A M} {n : ℕ} {m : A}
    (h : φ ^ n = m • 1) (hm : m ≠ 1) : Function.Injective ⇑(1 - φ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  -- `1 - φ ^ n = (∑ i < n, φ ^ i) * (1 - φ)` kills `v`, and it is multiplication by `1 - m`.
  have hn : (1 - φ ^ n) v = 0 := by
    rw [← geom_sum_mul_neg, _root_.mul_apply_eq_comp, hv, map_zero]
  have hmv : (1 - m) • v = 0 := by
    rw [sub_smul, one_smul]
    simpa [h] using hn
  exact (smul_eq_zero.mp hmv).resolve_left (sub_ne_zero.mpr hm.symm)

end TauCeti

namespace Module.End

/-- A product of endomorphisms each of which acts on `s` by the scalar `z` acts on `s` by
`z ^ l.length`. -/
theorem list_prod_apply_eq_pow_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {l : List (Module.End R M)} {z : R} {s : M} (h : ∀ a ∈ l, a s = z • s) :
    l.prod s = z ^ l.length • s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, _root_.mul_apply_eq_comp, ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha),
      map_smul, h a List.mem_cons_self, smul_smul, List.length_cons, pow_succ]

/-- `μ • g` squares to `1` for an involution `g` and `μ * μ = 1`. -/
theorem smul_mul_smul_self_eq_one {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {g : Module.End R M} (hg : Function.Involutive g) {μ : R} (hμ : μ * μ = 1) :
    (μ • g) * (μ • g) = 1 := by
  rw [smul_mul_smul_comm, hμ, one_smul]
  exact LinearMap.ext hg

/-- A finite nontrivial module has more than one endomorphism: `0` and `1` differ. -/
theorem one_lt_natCard {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial M]
    [Finite M] : 1 < Nat.card (Module.End R M) := by
  have : Finite (Module.End R M) := Finite.of_injective _ DFunLike.coe_injective
  exact Finite.one_lt_card

end Module.End
