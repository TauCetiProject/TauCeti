/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

import TauCeti.GroupTheory.Index.Quotient
import TauCeti.GroupTheory.Coset.Fiber
import Mathlib.Data.Rat.Cast.Order

/-!
# Kernels and cokernels of a composite

For homomorphisms `f : A →* B` and `g : B →* C` of arbitrary groups, this file proves the
cross-multiplied index identity

`[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`,

where `[B : f(A)]` is the cardinality of the coset space `B ⧸ f(A)`. It needs no finiteness
hypothesis: infinite orders and indices are read as `0`, and either both sides are `0` or all six
quantities are finite. The images need not be normal.

When the kernels and indices are finite, write `z(f) = [B : f(A)] / #ker(f)`. Dividing out gives
`z(g ∘ f) = z(g) · z(f)`. For abelian groups the indices are the orders of the cokernels, and this
is the count along the kernel–cokernel exact sequence

`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`.

For an isogeny `φ : E → E'` with dual `φ̂`, the composite `φ̂ ∘ φ` is multiplication by `deg φ`,
so on the points over a field this gives `z([deg φ]) = z(φ̂) · z(φ)` whenever the kernels and
cokernels involved are finite. Ratios of this kind over local fields are the local factors in
Cassels' proof that the Birch–Swinnerton-Dyer quotient is an isogeny invariant.

## Main results

* `MonoidHom.index_range_comp_mul_card_ker_mul_card_ker` and its additive form
  `AddMonoidHom.index_range_comp_mul_card_ker_mul_card_ker`: the cross-multiplied index identity
  for a composite.
* `MonoidHom.index_range_div_card_ker_comp` and its additive form: multiplicativity of the
  rational ratio when the kernels are finite.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I.7.
-/

public section

namespace MonoidHom

variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- **The index identity for a composite**: for `f : A →* B` and `g : B →* C`,
`[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`, with subgroup indices
counting cosets. No finiteness is required: infinite orders and indices are read as `0`. When all
of them are finite, this says `[B : f(A)] / #ker(f)` is multiplicative along the composite. -/
@[to_additive AddMonoidHom.index_range_comp_mul_card_ker_mul_card_ker
  /-- **The index identity for a composite**: for `f : A →+ B` and `g : B →+ C`,
  `[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`, with subgroup
  indices counting cosets. No finiteness is required: infinite orders and indices are read as
  `0`. When all of them are finite, this says `[B : f(A)] / #ker(f)` is multiplicative along the
  composite. -/]
theorem index_range_comp_mul_card_ker_mul_card_ker (f : A →* B) (g : B →* C) :
    (g.comp f).range.index * (Nat.card f.ker * Nat.card g.ker) =
      g.range.index * f.range.index * Nat.card (g.comp f).ker := by
  -- The image of `f(A)` in `B ⧸ ker g` has the same index as `gf(A)` has in `g(B)`.
  have hrange : (g.comp f).range.index =
      (f.range.map (QuotientGroup.mk' g.ker)).index * g.range.index := by
    rw [range_comp, Subgroup.index_map, Subgroup.index_map]
    simp [range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  -- The kernel of `g ∘ f` is the preimage of `ker g`, counted by the quotient-index formula.
  have hker := TauCeti.index_range_mul_card_comap_mul (f := f) (S := g.ker)
  rw [comap_ker] at hker
  rw [hrange, mul_assoc g.range.index, hker]
  ac_rfl

/-- The rational index/kernel ratio `[B : f(A)] / #ker(f)` is multiplicative under composition
when the kernels are finite. No finiteness of the indices is needed: an infinite index is read
as zero. -/
@[to_additive AddMonoidHom.index_range_div_card_ker_comp
  /-- The rational index/kernel ratio `[B : f(A)] / #ker(f)` is multiplicative under composition
  when the kernels are finite. No finiteness of the indices is needed: an infinite index is read
  as zero. -/]
theorem index_range_div_card_ker_comp (f : A →* B) (g : B →* C)
    [Finite f.ker] [Finite g.ker] :
    ((g.comp f).range.index : ℚ) / Nat.card (g.comp f).ker =
      ((g.range.index : ℚ) / Nat.card g.ker) *
        ((f.range.index : ℚ) / Nat.card f.ker) := by
  have := (g.finite_ker_comp f (Set.toFinite _) (Set.toFinite _)).to_subtype
  have hf : (Nat.card f.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hg : (Nat.card g.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hgf : (Nat.card (g.comp f).ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hgf (mul_ne_zero hg hf)).mpr
  simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (Nat.cast : ℕ → ℚ) (f.index_range_comp_mul_card_ker_mul_card_ker g)

end MonoidHom
