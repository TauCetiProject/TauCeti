/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

import TauCeti.GroupTheory.Index.Quotient

/-!
# Kernels and cokernels of a composite

For a homomorphism `f : A →* B` write `z(f) = [B : f(A)] / #ker(f)` for the ratio of the order of
its cokernel to the order of its kernel. For homomorphisms `f : A →* B` and `g : B →* C` this ratio
is multiplicative,

`z(g ∘ f) = z(g) · z(f)`,

which is the count along the kernel–cokernel exact sequence

`1 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 1`.

Here it is stated without division, as
`[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`, which needs no
finiteness hypothesis: infinite orders and indices are read as `0`, and either both sides are `0`
or all six quantities are finite. Neither the groups nor the cokernels need be commutative.

For an isogeny `φ : E → E'` with dual `φ̂`, the composite `φ̂ ∘ φ` is multiplication by `deg φ`,
so on the points over a field this gives `z([deg φ]) = z(φ̂) · z(φ)`. Ratios of this kind over
local fields are the local factors in Cassels' proof that the Birch–Swinnerton-Dyer quotient is
an isogeny invariant.

## Main results

* `MonoidHom.index_range_comp_mul_card_ker_mul_card_ker` and its additive form
  `AddMonoidHom.index_range_comp_mul_card_ker_mul_card_ker`: the multiplicativity of
  `#coker / #ker` along a composite.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I.7.
-/

public section

namespace MonoidHom

variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- **`#coker / #ker` is multiplicative along a composite**: for `f : A →* B` and `g : B →* C`,
`[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`. No finiteness is
required: infinite orders and indices are read as `0`. -/
@[to_additive AddMonoidHom.index_range_comp_mul_card_ker_mul_card_ker
  /-- **`#coker / #ker` is multiplicative along a composite**: for `f : A →+ B` and
  `g : B →+ C`, `[C : gf(A)] · #ker(f) · #ker(g) = [C : g(B)] · [B : f(A)] · #ker(g ∘ f)`. No
  finiteness is required: infinite orders and indices are read as `0`. -/]
theorem index_range_comp_mul_card_ker_mul_card_ker (f : A →* B) (g : B →* C) :
    (g.comp f).range.index * (Nat.card f.ker * Nat.card g.ker) =
      g.range.index * f.range.index * Nat.card (g.comp f).ker := by
  -- The image of `f(A)` in `B ⧸ ker g` has the same index as `gf(A)` has in `g(B)`.
  have hrange : (g.comp f).range.index =
      (f.range.map (QuotientGroup.mk' g.ker)).index * g.range.index := by
    rw [range_comp, Subgroup.index_map, Subgroup.index_map, QuotientGroup.ker_mk',
      range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.index_top, mul_one]
  -- The kernel of `g ∘ f` is the preimage of `ker g`, counted by the quotient-index formula.
  have hker := TauCeti.index_range_mul_card_comap_mul (f := f) (S := g.ker)
  rw [comap_ker] at hker
  rw [hrange, mul_assoc g.range.index, hker]
  ac_rfl

end MonoidHom
