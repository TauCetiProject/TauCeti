/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic

/-!
# Finiteness of the homology of a finite group

Let `G` be a finite group. In each degree `n` the inhomogeneous chains `Cₙ(G, A) = Gⁿ →₀ A` of a
finitely generated representation `A` over a noetherian ring `k` form a finitely generated
`k`-module, so every homology group `Hₙ(G, A)` is a finitely generated `k`-module.

Over `ℤ` this combines with the fact that positive-degree homology of a finite group is killed by
the order of the group (`groupHomology.natCard_nsmul_eq_zero`): a finitely generated torsion
abelian group is finite, so `Hₙ₊₁(G, A)` is finite for every finitely generated integral
representation `A`. In particular the integral homology `Hₙ₊₁(G, ℤ)` with trivial coefficients is
finite in every positive degree; for `n + 1 = 2` this is the finiteness of the Schur multiplier
`H₂(G, ℤ)`. Degree zero is excluded: `H₀(G, ℤ) ≅ ℤ` is infinite.

## Main results

* `groupHomology.moduleFinite`: the homology of a finite group with coefficients in a finitely
  generated representation over a noetherian ring is finitely generated in every degree.
* `groupHomology.finite_succ`: the positive-degree homology of a finite group with coefficients
  in a finitely generated integral representation is finite.

## References

* C. Löh, *Group Cohomology*, Theorem 1.7.15 and Corollary 1.7.16.
-/

public section

universe u

namespace groupHomology

/-- The homology of a finite group with coefficients in a finitely generated representation over
a noetherian ring is a finitely generated module in every degree. -/
instance moduleFinite {k G : Type u} [CommRing k] [IsNoetherianRing k] [Group G] [Finite G]
    (A : Rep k G) [Module.Finite k A] (n : ℕ) : Module.Finite k (groupHomology A n) :=
  -- The `n`-chains `Gⁿ →₀ A` are the middle term of the short complex computing `Hₙ(G, A)`.
  have : IsNoetherian k ((inhomogeneousChains A).sc n).X₂ :=
    inferInstanceAs (IsNoetherian k ((Fin n → G) →₀ A))
  ((inhomogeneousChains A).sc n).finite_homology

/-- The positive-degree homology of a finite group with coefficients in a finitely generated
integral representation is finite. In particular `Hₙ₊₁(G, ℤ)` with trivial coefficients is finite;
in degree two this is the finiteness of the Schur multiplier `H₂(G, ℤ)`. -/
instance finite_succ {G : Type} [Group G] [Finite G] (A : Rep ℤ G) [Module.Finite ℤ A] (n : ℕ) :
    Finite (groupHomology A (n + 1)) :=
  -- `#G` is a non-zero-divisor of `ℤ` killing every class. A non-zero-divisor `⟨a, h⟩` acts as
  -- `a` by definition (`Submonoid.mk_smul` is `rfl`). That lemma cannot be used as a rewrite here:
  -- elaborated alone it picks the `zsmul` action of the additive group, not the `ℤ`-module
  -- structure of the `ModuleCat` carrier that `Module.finite_of_fg_torsion` is stated for.
  Module.finite_of_fg_torsion _ fun x ↦
    ⟨⟨Nat.card G, mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')⟩,
      (Nat.cast_smul_eq_nsmul ℤ _ x).trans (natCard_nsmul_eq_zero x)⟩

end groupHomology
