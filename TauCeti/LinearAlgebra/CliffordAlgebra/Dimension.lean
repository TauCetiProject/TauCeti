/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
-- Private: `CliffordAlgebra.nonempty_evenOddEquivAddOne` is used only inside the proof that the
-- two halves of the `ℤ/2`-grading are equidimensional.
import TauCeti.LinearAlgebra.CliffordAlgebra.ParitySwap
-- Private: the ordered exterior-basis formula proves the empty and singleton basis identities.
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
-- Private: `Module.Finite.of_finite_end` shows that a spinor module is finite-dimensional.
import TauCeti.LinearAlgebra.Dual.Lemmas
-- Private: `Module.Basis.map_exteriorAlgebra` proves the naturality of the basis.
import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
-- Private: `LinearMap.BilinMap.toQuadraticMap_surjective` writes `-Q` as the quadratic form of a
-- bilinear form.
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# Freeness and dimension of a Clifford algebra

The Clifford relation `ι Q m * ι Q m = Q m` does not preserve the number of generators in a
product, so a Clifford algebra is not graded by degree; what it does do is leave the *size* of the
algebra alone. Over a ring in which `2` is invertible this is Mathlib's
`CliffordAlgebra.equivExterior`, a
linear (not algebra) isomorphism `CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M` valid for every
quadratic form. Deforming the form therefore deforms the multiplication and nothing else, and the
underlying module of `CliffordAlgebra Q` is as free, and as large, as the exterior algebra of `M`.

This file records that. Over every commutative ring, `CliffordAlgebra Q` is a free `R`-module
whenever `M` is free and a finite `R`-module whenever `M` is finite (`CliffordAlgebra.instFree`,
`CliffordAlgebra.instFinite`), and it has rank `2 ^ finrank R M` whenever `R` is nontrivial and `M`
is finite free: for free `M` the quadratic form `-Q` is that of a bilinear form, so
`CliffordAlgebra.changeFormEquiv` identifies `CliffordAlgebra Q` linearly with the exterior algebra
without dividing by `2`. Over a commutative ring in which `2` is invertible, there is moreover an
explicit basis `CliffordAlgebra.basis Q b : Basis (Finset I) R (CliffordAlgebra Q)` attached to a
basis `b` of `M` indexed by a linearly ordered `I`. The `2 ^ n` is `∑ₖ (n choose k)`
(`finrank_eq_sum_choose`), the count that a degree-graded argument would produce one exterior power
at a time; the basis, in contrast, is indexed by the finite subsets of a basis index set, because it
is transported from Mathlib's basis `Module.Basis.ExteriorAlgebra` of the exterior algebra.

A second section splits that count in half along Mathlib's `ℤ/2`-grading `evenOdd Q`. Over a field
the two halves of the grading of the Clifford algebra of a nonzero space are isomorphic for *every*
quadratic form, by the odd linear automorphism of
`TauCeti/LinearAlgebra/CliffordAlgebra/ParitySwap.lean`, so over every field, where the count
`2 ^ n` above is available, each has dimension `2 ^ (n - 1)`, as does the even subalgebra
`CliffordAlgebra.even Q`.

These counts are what make the structure theory of Clifford algebras run: over an algebraically
closed field a nondegenerate `Q` on a `2l`-dimensional space has
`finrank (CliffordAlgebra Q) = 2 ^ (2 * l) = (2 ^ l) ^ 2`, matching `Module.End` of the
`2 ^ l`-dimensional spin module, so a surjection between the two is forced to be an isomorphism,
while `finrank (even Q) = 2 ^ (2 * l - 1) = 2 * (2 ^ (l - 1)) ^ 2` matches the product of two
matrix algebras one size down, acting on the two half-spin summands.

## Implementation notes

`basis` transports Mathlib's `Module.Basis.ExteriorAlgebra` along `equivExterior`, so its elements
are not by definition the products `ι Q (b i₁) * ⋯ * ι Q (b iₖ)` of generators: `equivExterior` is
built from `CliffordAlgebra.changeForm`, which corrects a product of generators by lower-order
terms. Nothing below needs the products, only their number. Identifying the two families is the
Clifford analogue of a Poincaré-Birkhoff-Witt theorem, and is the content of the associated-graded
isomorphism `gr (CliffordAlgebra Q) ≅ ExteriorAlgebra R M` for the degree filtration of
`TauCeti/LinearAlgebra/CliffordAlgebra/Filtration.lean`; that isomorphism is
`CliffordAlgebra.associatedGradedEquivExterior` in `TauCeti.LinearAlgebra.CliffordAlgebra.PBW`.

## Main definitions

* `CliffordAlgebra.basis`: the basis of `CliffordAlgebra Q` indexed by the finite subsets of
  the index set of a basis of `M`, over a ring in which `2` is invertible.

## Main results

* `CliffordAlgebra.basis_empty` and `CliffordAlgebra.basis_singleton`: for every basis, the basis
  vectors indexed by `∅` and by `{i}` are `1` and the generator `ι Q (b i)`.
* `CliffordAlgebra.map_basis`: the basis is natural under isometric equivalences.
* `CliffordAlgebra.rank_eq_rank_exteriorAlgebra` and
  `CliffordAlgebra.finrank_eq_finrank_exteriorAlgebra`: the rank of `CliffordAlgebra Q`
  is the rank of `ExteriorAlgebra R M`. The right-hand sides do not mention `Q`, so this is the
  statement that the size of a Clifford algebra does not depend on the quadratic form.
* `CliffordAlgebra.instFree` and `CliffordAlgebra.instFinite`: the Clifford algebra
  of a free module is free, and of a finite module is finite.
* `CliffordAlgebra.finrank_eq_two_pow`: `finrank R (CliffordAlgebra Q) = 2 ^ finrank R M` over
  every commutative ring, with `CliffordAlgebra.finrank_eq_sum_choose` the same count as a sum of
  binomial coefficients.
* `CliffordAlgebra.two_mul_finrank_evenOdd`: over a field, each half of the grading of the Clifford
  algebra of a nonzero space is exactly half of it, for every quadratic form, and
  `CliffordAlgebra.finrank_evenOdd_of_finrank_eq_two_pow` reads that half off any count of the
  whole algebra by a power of two.
* `CliffordAlgebra.finrank_evenOdd` and `CliffordAlgebra.finrank_even`: over a field, each half of
  the grading of the Clifford algebra of a nonzero finite-dimensional space, and in particular the
  even subalgebra, has dimension `2 ^ (finrank K V - 1)`; for the zero form this is the even and
  the odd half of an exterior algebra.
* `CliffordAlgebra.finrank_eq_two_pow_of_bijective_lsmul`: a module on which
  the Clifford algebra of a `2l`-dimensional space acts as its whole endomorphism algebra has
  dimension `2 ^ l`.
* `CliffordAlgebra.even_finrank_of_algEquiv_end`: if a module's endomorphism algebra is
  isomorphic to the Clifford algebra, the underlying space has even dimension.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open Module

universe u v w

namespace CliffordAlgebra

open TauCeti

section General

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- The Clifford algebra of a free module is a free module, over every commutative ring. -/
instance instFree [Module.Free R M] : Module.Free R (CliffordAlgebra Q) := by
  -- `M` being free, `-Q` is the quadratic form of a bilinear form `B`, so `changeFormEquiv`
  -- identifies the algebra linearly with the exterior algebra, with no division by `2`.
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (-Q)
  exact Module.Free.of_equiv (changeFormEquiv (hB.trans (zero_sub Q).symm)).symm

/-- The Clifford algebra of a finite module is a finite module, over every commutative ring. -/
instance instFinite [Module.Finite R M] : Module.Finite R (CliffordAlgebra Q) := by
  -- It is a quotient of the Clifford algebra of a finite free module, which is finite by the same
  -- `changeFormEquiv` argument as `CliffordAlgebra.instFree`.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (-(Q.comp f))
  have := Module.Finite.equiv (changeFormEquiv (hB.trans (zero_sub (Q.comp f)).symm)).symm
  exact Module.Finite.of_surjective (map (Q₁ := Q.comp f) ⟨f, fun _ ↦ rfl⟩).toLinearMap
    (map_surjective _ hf)

/-- The Clifford algebra of a finite free module of rank `n` has rank `2 ^ n`, for every quadratic
form on it. -/
theorem finrank_eq_two_pow [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (CliffordAlgebra Q) = 2 ^ finrank R M := by
  -- As for `CliffordAlgebra.instFree`: `changeFormEquiv` along a bilinear form for `-Q` identifies
  -- the algebra linearly with the exterior algebra, with no division by `2`.
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (-Q)
  exact (changeFormEquiv (hB.trans (zero_sub Q).symm)).finrank_eq.trans
    ExteriorAlgebra.finrank_eq_two_pow

/-- The rank of a Clifford algebra as a sum of binomial coefficients: `2 ^ n = ∑ₖ (n choose k)`,
the count that adding up the exterior powers `⋀[R]^k M`, of ranks `(n choose k)`, produces. -/
theorem finrank_eq_sum_choose [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (CliffordAlgebra Q) =
      ∑ k ∈ Finset.range (finrank R M + 1), (finrank R M).choose k := by
  rw [finrank_eq_two_pow, Nat.sum_range_choose]

/-- A Clifford algebra of a finite free module has positive rank, its rank being a power of two. -/
theorem finrank_pos [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    0 < finrank R (CliffordAlgebra Q) := by
  rw [finrank_eq_two_pow]
  positivity

end General

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  (Q : QuadraticForm R M)

/-- The basis of `CliffordAlgebra Q` attached to a basis `b` of `M`, indexed by the finite subsets
of the index set of `b`, obtained by transporting Mathlib's basis of `ExteriorAlgebra R M` along
`CliffordAlgebra.equivExterior`.

Its elements are not products of generators by construction; see the implementation notes.

`@[expose]` because the characteristic equation `basis_apply` below is a public theorem whose proof
has to unfold this definition. -/
@[expose] noncomputable def basis {I : Type w} [LinearOrder I] (b : Basis I R M) :
    Basis (Finset I) R (CliffordAlgebra Q) :=
  b.ExteriorAlgebra.map (equivExterior Q).symm

@[simp]
theorem basis_apply {I : Type w} [LinearOrder I] (b : Basis I R M) (s : Finset I) :
    basis Q b s = (equivExterior Q).symm (b.ExteriorAlgebra s) :=
  rfl

variable {Q}

/-- For every basis, the basis vector indexed by the empty set is `1`. -/
-- Reduce this index before the general `basis_apply` formula exposes the transported basis.
@[simp high]
theorem basis_empty {I : Type w} [LinearOrder I] (b : Basis I R M) : basis Q b ∅ = 1 := by
  rw [basis_apply, b.exteriorAlgebra_eq_prod_map_sort]
  simp

/-- For every basis, the basis vector indexed by `{i}` is the generator `ι Q (b i)`. -/
-- Reduce this index before the general `basis_apply` formula exposes the transported basis.
@[simp high]
theorem basis_singleton {I : Type w} [LinearOrder I] (b : Basis I R M) (i : I) :
    basis Q b {i} = ι Q (b i) := by
  rw [basis_apply, b.exteriorAlgebra_eq_prod_map_sort]
  simp

variable (Q)

/-- `CliffordAlgebra.equivExterior` sends the basis element `basis Q b s` back to the exterior
algebra basis element `b.ExteriorAlgebra s` it was transported from.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, so the left-hand side is not in normal form. -/
theorem equivExterior_basis {I : Type w} [LinearOrder I] (b : Basis I R M) (s : Finset I) :
    equivExterior Q (basis Q b s) = b.ExteriorAlgebra s := by
  rw [basis_apply, LinearEquiv.apply_symm_apply]

variable {Q} in
/-- **The basis is natural under isometric equivalences**: the algebra map induced by an isometric
equivalence `e : Q ≃ Q'` sends the basis vector of `b` indexed by `s` to the basis vector of the
transported basis `b.map e` indexed by `s`. -/
theorem map_basis {M' : Type*} [AddCommGroup M'] [Module R M'] {Q' : QuadraticForm R M'}
    (e : Q.IsometryEquiv Q') {I : Type w} [LinearOrder I] (b : Basis I R M) (s : Finset I) :
    map e.toIsometry (basis Q b s) = basis Q' (b.map e.toLinearEquiv) s := by
  apply (equivExterior Q').injective
  rw [equivExterior_map, equivExterior_basis, equivExterior_basis]
  exact b.map_exteriorAlgebra s e.toLinearEquiv

/-- A Clifford algebra has the rank of the exterior algebra of the same module. The right-hand side
does not mention `Q`: deforming the quadratic form deforms the multiplication and leaves the
underlying module alone. -/
theorem rank_eq_rank_exteriorAlgebra :
    Module.rank R (CliffordAlgebra Q) = Module.rank R (ExteriorAlgebra R M) :=
  (equivExterior Q).rank_eq

/-- A Clifford algebra has the finite rank of the exterior algebra of the same module; the
finite-rank form of `rank_eq_rank_exteriorAlgebra`, again independent of `Q`. -/
theorem finrank_eq_finrank_exteriorAlgebra :
    finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) :=
  (equivExterior Q).finrank_eq

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- **Each half of the `ℤ/2`-grading is exactly half of the Clifford algebra**, over a field and
for a nonzero space, whatever the quadratic form.

The two halves are complementary (`CliffordAlgebra.evenOdd_isCompl`), so their dimensions add up to
the whole; and they are equidimensional by `CliffordAlgebra.nonempty_evenOddEquivAddOne`, which
produces an odd linear automorphism out of a vector and a linear functional rather than out of an
anisotropic vector, so it covers the zero form — the exterior algebra — as well. The hypothesis
`V ≠ 0` cannot be dropped: for `V = 0` the Clifford algebra is `K` and entirely even. -/
theorem two_mul_finrank_evenOdd [Nontrivial V] [Module.Finite K (CliffordAlgebra Q)] (i : ZMod 2) :
    2 * finrank K (evenOdd Q i) = finrank K (CliffordAlgebra Q) := by
  have hsum : finrank K (evenOdd Q 0) + finrank K (evenOdd Q 1) = finrank K (CliffordAlgebra Q) :=
    Submodule.finrank_add_eq_of_isCompl (evenOdd_isCompl Q)
  have hswap : finrank K (evenOdd Q 0) = finrank K (evenOdd Q 1) := by
    obtain ⟨f⟩ := nonempty_evenOddEquivAddOne Q 0
    -- `f` relates `evenOdd Q 0` to `evenOdd Q (0 + 1)`. Simplification does not close the gap to
    -- `evenOdd Q 1`: the numerals of `ZMod 2` elaborate through `OfNat`, not `Zero.zero`/`One.one`,
    -- so `zero_add` never matches the index. Name the index equation and rewrite the goal by it.
    have hone : (1 : ZMod 2) = 0 + 1 := by decide
    rw [hone]
    exact f.finrank_eq
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl <;> omega

/-- **Half of a power of two is one power of two down.** Whenever the Clifford algebra of a nonzero
space is counted by a positive power of two, `CliffordAlgebra.two_mul_finrank_evenOdd` splits that
count and each half of the `ℤ/2`-grading has dimension `2 ^ (n - 1)`.

The count of the whole algebra is left as a hypothesis: it is supplied by
`CliffordAlgebra.finrank_eq_two_pow`. -/
theorem finrank_evenOdd_of_finrank_eq_two_pow [Nontrivial V]
    [Module.Finite K (CliffordAlgebra Q)] {n : ℕ} (hn : 0 < n)
    (hQ : finrank K (CliffordAlgebra Q) = 2 ^ n) (i : ZMod 2) :
    finrank K (evenOdd Q i) = 2 ^ (n - 1) := by
  have hhalf := two_mul_finrank_evenOdd Q i
  rw [hQ] at hhalf
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
  omega

/-- Over a field, each half of the `ℤ/2`-grading of the Clifford algebra of a nonzero
finite-dimensional space has half the dimension of the whole: `2 ^ (n - 1)` for `n = finrank K V`.
The whole algebra is counted by `CliffordAlgebra.finrank_eq_two_pow` and halved by
`CliffordAlgebra.two_mul_finrank_evenOdd`; neither needs a hypothesis on the quadratic form, so this
covers the zero form, the even and odd halves of an exterior algebra, as well. -/
theorem finrank_evenOdd [Module.Finite K V] [Nontrivial V] (i : ZMod 2) :
    finrank K (evenOdd Q i) = 2 ^ (finrank K V - 1) :=
  finrank_evenOdd_of_finrank_eq_two_pow Q Module.finrank_pos (finrank_eq_two_pow Q) i

/-- Over a field, the even Clifford algebra of a nonzero
finite-dimensional space has dimension `2 ^ (n - 1)`, one power of two below the whole algebra.
This is the dimension count behind the identification of the even subalgebra with a product of two
matrix algebras one size down. -/
theorem finrank_even [Module.Finite K V] [Nontrivial V] :
    finrank K (_root_.CliffordAlgebra.even Q) = 2 ^ (finrank K V - 1) :=
  (LinearEquiv.ofEq _ _ (_root_.CliffordAlgebra.even_toSubmodule Q)).finrank_eq.trans
    (finrank_evenOdd Q 0)

/-- **Only even-dimensional spaces have spinor modules.** If `CliffordAlgebra Q` is isomorphic to
the endomorphism algebra of `S`, then `finrank K V` is even: comparing dimensions gives
`2 ^ finrank K V = (finrank K S) ^ 2`. -/
theorem even_finrank_of_algEquiv_end [Module.Finite K V] {S : Type*}
    [AddCommGroup S] [Module K S] (ρ : CliffordAlgebra Q ≃ₐ[K] Module.End K S) :
    Even (finrank K V) := by
  have : Module.Finite K (Module.End K S) := Module.Finite.equiv ρ.toLinearEquiv
  have := Module.Finite.of_finite_end K S
  have hdim := ρ.toLinearEquiv.finrank_eq
  rw [finrank_eq_two_pow, Module.finrank_linearMap] at hdim
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hdim.symm)
  rw [hk, ← pow_add] at hdim
  exact ⟨k, Nat.pow_right_injective le_rfl hdim⟩

/-- **The dimension of a spinor module.** If the Clifford algebra acts on a module `S` as the whole
endomorphism algebra `End_K S`, then `S` is finite-dimensional, `n = finrank K V` is even
(`CliffordAlgebra.even_finrank_of_algEquiv_end`) and `dim S = 2 ^ (n / 2)`: the algebra has
dimension `2 ^ n` and `End_K S` has dimension `(dim S) ^ 2`. -/
theorem finrank_eq_two_pow_of_bijective_lsmul [Module.Finite K V]
    {S : Type*} [AddCommGroup S] [Module K S] [Module (CliffordAlgebra Q) S]
    [IsScalarTower K (CliffordAlgebra Q) S]
    (h : Function.Bijective (Algebra.lsmul K K S : CliffordAlgebra Q →ₐ[K] Module.End K S)) :
    finrank K S = 2 ^ (finrank K V / 2) := by
  let ρ := AlgEquiv.ofBijective _ h
  have hV := even_finrank_of_algEquiv_end Q ρ
  have : Module.Finite K (Module.End K S) := Module.Finite.equiv ρ.toLinearEquiv
  have := Module.Finite.of_finite_end K S
  have hdim := ρ.toLinearEquiv.finrank_eq
  rw [finrank_eq_two_pow, Module.finrank_linearMap, ← Nat.div_two_mul_two_of_even hV, pow_mul,
    sq] at hdim
  exact Nat.mul_self_inj.1 hdim.symm

end Field

end CliffordAlgebra
