/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The fixed points of the `q`-power map in an extension of a finite field

For a finite field `K` with `q` elements and any field extension `L`, an element of `L` is fixed by
the `q`-power map exactly when it comes from `K`:

`a ^ q = a ↔ a ∈ Set.range (algebraMap K L)`.

So an element outside `K` is moved by the map. In a quadratic extension the map is moreover an
involution, since `L` then has `q²` elements, and it therefore exchanges the two roots of the
minimal polynomial of such an element; in particular it keeps it outside `K`. Those statements are
what the elliptic conjugacy classes of `GL₂(𝔽_q)` are read off from.

## Main results

* `TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`: the criterion above, with
  `TauCeti.FiniteField.pow_natCard_eq_self_iff` its `Nat.card` spelling.
* `TauCeti.algebraMap_bijective_of_pow_card_eq_self`: its immediate global consequence, that an
  extension *all* of whose elements are fixed by the `q`-power map is `K` itself.
* `TauCeti.FiniteField.pow_natCard_pow_natCard`: in a quadratic extension the `q`-power map is an
  involution, with `TauCeti.FiniteField.pow_natCard_ne` and
  `TauCeti.FiniteField.pow_natCard_notMem_range_algebraMap` its two consequences for an element
  outside `K`.

Mathlib has the easy direction (`FiniteField.pow_card`) but not the equivalence.
`IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field of a Galois extension by
being fixed, but it needs `[FiniteDimensional F E]` and quantifies over the whole Galois group
rather than the single `q`-power map.

Nothing is assumed of `L` beyond being a field extension: in particular it need not be
algebraically closed, which is the only case the source states.

This is the elementary field-theoretic input to the Silverman V.1 route to the Hasse bound: it says
that the `K`-rational coordinates are exactly the Frobenius-fixed ones.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/Curves/FrobeniusFixedLocus.lean`, declaration `frobenius_fixed_iff_mem_baseField`.

Changes from the source. It is stated there only for `L = AlgebraicClosure K`; here `L` is an
arbitrary field extension, since nothing in the argument uses algebraic closedness. The source
builds the root-set transport by hand, through a separability argument and a finset count; here
that is Mathlib's `Splits.image_rootSet` applied to `FiniteField.isSplittingField_sub`. And the
source's other public theorem is stated in terms of its own `private` finsets, so it cannot be
applied from outside; it is not reproduced. Nine declarations become one.
-/

public section

open Polynomial

namespace TauCeti

namespace FiniteField

/-- **An element of a field extension of a finite field is fixed by the `q`-power map exactly when
it comes from the base field**, where `q` is the cardinality of the base. -/
@[simp]
theorem pow_card_eq_self_iff_mem_range_algebraMap {K L : Type*} [Field K] [Fintype K]
    [CommRing L] [IsDomain L] [Algebra K L] (a : L) :
    a ^ Fintype.card K = a ↔ a ∈ Set.range (algebraMap K L) := by
  classical
  -- `X ^ q - X` splits over `K` with every element a root, and `Splits.image_rootSet`
  -- transports that root set along `K → L`
  have hne : (X ^ Fintype.card K - X : K[X]) ≠ 0 :=
    _root_.FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hsplits : ((X ^ Fintype.card K - X : K[X]).map (algebraMap K K)).Splits :=
    IsSplittingField.splits (L := K) (X ^ Fintype.card K - X)
  have himg := hsplits.image_rootSet (Algebra.ofId K L)
  have hK : (X ^ Fintype.card K - X : K[X]).rootSet K = Set.univ := by
    simp [Polynomial.rootSet_def, Polynomial.aroots_def, Algebra.algebraMap_self,
      _root_.FiniteField.roots_X_pow_card_sub_X K]
  rw [Set.ext_iff] at himg
  have := himg a
  simp only [hK, Set.image_univ, Algebra.ofId_apply, mem_rootSet_of_ne hne, aeval_def,
    eval₂_sub, eval₂_X_pow, eval₂_X, sub_eq_zero] at this
  exact this.symm

section Finite

variable {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]

/-- **The `Nat.card` spelling of
`TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`**, for a base field given as
`Finite` rather than as a `Fintype`. -/
@[simp]
theorem pow_natCard_eq_self_iff (a : L) :
    a ^ Nat.card K = a ↔ a ∈ Set.range (algebraMap K L) := by
  let _ := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact pow_card_eq_self_iff_mem_range_algebraMap a

/-- **An element outside the base field is not fixed by the `q`-power map.** -/
theorem pow_natCard_ne {a : L} (ha : a ∉ Set.range (algebraMap K L)) : a ^ Nat.card K ≠ a :=
  fun h => ha ((pow_natCard_eq_self_iff a).mp h)

/-! ### Quadratic extensions -/

/-- **In a quadratic extension of a field with `q` elements the `q`-power map is an involution**:
`L` has `q²` elements, so `a ^ (q²) = a`. -/
@[simp]
theorem pow_natCard_pow_natCard (h2 : Module.finrank K L = 2) (a : L) :
    (a ^ Nat.card K) ^ Nat.card K = a := by
  have : Module.Finite K L := Module.finite_of_finrank_eq_succ (n := 1) h2
  have : Finite L := Module.finite_of_finite K
  let _ := Fintype.ofFinite L
  have hcard : Nat.card L = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := L), h2]
  rw [← pow_mul, ← pow_two, ← hcard, Nat.card_eq_fintype_card]
  exact _root_.FiniteField.pow_card a

/-- **In a quadratic extension the `q`-th power of an element outside the base field is again
outside it**: the `q`-power map is an involution there, so a fixed value would force `a` itself to
be fixed. -/
theorem pow_natCard_notMem_range_algebraMap (h2 : Module.finrank K L = 2) {a : L}
    (ha : a ∉ Set.range (algebraMap K L)) : a ^ Nat.card K ∉ Set.range (algebraMap K L) := by
  intro hmem
  have h1 := (pow_natCard_eq_self_iff _).mpr hmem
  rw [pow_natCard_pow_natCard h2] at h1
  exact ha ((pow_natCard_eq_self_iff a).mp h1.symm)

end Finite

end FiniteField

/-- **A field extension in which `x ^ |K| = x` is `K` itself.** Every element of the extension is
then in the range of the algebra map by
`TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`. -/
theorem algebraMap_bijective_of_pow_card_eq_self {K L : Type*} [Field K] [Fintype K] [CommRing L]
    [IsDomain L] [Algebra K L] (h : ∀ x : L, x ^ Fintype.card K = x) :
    Function.Bijective (algebraMap K L) :=
  ⟨(algebraMap K L).injective,
    fun x => (FiniteField.pow_card_eq_self_iff_mem_range_algebraMap x).mp (h x)⟩

end TauCeti
