/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The sum of the positive coroots as a cocharacter

Let `P` be a root datum with character lattice `M` and cocharacter lattice `N`, and let `b` be a
base of `P`. The sum of the positive coroots

```text
2ρ^∨ = ∑_{α > 0} α^∨ ∈ N
```

is integral, whereas the half-sum `ρ^∨` need not be. Through the perfect pairing of `P` it is a
cocharacter `RootPairing.twoWeylCocharacter P b : Multiplicative M →* Multiplicative ℤ` of the
diagonalizable group `D(M)`, the split torus with character lattice `M`. A character `m` pairs
with it to `posCorootSum P b m`, and a root `α` to twice its height,
`⟨α, 2ρ^∨⟩ = 2 ht(α)`. So every positive root pairs positively with `2ρ^∨` and every negative root
negatively, and on points the character `α` composed with the cocharacter `2ρ^∨` is the power map
`u ↦ u ^ (2 ht(α))` of `𝔾ₘ`. Thus `2ρ^∨` is a regular cocharacter which is positive on the positive
system of `b`.

For the split torus `D(Multiplicative (σ →₀ ℤ))`, whose cocharacters are identified with
`σ → ℤ` by `TauCeti.SplitTorus.cocharEquiv`, a root datum whose pairing is the split-torus pairing
`TauCeti.SplitTorus.dotPairing` gives `2ρ^∨` the coordinates of the sum of the positive coroots
(`RootPairing.cocharEquiv_twoWeylCocharacter_eq_sum`).

## Main declarations

* `RootPairing.twoWeylCocharacter`: the cocharacter `2ρ^∨` of `D(M)`.
* `RootPairing.pairing_ofAdd_twoWeylCocharacter_eq_posCorootSum`: `⟨m, 2ρ^∨⟩` is the sum of the
  pairings of `m` with the positive coroots.
* `RootPairing.pairing_ofAdd_root_twoWeylCocharacter`: `⟨α, 2ρ^∨⟩ = 2 ht(α)`.
* `RootPairing.pairing_ofAdd_root_twoWeylCocharacter_pos_iff`: a root pairs positively with `2ρ^∨`
  exactly when it is positive.
* `RootPairing.charPoints_comp_cocharPoints_twoWeylCocharacter`: on points, `α ∘ 2ρ^∨` is the
  power endomorphism of `𝔾ₘ` with exponent `2 ht(α)`.
* `RootPairing.cocharEquiv_twoWeylCocharacter_eq_sum`: for a root datum on the split-torus lattices,
  the coordinates of `2ρ^∨` are the sum of the positive coroots.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3 (heights
  of roots).
* J. S. Milne, *Algebraic Groups* (2017), Chapter 21 (positive roots of a split reductive group).
-/

public section

open TauCeti

namespace RootPairing

section General

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Finite ι] (P : RootDatum ι M N)
  (b : P.Base)

/-- **The cocharacter `2ρ^∨`**: the sum of the positive coroots of the base `b`, as a cocharacter
of the diagonalizable group `D(M)` through the perfect pairing of `P`. It sends a character `m` to
its pairing with the sum of the positive roots of the dual root datum, written multiplicatively.
It is the cocharacter counterpart of `TauCeti.twoWeylVector`. -/
noncomputable def twoWeylCocharacter : Multiplicative M →* Multiplicative ℤ :=
  (P.toLinearMap.flip (twoWeylVector P.flip b.flip)).toAddMonoidHom.toMultiplicative

/-- The pairing of a character with `2ρ^∨` is its pairing in `P` with the sum of the positive roots
of the dual root datum. -/
@[simp]
theorem pairing_ofAdd_twoWeylCocharacter (m : M) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd m) (P.twoWeylCocharacter b) =
      P.toLinearMap m (twoWeylVector P.flip b.flip) := by
  simp [DiagonalizableGroup.pairing_def, twoWeylCocharacter]

variable [P.IsReduced]

/-- **The pairing of a character with `2ρ^∨` is the sum of its pairings with the positive
coroots.** -/
theorem pairing_ofAdd_twoWeylCocharacter_eq_posCorootSum (m : M) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd m) (P.twoWeylCocharacter b) =
      posCorootSum P b m := by
  simp only [pairing_ofAdd_twoWeylCocharacter, twoWeylVector_flip, map_sum, posCorootSum_def,
    coroot', LinearMap.flip_apply]

/-- **A root pairs with `2ρ^∨` to twice its height**, `⟨α, 2ρ^∨⟩ = 2 ht(α)`, the height being
taken relative to `b`. -/
theorem pairing_ofAdd_root_twoWeylCocharacter (i : ι) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) =
      2 * b.height i := by
  have := P.flip_isReduced
  rw [pairing_ofAdd_twoWeylCocharacter]
  -- The pairing of `P.root i` in `P` is the coroot functional of the index `i` in `P.flip`.
  exact coroot'_twoWeylVector_eq_two_mul_height_flip P.flip b.flip i

/-- **Every positive root pairs positively with `2ρ^∨`.** -/
theorem pairing_ofAdd_root_twoWeylCocharacter_pos {i : ι} (hi : i ∈ posRoots P b) :
    0 < DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) := by
  rw [pairing_ofAdd_root_twoWeylCocharacter]
  have := one_le_height_of_mem_posRoots P b hi
  omega

/-- **Every negative root pairs negatively with `2ρ^∨`.** -/
theorem pairing_ofAdd_root_twoWeylCocharacter_neg {i : ι} (hi : i ∈ negRoots P b) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) < 0 := by
  rw [pairing_ofAdd_root_twoWeylCocharacter]
  have := height_neg_of_mem_negRoots P b hi
  omega

/-- **A root pairs positively with `2ρ^∨` exactly when it is positive.** -/
theorem pairing_ofAdd_root_twoWeylCocharacter_pos_iff (i : ι) :
    0 < DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) ↔
      i ∈ posRoots P b := by
  refine ⟨fun h ↦ ?_, P.pairing_ofAdd_root_twoWeylCocharacter_pos b⟩
  by_contra hi
  exact (P.pairing_ofAdd_root_twoWeylCocharacter_neg b
    ((not_mem_posRoots_iff_mem_negRoots P b i).mp hi)).not_gt h

/-- **No root pairs to `0` with `2ρ^∨`**: `2ρ^∨` is a regular cocharacter. -/
theorem pairing_ofAdd_root_twoWeylCocharacter_ne_zero (i : ι) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) ≠ 0 := by
  rw [pairing_ofAdd_root_twoWeylCocharacter]
  have := b.height_ne_zero i
  omega

/-- **A root pairs nonnegatively with `2ρ^∨` exactly when it is positive.** -/
theorem pairing_ofAdd_root_twoWeylCocharacter_nonneg_iff (i : ι) :
    0 ≤ DiagonalizableGroup.pairing (Multiplicative.ofAdd (P.root i)) (P.twoWeylCocharacter b) ↔
      i ∈ posRoots P b := by
  rw [← pairing_ofAdd_root_twoWeylCocharacter_pos_iff, le_iff_lt_or_eq,
    or_iff_left (P.pairing_ofAdd_root_twoWeylCocharacter_ne_zero b i).symm]

/-- **On points, a root composed with `2ρ^∨` is the power map with exponent `2 ht(α)`.** For every
`R`-algebra `A`, the cocharacter `2ρ^∨` sends a unit `u` to a point of `D(M)` on which the root
`α` takes the value `u ^ (2 ht(α))`. -/
theorem charPoints_comp_cocharPoints_twoWeylCocharacter {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] (i : ι) :
    (DiagonalizableGroup.charPoints (R := R) (A := A) (Multiplicative.ofAdd (P.root i))).comp
        (DiagonalizableGroup.cocharPoints (P.twoWeylCocharacter b)) =
      DiagonalizableGroup.powEnd (2 * b.height i) := by
  rw [DiagonalizableGroup.charPoints_comp_cocharPoints, pairing_ofAdd_root_twoWeylCocharacter]

end General

section SplitTorus

variable {ι σ : Type*} [Finite ι] {P : RootDatum ι (σ →₀ ℤ) (σ → ℤ)} (b : P.Base)

/-- For a root datum on the split-torus lattices whose pairing is the split-torus pairing, the
coordinates of `2ρ^∨` are the sum of the positive roots of the dual root datum. -/
theorem cocharEquiv_twoWeylCocharacter (hP : P.toLinearMap = SplitTorus.dotPairing) :
    SplitTorus.cocharEquiv (P.twoWeylCocharacter b) = twoWeylVector P.flip b.flip := by
  classical
  ext i
  rw [SplitTorus.cocharEquiv_apply, ← DiagonalizableGroup.pairing_def,
    pairing_ofAdd_twoWeylCocharacter, hP, SplitTorus.dotPairing_apply,
    Finsupp.sum_single_index (zero_mul _), one_mul]

/-- **The coordinates of `2ρ^∨` are the sum of the positive coroots**, for a root datum on the
split-torus lattices whose pairing is the split-torus pairing. -/
theorem cocharEquiv_twoWeylCocharacter_eq_sum [P.IsReduced]
    (hP : P.toLinearMap = SplitTorus.dotPairing) :
    SplitTorus.cocharEquiv (P.twoWeylCocharacter b) = ∑ i ∈ posRootsFinset P b, P.coroot i := by
  rw [cocharEquiv_twoWeylCocharacter b hP, twoWeylVector_flip]

end SplitTorus

end RootPairing
