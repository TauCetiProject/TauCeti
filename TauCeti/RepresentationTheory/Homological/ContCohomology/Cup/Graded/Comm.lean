/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology

/-!
# Graded commutativity of the cup product

Let `P : TopPairing X Y Z` be a coefficient pairing of topological representations of a
topological group `G`, and let `P.flip : TopPairing Y X Z` be the opposite pairing
`TauCeti.TopPairing.flip`, `P.flip.bil y x = P.bil x y`. On continuous cohomology the cup
products in the two orders are related by graded commutativity,

```text
a ⌣_P b = (-1)^(m n) (b ⌣_{P.flip} a),     a ∈ Hᵐ(G, X), b ∈ Hⁿ(G, Y),
```

which this file proves in every bidegree (`TauCeti.TopPairing.cup_gradedComm`). In bidegree
`(1, 1)` it reads `cup P 1 1 a b = - cup P.flip 1 1 b a`, the identity against which the cup
square `H¹(G, M) × H¹(G, M) → H²(G, M)` of a commutative coefficient ring is stated.

In bidegree `(0, n)` the identity already holds on cocycles. A homogeneous zero-cocycle is a
constant function, and the two Alexander–Whitney products therefore pair the same constant
coefficient with the same value of the `n`-cochain. The recursion on Mathlib's iterated-curried
coinduction resolution is recorded by
`TauCeti.TopPairing.resolutionCupPairing_zero_eq_flip`; its restrictions to homogeneous cochains
and cohomology are `TauCeti.TopPairing.cupCochain_zero_eq_flip` and
`TauCeti.TopPairing.cup_zero_eq_flip`.

In general the identity fails on cochains, and the proof is a homotopy: Steenrod's **cup-one
product** `TauCeti.TopPairing.cupOne`. For `a` of degree `m` and `b` of degree `n + 1`
it has degree `m + n` and, in homogeneous coordinates,

```text
(a ∪₁ b) (g₀, …, g_{m+n}) =
  ∑_{i < m} (-1)^((m - 1 - i) n) μ (a (g₀, …, gᵢ, g_{i+n+1}, …, g_{m+n})) (b (gᵢ, …, g_{i+n+1})).
```

On the curried resolution this is a recursion on the first vertex: `a ∪₁ b = 0` when `a` has
degree zero, and `(a ∪₁ b) g = (a g) ∪₁ b + (-1)^(m n) ((b g) ⌣_{P.flip} (a g))` when `a` has
degree `m + 1`, the second term collecting the summand `i = 0`. Its boundary is
(`TauCeti.TopPairing.d_cupOne`)

```text
d (a ∪₁ b) = (d a) ∪₁ b - (-1)^m (a ∪₁ d b) + (-1)^m (a ⌣ b) - (-1)^(m n) (b ⌣_{P.flip} a),
```

For cocycles only the last two terms survive, so `(-1)^m (a ∪₁ b)` is a primitive of
`(a ⌣ b) - (-1)^(m (n + 1)) (b ⌣_{P.flip} a)`, which is graded commutativity in bidegree
`(m, n + 1)`. Bidegree `(m, 0)` is the case `(0, m)` for the opposite pairing.

The same homotopy in bidegree `(1, 1)` is formalized on the explicit inhomogeneous model of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product` as
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`, with descent
`TauCeti.ContCohomology.explicitCup11_eq_neg_flip`; this file works on Mathlib's
`continuousCohomology`, so that it applies to `TauCeti.TopPairing.cup`.

## Main definitions

* `TauCeti.TopPairing.cupOne`: the cup-one product on the coinduced resolution, with
  explicit total degree.
* `TauCeti.TopPairing.cupOneCochain`: the cup-one product of homogeneous cochains, as a
  bilinear map.

## Main results

* `TauCeti.TopPairing.cup_zero_eq_flip`: graded commutativity in bidegree `(0, n)`, without a
  sign.
* `TauCeti.TopPairing.d_cupOne`: the boundary of the cup-one product.
* `TauCeti.TopPairing.d_cupOneCochain`: the boundary of the cup-one product of two
  cocycles is `(-1)^m (a ⌣ b) - (-1)^(m n) (b ⌣ᵒᵖ a)`.
* `TauCeti.TopPairing.cup_gradedComm`: **graded commutativity in every bidegree**,
  `a ⌣_P b = (-1)^(m n) (b ⌣_{P.flip} a)`, with the degree transport between `n + m` and `m + n`
  explicit.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.6).
* N. E. Steenrod, *Products of cocycles and extensions of mappings*, Ann. of Math. 48 (1947),
  290–320, for the `∪₁` product.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.4).
-/

public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology ContinuousMap

universe u v w

namespace TopPairing

section degreeZero

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### Graded commutativity with a degree-zero cocycle -/

/-- Pairing a fixed coefficient pointwise with an `(n + 1)`-fold iterated function is the
Alexander–Whitney pairing in the opposite order against the constant zero-degree resolution
element. This is the recursive identity behind graded commutativity in bidegree `(0, n)`. -/
private theorem pointwise_succ_eq_flip_resolutionCup : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V),
    P.pointwise (n + 1) (k + 1) (congrArg Nat.succ hk) (x, b) =
      P.flip.resolutionCup n 0 k (by omega) (b, (TopRep.d X 0).hom x)
  | 0, 0, _, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.pointwise_succ_apply, P.pointwise_zero_apply,
        P.flip.resolutionCup_zero_apply, P.flip.pointwise_zero_apply, flip_bil]
      rfl
  | n + 1, k + 1, hk, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.pointwise_succ_apply, P.flip.resolutionCup_succ_apply]
      exact pointwise_succ_eq_flip_resolutionCup n k (Nat.succ.inj hk) x (b g)

/-- The Alexander–Whitney pairing of the constant zero-degree resolution element with a degree
`n` element agrees with the opposite pairing in bidegree `(n, 0)`. -/
private theorem resolutionCup_zero_eq_flip : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup 0 n k (by omega) ((TopRep.d X 0).hom x, b) =
      P.flip.resolutionCup n 0 k (by omega) (b, (TopRep.d X 0).hom x)
  | 0, 0, _, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.resolutionCup_zero_apply, P.flip.resolutionCup_zero_apply,
        P.pointwise_zero_apply, P.flip.pointwise_zero_apply, flip_bil]
  | n + 1, k + 1, hk, x, b => ContinuousMap.ext fun g ↦ by
      rw [P.resolutionCup_zero_apply, P.flip.resolutionCup_succ_apply]
      exact P.pointwise_succ_eq_flip_resolutionCup n k (Nat.succ.inj hk) x (b g)

/-- **Graded commutativity on the resolution in bidegree `(0, n)`**, for a constant
zero-degree element. The opposite product is transported from degree `n + 0` to degree `0 + n`.
-/
theorem resolutionCupPairing_zero_eq_flip (n : ℕ) (x : X.V)
    (b : (TopRep.resolution'X Y n).V) :
    P.resolutionCupPairing 0 n ((TopRep.d X 0).hom x) b =
      ((TopRep.resolution Z).XIsoOfEq (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCupPairing n 0 b ((TopRep.d X 0).hom x)) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply]
  calc
    _ = P.flip.resolutionCup n 0 (0 + n) (by omega)
        (b, (TopRep.d X 0).hom x) :=
      P.resolutionCup_zero_eq_flip n (0 + n) (by omega) x b
    _ = ((TopRep.resolution Z).XIsoOfEq
          (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCup n 0 (n + 0) (Nat.add_comm n 0)
          (b, (TopRep.d X 0).hom x)) :=
      (P.flip.resolutionCup_cast (Nat.add_comm n 0) (by omega)
        (by omega : n + 0 + 1 = 0 + n + 1) (b, (TopRep.d X 0).hom x)).symm

/-- **Graded commutativity of homogeneous cochains in bidegree `(0, n)`**: if `a` is a
zero-cocycle, then `a ⌣_P b` is the degree transport of `b ⌣_{P.flip} a`. No cocycle condition
on `b` is needed. -/
theorem cupCochain_zero_eq_flip (n : ℕ) {a : (TopRep.homogeneousCochains X).X 0}
    (ha : ((TopRep.homogeneousCochains X).d 0 1).hom a = 0)
    (b : (TopRep.homogeneousCochains Y).X n) :
    P.cupCochain 0 n a b =
      ((TopRep.homogeneousCochains Z).XIsoOfEq (by omega : n + 0 = 0 + n)).hom
        (P.flip.cupCochain n 0 b a) := by
  apply Subtype.ext
  rw [coe_cupCochain, ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply,
    coe_cupCochain, TopRep.homogeneousCochains.eq_d_zero_apply_of_d_eq_zero ha]
  exact P.resolutionCupPairing_zero_eq_flip n (a.val 1) b.val

/-- **Graded commutativity of the cup product in bidegree `(0, n)`**:
`a ⌣_P b = b ⌣_{P.flip} a`, with the opposite product transported from degree `n + 0` to
degree `0 + n`. This is the zero-degree base case of the all-bidegree graded-commutativity
homotopy. -/
theorem cup_zero_eq_flip (n : ℕ) (a : continuousCohomology 0 X)
    (b : continuousCohomology n Y) :
    P.cup 0 n a b =
      (ContinuousCohomology.degreeCast Z (by omega : n + 0 = 0 + n)).hom
        (P.flip.cup n 0 b a) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains X).homologyπ_surjective 0 a
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains Y).homologyπ_surjective n b
  rw [cup_π, cup_π]
  refine ContinuousCohomology.π_eq_degreeCast_π (by omega : n + 0 = 0 + n) _ _ ?_
  rw [iCycles_cupCocycles, iCycles_cupCocycles]
  exact P.cupCochain_zero_eq_flip n
    ((TopRep.homogeneousCochains X).d_iCycles_apply 1 a) _

end degreeZero

section cupOne

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### The cup-one product on the resolution -/

/-- **The cup-one product on the coinduced resolution**, Steenrod's `∪₁`, with explicit total
degree: an element `a` of the `(m + 1)`-st term of the resolution of `X` (a degree-`m` element)
paired with an element `b` of the `(n + 2)`-nd term of the resolution of `Y` (a degree-`(n + 1)`
element) gives an element of the `(k + 1)`-st term of the resolution of `Z`, for `k = n + m`.

It vanishes for `m = 0`, and otherwise fixes the first vertex:
`(a ∪₁ b) g = (a g) ∪₁ b + (-1)^(m n) ((b g) ⌣_{P.flip} (a g))` for `a` of degree `m + 1`. In
homogeneous coordinates this is Steenrod's sum
`∑_{i < m} (-1)^((m - 1 - i) n) μ (a (g₀, …, gᵢ, g_{i+n+1}, …, g_{m+n})) (b (gᵢ, …, g_{i+n+1}))`.
Its boundary is `TauCeti.TopPairing.d_cupOne`. -/
def cupOne : (m n k : ℕ) → k = n + m →
    C((TopRep.resolutionX X (m + 1)).V × (TopRep.resolutionX Y (n + 2)).V,
      (TopRep.resolutionX Z (k + 1)).V)
  | 0, _, _, _ => 0
  | m + 1, n, k + 1, hk =>
    ⟨fun p ↦ (cupOne m n k (by omega)).comp (p.1.prodMk (const G p.2)) +
        (-1 : R) ^ (m * n) • (P.flip.resolutionCup n m k (by omega)).comp (p.2.prodMk p.1),
      by
        refine ((continuous_postcomp _).comp continuous_prodMk_const_right).add ?_
        exact (continuous_const_smul _).comp
          ((continuous_postcomp _).comp (ContinuousMap.continuous_prodMk.comp continuous_swap))⟩
  | _ + 1, _, 0, hk => absurd hk (by omega)

/-- The cup-one product vanishes when the first factor has degree zero. -/
@[simp]
theorem cupOne_zero {n k : ℕ} (hk : k = n + 0) : P.cupOne 0 n k hk = 0 := by
  rw [cupOne]

/-- **The recursion of the cup-one product**: fixing the first vertex `g` leaves the cup-one
product of `a g` with `b`, plus the signed opposite Alexander–Whitney product of `b g` with
`a g`. -/
@[simp]
theorem cupOne_succ_apply {m n k : ℕ} (hk : k + 1 = n + (m + 1))
    (a : C(G, (TopRep.resolutionX X (m + 1)).V)) (b : (TopRep.resolutionX Y (n + 2)).V)
    (g : G) :
    (P.cupOne (m + 1) n (k + 1) hk (a, b) : C(G, (TopRep.resolutionX Z (k + 1)).V)) g =
      P.cupOne m n k (by omega) (a g, b) +
        (-1 : R) ^ (m * n) • P.flip.resolutionCup n m k (by omega) (b g, a g) := by
  rw [cupOne]
  rfl

theorem cupOne_add_left : ∀ (m n k : ℕ) (hk : k = n + m)
    (a a' : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V),
    P.cupOne m n k hk (a + a', b) =
      P.cupOne m n k hk (a, b) + P.cupOne m n k hk (a', b)
  | 0, n, k, hk, a, a', b => by simp only [cupOne_zero, ContinuousMap.zero_apply, add_zero]
  | m + 1, n, k + 1, hk, a, a', b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, cupOne_succ_apply, cupOne_succ_apply,
      cupOne_succ_apply, ContinuousMap.add_apply,
      cupOne_add_left m n k _ (a g) (a' g) b, P.flip.resolutionCup_add_right, smul_add]
    abel

theorem cupOne_smul_left : ∀ (m n k : ℕ) (hk : k = n + m) (r : R)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V),
    P.cupOne m n k hk (r • a, b) = r • P.cupOne m n k hk (a, b)
  | 0, n, k, hk, r, a, b => by simp only [cupOne_zero, ContinuousMap.zero_apply, smul_zero]
  | m + 1, n, k + 1, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, cupOne_succ_apply, cupOne_succ_apply,
      ContinuousMap.smul_apply, cupOne_smul_left m n k _ r (a g) b,
      P.flip.resolutionCup_smul_right, smul_add, smul_comm r]

theorem cupOne_add_right : ∀ (m n k : ℕ) (hk : k = n + m)
    (a : (TopRep.resolutionX X (m + 1)).V) (b b' : (TopRep.resolutionX Y (n + 2)).V),
    P.cupOne m n k hk (a, b + b') =
      P.cupOne m n k hk (a, b) + P.cupOne m n k hk (a, b')
  | 0, n, k, hk, a, b, b' => by simp only [cupOne_zero, ContinuousMap.zero_apply, add_zero]
  | m + 1, n, k + 1, hk, a, b, b' => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, cupOne_succ_apply, cupOne_succ_apply,
      cupOne_succ_apply, ContinuousMap.add_apply,
      cupOne_add_right m n k _ (a g) b b', P.flip.resolutionCup_add_left, smul_add]
    abel

theorem cupOne_smul_right : ∀ (m n k : ℕ) (hk : k = n + m) (r : R)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V),
    P.cupOne m n k hk (a, r • b) = r • P.cupOne m n k hk (a, b)
  | 0, n, k, hk, r, a, b => by simp only [cupOne_zero, ContinuousMap.zero_apply, smul_zero]
  | m + 1, n, k + 1, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, cupOne_succ_apply, cupOne_succ_apply,
      ContinuousMap.smul_apply, cupOne_smul_right m n k _ r (a g) b,
      P.flip.resolutionCup_smul_left, smul_add, smul_comm r]

/-- The cup-one product preserves subtraction in its first argument. -/
private theorem cupOne_sub_left (m n k : ℕ) (hk : k = n + m)
    (a a' : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V) :
    P.cupOne m n k hk (a - a', b) =
      P.cupOne m n k hk (a, b) - P.cupOne m n k hk (a', b) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, P.cupOne_add_left, ← neg_one_smul R a',
    P.cupOne_smul_left, neg_one_smul]

/-- **The cup-one product is equivariant.** -/
theorem cupOne_ρ : ∀ (m n k : ℕ) (hk : k = n + m) (g : G)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V),
    P.cupOne m n k hk
        ((TopRep.resolutionX X (m + 1)).ρ g a, (TopRep.resolutionX Y (n + 2)).ρ g b) =
      (TopRep.resolutionX Z (k + 1)).ρ g (P.cupOne m n k hk (a, b))
  | 0, n, k, hk, g, a, b => by simp only [cupOne_zero, ContinuousMap.zero_apply, map_zero]
  | m + 1, n, k + 1, hk, g, a, b => ContinuousMap.ext fun h ↦ by
    rw [TopRep.resolutionX_succ_ρ_apply_apply, cupOne_succ_apply,
      cupOne_succ_apply, TopRep.resolutionX_succ_ρ_apply_apply,
      TopRep.resolutionX_succ_ρ_apply_apply, cupOne_ρ m n k _ g (a (g⁻¹ * h)) b,
      P.flip.resolutionCup_ρ, map_add, map_smul]

/-! ### The boundary of the cup-one product -/

/-- **The cup-one boundary formula on the resolution.** For `a` of degree `m` and `b` of degree
`n + 1`,
`d (a ∪₁ b) = (d a) ∪₁ b - (-1)^m (a ∪₁ d b) + (-1)^m (a ⌣ b) - (-1)^(m n) (b ⌣_{P.flip} a)`.
On cocycles only the last two terms survive, so the cup-one product is a homotopy between
`(-1)^m (a ⌣ b)` and `(-1)^(m n) (b ⌣_{P.flip} a)`. -/
theorem d_cupOne : ∀ (m n k : ℕ) (hk : k = n + m)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 2)).V),
    (TopRep.d Z (k + 1)).hom (P.cupOne m n k hk (a, b)) =
      P.cupOne (m + 1) n (k + 1) (by omega) ((TopRep.d X (m + 1)).hom a, b) -
        (-1 : R) ^ m • P.cupOne m (n + 1) (k + 1) (by omega)
          (a, (TopRep.d Y (n + 2)).hom b) +
        (-1 : R) ^ m • P.resolutionCup m (n + 1) (k + 1) (by omega) (a, b) -
        (-1 : R) ^ (m * n) • P.flip.resolutionCup (n + 1) m (k + 1) (by omega) (b, a)
  | 0, n, k, hk, a, b => ContinuousMap.ext fun g ↦ by
    -- at `g`, the cup-one term is `(b g) ⌣ᵒᵖ a - (b g) ⌣ᵒᵖ (a g)`, and the last factor is
    -- constant, so it cancels against the ordinary cup term
    have hda : ((TopRep.d X 1).hom a : C(G, C(G, X.V))) g =
        a - (TopRep.d X 0).hom (a g) :=
      TopRep.hom_d_succ_apply_apply X 0 a g
    rw [cupOne_zero, ContinuousMap.zero_apply, map_zero, ContinuousMap.zero_apply,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      cupOne_succ_apply, cupOne_zero, cupOne_zero,
      ContinuousMap.zero_apply, ContinuousMap.zero_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply, ContinuousMap.smul_apply, ContinuousMap.zero_apply,
      P.resolutionCup_zero_apply, P.flip.resolutionCup_succ_apply, hda,
      P.flip.resolutionCup_sub_right, ← P.resolutionCup_zero_eq_flip n k (by omega),
      P.resolutionCup_zero_d_zero]
    simp only [zero_mul, pow_zero, one_smul, smul_zero]
    abel
  | m + 1, n, k + 1, hk, a, b => ContinuousMap.ext fun g ↦ by
    have hd : ((TopRep.d Z (k + 2)).hom (P.cupOne (m + 1) n (k + 1) hk (a, b)) :
        C(G, (TopRep.resolutionX Z (k + 2)).V)) g =
        P.cupOne (m + 1) n (k + 1) hk (a, b) -
          (TopRep.d Z (k + 1)).hom ((P.cupOne (m + 1) n (k + 1) hk (a, b) :
            C(G, (TopRep.resolutionX Z (k + 1)).V)) g) :=
      TopRep.hom_d_succ_apply_apply Z (k + 1) _ g
    have hda : (TopRep.d X (m + 1)).hom (a g) =
        a - ((TopRep.d X (m + 2)).hom a : C(G, (TopRep.resolutionX X (m + 2)).V)) g := by
      rw [TopRep.hom_d_succ_apply_apply, sub_sub_cancel]
    have hdb : (TopRep.d Y (n + 1)).hom (b g) =
        b - ((TopRep.d Y (n + 2)).hom b : C(G, (TopRep.resolutionX Y (n + 2)).V)) g := by
      rw [TopRep.hom_d_succ_apply_apply, sub_sub_cancel]
    -- expand the left side at `g` by the recursion, the inductive hypothesis at `a g`, and the
    -- Leibniz rule for the opposite Alexander–Whitney product
    rw [hd, cupOne_succ_apply, map_add, map_smul,
      d_cupOne m n k (by omega) (a g) b,
      P.flip.resolutionCup_leibniz n m k (by omega) (b g) (a g), hda, hdb,
      P.cupOne_sub_left, P.flip.resolutionCup_sub_left,
      P.flip.resolutionCup_sub_right]
    have hexponent : m + 1 + m * (n + 1) = 2 * m + (m * n + 1) := by ring
    have hsign : (-1 : R) ^ (m + 1) * (-1 : R) ^ (m * (n + 1)) = -(-1 : R) ^ (m * n) := by
      rw [← pow_add, hexponent, pow_add, pow_mul,
        neg_one_sq, one_pow, one_mul, pow_succ, mul_neg_one]
    -- expand the right side at `g` by the recursions
    rw [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply,
      cupOne_succ_apply, cupOne_succ_apply, P.resolutionCup_succ_apply,
      P.flip.resolutionCup_succ_apply]
    simp only [smul_add, smul_smul, hsign]
    module

/-! ### The cup-one product of homogeneous cochains -/

/-- **The cup-one product of homogeneous cochains**, as an `R`-bilinear map from `m`-cochains of
`X` and `(n + 1)`-cochains of `Y` to `(m + n)`-cochains of `Z`: the cup-one product of the
underlying elements of the resolution, which is invariant by equivariance. -/
def cupOneCochain (m n : ℕ) : (TopRep.homogeneousCochains X).X m →ₗ[R]
    (TopRep.homogeneousCochains Y).X (n + 1) →ₗ[R] (TopRep.homogeneousCochains Z).X (m + n) :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨P.cupOne m n (m + n) (Nat.add_comm m n) (a.1, b.1), fun g ↦ by
      rw [← P.cupOne_ρ, a.2 g, b.2 g]⟩)
    (fun a a' b ↦ Subtype.ext (P.cupOne_add_left m n _ _ a.1 a'.1 b.1))
    (fun r a b ↦ Subtype.ext (P.cupOne_smul_left m n _ _ r a.1 b.1))
    (fun a b b' ↦ Subtype.ext (P.cupOne_add_right m n _ _ a.1 b.1 b'.1))
    (fun r a b ↦ Subtype.ext (P.cupOne_smul_right m n _ _ r a.1 b.1))

/-- The underlying resolution element of `cupOneCochain` is `cupOne`. -/
-- Not a `simp` lemma, for the same reason as `coe_cupCochain`: `simp` rewrites the implicit
-- carrier `(TopRep.resolution' Z).X (m + n)` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`; use it with `rw`.
theorem coe_cupOneCochain (m n : ℕ) (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X (n + 1)) :
    Subtype.val (P.cupOneCochain m n a b) =
      P.cupOne m n (m + n) (Nat.add_comm m n) (a.1, b.1) := by
  rw [cupOneCochain, LinearMap.mk₂_apply]

/-- **The differential of the cup-one product of two cocycles**: for a cocycle `a` of degree `m`
and a cocycle `b` of degree `n + 1`, `d (a ∪₁ b) = (-1)^m (a ⌣ b) - (-1)^(m n) (b ⌣ᵒᵖ a)`, both
products transported to degree `m + n + 1`. -/
theorem d_cupOneCochain (m n : ℕ) {a : (TopRep.homogeneousCochains X).X m}
    (ha : ((TopRep.homogeneousCochains X).d m (m + 1)).hom a = 0)
    {b : (TopRep.homogeneousCochains Y).X (n + 1)}
    (hb : ((TopRep.homogeneousCochains Y).d (n + 1) (n + 1 + 1)).hom b = 0) :
    ((TopRep.homogeneousCochains Z).d (m + n) (m + n + 1)).hom
        (P.cupOneCochain m n a b) =
      (-1 : R) ^ m • ((TopRep.homogeneousCochains Z).XIsoOfEq
          (by omega : m + (n + 1) = m + n + 1)).hom (P.cupCochain m (n + 1) a b) -
        (-1 : R) ^ (m * n) • ((TopRep.homogeneousCochains Z).XIsoOfEq
          (by omega : n + 1 + m = m + n + 1)).hom (P.flip.cupCochain (n + 1) m b a) := by
  have hda : (TopRep.d X (m + 1)).hom a.val = 0 :=
    (TopRep.homogeneousCochains.d_apply X m a).symm.trans (congrArg Subtype.val ha)
  have hdb : (TopRep.d Y (n + 2)).hom b.val = 0 :=
    (TopRep.homogeneousCochains.d_apply Y (n + 1) b).symm.trans (congrArg Subtype.val hb)
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply, P.coe_cupOneCochain, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_smul,
    ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply,
    ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply, P.coe_cupCochain,
    P.flip.coe_cupCochain, P.resolutionCupPairing_apply, P.flip.resolutionCupPairing_apply,
    P.resolutionCup_cast (hk' := by omega), P.flip.resolutionCup_cast (hk' := by omega),
    P.d_cupOne, hda, hdb,
    ← zero_smul R (0 : (TopRep.resolutionX X (m + 1 + 1)).V), P.cupOne_smul_left,
    ← zero_smul R (0 : (TopRep.resolutionX Y (n + 1 + 2)).V), P.cupOne_smul_right]
  module

/-! ### Graded commutativity on classes -/

/-- After transporting both products to degree `m + n + 1`, the class of `a ⌣ b` is
`(-1)^(m (n + 1))` times the class of `b ⌣ᵒᵖ a`. This is the cocycle-level descent of
`d_cupOneCochain`. -/
private theorem π_cocyclesDegreeCast_cupCocycles (m n : ℕ) (a : cocycles X m)
    (b : cocycles Y (n + 1)) :
    π Z (m + n + 1) (ContinuousCohomology.cocyclesDegreeCast (by omega : m + (n + 1) = m + n + 1)
        (P.cupCocycles m (n + 1) a b)) =
      (-1 : R) ^ (m * (n + 1)) • π Z (m + n + 1) (ContinuousCohomology.cocyclesDegreeCast
        (by omega : n + 1 + m = m + n + 1) (P.flip.cupCocycles (n + 1) m b a)) := by
  rw [← sub_eq_zero, ← map_smul, ← map_sub]
  set L := TopRep.homogeneousCochains Z
  refine (L.homologyπ_eq_zero_iff (m + n + 1) (CochainComplex.prev_nat_succ (m + n))).2
    ⟨(-1 : R) ^ m • P.cupOneCochain m n ((TopRep.homogeneousCochains X).iCycles m a)
      ((TopRep.homogeneousCochains Y).iCycles (n + 1) b),
      L.iCycles_injective (m + n + 1) ?_⟩
  rw [L.iCycles_toCycles_apply, map_smul, P.d_cupOneCochain m n
    ((TopRep.homogeneousCochains X).d_iCycles_apply (m + 1) a)
    ((TopRep.homogeneousCochains Y).d_iCycles_apply (n + 1 + 1) b), map_sub, map_smul,
    ContinuousCohomology.iCycles_cocyclesDegreeCast,
    ContinuousCohomology.iCycles_cocyclesDegreeCast, iCycles_cupCocycles, iCycles_cupCocycles]
  have hsign : (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hsign' : (-1 : R) ^ m * (-1 : R) ^ (m * n) = (-1 : R) ^ (m * (n + 1)) := by
    rw [← pow_add, mul_add_one, add_comm]
  rw [smul_sub, smul_smul, smul_smul, hsign, hsign', one_smul]

/-- **Graded commutativity of the cup product**: `a ⌣_P b = (-1)^(m n) (b ⌣_{P.flip} a)` for
`a` of degree `m` and `b` of degree `n`, with the opposite product transported from degree
`n + m` to degree `m + n`. -/
theorem cup_gradedComm (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n Y) :
    P.cup m n a b =
      (ContinuousCohomology.degreeCast Z (Nat.add_comm n m)).hom
        ((-1 : R) ^ (m * n) • P.flip.cup n m b a) := by
  cases n with
  | zero =>
    rw [mul_zero, pow_zero, one_smul, P.flip.cup_zero_eq_flip, flip_flip,
      ← ConcreteCategory.comp_apply, ContinuousCohomology.degreeCast_hom_comp_degreeCast_hom,
      ContinuousCohomology.degreeCast_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
  | succ n =>
    obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains X).homologyπ_surjective m a
    obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains Y).homologyπ_surjective (n + 1) b
    have key := P.π_cocyclesDegreeCast_cupCocycles m n a b
    rw [ContinuousCohomology.π_cocyclesDegreeCast, ContinuousCohomology.π_cocyclesDegreeCast]
      at key
    rw [cup_π, cup_π, ← Iso.hom_inv_id_apply
        (ContinuousCohomology.degreeCast Z (by omega : m + (n + 1) = m + n + 1))
        (π Z (m + (n + 1)) _), key, map_smul, map_smul, ← Iso.symm_hom,
      ContinuousCohomology.degreeCast_symm, ← ConcreteCategory.comp_apply,
      ContinuousCohomology.degreeCast_hom_comp_degreeCast_hom]

end cupOne

end TopPairing

end TauCeti
