/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology

/-!
# Associativity of the cup product on continuous cohomology

Let `μ₁ : TopPairing A B D`, `μ₂ : TopPairing D C E`, `ν₁ : TopPairing B C F` and
`ν₂ : TopPairing A F E` be four coefficient pairings of topological representations of a
topological group `G`, compatible in the sense that

```text
μ₂ (μ₁ a b) c = ν₂ a (ν₁ b c)    for all a : A, b : B, c : C.
```

Then the two parenthesizations of a threefold cup product agree on continuous cohomology:

```text
(x ⌣_{μ₁} y) ⌣_{μ₂} z = x ⌣_{ν₂} (y ⌣_{ν₁} z)
```

for `x ∈ Hᵐ(G, A)`, `y ∈ Hⁿ(G, B)` and `z ∈ Hᵖ(G, C)`, where the right-hand side, which lives in
degree `m + (n + p)`, is transported to the degree `m + n + p` of the left-hand side
(`TauCeti.TopPairing.cup_assoc`). Four pairings are needed to type the two sides at all, and the
single-ring specialization that the applications use, one coefficient object `X` with an
associative pairing `P : TopPairing X X X` in all four places, is the instance
`cup_assoc P P P P`. For a discrete `G`-ring `S` acted on by ring automorphisms, with all four
pairings its multiplication `TauCeti.ofDiscreteModulePairing AddMonoidHom.mul`, this instance is
stated separately as `TauCeti.TopPairing.cup_assoc_mul`: associativity of the cohomology ring
`H^•(G, S)`.

The identity already holds on homogeneous cochains, before any passage to cohomology. The
Alexander–Whitney formula

```text
(a ⌣ b) (g₀, …, g_{m+n}) = μ (a (g₀, …, g_m)) (b (g_m, …, g_{m+n}))
```

pairs the leading `m + 1` arguments into `a` and the trailing `n + 1` into `b`, so both
parenthesizations of `a ⌣ b ⌣ c` evaluate to

```text
μ₂ (μ₁ (a (g₀, …, g_m)) (b (g_m, …, g_{m+n}))) (c (g_{m+n}, …, g_{m+n+p}))
```

and the two sides differ only by the coefficient identity. This is Brown's cochain-level
associativity (V (3.5)); no chain homotopy is involved, in contrast with graded commutativity,
which fails on cochains. On the curried coinduced resolution the proof is an induction along the
recursion `(a ⌣ b) g = (a g) ⌣ b` of `TauCeti.TopPairing.resolutionCup`, whose base cases are the
corresponding identities for the pointwise pairing `TauCeti.TopPairing.pointwise`.

## Degrees

The resolution-level identity `TauCeti.TopPairing.resolutionCup_assoc` is stated, as everything in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded`, with the total degrees as
explicit arguments together with the equations they satisfy, so that both parenthesizations land
in the same term of the resolution and no transport appears. The bilinear forms
`TauCeti.TopPairing.resolutionCupPairing_assoc` and `TauCeti.TopPairing.cupCochain_assoc` land in
degrees `m + n + p` and `m + (n + p)`, which are equal but not definitionally, so the right-hand
side is transported through `HomologicalComplex.XIsoOfEq`; on cohomology the transport is
`TauCeti.ContinuousCohomology.degreeCast`.

## Main results

* `TauCeti.TopPairing.resolutionCup_assoc`: associativity of the Alexander–Whitney pairing on the
  coinduced resolution.
* `TauCeti.TopPairing.cupCochain_assoc`: **associativity of the cup product of homogeneous
  cochains**, an identity of cochains and not only of classes.
* `TauCeti.TopPairing.cup_assoc`: **associativity of the cup product on continuous cohomology**.
* `TauCeti.TopPairing.cup_assoc_mul`: the specialization to a discrete `G`-ring with its
  multiplication as the pairing, **associativity of the cohomology ring**.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.5), for
  associativity at the cochain level.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.4).
-/

public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology

universe u v w

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C D E F : TopRep.{max v w} R G}
  (μ₁ : TopPairing A B D) (μ₂ : TopPairing D C E) (ν₁ : TopPairing B C F) (ν₂ : TopPairing A F E)
  (hcoeff : ∀ (a : A.V) (b : B.V) (c : C.V), μ₂.bil (μ₁.bil a b) c = ν₂.bil a (ν₁.bil b c))

include hcoeff

/-! ### Associativity on the resolution -/

/-- The coefficient identity applied at every value of an iterated map: pairing `μ₁ x y` with every
value of `F` is pairing `x` with every value of the map obtained by pairing `y` with every value
of `F`. -/
private theorem pointwise_pointwise : ∀ (p k : ℕ) (hk : k = p) (x : A.V) (y : B.V)
    (F : (TopRep.resolutionX C p).V),
    μ₂.pointwise p k hk (μ₁.bil x y, F) = ν₂.pointwise k k rfl (x, ν₁.pointwise p k hk (y, F))
  | 0, 0, _, x, y, F => by
    rw [μ₂.pointwise_zero_apply, ν₂.pointwise_zero_apply, ν₁.pointwise_zero_apply]
    exact hcoeff x y F
  | p + 1, k + 1, hk, x, y, F => ContinuousMap.ext fun g ↦ by
    rw [μ₂.pointwise_succ_apply, ν₂.pointwise_succ_apply, ν₁.pointwise_succ_apply]
    exact pointwise_pointwise p k (Nat.succ.inj hk) x y (F g)
  | 0, _ + 1, hk, _, _, _ => absurd hk (by omega)
  | _ + 1, 0, hk, _, _, _ => absurd hk (by omega)

/-- The base case of the associativity recursion, in which the left factor is a coefficient `x`
paired with every value of `b`: pairing `x` into `b` and then cupping with `c` is pairing `x` into
`b ⌣ c`. -/
private theorem resolutionCup_pointwise : ∀ (n p k₁ k₂ k : ℕ) (hk₁ : k₁ = n) (hk₂ : k₂ = p + n)
    (hk : k = p + k₁) (x : A.V) (b : (TopRep.resolutionX B (n + 1)).V)
    (c : (TopRep.resolutionX C (p + 1)).V),
    μ₂.resolutionCup k₁ p k hk (μ₁.pointwise (n + 1) (k₁ + 1) (by omega) (x, b), c) =
      ν₂.pointwise (k₂ + 1) (k + 1) (by omega) (x, ν₁.resolutionCup n p k₂ hk₂ (b, c))
  | 0, p, k₁, k₂, k, hk₁, hk₂, hk, x, b, c => by
    obtain rfl : k₁ = 0 := hk₁
    obtain rfl : k = k₂ := by omega
    refine ContinuousMap.ext fun g ↦ ?_
    rw [μ₂.resolutionCup_zero_apply, μ₁.pointwise_succ_apply, μ₁.pointwise_zero_apply,
      ν₂.pointwise_succ_apply, ν₁.resolutionCup_zero_apply]
    exact pointwise_pointwise μ₁ μ₂ ν₁ ν₂ hcoeff p k hk x (b g) (c g)
  | n + 1, p, k₁, k₂, k, hk₁, hk₂, hk, x, b, c => by
    obtain ⟨k₁, rfl⟩ : ∃ k₁', k₁ = k₁' + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine ContinuousMap.ext fun g ↦ ?_
    rw [μ₂.resolutionCup_succ_apply, μ₁.pointwise_succ_apply, ν₂.pointwise_succ_apply,
      ν₁.resolutionCup_succ_apply]
    exact resolutionCup_pointwise n p k₁ k₂ k (by omega) (by omega) (by omega) x (b g) c

/-- **Associativity of the Alexander–Whitney pairing on the coinduced resolution**, with explicit
total degrees: `(a ⌣_{μ₁} b) ⌣_{μ₂} c = a ⌣_{ν₂} (b ⌣_{ν₁} c)` for compatible pairings. Both sides
live in the `(k + 1)`-st term of the resolution of `E`, for `k = p + (n + m) = (p + n) + m`. -/
theorem resolutionCup_assoc : ∀ (m n p k₁ k₂ k : ℕ) (hk₁ : k₁ = n + m) (hk₂ : k₂ = p + n)
    (hk : k = p + k₁) (hk' : k = k₂ + m) (a : (TopRep.resolutionX A (m + 1)).V)
    (b : (TopRep.resolutionX B (n + 1)).V) (c : (TopRep.resolutionX C (p + 1)).V),
    μ₂.resolutionCup k₁ p k hk (μ₁.resolutionCup m n k₁ hk₁ (a, b), c) =
      ν₂.resolutionCup m k₂ k hk' (a, ν₁.resolutionCup n p k₂ hk₂ (b, c))
  | 0, 0, p, k₁, k₂, k, hk₁, hk₂, hk, hk', a, b, c => by
    obtain rfl : k₁ = 0 := by omega
    obtain rfl : k = k₂ := by omega
    refine ContinuousMap.ext fun g ↦ ?_
    rw [μ₂.resolutionCup_zero_apply, μ₁.resolutionCup_zero_apply, μ₁.pointwise_zero_apply,
      ν₂.resolutionCup_zero_apply, ν₁.resolutionCup_zero_apply]
    exact pointwise_pointwise μ₁ μ₂ ν₁ ν₂ hcoeff p k hk (a g) (b g) (c g)
  | 0, n + 1, p, k₁, k₂, k, hk₁, hk₂, hk, hk', a, b, c => by
    obtain ⟨k₁, rfl⟩ : ∃ k₁', k₁ = k₁' + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine ContinuousMap.ext fun g ↦ ?_
    rw [μ₂.resolutionCup_succ_apply, μ₁.resolutionCup_zero_apply, ν₂.resolutionCup_zero_apply,
      ν₁.resolutionCup_succ_apply]
    exact resolutionCup_pointwise μ₁ μ₂ ν₁ ν₂ hcoeff n p k₁ k₂ k (by omega) (by omega) (by omega)
      (a g) (b g) c
  | m + 1, n, p, k₁, k₂, k, hk₁, hk₂, hk, hk', a, b, c => by
    obtain ⟨k₁, rfl⟩ : ∃ k₁', k₁ = k₁' + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine ContinuousMap.ext fun g ↦ ?_
    rw [μ₂.resolutionCup_succ_apply, μ₁.resolutionCup_succ_apply, ν₂.resolutionCup_succ_apply]
    exact resolutionCup_assoc m n p k₁ k₂ k (by omega) hk₂ (by omega) (by omega) (a g) b c

/-- **Associativity of the Alexander–Whitney pairing, as bilinear maps**: the right-hand side lives
in degree `m + (n + p)` and is transported to `m + n + p`. -/
theorem resolutionCupPairing_assoc (m n p : ℕ) (a : (TopRep.resolution'X A m).V)
    (b : (TopRep.resolution'X B n).V) (c : (TopRep.resolution'X C p).V) :
    μ₂.resolutionCupPairing (m + n) p (μ₁.resolutionCupPairing m n a b) c =
      ((TopRep.resolution E).XIsoOfEq (by omega : m + (n + p) + 1 = m + n + p + 1)).hom.hom
        (ν₂.resolutionCupPairing m (n + p) a (ν₁.resolutionCupPairing n p b c)) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply, resolutionCupPairing_apply,
    resolutionCupPairing_apply, resolutionCup_cast (hk' := by omega)]
  exact resolutionCup_assoc μ₁ μ₂ ν₁ ν₂ hcoeff m n p (m + n) (n + p) (m + n + p) _ _ _ _ a b c

/-! ### Associativity on cochains and on cohomology -/

/-- **Associativity of the cup product of homogeneous cochains**:
`(a ⌣_{μ₁} b) ⌣_{μ₂} c = a ⌣_{ν₂} (b ⌣_{ν₁} c)` for compatible pairings, as an identity of
cochains, where the right-hand side lives in degree `m + (n + p)` and is transported to
`m + n + p`. -/
theorem cupCochain_assoc (m n p : ℕ) (a : (homogeneousCochains A).X m)
    (b : (homogeneousCochains B).X n) (c : (homogeneousCochains C).X p) :
    μ₂.cupCochain (m + n) p (μ₁.cupCochain m n a b) c =
      ((homogeneousCochains E).XIsoOfEq (by omega : m + (n + p) = m + n + p)).hom
        (ν₂.cupCochain m (n + p) a (ν₁.cupCochain n p b c)) := by
  apply Subtype.ext
  rw [coe_cupCochain, coe_cupCochain,
    ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply, coe_cupCochain,
    coe_cupCochain]
  exact resolutionCupPairing_assoc μ₁ μ₂ ν₁ ν₂ hcoeff m n p a.1 b.1 c.1

/-- **Associativity of the cup product on continuous cohomology**: for compatible pairings
`μ₂ (μ₁ a b) c = ν₂ a (ν₁ b c)` and classes `x ∈ Hᵐ(G, A)`, `y ∈ Hⁿ(G, B)`, `z ∈ Hᵖ(G, C)`,

```text
(x ⌣_{μ₁} y) ⌣_{μ₂} z = x ⌣_{ν₂} (y ⌣_{ν₁} z),
```

where the right-hand side lives in degree `m + (n + p)` and is transported to `m + n + p`. For one
coefficient object `X` with an associative pairing `P : TopPairing X X X` in all four places, this
is associativity of the cup product of the cohomology ring `H^•(G, X)`. -/
theorem cup_assoc (m n p : ℕ) (x : continuousCohomology m A) (y : continuousCohomology n B)
    (z : continuousCohomology p C) :
    μ₂.cup (m + n) p (μ₁.cup m n x y) z =
      (ContinuousCohomology.degreeCast E (Nat.add_assoc m n p).symm).hom
        (ν₂.cup m (n + p) x (ν₁.cup n p y z)) := by
  obtain ⟨a, rfl⟩ := (homogeneousCochains A).homologyπ_surjective m x
  obtain ⟨b, rfl⟩ := (homogeneousCochains B).homologyπ_surjective n y
  obtain ⟨c, rfl⟩ := (homogeneousCochains C).homologyπ_surjective p z
  rw [cup_π, cup_π, cup_π, cup_π]
  refine ContinuousCohomology.π_eq_degreeCast_π (Nat.add_assoc m n p).symm _ _ ?_
  rw [iCycles_cupCocycles, iCycles_cupCocycles, iCycles_cupCocycles, iCycles_cupCocycles]
  exact cupCochain_assoc μ₁ μ₂ ν₁ ν₂ hcoeff m n p _ _ _

end TopPairing

namespace TopPairing

/-! ### Associativity for a discrete `G`-ring

The specialization the applications use: one discrete coefficient ring `S` acted on by ring
automorphisms, all four pairings its multiplication `AddMonoidHom.mul`, and the coefficient
identity `mul_assoc`. The equivariance a discrete-module pairing has to come with is `smul_mul'`,
which applies to `AddMonoidHom.mul` as it stands, exactly as for the low-degree
`TauCeti.ContCohomology.explicitCup_assoc000_mul` and its siblings. -/

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S : Type (max v w)} [Ring S] [TopologicalSpace S] [DiscreteTopology S] [MulSemiringAction G S]

/-- **Associativity of the cup product of the cohomology ring of a discrete `G`-ring**: for a
discrete ring `S` acted on by ring automorphisms and classes `x ∈ Hᵐ(G, S)`, `y ∈ Hⁿ(G, S)`,
`z ∈ Hᵖ(G, S)`, with the multiplication of `S` as the coefficient pairing throughout,
`(x ⌣ y) ⌣ z = x ⌣ (y ⌣ z)`, where the right-hand side lives in degree `m + (n + p)` and is
transported to `m + n + p`. This is `TauCeti.TopPairing.cup_assoc` at the pairing
`TauCeti.ofDiscreteModulePairing AddMonoidHom.mul` with coefficient identity `mul_assoc`. -/
theorem cup_assoc_mul (m n p : ℕ) (x : continuousCohomology m (ofDiscreteModule ℤ G S))
    (y : continuousCohomology n (ofDiscreteModule ℤ G S))
    (z : continuousCohomology p (ofDiscreteModule ℤ G S)) :
    (ofDiscreteModulePairing AddMonoidHom.mul fun g a b ↦ (smul_mul' g a b).symm).cup (m + n) p
        ((ofDiscreteModulePairing AddMonoidHom.mul fun g a b ↦ (smul_mul' g a b).symm).cup m n
          x y) z =
      (ContinuousCohomology.degreeCast (ofDiscreteModule ℤ G S) (Nat.add_assoc m n p).symm).hom
        ((ofDiscreteModulePairing AddMonoidHom.mul fun g a b ↦ (smul_mul' g a b).symm).cup m
          (n + p) x
          ((ofDiscreteModulePairing AddMonoidHom.mul fun g a b ↦ (smul_mul' g a b).symm).cup n p
            y z)) :=
  cup_assoc _ _ _ _ (fun (a b c : S) ↦ by
    -- the values of the multiplication pairing, at this pairing so that `rw` keys on it
    have h := ofDiscreteModulePairing_bil_apply (G := G) (AddMonoidHom.mul (R := S))
      fun g a b ↦ (smul_mul' g a b).symm
    rw [h a b, h b c, h _ c, h a _]
    exact mul_assoc a b c) m n p x y z

end TopPairing

end TauCeti
