/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.IntLinear
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete
public import TauCeti.Topology.CompactOpen

/-!
# The Alexander–Whitney cup product on homogeneous cochains

Mathlib computes the continuous cohomology of a topological representation `X : TopRep R G` as the
homology of the homogeneous cochains `TopRep.homogeneousCochains X`: the `m`-cochains are the
`G`-invariant elements of the `(m + 1)`-st term `C(G, C(G, …, C(G, X.V)))` of the coinduced
resolution `TopRep.resolutionX X`, and the differential is the recursion
`(d F) g = F - d (F g)` of `TopRep.d`. This file constructs the cup product of that complex.

A **coefficient pairing** `TauCeti.TopPairing X Y Z` is an `R`-bilinear map
`X.V →ₗ[R] Y.V →ₗ[R] Z.V` that is jointly continuous and `G`-equivariant. Given one, the
Alexander–Whitney formula

```text
(a ⌣ b) (g₀, …, g_{m+n}) = μ (a (g₀, …, g_m)) (b (g_m, …, g_{m+n}))
```

pairs an `m`-cochain with an `n`-cochain. Read on the curried resolution it is the recursion
`(a ⌣ b) g = (a g) ⌣ b` on the first argument, whose base case pairs the coefficient `a g` with
every value of `b g` (`TauCeti.TopPairing.pointwise`). The pairing is first built as a jointly
continuous map on the resolution with an explicit total degree
(`TauCeti.TopPairing.resolutionCup`), whose two defining equations,
`TauCeti.TopPairing.resolutionCup_zero_apply` and `TauCeti.TopPairing.resolutionCup_succ_apply`,
hold by definition. It is bilinear, equivariant, and satisfies the Leibniz rule

```text
d (a ⌣ b) = d a ⌣ b + (-1)^m (a ⌣ d b)
```

(`TauCeti.TopPairing.resolutionCup_leibniz`), so it descends to a bilinear map of homogeneous
cochains `TauCeti.TopPairing.cupCochain`, with the Leibniz rule
`TauCeti.TopPairing.cupCochain_leibniz`.
Cocycles therefore cup to cocycles and coboundaries to coboundaries, which is what the cup
product on continuous cohomology is built from.

## Degrees

The total degree of `a ⌣ b` is `m + n`, but the recursion on `m` produces `n + m`, and the two
are not definitionally equal. The resolution-level constructions therefore carry the total degree
`k` as an explicit argument together with a proof `k = n + m`, so that every identity between
them is stated without transport; `TauCeti.TopPairing.resolutionCup_cast` transports along an
equality of degrees through Mathlib's `HomologicalComplex.XIsoOfEq`, whose evaluation rules are in
`TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast`. The bilinear maps
`TauCeti.TopPairing.resolutionCupPairing` and `TauCeti.TopPairing.cupCochain` land in degree
`m + n`; in their Leibniz rules the term `d a ⌣ b` lives in degree `m + 1 + n` and is transported.

## Local compactness

For fixed inputs `a` and `b`, the base case `g ↦ (a g) ⌣ (b g)` is the pointwise pairing composed
with the continuous map `g ↦ (a g, b g)`, and the successor step `(a ⌣ b) g = (a g) ⌣ b` is
postcomposition with a fixed continuous map, so both values are continuous maps on `G` for every
topological group `G`. The successor step, however, needs the base case to be jointly continuous
in the pair `(a, b)` in order to be a well-defined continuous map, and joint continuity of
`(a, b) ↦ (g ↦ (a g, b g))` is continuity of evaluation `C(G, -) × G → -` for the compact-open
topology; this is where `LocallyCompactSpace G` enters. Compact groups, in particular profinite
groups, are locally compact, so the hypothesis is automatic in the arithmetic applications.

## Main definitions

* `TauCeti.TopPairing`: an equivariant jointly continuous bilinear pairing of topological
  representations, with `TauCeti.ofDiscreteModulePairing` for an equivariant biadditive map of
  discrete modules.
* `TauCeti.TopPairing.pointwise`: pairing a coefficient with every value of an iterated map.
* `TauCeti.TopPairing.resolutionCup`: the Alexander–Whitney pairing on the coinduced resolution,
  with explicit total degree.
* `TauCeti.TopPairing.resolutionCupPairing`: the same as a bilinear map into degree `m + n`.
* `TauCeti.TopPairing.cupCochain`: the cup product of homogeneous cochains.

## Main results

* `TauCeti.TopPairing.resolutionCup_ρ`, `TauCeti.TopPairing.continuous_resolutionCupPairing`:
  the resolution pairing is equivariant and jointly continuous.
* `TauCeti.TopPairing.resolutionCup_leibniz`, `TauCeti.TopPairing.resolutionCupPairing_leibniz`,
  `TauCeti.TopPairing.cupCochain_leibniz`: the **Leibniz rule**.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the
  Alexander–Whitney formula on the standard resolution.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.1), for the Leibniz rule.
-/

public section

namespace TauCeti

open CategoryTheory ContRepresentation ContinuousMap

universe u v w

/-! ### Coefficient pairings -/

section TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R] {G : Type v} [Monoid G]

/-- A **coefficient pairing** of topological representations: an `R`-bilinear map
`X.V →ₗ[R] Y.V →ₗ[R] Z.V` that is jointly continuous and `G`-equivariant. Joint continuity is
automatic for discrete coefficients and is not automatic in general, so it is carried as a field.
-/
@[ext]
structure TopPairing (X Y Z : TopRep.{w} R G) where
  /-- the underlying bilinear map -/
  bil : X.V →ₗ[R] Y.V →ₗ[R] Z.V
  /-- joint continuity -/
  cont : Continuous fun p : X.V × Y.V ↦ bil p.1 p.2
  /-- equivariance -/
  equivariant (g : G) (x : X.V) (y : Y.V) : bil (X.ρ g x) (Y.ρ g y) = Z.ρ g (bil x y)

variable {M N P : Type w} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction G P]

/-- An equivariant biadditive map of discrete `G`-modules, `μ (g • m) (g • n) = g • μ m n`, as a
coefficient pairing of the corresponding objects `TauCeti.ofDiscreteModule ℤ G M`. Joint
continuity holds because the modules are discrete. -/
def ofDiscreteModulePairing (μ : M →+ N →+ P)
    (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n) :
    TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G N) (ofDiscreteModule ℤ G P) where
  bil := μ.toIntLinearMap₂
  cont := continuous_of_discreteTopology
  equivariant g m n := by
    -- stated over `M`, `N`, `P` themselves, then transported to the carriers of the objects
    have h (m : M) (n : N) :
        μ.toIntLinearMap₂ (g • m) (g • n) = g • μ.toIntLinearMap₂ m n := by
      rw [AddMonoidHom.toIntLinearMap₂_apply, AddMonoidHom.toIntLinearMap₂_apply]
      exact hμ g m n
    exact h m n

@[simp]
theorem ofDiscreteModulePairing_bil_apply (μ : M →+ N →+ P)
    (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n) (m : M) (n : N) :
    (ofDiscreteModulePairing μ hμ).bil m n = μ m n := by
  rw [ofDiscreteModulePairing]
  exact μ.toIntLinearMap₂_apply m n

end TopPairing

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-! ### Pairing a coefficient with every value of an iterated map

The `n`-th term of the coinduced resolution of `Y` is the iterated function space
`C(G, C(G, …, Y.V))`. Pairing a fixed coefficient `x : X.V` with every value of such a function
gives an element of the `n`-th term of the resolution of `Z`. The target degree `k` is an explicit
argument with a proof `k = n`, so that the recursion below reduces definitionally in both the
degree of the source and that of the target. -/

/-- Pairing a coefficient `x : X.V` with every value of an `n`-fold iterated continuous map
`F : C(G, C(G, …, Y.V))`, as a jointly continuous map into the `k`-th term of the resolution of
`Z`, for `k = n`. -/
def pointwise : (n k : ℕ) → k = n →
    C(X.V × (TopRep.resolutionX Y n).V, (TopRep.resolutionX Z k).V)
  | 0, 0, _ => ⟨fun p ↦ P.bil p.1 p.2, P.cont⟩
  | n + 1, k + 1, hk =>
    ⟨fun p ↦ (pointwise n k (Nat.succ.inj hk)).comp ((const G p.1).prodMk p.2),
      (continuous_postcomp _).comp continuous_prodMk_const⟩
  | 0, _ + 1, hk => absurd hk (by omega)
  | _ + 1, 0, hk => absurd hk (by omega)

theorem pointwise_zero_apply (hk : 0 = 0) (x : X.V) (y : Y.V) :
    P.pointwise 0 0 hk (x, y) = P.bil x y := by
  rw [pointwise]
  rfl

theorem pointwise_succ_apply {n k : ℕ} (hk : k + 1 = n + 1) (x : X.V)
    (F : C(G, (TopRep.resolutionX Y n).V)) (h : G) :
    (P.pointwise (n + 1) (k + 1) hk (x, F) : C(G, (TopRep.resolutionX Z k).V)) h =
      P.pointwise n k (Nat.succ.inj hk) (x, F h) := by
  rw [pointwise]
  rfl

/-- Transport along an equality of degrees carries the pointwise pairing at one degree to the
pointwise pairing at the other. -/
theorem pointwise_cast {n k k' : ℕ} (hk : k = n) (hk' : k' = n) (h : k = k')
    (p : X.V × (TopRep.resolutionX Y n).V) :
    ((TopRep.resolution Z).XIsoOfEq h).hom.hom (P.pointwise n k hk p) =
      P.pointwise n k' hk' p := by
  subst h
  simp [ContIntertwiningMap.id_apply]

theorem pointwise_add_left : ∀ (n k : ℕ) (hk : k = n) (x x' : X.V)
    (F : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (x + x', F) = P.pointwise n k hk (x, F) + P.pointwise n k hk (x', F)
  | 0, 0, _, x, x', F => by
    rw [pointwise_zero_apply, pointwise_zero_apply, pointwise_zero_apply, map_add,
      LinearMap.add_apply]
  | n + 1, k + 1, hk, x, x', F => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.add_apply, pointwise_succ_apply, pointwise_succ_apply,
      pointwise_succ_apply]
    exact pointwise_add_left n k (Nat.succ.inj hk) x x' (F h)

theorem pointwise_sub_left : ∀ (n k : ℕ) (hk : k = n) (x x' : X.V)
    (F : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (x - x', F) = P.pointwise n k hk (x, F) - P.pointwise n k hk (x', F)
  | 0, 0, _, x, x', F => by
    rw [pointwise_zero_apply, pointwise_zero_apply, pointwise_zero_apply, map_sub,
      LinearMap.sub_apply]
  | n + 1, k + 1, hk, x, x', F => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.sub_apply, pointwise_succ_apply, pointwise_succ_apply,
      pointwise_succ_apply]
    exact pointwise_sub_left n k (Nat.succ.inj hk) x x' (F h)

theorem pointwise_smul_left : ∀ (n k : ℕ) (hk : k = n) (r : R) (x : X.V)
    (F : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (r • x, F) = r • P.pointwise n k hk (x, F)
  | 0, 0, _, r, x, F => by
    rw [pointwise_zero_apply, pointwise_zero_apply, map_smul, LinearMap.smul_apply]
  | n + 1, k + 1, hk, r, x, F => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.smul_apply, pointwise_succ_apply, pointwise_succ_apply]
    exact pointwise_smul_left n k (Nat.succ.inj hk) r x (F h)

theorem pointwise_add_right : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (F F' : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (x, F + F') = P.pointwise n k hk (x, F) + P.pointwise n k hk (x, F')
  | 0, 0, _, x, F, F' => by
    rw [pointwise_zero_apply, pointwise_zero_apply, pointwise_zero_apply, map_add]
  | n + 1, k + 1, hk, x, F, F' => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.add_apply, pointwise_succ_apply, pointwise_succ_apply,
      pointwise_succ_apply, ContinuousMap.add_apply]
    exact pointwise_add_right n k (Nat.succ.inj hk) x (F h) (F' h)

theorem pointwise_sub_right : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (F F' : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (x, F - F') = P.pointwise n k hk (x, F) - P.pointwise n k hk (x, F')
  | 0, 0, _, x, F, F' => by
    rw [pointwise_zero_apply, pointwise_zero_apply, pointwise_zero_apply, map_sub]
  | n + 1, k + 1, hk, x, F, F' => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.sub_apply, pointwise_succ_apply, pointwise_succ_apply,
      pointwise_succ_apply, ContinuousMap.sub_apply]
    exact pointwise_sub_right n k (Nat.succ.inj hk) x (F h) (F' h)

theorem pointwise_smul_right : ∀ (n k : ℕ) (hk : k = n) (r : R) (x : X.V)
    (F : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (x, r • F) = r • P.pointwise n k hk (x, F)
  | 0, 0, _, r, x, F => by
    rw [pointwise_zero_apply, pointwise_zero_apply, map_smul]
  | n + 1, k + 1, hk, r, x, F => ContinuousMap.ext fun h ↦ by
    rw [ContinuousMap.smul_apply, pointwise_succ_apply, pointwise_succ_apply,
      ContinuousMap.smul_apply]
    exact pointwise_smul_right n k (Nat.succ.inj hk) r x (F h)

/-- The pointwise pairing is equivariant. -/
theorem pointwise_ρ : ∀ (n k : ℕ) (hk : k = n) (g : G) (x : X.V)
    (F : (TopRep.resolutionX Y n).V),
    P.pointwise n k hk (X.ρ g x, (TopRep.resolutionX Y n).ρ g F) =
      (TopRep.resolutionX Z k).ρ g (P.pointwise n k hk (x, F))
  | 0, 0, _, g, x, F => P.equivariant g x F
  | n + 1, k + 1, hk, g, x, F => ContinuousMap.ext fun h ↦ by
    rw [pointwise_succ_apply]
    exact pointwise_ρ n k (Nat.succ.inj hk) g x (F (g⁻¹ * h))

/-- The pointwise pairing commutes with the differential of the resolution: the differential is
natural in the coefficients, for a continuous linear map that need not be equivariant. -/
theorem d_pointwise : ∀ (n k : ℕ) (hk : k = n) (x : X.V) (F : (TopRep.resolutionX Y n).V),
    (TopRep.d Z k).hom (P.pointwise n k hk (x, F)) =
      P.pointwise (n + 1) (k + 1) (by omega) (x, (TopRep.d Y n).hom F)
  | 0, 0, _, x, F => ContinuousMap.ext fun h ↦ by
    rw [pointwise_succ_apply, pointwise_zero_apply]
    rfl
  | n + 1, k + 1, hk, x, F => ContinuousMap.ext fun h ↦ by
    -- both sides evaluated at `h` are `pointwise (n + 1) (x, F) - pointwise (n + 1) (x, d (F h))`
    have hd : ((TopRep.d Z (k + 1)).hom (P.pointwise (n + 1) (k + 1) hk (x, F)) :
        C(G, (TopRep.resolutionX Z (k + 1)).V)) h =
        P.pointwise (n + 1) (k + 1) hk (x, F) -
          (TopRep.d Z k).hom ((P.pointwise (n + 1) (k + 1) hk (x, F) :
            C(G, (TopRep.resolutionX Z k).V)) h) := rfl
    have hdF : ((TopRep.d Y (n + 1)).hom F : C(G, (TopRep.resolutionX Y (n + 1)).V)) h =
        F - (TopRep.d Y n).hom (F h) := rfl
    rw [hd, pointwise_succ_apply, pointwise_succ_apply, hdF, pointwise_sub_right,
      d_pointwise n k (Nat.succ.inj hk) x (F h)]

/-! ### The Alexander–Whitney pairing on the resolution -/

variable [LocallyCompactSpace G]

/-- **The Alexander–Whitney pairing on the coinduced resolution**, with explicit total degree:
an element of the `(m + 1)`-st term of the resolution of `X` paired with an element of the
`(n + 1)`-st term of the resolution of `Y` gives an element of the `(k + 1)`-st term of the
resolution of `Z`, for `k = n + m`. The recursion is `(a ⌣ b) g = (a g) ⌣ b`, and the base case
pairs the coefficient `a g` with every value of `b g`. -/
def resolutionCup : (m n k : ℕ) → k = n + m →
    C((TopRep.resolutionX X (m + 1)).V × (TopRep.resolutionX Y (n + 1)).V,
      (TopRep.resolutionX Z (k + 1)).V)
  | 0, n, k, hk => ⟨fun p ↦ (P.pointwise n k hk).comp (p.1.prodMk p.2),
      (continuous_postcomp _).comp ContinuousMap.continuous_prodMk⟩
  | m + 1, n, k + 1, hk =>
    ⟨fun p ↦ (resolutionCup m n k (Nat.succ.inj hk)).comp (p.1.prodMk (const G p.2)),
      (continuous_postcomp _).comp ContinuousMap.continuous_prodMk_const_right⟩
  | _ + 1, _, 0, hk => absurd hk (by omega)

theorem resolutionCup_zero_apply {n k : ℕ} (hk : k = n + 0) (a : C(G, X.V))
    (b : C(G, (TopRep.resolutionX Y n).V)) (g : G) :
    (P.resolutionCup 0 n k hk (a, b) : C(G, (TopRep.resolutionX Z k).V)) g =
      P.pointwise n k hk (a g, b g) := by
  rw [resolutionCup]
  rfl

theorem resolutionCup_succ_apply {m n k : ℕ} (hk : k + 1 = n + (m + 1))
    (a : C(G, (TopRep.resolutionX X (m + 1)).V)) (b : (TopRep.resolutionX Y (n + 1)).V)
    (g : G) :
    (P.resolutionCup (m + 1) n (k + 1) hk (a, b) : C(G, (TopRep.resolutionX Z (k + 1)).V)) g =
      P.resolutionCup m n k (Nat.succ.inj hk) (a g, b) := by
  rw [resolutionCup]
  rfl

/-- Transport along an equality of degrees carries the resolution pairing at one total degree to
the resolution pairing at the other. -/
theorem resolutionCup_cast {m n k k' : ℕ} (hk : k = n + m) (hk' : k' = n + m)
    (h : k + 1 = k' + 1)
    (p : (TopRep.resolutionX X (m + 1)).V × (TopRep.resolutionX Y (n + 1)).V) :
    ((TopRep.resolution Z).XIsoOfEq h).hom.hom (P.resolutionCup m n k hk p) =
      P.resolutionCup m n k' hk' p := by
  obtain rfl : k = k' := by omega
  simp [ContIntertwiningMap.id_apply]

theorem resolutionCup_add_left : ∀ (m n k : ℕ) (hk : k = n + m)
    (a a' : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk (a + a', b) =
      P.resolutionCup m n k hk (a, b) + P.resolutionCup m n k hk (a', b)
  | 0, n, k, hk, a, a', b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, resolutionCup_zero_apply, resolutionCup_zero_apply,
      resolutionCup_zero_apply, ContinuousMap.add_apply, pointwise_add_left]
  | m + 1, n, k + 1, hk, a, a', b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, resolutionCup_succ_apply, resolutionCup_succ_apply,
      resolutionCup_succ_apply, ContinuousMap.add_apply]
    exact resolutionCup_add_left m n k (Nat.succ.inj hk) (a g) (a' g) b

theorem resolutionCup_sub_left : ∀ (m n k : ℕ) (hk : k = n + m)
    (a a' : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk (a - a', b) =
      P.resolutionCup m n k hk (a, b) - P.resolutionCup m n k hk (a', b)
  | 0, n, k, hk, a, a', b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.sub_apply, resolutionCup_zero_apply, resolutionCup_zero_apply,
      resolutionCup_zero_apply, ContinuousMap.sub_apply, pointwise_sub_left]
  | m + 1, n, k + 1, hk, a, a', b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.sub_apply, resolutionCup_succ_apply, resolutionCup_succ_apply,
      resolutionCup_succ_apply, ContinuousMap.sub_apply]
    exact resolutionCup_sub_left m n k (Nat.succ.inj hk) (a g) (a' g) b

theorem resolutionCup_smul_left : ∀ (m n k : ℕ) (hk : k = n + m) (r : R)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk (r • a, b) = r • P.resolutionCup m n k hk (a, b)
  | 0, n, k, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, resolutionCup_zero_apply, resolutionCup_zero_apply,
      ContinuousMap.smul_apply, pointwise_smul_left]
  | m + 1, n, k + 1, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, resolutionCup_succ_apply, resolutionCup_succ_apply,
      ContinuousMap.smul_apply]
    exact resolutionCup_smul_left m n k (Nat.succ.inj hk) r (a g) b

theorem resolutionCup_add_right : ∀ (m n k : ℕ) (hk : k = n + m)
    (a : (TopRep.resolutionX X (m + 1)).V) (b b' : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk (a, b + b') =
      P.resolutionCup m n k hk (a, b) + P.resolutionCup m n k hk (a, b')
  | 0, n, k, hk, a, b, b' => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, resolutionCup_zero_apply, resolutionCup_zero_apply,
      resolutionCup_zero_apply, ContinuousMap.add_apply, pointwise_add_right]
  | m + 1, n, k + 1, hk, a, b, b' => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.add_apply, resolutionCup_succ_apply, resolutionCup_succ_apply,
      resolutionCup_succ_apply]
    exact resolutionCup_add_right m n k (Nat.succ.inj hk) (a g) b b'

theorem resolutionCup_smul_right : ∀ (m n k : ℕ) (hk : k = n + m) (r : R)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk (a, r • b) = r • P.resolutionCup m n k hk (a, b)
  | 0, n, k, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, resolutionCup_zero_apply, resolutionCup_zero_apply,
      ContinuousMap.smul_apply, pointwise_smul_right]
  | m + 1, n, k + 1, hk, r, a, b => ContinuousMap.ext fun g ↦ by
    rw [ContinuousMap.smul_apply, resolutionCup_succ_apply, resolutionCup_succ_apply]
    exact resolutionCup_smul_right m n k (Nat.succ.inj hk) r (a g) b

/-- **The resolution pairing is equivariant.** -/
theorem resolutionCup_ρ : ∀ (m n k : ℕ) (hk : k = n + m) (g : G)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    P.resolutionCup m n k hk
        ((TopRep.resolutionX X (m + 1)).ρ g a, (TopRep.resolutionX Y (n + 1)).ρ g b) =
      (TopRep.resolutionX Z (k + 1)).ρ g (P.resolutionCup m n k hk (a, b))
  | 0, n, k, hk, g, a, b => ContinuousMap.ext fun h ↦ by
    rw [resolutionCup_zero_apply]
    exact pointwise_ρ P n k hk g (a (g⁻¹ * h)) (b (g⁻¹ * h))
  | m + 1, n, k + 1, hk, g, a, b => ContinuousMap.ext fun h ↦ by
    rw [resolutionCup_succ_apply]
    exact resolutionCup_ρ m n k (Nat.succ.inj hk) g (a (g⁻¹ * h)) b

/-- Pairing the constant map at `x` with `b` is the pointwise pairing of `x` with `b`. -/
theorem resolutionCup_zero_d_zero {n k : ℕ} (hk : k = n + 0) (x : X.V)
    (b : (TopRep.resolutionX Y (n + 1)).V) :
    P.resolutionCup 0 n k hk ((TopRep.d X 0).hom x, b) =
      P.pointwise (n + 1) (k + 1) (by omega) (x, b) :=
  ContinuousMap.ext fun h ↦ by
    rw [resolutionCup_zero_apply, pointwise_succ_apply]
    rfl

/-- **The Leibniz rule on the resolution**, with the sign convention
`d (a ⌣ b) = d a ⌣ b + (-1)^m (a ⌣ d b)` for `a` of degree `m`. -/
theorem resolutionCup_leibniz : ∀ (m n k : ℕ) (hk : k = n + m)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    (TopRep.d Z (k + 1)).hom (P.resolutionCup m n k hk (a, b)) =
      P.resolutionCup (m + 1) n (k + 1) (by omega) ((TopRep.d X (m + 1)).hom a, b) +
        (-1 : R) ^ m • P.resolutionCup m (n + 1) (k + 1) (by omega) (a, (TopRep.d Y (n + 1)).hom b)
  | 0, n, k, hk, a, b => ContinuousMap.ext fun g ↦ by
    -- at `g`: `a ⌣ b - d (μ (a g) (b g))` against
    -- `(a ⌣ b - x ⌣ b) + (x ⌣ b - x ⌣ d (b g))` for `x = a g`
    have hd : ((TopRep.d Z (k + 1)).hom (P.resolutionCup 0 n k hk (a, b)) :
        C(G, (TopRep.resolutionX Z (k + 1)).V)) g =
        P.resolutionCup 0 n k hk (a, b) - (TopRep.d Z k).hom (P.pointwise n k hk (a g, b g)) :=
      rfl
    have hda : ((TopRep.d X 1).hom a : C(G, C(G, X.V))) g = a - (TopRep.d X 0).hom (a g) := rfl
    have hdb : ((TopRep.d Y (n + 1)).hom b : C(G, (TopRep.resolutionX Y (n + 1)).V)) g =
        b - (TopRep.d Y n).hom (b g) := rfl
    have h₂ : ((-1 : R) ^ 0 • P.resolutionCup 0 (n + 1) (k + 1) (by omega)
        (a, (TopRep.d Y (n + 1)).hom b) : C(G, (TopRep.resolutionX Z (k + 1)).V)) g =
        P.pointwise (n + 1) (k + 1) (by omega) (a g, ((TopRep.d Y (n + 1)).hom b :
          C(G, (TopRep.resolutionX Y (n + 1)).V)) g) := by
      rw [pow_zero, one_smul, resolutionCup_zero_apply]
    rw [hd, ContinuousMap.add_apply, resolutionCup_succ_apply, hda, resolutionCup_sub_left,
      resolutionCup_zero_d_zero, h₂, hdb, pointwise_sub_right, d_pointwise]
    abel
  | m + 1, n, k + 1, hk, a, b => ContinuousMap.ext fun g ↦ by
    have hd : ((TopRep.d Z (k + 2)).hom (P.resolutionCup (m + 1) n (k + 1) hk (a, b)) :
        C(G, (TopRep.resolutionX Z (k + 2)).V)) g =
        P.resolutionCup (m + 1) n (k + 1) hk (a, b) -
          (TopRep.d Z (k + 1)).hom (P.resolutionCup m n k (Nat.succ.inj hk) (a g, b)) := rfl
    have hda : ((TopRep.d X (m + 2)).hom a : C(G, (TopRep.resolutionX X (m + 2)).V)) g =
        a - (TopRep.d X (m + 1)).hom (a g) := rfl
    rw [hd, resolutionCup_leibniz m n k (Nat.succ.inj hk) (a g) b, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, resolutionCup_succ_apply, resolutionCup_succ_apply, hda,
      resolutionCup_sub_left, pow_succ, mul_neg_one, neg_smul]
    abel

/-! ### The pairing as a bilinear map into degree `m + n` -/

/-- **The Alexander–Whitney pairing on the resolution**, as an `R`-bilinear map from the `m`-th
and `n`-th terms of the shifted resolutions of `X` and `Y` to the `(m + n)`-th term of the shifted
resolution of `Z`; the terms of the shifted resolution are the modules whose invariants are the
homogeneous cochains. -/
def resolutionCupPairing (m n : ℕ) :
    (TopRep.resolution'X X m).V →ₗ[R] (TopRep.resolution'X Y n).V →ₗ[R]
      (TopRep.resolution'X Z (m + n)).V :=
  LinearMap.mk₂ R (fun a b ↦ P.resolutionCup m n (m + n) (Nat.add_comm m n) (a, b))
    (fun a a' b ↦ P.resolutionCup_add_left m n (m + n) _ a a' b)
    (fun r a b ↦ P.resolutionCup_smul_left m n (m + n) _ r a b)
    (fun a b b' ↦ P.resolutionCup_add_right m n (m + n) _ a b b')
    (fun r a b ↦ P.resolutionCup_smul_right m n (m + n) _ r a b)

theorem resolutionCupPairing_apply (m n : ℕ) (a : (TopRep.resolution'X X m).V)
    (b : (TopRep.resolution'X Y n).V) :
    P.resolutionCupPairing m n a b = P.resolutionCup m n (m + n) (Nat.add_comm m n) (a, b) := by
  rw [resolutionCupPairing, LinearMap.mk₂_apply]

/-- **The base case of the Alexander–Whitney recursion**: a `0`-cochain `a` cupped with `b` is the
pointwise pairing of `a g` with every value of `b g`, transported from degree `n` to `0 + n`. -/
@[simp]
theorem resolutionCupPairing_apply_zero (n : ℕ) (a : (TopRep.resolution'X X 0).V)
    (b : (TopRep.resolution'X Y n).V) (g : G) :
    (P.resolutionCupPairing 0 n a b : C(G, (TopRep.resolutionX Z (0 + n)).V)) g =
      ((TopRep.resolution Z).XIsoOfEq (Nat.zero_add n).symm).hom.hom
        (P.pointwise n n rfl (a g, b g)) := by
  rw [resolutionCupPairing_apply, resolutionCup_zero_apply, pointwise_cast]

/-- **The successor case of the Alexander–Whitney recursion**: `(a ⌣ b) g = (a g) ⌣ b`,
transported from degree `m + n + 1` to `m + 1 + n`. -/
@[simp]
theorem resolutionCupPairing_apply_succ (m n : ℕ) (a : (TopRep.resolution'X X (m + 1)).V)
    (b : (TopRep.resolution'X Y n).V) (g : G) :
    (P.resolutionCupPairing (m + 1) n a b : C(G, (TopRep.resolutionX Z (m + 1 + n)).V)) g =
      ((TopRep.resolution Z).XIsoOfEq (by omega : m + n + 1 = m + 1 + n)).hom.hom
        (P.resolutionCupPairing m n (a g) b) := by
  -- `m + 1 + n` is not syntactically a successor, so move to degree `m + n + 1` first
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply,
    ← P.resolutionCup_cast (k := m + n + 1) (hk := by omega) (h := by omega),
    ContinuousCohomology.resolution_XIsoOfEq_hom_apply_apply, resolutionCup_succ_apply]

/-- **The resolution pairing is jointly continuous.** -/
theorem continuous_resolutionCupPairing (m n : ℕ) :
    Continuous fun p : (TopRep.resolution'X X m).V × (TopRep.resolution'X Y n).V ↦
      P.resolutionCupPairing m n p.1 p.2 :=
  (P.resolutionCup m n (m + n) (Nat.add_comm m n)).continuous

/-- **The resolution pairing is equivariant.** -/
theorem resolutionCupPairing_ρ (m n : ℕ) (g : G) (a : (TopRep.resolution'X X m).V)
    (b : (TopRep.resolution'X Y n).V) :
    P.resolutionCupPairing m n ((TopRep.resolution'X X m).ρ g a)
        ((TopRep.resolution'X Y n).ρ g b) =
      (TopRep.resolution'X Z (m + n)).ρ g (P.resolutionCupPairing m n a b) :=
  P.resolutionCup_ρ m n (m + n) _ g a b

/-- **The Leibniz rule on the resolution, in degree `m + n`**: the term `d a ⌣ b` lives in degree
`m + 1 + n` and is transported to `m + n + 1`. -/
theorem resolutionCupPairing_leibniz (m n : ℕ) (a : (TopRep.resolution'X X m).V)
    (b : (TopRep.resolution'X Y n).V) :
    (TopRep.d Z (m + n + 1)).hom (P.resolutionCupPairing m n a b) =
      ((TopRep.resolution Z).XIsoOfEq (by omega : m + 1 + n + 1 = m + n + 1 + 1)).hom.hom
          (P.resolutionCupPairing (m + 1) n ((TopRep.d X (m + 1)).hom a) b) +
        (-1 : R) ^ m • P.resolutionCupPairing m (n + 1) a ((TopRep.d Y (n + 1)).hom b) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply, resolutionCupPairing_apply,
    resolutionCup_cast (hk' := by omega)]
  exact P.resolutionCup_leibniz m n (m + n) _ a b

/-! ### The cup product of homogeneous cochains -/

/-- **The cup product of homogeneous cochains**: the Alexander–Whitney pairing restricted to the
`G`-invariant elements, which it preserves by equivariance. -/
def cupCochain (m n : ℕ) :
    (TopRep.homogeneousCochains X).X m →ₗ[R] (TopRep.homogeneousCochains Y).X n →ₗ[R]
      (TopRep.homogeneousCochains Z).X (m + n) :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨P.resolutionCupPairing m n a.1 b.1, fun g ↦ by
      rw [← P.resolutionCupPairing_ρ, a.2 g, b.2 g]⟩)
    (fun a a' b ↦ Subtype.ext (LinearMap.map_add₂ _ a.1 a'.1 b.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul₂ _ r a.1 b.1))
    (fun a b b' ↦ Subtype.ext (map_add _ b.1 b'.1))
    (fun r a b ↦ Subtype.ext (LinearMap.map_smul _ r b.1))

/-- The underlying resolution element of a cup product of homogeneous cochains is the
Alexander–Whitney pairing of the underlying elements. Not a `simp` lemma: `simp` rewrites the
implicit carrier `(TopRep.resolution' Z).X (m + n)` on the left-hand side through
`CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
form; use it with `rw`. -/
theorem coe_cupCochain (m n : ℕ) (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X n) :
    Subtype.val (P.cupCochain m n a b) = P.resolutionCupPairing m n a.1 b.1 := by
  rw [cupCochain, LinearMap.mk₂_apply]

/-- **The Leibniz rule for the cup product of homogeneous cochains**,
`d (a ⌣ b) = d a ⌣ b + (-1)^m (a ⌣ d b)`, where the term `d a ⌣ b` lives in degree `m + 1 + n`
and is transported to `m + n + 1`. -/
theorem cupCochain_leibniz (m n : ℕ) (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X n) :
    ((TopRep.homogeneousCochains Z).d (m + n) (m + n + 1)).hom (P.cupCochain m n a b) =
      ((TopRep.homogeneousCochains Z).XIsoOfEq (by omega : m + 1 + n = m + n + 1)).hom
          (P.cupCochain (m + 1) n (((TopRep.homogeneousCochains X).d m (m + 1)).hom a) b) +
        (-1 : R) ^ m • P.cupCochain m (n + 1) a
          (((TopRep.homogeneousCochains Y).d n (n + 1)).hom b) := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply, coe_cupCochain, Submodule.coe_add, Submodule.coe_smul,
    ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply, coe_cupCochain, coe_cupCochain,
    TopRep.homogeneousCochains.d_apply, TopRep.homogeneousCochains.d_apply]
  exact P.resolutionCupPairing_leibniz m n a.1 b.1

end TopPairing

end TauCeti
