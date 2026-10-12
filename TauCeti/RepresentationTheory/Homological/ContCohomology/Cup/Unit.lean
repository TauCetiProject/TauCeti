/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# The unit of the cup product on continuous cohomology

Let `u` be a `G`-invariant vector of a topological representation `Y`, and let `P` be a coefficient
pairing for which `u` is a unit. The degree-zero class of `u`
(`TauCeti.ContinuousCohomology.degreeZeroClass`) is then a unit for the cup product
`TauCeti.TopPairing.cup` on continuous cohomology:

```text
a ⌣ [u] = a   if  P.bil x u = x  for all x   (P : TopPairing X Y X),
[u] ⌣ a = a   if  P.bil u x = x  for all x   (P : TopPairing Y X X).
```

The main application is a discrete `G`-ring with its multiplication as the pairing and `u = 1`,
where these are the unit laws `1 ⌣ a = a = a ⌣ 1` of the cohomology ring.

The class of `u` is represented by the constant `0`-cocycle `g ↦ u`
(`TauCeti.ContinuousCohomology.degreeZeroCocycle`), and on it both identities already hold at the
level of homogeneous cochains: the Alexander–Whitney formula
`(a ⌣ b) (g₀, …, g_{m+n}) = μ (a (g₀, …, g_m)) (b (g_m, …, g_{m+n}))` pairs every value of `a` with
`u`, or `u` with every value of `a`. On the right the total degree `m + 0` is `m` by definition. On
the left the total degree `0 + n` is only propositionally `n`, so the cochain-level identity carries
the transport `HomologicalComplex.XIsoOfEq` and the class-level identity carries the transport
`TauCeti.ContinuousCohomology.degreeCast` along `n = 0 + n`.

## Main results

* `TauCeti.TopPairing.cupCochain_degreeZeroCocycle_right`,
  `TauCeti.TopPairing.cupCochain_degreeZeroCocycle_left`: the unit laws for the cup product of
  homogeneous cochains.
* `TauCeti.TopPairing.cup_one_right`, `TauCeti.TopPairing.cup_one_left`: **the unit laws for the cup
  product on continuous cohomology**.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3.
-/

public section

namespace TauCeti

open CategoryTheory TopRep _root_.ContinuousCohomology
open TauCeti.ContinuousCohomology (degreeZeroClass degreeZeroCocycle)

universe u v w

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y : TopRep.{max v w} R G}

/-! ### The unit on the right -/

section Right

variable (P : TopPairing X Y X) (u : Y.V) (hu : ∀ x : X.V, P.bil x u = x)

include hu

/-- On the resolution, pairing with the constant map at a right unit `u` is the identity. -/
private theorem resolutionCup_d_zero_of_right_unit : ∀ (m : ℕ) (hk : m = 0 + m)
    (a : (TopRep.resolutionX X (m + 1)).V),
    P.resolutionCup m 0 m hk (a, (TopRep.d Y 0).hom u) = a
  | 0, hk, a => ContinuousMap.ext fun g ↦ by
    rw [resolutionCup_zero_apply, pointwise_zero_apply]
    exact hu (a g)
  | m + 1, hk, a => ContinuousMap.ext fun g ↦ by
    rw [resolutionCup_succ_apply]
    exact resolutionCup_d_zero_of_right_unit m (by omega) (a g)

/-- **The right unit law for the cup product of homogeneous cochains**: cupping with the constant
`0`-cocycle of a right unit `u` is the identity. -/
theorem cupCochain_degreeZeroCocycle_right (hinv : ∀ g : G, Y.ρ g u = u) (m : ℕ)
    (a : (homogeneousCochains X).X m) :
    P.cupCochain m 0 a ((homogeneousCochains Y).iCycles 0 (degreeZeroCocycle Y u hinv)) = a := by
  apply Subtype.ext
  rw [coe_cupCochain, ContinuousCohomology.coe_iCycles_degreeZeroCocycle,
    resolutionCupPairing_apply]
  exact P.resolutionCup_d_zero_of_right_unit u hu m _ a.1

/-- **The right unit law for the cup product on continuous cohomology**: if `u` is an invariant
vector with `P.bil x u = x` for every `x`, then `a ⌣ [u] = a` for every class `a`. For a discrete
`G`-ring and its multiplication this is `a ⌣ 1 = a`. -/
@[simp]
theorem cup_one_right (hinv : ∀ g : G, Y.ρ g u = u) (m : ℕ) (a : continuousCohomology m X) :
    P.cup m 0 a (degreeZeroClass Y u hinv) = a := by
  obtain ⟨a, rfl⟩ := (homogeneousCochains X).homologyπ_surjective m a
  rw [← ContinuousCohomology.π_degreeZeroCocycle u hinv, cup_π]
  congr 1
  -- the total degree `m + 0` is `m` by definition, but not syntactically, so `rw` cannot see it
  exact (homogeneousCochains X).iCycles_injective m ((P.iCycles_cupCocycles m 0 a _).trans
    (P.cupCochain_degreeZeroCocycle_right u hu hinv m _))

end Right

/-! ### The unit on the left -/

section Left

variable (P : TopPairing Y X X) (u : Y.V) (hu : ∀ x : X.V, P.bil u x = x)

include hu

/-- Pairing a left unit `u` with every value of an iterated map is the identity. -/
private theorem pointwise_of_left_unit : ∀ (n : ℕ) (F : (TopRep.resolutionX X n).V),
    P.pointwise n n rfl (u, F) = F
  | 0, F => by
    rw [pointwise_zero_apply]
    exact hu F
  | n + 1, F => ContinuousMap.ext fun g ↦ by
    rw [pointwise_succ_apply]
    exact pointwise_of_left_unit n (F g)

/-- **The left unit law for the cup product of homogeneous cochains**: cupping the constant
`0`-cocycle of a left unit `u` with `a` is `a`, transported from degree `n` to `0 + n`. -/
theorem cupCochain_degreeZeroCocycle_left (hinv : ∀ g : G, Y.ρ g u = u) (n : ℕ)
    (a : (homogeneousCochains X).X n) :
    P.cupCochain 0 n ((homogeneousCochains Y).iCycles 0 (degreeZeroCocycle Y u hinv)) a =
      ((homogeneousCochains X).XIsoOfEq (Nat.zero_add n).symm).hom a := by
  apply Subtype.ext
  rw [coe_cupCochain, ContinuousCohomology.coe_homogeneousCochains_XIsoOfEq_hom_apply]
  refine ContinuousMap.ext fun g ↦ ?_
  rw [resolutionCupPairing_apply_zero, ContinuousCohomology.resolution_XIsoOfEq_hom_apply_apply,
    ContinuousCohomology.coe_iCycles_degreeZeroCocycle]
  exact congrArg _ (P.pointwise_of_left_unit u hu n (a.1 g))

/-- **The left unit law for the cup product on continuous cohomology**: if `u` is an invariant
vector with `P.bil u x = x` for every `x`, then `[u] ⌣ a = a` for every class `a`, where the
right-hand side is transported from degree `n` to the degree `0 + n` of the cup product. For a
discrete `G`-ring and its multiplication this is `1 ⌣ a = a`. -/
@[simp]
theorem cup_one_left (hinv : ∀ g : G, Y.ρ g u = u) (n : ℕ) (a : continuousCohomology n X) :
    P.cup 0 n (degreeZeroClass Y u hinv) a =
      (ContinuousCohomology.degreeCast X (Nat.zero_add n).symm).hom a := by
  obtain ⟨a, rfl⟩ := (homogeneousCochains X).homologyπ_surjective n a
  rw [← ContinuousCohomology.π_degreeZeroCocycle u hinv, cup_π]
  refine ContinuousCohomology.π_eq_degreeCast_π (Nat.zero_add n).symm _ _ ?_
  rw [iCycles_cupCocycles]
  exact P.cupCochain_degreeZeroCocycle_left u hu hinv n _

end Left

end TopPairing

end TauCeti
