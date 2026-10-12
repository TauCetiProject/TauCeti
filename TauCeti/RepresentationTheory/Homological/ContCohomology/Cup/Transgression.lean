/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Heisenberg
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression

/-!
# The transgression of a cup product through a Heisenberg cochain

Let `G` be a topological group, let `M`, `A` and `P` be topological `G`-modules with an equivariant
pairing `μ : M →+ A →+ P`, let `a` and `b` be continuous `1`-cocycles with values in `M` and `A`,
and let `h` be a Heisenberg cochain for `(a, b)`
(`TauCeti.ContCohomology.IsHeisenbergCochain`, a continuous `1`-cochain whose coboundary is
`-(a ⌣ b)`).

The main theorem is the computation of the transgression through `h`. Let `N` be a closed normal
subgroup of a profinite group `G` on which `a` and `b` vanish, so that they descend to cocycles `a'`
and `b'` on `G ⧸ N` with values in the `N`-invariants. Then `-h` is a transgression lift of its
restriction `-h|_N`, which is a conjugation-invariant continuous `1`-cocycle on `N`, and

```text
tg [-h|_N] = a' ⌣ b'   in H²(G ⧸ N, P ^ N).
```

When the transgression is bijective, for instance for a minimal presentation `1 → R → F → G → 1` of
a pro-`p` group by a free pro-`p` group `F` and `𝔽_p`-coefficients, this identifies the cup
product `a' ⌣ b' ∈ H²(G, 𝔽_p)` with the character `r ↦ -h r` of `R ⧸ Rᵖ[R, F]`; so the value of the
cup product on a relator `r ∈ R ⊆ Fᵖ[F, F]` is `-h r`, which the commutator and power formulas of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Heisenberg` evaluate once `r` is
written as a product of `p`-th powers and commutators of the generators, as in Labute's
Proposition 3.

## Main definitions

* `TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict`: the restriction `-h|_N`, a continuous
  `1`-cocycle on a normal subgroup `N` on which `a` and `b` vanish.

## Main results

* `TauCeti.ContCohomology.IsHeisenbergCochain.isTransgressionLift`: `-h` is a transgression lift of
  `-h|_N`, and `TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_mem_H1ConjInvariants`: the
  class of `-h|_N` is conjugation-invariant.
* `TauCeti.ContCohomology.IsHeisenbergCochain.transgression_negRestrict`: **the transgression of
  `-h|_N` is the cup product of the descended cocycles.**

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.4
  and Proposition 3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §9.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uA uP

section Lift

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P]
  {μ : M →+ A →+ P} {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  {N : Subgroup G} [N.Normal]
include hh

namespace IsHeisenbergCochain

/-- **A Heisenberg cochain is a transgression lift.** If `a` and `b` vanish on the normal subgroup
`N`, then `-h` is a transgression lift of its restriction `-h|_N`. -/
theorem isTransgressionLift (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    IsTransgressionLift (fun n : N => -h n) (fun g => -h g) where
  continuous := hh.continuous.neg
  apply_mul g n := by
    rw [hh.apply_mul, hbN n, smul_zero, map_zero, add_zero, smul_neg]
    abel
  smul_conj_sub g n := by
    rw [d0_apply, Subgroup.smul_def, Subgroup.inverseConjugationHom_apply, Subgroup.coe_mk]
    simp only [smul_neg]
    rw [hh.apply_conj haN hbN g n]
    abel

/-- **The restriction `-h|_N`** of a Heisenberg cochain to a normal subgroup `N` on which `a` and
`b` vanish, a continuous `1`-cocycle on `N`. Its class is conjugation-invariant
(`TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_mem_H1ConjInvariants`) and transgresses
to the cup product of the descended cocycles
(`TauCeti.ContCohomology.IsHeisenbergCochain.transgression_negRestrict`). -/
def negRestrict (haN : ∀ n : N, (a : G → M) n = 0) (hbN : ∀ n : N, (b : G → A) n = 0) :
    Z1 N P :=
  ⟨fun n : N => -h n, (hh.isTransgressionLift haN hbN).mem_Z1⟩

/-- The restriction `-h|_N`, as a function on `N`. -/
@[simp]
theorem coe_negRestrict (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    (hh.negRestrict haN hbN : N → P) = fun n : N => -h n :=
  (rfl)

variable [ContinuousSMul G P]

/-- The class of `-h|_N` in `H¹(N, P)` is conjugation-invariant. -/
theorem negRestrict_mem_H1ConjInvariants (haN : ∀ n : N, (a : G → M) n = 0)
    (hbN : ∀ n : N, (b : G → A) n = 0) :
    (hh.negRestrict haN hbN : H1 N P) ∈ H1ConjInvariants G P N :=
  IsTransgressionLift.mk_mem_H1ConjInvariants (hh.isTransgressionLift haN hbN)

end IsHeisenbergCochain

end Lift

section Transgression

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
  {N : Subgroup G} [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N A)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N P)]
  {μ : M →+ A →+ P} (hμ : Continuous fun p : M × A => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : A), μ (g • m) (g • x) = g • μ m x)
  {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  (hN : IsClosed (N : Set G)) (haN : ∀ n : N, (a : G → M) n = 0)
  (hbN : ∀ n : N, (b : G → A) n = 0)
include hμ hequiv hh hN haN hbN

/-- **The transgression of `-h|_N` is the cup product.** Let `N` be a closed normal subgroup of a
profinite group `G`, let `a` and `b` be continuous `1`-cocycles vanishing on `N`, with descents `a'`
and `b'` to `G ⧸ N` valued in the `N`-invariants, and let `h` be a Heisenberg cochain for `(a, b)`.
Then the transgression `H¹(N, P)^{G ⧸ N} → H²(G ⧸ N, P ^ N)` sends the class of `-h|_N` to the
explicit `(1,1)` cup product `a' ⌣ b'` for the pairing induced by `μ` on the invariants. -/
theorem IsHeisenbergCochain.transgression_negRestrict :
    transgression G P N hN
        ⟨hh.negRestrict haN hbN, hh.negRestrict_mem_H1ConjInvariants haN hbN⟩ =
      explicitCup11 (G ⧸ N) (FixedPoints.addSubgroup N M) (FixedPoints.addSubgroup N A)
        (FixedPoints.addSubgroup N P) (Subgroup.fixedPointsPairing N μ fun n => hequiv (n : G))
        (Subgroup.continuous_fixedPointsPairing N μ (fun n => hequiv (n : G)) hμ)
        (Subgroup.fixedPointsPairing_quotient_smul N μ hequiv)
        (descendZ1 a haN) (descendZ1 b hbN) := by
  have hf : IsTransgressionLift ((hh.negRestrict haN hbN : Z1 N P) : N → P) fun g => -h g := by
    rw [coe_negRestrict]
    exact hh.isTransgressionLift haN hbN
  rw [transgression_eq_mk_cocycle G P N hN _ (hh.negRestrict haN hbN) rfl hf, explicitCup11_mk]
  refine congrArg (fun z : Z2 (G ⧸ N) (FixedPoints.addSubgroup N P) =>
    (z : H2 (G ⧸ N) (FixedPoints.addSubgroup N P))) (Subtype.ext (funext fun q => ?_))
  obtain ⟨q₁, q₂⟩ := q
  induction q₁ using QuotientGroup.induction_on with
  | H g =>
    induction q₂ using QuotientGroup.induction_on with
    | H g' =>
      refine Subtype.ext ?_
      rw [IsTransgressionLift.coe_cocycle_apply_mk, Subgroup.coe_fixedPointsPairing,
        coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup,
        coe_descendZ1_apply_mk, coe_descendZ1_apply_mk]
      exact congrFun hh.d1_neg (g, g')

end Transgression

end TauCeti.ContCohomology
