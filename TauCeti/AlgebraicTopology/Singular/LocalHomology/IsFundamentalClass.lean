/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.ULift
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Fundamental classes with coefficients in a ring

Let `M` be a space, `R` a ring and `N` an `R`-module. A class `μ` of the singular homology
`Hₙ(M; N)` is a *fundamental class* (`TauCeti.IsFundamentalClass`) when, for every point `x` of
`M`, its image in the local homology `Hₙ(M, M ∖ {x}; N)` generates that `R`-module. The image is
`TauCeti.singularHomologyToLocalHomology`, the quotient map `Hₙ(M; N) ⟶ Hₙ(M, M ∖ M; N)` followed
by restriction to `{x}`. With `N = R` this is the notion of an `R`-fundamental class of Hatcher,
p.236: for a topological `n`-manifold the local homology at each point is a copy of `R`, and the
image of `μ` must be a generator there.

The predicate needs no orientation datum, which is what closed-manifold duality over an arbitrary
commutative ring consumes. The integral fundamental class `o.fundamentalClass hn` of an oriented
compact manifold, and its rational normalization `o.rationalFundamentalClass hn` on a connected
one, are fundamental classes in this sense.

## Main definitions

* `TauCeti.IsFundamentalClass`: the image of `μ ∈ Hₙ(M; N)` in the local homology at every point
  generates it.

## Main results

* `TauCeti.isFundamentalClass_smul_iff_of_isUnit`: multiplying by a unit preserves fundamental
  classes.
* `TauCeti.isFundamentalClass_iff_isUnit_of_linearEquiv`: for local homology identified with the
  coefficient ring `R` at every point, `μ` is a fundamental class exactly when each of its local
  coordinates is a unit of `R`.
* `TauCeti.isFundamentalClass_of_subsingleton`: over the zero ring every class is fundamental.
* `TauCeti.not_isFundamentalClass_zero`: on a nonempty `n`-manifold with nontrivial coefficients,
  the zero class of `Hₙ(M; N)` is not fundamental.
* `TauCeti.IsFundamentalClass.isFundamentalClass_smul_iff`: on a nonempty `n`-manifold with
  faithful coefficients over a commutative ring, `r • μ` is fundamental for a fundamental class
  `μ` exactly when `r` is a unit.
* `TauCeti.isFundamentalClass_iff_ne_zero`: over a division ring, on a compact connected manifold,
  the fundamental classes are exactly the nonzero top-dimensional classes.
* `TauCeti.isFundamentalClass_iff_forall_isLocalOrientation`: with integral coefficients, `μ` is a
  fundamental class exactly when its image at each point is a local orientation.
* `TauCeti.HomologicalOrientation.isFundamentalClass_fundamentalClass`: the integral fundamental
  class of a compact oriented manifold is a fundamental class.
* `TauCeti.HomologicalOrientation.isFundamentalClass_zsmul_fundamentalClass_iff`: on a nonempty
  compact oriented manifold, `c • [M]` is a fundamental class exactly when `c = ±1`. In
  particular `2 • [M]` is not (`not_isFundamentalClass_two_zsmul_fundamentalClass`); for `M` the
  circle, the image of `2 • [S¹]` at each point is twice a generator.
* `TauCeti.HomologicalOrientation.isFundamentalClass_rationalFundamentalClass`: the rational
  fundamental class of a compact connected oriented manifold is a fundamental class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe w u

namespace TauCeti

section Definition

variable {M : Type w} [TopologicalSpace M] {R : Type u} [Ring R] {N : ModuleCat.{w} R} {n : ℕ}

/-- **Fundamental classes with coefficients.** A class `μ` of `Hₙ(M; N)` is a *fundamental class*
when, for every point `x` of `M`, its image in the local homology `Hₙ(M, M ∖ {x}; N)` generates
that `R`-module. The image is the quotient map to `Hₙ(M, M ∖ M; N)` followed by restriction to
`{x}`. For `N = R` and `M` a topological `n`-manifold this is an `R`-fundamental class in the sense
of Hatcher, p.236. -/
def IsFundamentalClass (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    Prop :=
  ∀ x : M, Submodule.span R {singularHomologyToLocalHomology N x n μ} = ⊤

theorem isFundamentalClass_iff
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ ↔
      ∀ x : M, Submodule.span R {singularHomologyToLocalHomology N x n μ} = ⊤ :=
  Iff.rfl

/-- Multiplying a class by a unit of `R` does not change whether it is fundamental. -/
theorem isFundamentalClass_smul_iff_of_isUnit {r : R} (hr : IsUnit r)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)} :
    IsFundamentalClass (r • μ) ↔ IsFundamentalClass μ := by
  simp only [isFundamentalClass_iff, map_smul, Submodule.span_singleton_smul_eq hr]

/-- A class is fundamental exactly when its negative is. -/
@[simp]
theorem isFundamentalClass_neg_iff
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)} :
    IsFundamentalClass (-μ) ↔ IsFundamentalClass μ := by
  rw [← neg_one_smul R μ, isFundamentalClass_smul_iff_of_isUnit isUnit_one.neg]

/-- **Over the zero ring every class is fundamental**: every module over it is trivial. -/
theorem isFundamentalClass_of_subsingleton [Subsingleton R]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ := by
  refine (isFundamentalClass_iff μ).2 fun x ↦ ?_
  have := Module.subsingleton R (localHomology N ({x} : Set M) n : ModuleCat.{w} R)
  exact Subsingleton.elim _ _

/-- **Fundamental classes through local coordinates.** If the local homology `Hₙ(M, M ∖ {x}; N)`
is identified with the ring `R` at every point, a class is fundamental exactly when its coordinate
at every point is a unit. Over a noncommutative ring this needs every left inverse to be a
two-sided inverse. -/
theorem isFundamentalClass_iff_isUnit_of_linearEquiv [IsDedekindFiniteMonoid R]
    (e : ∀ x : M, (localHomology N ({x} : Set M) n : ModuleCat.{w} R) ≃ₗ[R] R)
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ ↔ ∀ x : M, IsUnit (e x (singularHomologyToLocalHomology N x n μ)) :=
  forall_congr' fun x ↦ (e x).span_singleton_eq_top_iff_isUnit

end Definition

section Manifold

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **The zero class is not fundamental** in the top degree `n` of a nonempty `n`-manifold with
nontrivial coefficients: the local homology `Hₙ(M, M ∖ {x}; N)` at a point is then a nontrivial
copy of the coefficients, which `0 ∈ Hₙ(M; N)` does not generate. -/
theorem not_isFundamentalClass_zero [T1Space M] [Nonempty M] {R : Type u} [Ring R]
    (N : ModuleCat.{w} R) [Nontrivial N] :
    ¬ IsFundamentalClass (0 : ((TopCat.toSSet.obj (TopCat.of M)).homology N n :
      ModuleCat.{w} R)) := by
  subst hn
  obtain ⟨x⟩ := ‹Nonempty M›
  intro h
  have : Nontrivial (localHomology N ({x} : Set M) (finrank ℝ E) : ModuleCat.{w} R) :=
    (singularHomologyComplSingletonFinrankIso N (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv.toEquiv.nontrivial
  have hx := (isFundamentalClass_iff _).1 h x
  rw [map_zero, Submodule.span_singleton_eq_bot.2 rfl] at hx
  exact bot_ne_top hx

include hn in
/-- **Multiples of a fundamental class.** On a nonempty `n`-manifold, with faithful coefficients
`N` over a commutative ring `R`, a multiple `r • μ` of a fundamental class `μ ∈ Hₙ(M; N)` is a
fundamental class exactly when `r` is a unit. -/
theorem IsFundamentalClass.isFundamentalClass_smul_iff [T1Space M] [Nonempty M] {R : Type u}
    [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (r : R) : IsFundamentalClass (r • μ) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun hr ↦ (isFundamentalClass_smul_iff_of_isUnit hr).2 hμ⟩
  subst hn
  obtain ⟨x⟩ := ‹Nonempty M›
  have hv := (isFundamentalClass_iff μ).1 hμ x
  have hrv := (isFundamentalClass_iff _).1 h x
  rw [map_smul] at hrv
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1
    (hrv.symm ▸ Submodule.mem_top : singularHomologyToLocalHomology N x _ μ ∈ _)
  -- `s * r` fixes the image of `μ`, hence every multiple of it, that is every local class.
  have hsr (z : (localHomology N ({x} : Set M) (finrank ℝ E) : ModuleCat.{w} R)) :
      (s * r) • z = z := by
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 (hv.symm ▸ Submodule.mem_top : z ∈ _)
    rw [smul_comm (s * r) t, mul_smul, hs]
  let e := (singularHomologyComplSingletonFinrankIso N (chartAt E x)
    (mem_chart_source E x)).toLinearEquiv
  refine IsUnit.of_mul_eq_one_right s (FaithfulSMul.eq_of_smul_eq_smul fun y : N ↦ ?_)
  rw [one_smul, ← e.apply_symm_apply y, ← map_smul, hsr]

include hn in
/-- **Fundamental classes over a division ring.** On a nonempty compact connected `n`-manifold, a
class of `Hₙ(M; K)` is a fundamental class exactly when it is nonzero: its image at each point is
then a nonzero element of the one-dimensional local homology. -/
theorem isFundamentalClass_iff_ne_zero [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {K : Type w} [DivisionRing K]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
    IsFundamentalClass μ ↔ μ ≠ 0 := by
  have : Nonempty M := ConnectedSpace.toNonempty
  refine ⟨fun h hμ ↦ not_isFundamentalClass_zero hn (ModuleCat.of K K) (hμ ▸ h), fun hμ ↦ ?_⟩
  subst hn
  rw [isFundamentalClass_iff_isUnit_of_linearEquiv fun x ↦
    (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K) (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv]
  refine fun x ↦ isUnit_iff_ne_zero.2 ((LinearEquiv.map_ne_zero_iff _).2 ?_)
  rw [← map_zero (singularHomologyToLocalHomology (ModuleCat.of K K) x _)]
  exact (singularHomologyToLocalHomology_injective _ rfl x).ne hμ

end Manifold

section Integral

variable {M : Type w} [TopologicalSpace M] {n : ℕ}

/-- **Integral fundamental classes.** With integral coefficients, a class is fundamental exactly
when its image in the local homology at every point is a local orientation. -/
theorem isFundamentalClass_iff_forall_isLocalOrientation
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
      ModuleCat.{w} ℤ)) :
    IsFundamentalClass μ ↔ ∀ x : M, IsLocalOrientation x n
      (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ) :=
  forall_congr' fun x ↦ by
    rw [Submodule.span_singleton_eq_top_iff, isLocalOrientation_iff]
    exact forall_congr' fun _ ↦ exists_congr fun c ↦
      iff_of_eq (congrArg (· = _) (int_smul_eq_zsmul _ c _))

end Integral

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) [CompactSpace M]

/-- **The integral fundamental class is a fundamental class**: its image at every point is the
local orientation there, which generates the local homology. -/
theorem isFundamentalClass_fundamentalClass : IsFundamentalClass (o.fundamentalClass hn) :=
  (isFundamentalClass_iff_forall_isLocalOrientation _).2 fun x ↦ by
    rw [o.singularHomologyToLocalHomology_fundamentalClass hn x]
    exact (o x).property

/-- **Multiples of the fundamental class.** On a nonempty compact oriented manifold, `c • [M]` is
a fundamental class exactly when `c` is a unit, that is `c = ±1`. -/
theorem isFundamentalClass_zsmul_fundamentalClass_iff [Nonempty M] (c : ℤ) :
    IsFundamentalClass (c • o.fundamentalClass hn) ↔ IsUnit c := by
  rw [← int_smul_eq_zsmul]
  exact (o.isFundamentalClass_fundamentalClass hn).isFundamentalClass_smul_iff hn c

/-- **Twice the fundamental class is not a fundamental class** on a nonempty compact oriented
manifold, for instance the circle: its image at each point is twice a generator of `ℤ`. -/
theorem not_isFundamentalClass_two_zsmul_fundamentalClass [Nonempty M] :
    ¬ IsFundamentalClass ((2 : ℤ) • o.fundamentalClass hn) := by
  rw [o.isFundamentalClass_zsmul_fundamentalClass_iff hn, Int.isUnit_iff]
  omega

/-- **The rational fundamental class is a fundamental class** on a compact connected oriented
manifold: it is nonzero, and over the field `ℚ` every nonzero top-dimensional class is
fundamental. -/
theorem isFundamentalClass_rationalFundamentalClass [ConnectedSpace M] :
    IsFundamentalClass (N := ModuleCat.of ℚ ℚ) (n := n) (o.rationalFundamentalClass hn) := by
  refine (isFundamentalClass_iff_ne_zero hn _).2 ?_
  rw [rationalFundamentalClass_def]
  exact (o.rationalFundamentalClassEquiv hn).map_ne_zero_iff.2 one_ne_zero

end HomologicalOrientation

end TauCeti
