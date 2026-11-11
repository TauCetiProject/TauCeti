/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Fundamental classes with coefficients in a ring

Let `M` be a space, `R` a ring and `N` an `R`-module. A class `μ` of the singular homology
`Hₙ(M; N)` is a *fundamental class* (`TauCeti.IsFundamentalClass`) when, for every point `x` of
`M`, its image in the local homology `Hₙ(M, M ∖ {x}; N)` generates that `R`-module. The image is
the quotient map `Hₙ(M; N) ⟶ Hₙ(M, M ∖ M; N)` followed by restriction to `{x}`. With `N = R` this
is the notion of an `R`-fundamental class of Hatcher, p.236: for a topological `n`-manifold the
local homology at each point is a copy of `R`, and the image of `μ` must be a generator there.

The predicate needs no orientation datum, which is what closed-manifold duality over an arbitrary
commutative ring consumes. The integral fundamental class `o.fundamentalClass hn` of an oriented
compact manifold, and its rational normalization `o.rationalFundamentalClass hn` on a connected
one, are fundamental classes in this sense.

## Main definitions

* `TauCeti.IsFundamentalClass`: the image of `μ ∈ Hₙ(M; N)` in the local homology at every point
  generates it.

## Main results

* `TauCeti.isFundamentalClass_iff_isUnit_of_linearEquiv`: for local homology identified with a
  commutative ring `R` at every point, `μ` is a fundamental class exactly when each of its local
  coordinates is a unit of `R`.
* `TauCeti.isFundamentalClass_of_subsingleton`: over the zero ring every class is fundamental.
* `TauCeti.not_isFundamentalClass_zero`: on a nonempty `n`-manifold with nontrivial coefficients,
  the zero class is not fundamental.
* `TauCeti.isFundamentalClass_iff_ne_zero`: over a field, on a compact connected manifold, the
  fundamental classes are exactly the nonzero top-dimensional classes.
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

For a finite discrete space (a `0`-manifold), `isFundamentalClass_iff_isUnit_of_linearEquiv` says
that a class of `H₀(M; R)` is fundamental exactly when its coordinate at every point is a unit:
over `ℤ` on two points, `(u₁, u₂)` is fundamental exactly when `u₁, u₂ = ±1`, and `(1, 0)` is not.

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

variable (N) in
/-- The map `Hₙ(M; N) → Hₙ(M, M ∖ {x}; N)` from the singular homology of `M` to its local
homology at `x`: the quotient map to `Hₙ(M, M ∖ M; N)` followed by restriction to `{x}`. -/
def singularHomologyToLocalHomology (x : M) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R) →ₗ[R]
      (localHomology N ({x} : Set M) n : ModuleCat.{w} R) :=
  ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ (C := ModuleCat.{w} R) N n ≫
    localHomologyRestriction N (subset_univ {x}) n).hom

theorem singularHomologyToLocalHomology_apply (x : M)
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    singularHomologyToLocalHomology N x n μ =
      localHomologyRestriction N (subset_univ {x}) n
        (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
          (C := ModuleCat.{w} R) N n).hom μ) :=
  (rfl)

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

/-- A class is fundamental exactly when its negative is. -/
@[simp]
theorem isFundamentalClass_neg_iff
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)} :
    IsFundamentalClass (-μ) ↔ IsFundamentalClass μ := by
  simp only [isFundamentalClass_iff, map_neg, ← Set.neg_singleton, Submodule.span_neg]

/-- **Over the zero ring every class is fundamental**: every module over it is trivial. -/
theorem isFundamentalClass_of_subsingleton [Subsingleton R]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ := by
  refine (isFundamentalClass_iff μ).2 fun x ↦ ?_
  have := Module.subsingleton R (localHomology N ({x} : Set M) n : ModuleCat.{w} R)
  exact Subsingleton.elim _ _

/-- An element of a module identified with a commutative ring `R` generates it exactly when its
coordinate is a unit. -/
private theorem span_singleton_eq_top_iff_isUnit {R P : Type*} [CommRing R] [AddCommGroup P]
    [Module R P] (e : P ≃ₗ[R] R) (v : P) :
    Submodule.span R {v} = ⊤ ↔ IsUnit (e v) := by
  rw [Submodule.span_singleton_eq_top_iff]
  refine ⟨fun h ↦ ?_, fun h w ↦ ⟨e w * ↑h.unit⁻¹, e.injective ?_⟩⟩
  · obtain ⟨r, hr⟩ := h (e.symm 1)
    exact IsUnit.of_mul_eq_one_right r (by simpa using congrArg e hr)
  · rw [map_smul, smul_eq_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

end Definition

section CommRing

variable {M : Type w} [TopologicalSpace M] {R : Type u} [CommRing R] {N : ModuleCat.{w} R} {n : ℕ}

/-- **Fundamental classes through local coordinates.** If the local homology `Hₙ(M, M ∖ {x}; N)`
is identified with the commutative ring `R` at every point, a class is fundamental exactly when its
coordinate at every point is a unit. For a finite discrete space and `n = 0`, this says that a
class of `H₀(M; R)` is fundamental exactly when each of its entries is a unit. -/
theorem isFundamentalClass_iff_isUnit_of_linearEquiv
    (e : ∀ x : M, (localHomology N ({x} : Set M) n : ModuleCat.{w} R) ≃ₗ[R] R)
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ ↔ ∀ x : M, IsUnit (e x (singularHomologyToLocalHomology N x n μ)) :=
  forall_congr' fun x ↦ span_singleton_eq_top_iff_isUnit (e x) _

end CommRing

section Manifold

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **The zero class is not fundamental** on a nonempty manifold with nontrivial coefficients: the
local homology at a point is then a nontrivial copy of the coefficients, which `0` does not
generate. -/
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
/-- On a compact connected manifold, a top-dimensional class is determined by its image in the
local homology at any one point. -/
private theorem localHomologyRestriction_singularHomologyπ_injective [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (x : M) :
    Function.Injective (singularHomologyToLocalHomology N x n) := by
  have : IsEmpty (TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).snd := by
    simp only [compl_univ]
    exact inferInstanceAs (IsEmpty (∅ : Set M))
  have hπ : IsIso ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{w} Λ) N n) := inferInstance
  exact (localHomologySystemCone_π_app_injective N hn (FundamentalGroupoid.mk x)).comp
    ((ConcreteCategory.isIso_iff_bijective _).1 hπ).1

include hn in
/-- **Fundamental classes over a field.** On a nonempty compact connected `n`-manifold, a class of
`Hₙ(M; K)` is a fundamental class exactly when it is nonzero: its image at each point is then a
nonzero element of the one-dimensional local homology. -/
theorem isFundamentalClass_iff_ne_zero [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {K : Type w} [Field K]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
    IsFundamentalClass μ ↔ μ ≠ 0 := by
  have : Nonempty M := ConnectedSpace.toNonempty
  refine ⟨fun h hμ ↦ not_isFundamentalClass_zero hn (ModuleCat.of K K) (hμ ▸ h),
    fun hμ ↦ (isFundamentalClass_iff μ).2 fun x ↦ ?_⟩
  have himg := (localHomologyRestriction_singularHomologyπ_injective hn (ModuleCat.of K K) x).ne
    hμ
  rw [map_zero] at himg
  subst hn
  let e := (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K) (chartAt E x)
    (mem_chart_source E x)).toLinearEquiv
  rw [span_singleton_eq_top_iff_isUnit e, isUnit_iff_ne_zero]
  exact e.map_ne_zero_iff.2 himg

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
    rw [singularHomologyToLocalHomology_apply,
      o.localHomologyRestriction_singularHomologyπ_fundamentalClass hn x]
    exact (o x).property

/-- **Multiples of the fundamental class.** On a nonempty compact oriented manifold, `c • [M]` is
a fundamental class exactly when `c` is a unit, that is `c = ±1`: its image at `x` is `c • o x`,
and `o x` has infinite order. -/
theorem isFundamentalClass_zsmul_fundamentalClass_iff [Nonempty M] (c : ℤ) :
    IsFundamentalClass (c • o.fundamentalClass hn) ↔ IsUnit c := by
  have himg (x : M) : singularHomologyToLocalHomology _ x n (c • o.fundamentalClass hn) =
      c • (o x).val := by
    rw [map_zsmul, singularHomologyToLocalHomology_apply,
      o.localHomologyRestriction_singularHomologyπ_fundamentalClass hn x]
  simp only [isFundamentalClass_iff_forall_isLocalOrientation, himg]
  refine ⟨fun h ↦ ?_, fun hc x ↦ ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty M›
    obtain ⟨d, hd⟩ := (isLocalOrientation_iff _ _ _).1 (h x) (o x).val
    rw [smul_smul] at hd
    exact IsUnit.of_mul_eq_one_right d
      (o.zsmul_left_injective hn x (show (d * c) • (o x).val = (1 : ℤ) • (o x).val by
        rw [one_smul]; exact hd))
  · rcases Int.isUnit_iff.1 hc with rfl | rfl
    · simpa using (o x).property
    · simpa using (o x).property.neg

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
