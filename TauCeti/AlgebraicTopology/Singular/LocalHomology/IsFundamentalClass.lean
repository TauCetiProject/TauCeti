/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.ULift
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Section

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

With coefficients in a commutative ring `K` whose only unit is `1`, such as `ZMod 2`, or more
generally a Dedekind-finite ring with this property, every compact manifold has exactly one
fundamental class, oriented or not and connected or not
(`TauCeti.existsUnique_isFundamentalClass_of_subsingleton_units`; Hatcher, Theorem 3.26). The local
homology `Hₙ(M, M ∖ {x}; K) ≅ K` then has a single generator, so transport along paths, being an
isomorphism, preserves the generators (`TauCeti.localHomologyTransport_eq_of_span_eq_top`), and
this parallel family of generators glues to a global class. On a connected manifold every
top-dimensional class with coefficients in a commutative ring, or more generally a Dedekind-finite
ring, is a unique multiple of a fundamental class
(`TauCeti.IsFundamentalClass.existsUnique_eq_smul`); for the image of a fundamental class under a
map this multiple is the degree of the map with coefficients in `K`, the mod `2` degree for
`K = ZMod 2`.

## Main definitions

* `TauCeti.IsFundamentalClass`: the image of `μ ∈ Hₙ(M; N)` in the local homology at every point
  generates it.

## Main results

* `TauCeti.isFundamentalClass_smul_iff_of_isUnit`: multiplying by a unit preserves fundamental
  classes.
* `TauCeti.IsFundamentalClass.of_smul`: a class with a fundamental multiple is fundamental.
* `TauCeti.isFundamentalClass_iff_isUnit_of_linearEquiv`: for local homology identified with the
  coefficient ring `R` at every point, `μ` is a fundamental class exactly when each of its local
  coordinates is a unit of `R`.
* `TauCeti.isFundamentalClass_of_subsingleton`: over the zero ring every class is fundamental.
* `TauCeti.IsFundamentalClass.singularHomologyToLocalHomology_ne_zero`: on an `n`-manifold with
  nontrivial coefficients, a fundamental class has a nonzero image in every local homology group.
* `TauCeti.isFundamentalClass_singularHomologyFunctor_map_app_iff`: changing the coefficients along
  an isomorphism `N ≅ N'` preserves and reflects fundamental classes.
* `TauCeti.not_isFundamentalClass_zero`: on a nonempty `n`-manifold with nontrivial coefficients,
  the zero class of `Hₙ(M; N)` is not fundamental.
* `TauCeti.IsFundamentalClass.isFundamentalClass_smul_iff`: on a nonempty `n`-manifold with
  faithful coefficients over a commutative ring, `r • μ` is fundamental for a fundamental class
  `μ` exactly when `r` is a unit.
* `TauCeti.isFundamentalClass_iff_ne_zero`: over a division ring, on a compact connected manifold,
  the fundamental classes are exactly the nonzero top-dimensional classes.
* `TauCeti.IsFundamentalClass.exists_linearEquiv_isUnit`: on a compact connected manifold, with
  coefficients free of rank one over a Dedekind-finite ring `k`, the top homology carrying a
  fundamental class `μ` is a copy of `k` in which `μ` is a unit.
* `TauCeti.IsFundamentalClass.existsUnique_eq_smul`: on a connected manifold, with
  coefficients in a Dedekind-finite ring `K`, every top-dimensional class is `c • μ` for a unique
  `c : K`.
* `TauCeti.localHomologyTransport_eq_of_span_eq_top`: when `1` is the only unit of the
  coefficients, transport of local homology sends the generator to the generator.
* `TauCeti.existsUnique_isFundamentalClass_of_subsingleton_units`: when `1` is the only unit of the
  coefficients, for instance over `ZMod 2`, a compact manifold has exactly one fundamental class.
* `TauCeti.IsFundamentalClass.eq_of_subsingleton_units`: so any two such fundamental classes are
  equal.
* `TauCeti.IsFundamentalClass.map_homeomorph`: homeomorphisms carry fundamental classes to
  fundamental classes.
* `TauCeti.isFundamentalClass_iff_forall_isLocalOrientation`: with integral coefficients, `μ` is a
  fundamental class exactly when its image at each point is a local orientation.
* `TauCeti.HomologicalOrientation.isFundamentalClass_fundamentalClass`: the integral fundamental
  class of a compact oriented manifold is a fundamental class.
* `TauCeti.HomologicalOrientation.isFundamentalClass_zsmul_fundamentalClass_iff`: on a nonempty
  compact oriented manifold, `c • [M]` is a fundamental class exactly when `c = ±1`. In
  particular `2 • [M]` is not (`not_isFundamentalClass_two_zsmul_fundamentalClass`); for `M` the
  circle, the image of `2 • [S¹]` at each point is twice a generator.
* `TauCeti.HomologicalOrientation.isFundamentalClass_iff_eq_or_eq_neg`: on a compact connected
  oriented manifold, the integral fundamental classes are exactly `[M]` and `-[M]`.
* `TauCeti.HomologicalOrientation.exists_eq_smul_mapFundamentalClass_of_isFundamentalClass`: the
  integral fundamental classes of a space homeomorphic to such a manifold through `e` are
  `±e_*[M]`.
* `TauCeti.HomologicalOrientation.isFundamentalClass_rationalFundamentalClass`: the rational
  fundamental class of a compact connected oriented manifold is a fundamental class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe w u

namespace TauCeti

section Manifold

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **Top-dimensional classes are multiples of a fundamental class.** On a connected
`n`-manifold, with coefficients in a Dedekind-finite ring `K` (for instance a commutative ring),
every class `γ` of `Hₙ(M; K)` is `c • μ` for exactly one `c : K`, where `μ` is a fundamental
class. For a map `f` from a compact manifold with fundamental class `μ'`, the coefficient of
`f_* μ'` is the degree of `f` with coefficients in `K`. -/
theorem IsFundamentalClass.existsUnique_eq_smul [T2Space M] [ConnectedSpace M]
    {K : Type w} [Ring K] [IsDedekindFiniteMonoid K]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)}
    (hμ : IsFundamentalClass μ)
    (γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
    ∃! c : K, γ = c • μ := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · -- Over the zero ring the homology is trivial.
    have := Module.subsingleton K
      ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)
    exact ⟨0, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  -- The fundamental class is nonzero, so `Hₙ(M; K) ≠ 0` and the connected manifold is compact.
  have : T1Space M := ChartedSpace.t1Space E M
  have : Nonempty M := ConnectedSpace.toNonempty
  have : CompactSpace M := compactSpace_of_nontrivial_singularHomology (ModuleCat.of K K) hn le_rfl
    (h := ⟨⟨μ, 0, fun h0 ↦ not_isFundamentalClass_zero hn (ModuleCat.of K K) (h0 ▸ hμ)⟩⟩)
  obtain ⟨e, u, hu⟩ := hμ.exists_linearEquiv_isUnit hn (LinearEquiv.refl K K)
  -- In the coordinate `e`, the equation `γ = c • μ` reads `e γ = c * u` for the unit `u = e μ`.
  have key (c : K) : γ = c • μ ↔ c = e γ * ↑u⁻¹ := by
    rw [← e.injective.eq_iff, map_smul, smul_eq_mul, ← hu, eq_comm, Units.eq_mul_inv_iff_mul_eq]
  exact ⟨e γ * ↑u⁻¹, (key _).2 rfl, fun c hc ↦ (key c).1 hc⟩

end Manifold

section SubsingletonUnits

variable (K : Type w) [Ring K] [IsDedekindFiniteMonoid K] [Subsingleton Kˣ]
  {M E : Type w} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

omit [T2Space M] in
include hn in
/-- **The local homology has a single generator when `1` is the only unit of the coefficients.**
On an `n`-manifold, with coefficients in a ring `K` whose only unit is `1`, such as `ZMod 2`, and
in which one-sided inverses are inverses, the local homology `Hₙ(M, M ∖ {x}; K) ≅ K` has exactly
one generator, the class corresponding to `1`. -/
theorem eq_of_span_localHomology_eq_top {x : M}
    {a b : (localHomology (ModuleCat.of K K) ({x} : Set M) n : ModuleCat.{w} K)}
    (ha : Submodule.span K {a} = ⊤) (hb : Submodule.span K {b} = ⊤) : a = b := by
  have : T1Space M := ChartedSpace.t1Space E M
  exact (localHomologySingletonLinearEquiv (ModuleCat.of K K) hn (LinearEquiv.refl K K)
    x).eq_of_span_singleton_eq_top ha hb

include hn in
/-- **Transport preserves the generator of local homology when `1` is the only unit of the
coefficients.** On an `n`-manifold, with coefficients in a Dedekind-finite ring `K` whose only
unit is `1`, the transport of local homology along a path sends the generator of
`Hₙ(M, M ∖ {x}; K)` to the generator of `Hₙ(M, M ∖ {y}; K)`: the transport is an isomorphism,
so it preserves generators, and each of these modules has only one. With integral coefficients
the transport along a loop can instead reverse the local orientation. -/
theorem localHomologyTransport_eq_of_span_eq_top {x y : FundamentalGroupoid M} (f : x ⟶ y)
    {a : (localHomology (ModuleCat.of K K) ({x.as} : Set M) n : ModuleCat.{w} K)}
    {b : (localHomology (ModuleCat.of K K) ({y.as} : Set M) n : ModuleCat.{w} K)}
    (ha : Submodule.span K {a} = ⊤) (hb : Submodule.span K {b} = ⊤) :
    localHomologyTransport (ModuleCat.of K K) M E n f a = b := by
  let e := (asIso ((localHomologySystem (ModuleCat.of K K) M E n).map f)).toLinearEquiv
  exact eq_of_span_localHomology_eq_top K hn (e.span_singleton_apply_eq_top_iff.2 ha) hb

include hn in
/-- **Every compact manifold has a unique fundamental class when `1` is the only unit of the
coefficients.** On a compact `n`-manifold, with coefficients in a Dedekind-finite ring `K` (for
instance a commutative ring) whose only unit is `1`, such as `ZMod 2`, there is exactly one
fundamental class in `Hₙ(M; K)`. No orientation
and no connectedness is needed: the generators of the local homology groups
`Hₙ(M, M ∖ {x}; K) ≅ K` form a family invariant under transport
(`TauCeti.localHomologyTransport_eq_of_span_eq_top`), which glues to a single class. For
`K = ZMod 2` this is the mod `2` fundamental class of Hatcher, Theorem 3.26. -/
theorem existsUnique_isFundamentalClass_of_subsingleton_units [CompactSpace M] :
    ∃! μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K),
      IsFundamentalClass μ := by
  let e (x : M) := localHomologySingletonLinearEquiv (ModuleCat.of K K) hn (LinearEquiv.refl K K) x
  have hg (x : M) : Submodule.span K {(e x).symm 1} = ⊤ :=
    (e x).symm.span_singleton_apply_eq_top_iff.2 (Ideal.span_singleton_one)
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant
    (ModuleCat.of K K) hn (fun x ↦ (e x).symm 1)
    fun f ↦ localHomologyTransport_eq_of_span_eq_top K hn f (hg _) (hg _)
  exact ⟨μ, (isFundamentalClass_iff _).2 fun x ↦ (hμ x).symm ▸ hg x, fun ν hν ↦
    huniq ν fun x ↦ eq_of_span_localHomology_eq_top K hn ((isFundamentalClass_iff _).1 hν x) (hg x)⟩

variable {K} in
include hn in
/-- On a compact `n`-manifold, with coefficients in a Dedekind-finite ring whose only unit is `1`,
any two fundamental classes are equal. -/
theorem IsFundamentalClass.eq_of_subsingleton_units [CompactSpace M]
    {μ ν : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)}
    (hμ : IsFundamentalClass μ) (hν : IsFundamentalClass ν) : μ = ν :=
  (existsUnique_isFundamentalClass_of_subsingleton_units K hn).unique hμ hν

end SubsingletonUnits

section Integral

variable {M : Type w} [TopologicalSpace M] {n : ℕ}

/-- **Integral fundamental classes.** With integral coefficients, a class is fundamental exactly
when its image in the local homology at every point is a local orientation. -/
theorem isFundamentalClass_iff_forall_isLocalOrientation
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
      ModuleCat.{w} ℤ)) :
    IsFundamentalClass μ ↔ ∀ x : M, IsLocalOrientation x n
      (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ) := by
  rw [isFundamentalClass_iff]
  exact forall_congr' fun _ ↦ (isLocalOrientation_iff_span_eq_top _ _ _).symm

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

/-- **The fundamental classes of a connected manifold.** On a compact connected oriented manifold,
the integral fundamental classes are exactly `[M]` and `-[M]`. -/
theorem isFundamentalClass_iff_eq_or_eq_neg [ConnectedSpace M]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)) :
    IsFundamentalClass μ ↔ μ = o.fundamentalClass hn ∨ μ = -o.fundamentalClass hn := by
  have : Nonempty M := ConnectedSpace.toNonempty
  obtain ⟨c, rfl⟩ := o.exists_eq_zsmul_fundamentalClass hn μ
  rw [o.isFundamentalClass_zsmul_fundamentalClass_iff hn, Int.isUnit_iff]
  refine ⟨?_, ?_⟩
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · exact Or.inl (((o.fundamentalClassEquiv hn).injective (by simpa using h)))
    · exact Or.inr (((o.fundamentalClassEquiv hn).injective (by simpa using h)))

open AlgebraicTopology CategoryTheory in
/-- **Fundamental classes of a homeomorphic copy.** If `e : M ≃ₜ X` is a homeomorphism from a
compact connected oriented manifold, every integral fundamental class of `X` is `±` the image
`e_*[M]` of the fundamental class of `M`. -/
theorem exists_eq_smul_mapFundamentalClass_of_isFundamentalClass [ConnectedSpace M] {X : Type}
    [TopologicalSpace X] (e : M ≃ₜ X)
    {μ : ((TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ μ = s • o.mapFundamentalClass hn (e : C(M, X)) := by
  -- Pull `μ` back to `M`, where it is `±[M]`, and push it forward again along `e`.
  have hμe : (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (e : C(M, X)))).hom
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (e.symm : C(X, M)))).hom μ) = μ :=
    congrArg (fun φ ↦ φ.hom μ) (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo (X := TopCat.of M) e)).inv_hom_id
  rcases (o.isFundamentalClass_iff_eq_or_eq_neg hn _).1 (hμ.map_homeomorph e.symm) with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul, mapFundamentalClass_def, ← h]
    exact hμe.symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [neg_one_zsmul, ← mapFundamentalClass_neg, mapFundamentalClass_def, fundamentalClass_neg,
      ← h]
    exact hμe.symm

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
