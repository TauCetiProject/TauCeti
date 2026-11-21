/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import TauCeti.Algebra.Group.Action.ULift
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

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
commutative ring consumes. The integral and rational fundamental-class specializations for
`TauCeti.HomologicalOrientation` live in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass`.

## Main definitions

* `TauCeti.IsFundamentalClass`: the image of `μ ∈ Hₙ(M; N)` in the local homology at every point
  generates it.

## Main results

* `TauCeti.isFundamentalClass_iff_singularHomologyπ`: characterization via `singularHomologyπ`.
* `TauCeti.IsFundamentalClass.map_coefficientsIso`: invariance under coefficient isomorphisms.
* `TauCeti.IsFundamentalClass.extendScalarsObj`, `extendScalars`: exact scalar-extension invariance.
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
* `TauCeti.IsFundamentalClass.exists_linearEquiv_isUnit`: on a compact connected manifold, with
  coefficients free of rank one over a Dedekind-finite ring `k`, the top homology carrying a
  fundamental class `μ` is a copy of `k` in which `μ` is a unit.
* `TauCeti.IsFundamentalClass.map_homeomorph`: homeomorphisms carry fundamental classes to
  fundamental classes.
* `TauCeti.isFundamentalClass_iff_forall_isLocalOrientation`: with integral coefficients, `μ` is a
  fundamental class exactly when its image at each point is a local orientation.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236.
-/

public section

noncomputable section

open CategoryTheory Module Set
open scoped ChangeOfRings

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

/-- `TauCeti.IsFundamentalClass` expressed via `TopPair.singularHomologyπ`. -/
theorem isFundamentalClass_iff_singularHomologyπ
    (μ : ↑((TopCat.toSSet.obj (TopCat.of M)).homology N n)) : IsFundamentalClass μ ↔ ∀ x : M,
      Submodule.span R {((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} R) N n).hom μ} = ⊤ := (isFundamentalClass_iff μ).trans
  (forall_congr' fun _ ↦ by rw [singularHomologyToLocalHomology_eq_singularHomologyπ])
/-- An isomorphism of coefficient modules `e : N ≅ N'` preserves fundamental classes. -/
theorem IsFundamentalClass.map_coefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    {μ : ↑((TopCat.toSSet.obj (TopCat.of M)).homology N n)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass
      ((SSet.homologyIsoOfCoefficientsIso e (TopCat.toSSet.obj (TopCat.of M)) n).hom μ) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2 ((isFundamentalClass_iff μ).1 hμ x)
section
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]
/-- Exact scalar extension along `f : R →+* S` preserves fundamental classes for arbitrary `N`. -/
theorem IsFundamentalClass.extendScalarsObj {N : ModuleCat.{w} R}
    {μ : ↑((TopCat.toSSet.obj (TopCat.of M)).homology N n)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass ((SSet.homologyObjIso (ModuleCat.extendScalars.{w, w, w} f) N
      (TopCat.toSSet.obj (TopCat.of M)) n).hom ((1 : S) ⊗ₜ[R, f] μ)) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyObjIso_hom_tmul]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
      (ModuleCat.ExtendScalars.span_singleton_one_tmul_eq_top f ((isFundamentalClass_iff μ).1 hμ x))
/-- **Exact extension of scalars preserves fundamental classes** for ring coefficients. -/
theorem IsFundamentalClass.extendScalars
    {μ : ↑((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass ((f.singularHomologyExtendScalarsIso M n).hom ((1 : S) ⊗ₜ[R, f] μ)) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
      (ModuleCat.ExtendScalars.span_singleton_one_tmul_eq_top f ((isFundamentalClass_iff μ).1 hμ x))
end

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

section Homeomorph

variable {M M' : Type w} [TopologicalSpace M] [TopologicalSpace M'] {R : Type u} [Ring R]
  {N : ModuleCat.{w} R} {n : ℕ}

open AlgebraicTopology in
/-- **Fundamental classes are natural under homeomorphisms**: a homeomorphism `e : M ≃ₜ M'`
carries a fundamental class of `M` to a fundamental class of `M'`. -/
theorem IsFundamentalClass.map_homeomorph
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (e : M ≃ₜ M') :
    IsFundamentalClass
      ((((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map
        (TopCat.ofHom (e : C(M, M')))).hom μ) := by
  intro y
  obtain ⟨x, rfl⟩ : ∃ x, (e : C(M, M')) x = y := e.surjective y
  have hx : (e : C(M, M')) ⁻¹' {(e : C(M, M')) x} ⊆ {x} := fun z hz ↦ e.injective hz
  have hx' : (e.symm : C(M', M)) ⁻¹' {x} ⊆ {(e : C(M, M')) x} := fun z hz ↦
    e.symm_apply_eq.1 hz
  -- The map of local homology induced by `e` has the one induced by `e.symm` as a section.
  have hsurj : Function.Surjective (localHomologyMap N (e : C(M, M')) hx n) := fun z ↦ by
    refine ⟨localHomologyMap N (e.symm : C(M', M)) hx' n z, ?_⟩
    rw [← ConcreteCategory.comp_apply, localHomologyMap_comp,
      localHomologyMap_congr N (ContinuousMap.ext fun y ↦ e.apply_symm_apply y :
        (e : C(M, M')).comp e.symm = ContinuousMap.id M'), localHomologyMap_id]
    exact congrArg (fun φ ↦ φ.hom z) (localHomologyRestriction_refl N _ n)
  have h := congrArg (Submodule.map (localHomologyMap N (e : C(M, M')) hx n).hom) (hμ x)
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.2 hsurj] at h
  -- The local class of `e_* μ` at `e x` is read through the naturality of local homology.
  rw [singularHomologyFunctor_obj_map_hom_apply,
    singularHomologyToLocalHomology_singularHomologyMap N (e : C(M, M')) hx]
  exact h

end Homeomorph

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
  have hrv := (isFundamentalClass_iff _).1 h x
  rw [map_smul] at hrv
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1
    (hrv.symm ▸ Submodule.mem_top : singularHomologyToLocalHomology N x _ μ ∈ _)
  rw [smul_smul] at hs
  exact IsUnit.of_mul_eq_one_right s
    ((singularHomologyComplSingletonFinrankIso N (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv.eq_one_of_smul_eq_self_of_span_singleton_eq_top
      ((isFundamentalClass_iff μ).1 hμ x) hs)

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

include hn in
/-- **The top homology of a manifold with a fundamental class is free of rank one.** On a compact
connected `n`-manifold, with coefficients `R ≃ₗ[k] k` over a Dedekind-finite ring `k` (for instance
a commutative ring or a domain), if `μ ∈ Hₙ(M; R)` is a fundamental class then `Hₙ(M; R)` is
isomorphic to `k` by an equivalence sending `μ` to a unit: restriction to the local homology at a
point is injective (`TauCeti.singularHomologyToLocalHomology_injective`), surjective since its
image contains the generator given by `μ`, and carries `μ` to a generator. -/
theorem IsFundamentalClass.exists_linearEquiv_isUnit [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k}
    (eR : R ≃ₗ[k] k) {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) :
    ∃ e : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k) ≃ₗ[k] k,
      IsUnit (e μ) := by
  obtain ⟨x⟩ : Nonempty M := ConnectedSpace.toNonempty
  have hsurj : Function.Surjective (singularHomologyToLocalHomology R x n) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (isFundamentalClass_iff μ).1 hμ x,
      Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_range_self _ μ
  let eL := localHomologySingletonLinearEquiv R hn eR x
  refine ⟨(LinearEquiv.ofBijective _
    ⟨singularHomologyToLocalHomology_injective R hn x, hsurj⟩).trans eL, ?_⟩
  -- The image of `μ` generates the local homology, so its coordinate is a unit.
  exact eL.span_singleton_eq_top_iff_isUnit.1 ((isFundamentalClass_iff μ).1 hμ x)

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

end TauCeti
