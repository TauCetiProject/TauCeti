/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.ULift
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
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
* `TauCeti.isFundamentalClass_iff_isUnit_of_linearEquiv`: for local homology identified with the
  coefficient ring `R` at every point, `μ` is a fundamental class exactly when each of its local
  coordinates is a unit of `R`.
* `TauCeti.isFundamentalClass_of_subsingleton`: over the zero ring every class is fundamental.
* `TauCeti.isFundamentalClass_singularHomologyFunctor_map_app_iff`: changing the coefficients along
  an isomorphism `N ≅ N'` preserves and reflects fundamental classes.
* `TauCeti.IsFundamentalClass.singularHomologyToLocalHomology_ne_zero`: on an `n`-manifold with
  nontrivial coefficients, a fundamental class has a nonzero image in every local homology group.
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

section Coefficients

variable {M : Type w} [TopologicalSpace M] {R : Type u} [Ring R] {N N' : ModuleCat.{w} R} {n : ℕ}

/-- **Fundamental classes do not depend on the presentation of the coefficients.** Changing the
coefficients of `Hₙ(M; N)` along an isomorphism `N ≅ N'` carries fundamental classes to
fundamental classes, and only them. -/
@[simp]
theorem isFundamentalClass_singularHomologyFunctor_map_app_iff (e : N ≅ N')
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) n).map e.hom).app
          (TopCat.of M) μ) ↔ IsFundamentalClass μ := by
  refine ((isFundamentalClass_iff _).trans (forall_congr' fun x ↦ ?_)).trans
    (isFundamentalClass_iff μ).symm
  -- At each point the coefficient change acts on the local homology by an isomorphism `L`, and
  -- the map to local homology intertwines it with the coefficient change on `Hₙ(M)`.
  let P := TopPair.toSSetPair.obj (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)))
  let L := asIso (HomologicalComplex.homologyMap
    (((SSetPair.chainComplexFunctor (ModuleCat.{w} R)).map e.hom).app P) n)
  have h := congrArg (fun φ ↦ φ.hom μ) (SSetPair.homologyπ_coefficient_naturality P e.hom n)
  have key : singularHomologyToLocalHomology N' x n
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} R) n).map e.hom).app
        (TopCat.of M) μ) = L.toLinearEquiv (singularHomologyToLocalHomology N x n μ) := by
    rw [singularHomologyFunctor_map_app_hom_apply,
      singularHomologyToLocalHomology_eq_singularHomologyπ,
      singularHomologyToLocalHomology_eq_singularHomologyπ]
    -- `TopPair.singularHomologyπ` is an abbreviation for `SSetPair.homologyπ` of `P`, and the
    -- composites in `h` are applied to `μ`, so `h` closes the goal as stated.
    exact h
  rw [key]
  exact L.toLinearEquiv.span_singleton_apply_eq_top_iff

end Coefficients

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
/-- **A fundamental class has nonzero local images** in the top degree `n` of an `n`-manifold with
nontrivial coefficients: the local homology `Hₙ(M, M ∖ {x}; N)` at a point is then a nontrivial
copy of the coefficients, which `0` does not generate. -/
theorem IsFundamentalClass.singularHomologyToLocalHomology_ne_zero [T1Space M] {R : Type u}
    [Ring R] {N : ModuleCat.{w} R} [Nontrivial N]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (x : M) : singularHomologyToLocalHomology N x n μ ≠ 0 := by
  subst hn
  have : Nontrivial (localHomology N ({x} : Set M) (finrank ℝ E) : ModuleCat.{w} R) :=
    (singularHomologyComplSingletonFinrankIso N (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv.toEquiv.nontrivial
  intro h
  have hx := (isFundamentalClass_iff μ).1 hμ x
  rw [h, Submodule.span_singleton_eq_bot.2 rfl] at hx
  exact bot_ne_top hx

include hn in
/-- **The zero class is not fundamental** in the top degree `n` of a nonempty `n`-manifold with
nontrivial coefficients: the local homology `Hₙ(M, M ∖ {x}; N)` at a point is then a nontrivial
copy of the coefficients, which `0 ∈ Hₙ(M; N)` does not generate. -/
theorem not_isFundamentalClass_zero [T1Space M] [Nonempty M] {R : Type u} [Ring R]
    (N : ModuleCat.{w} R) [Nontrivial N] :
    ¬ IsFundamentalClass (0 : ((TopCat.toSSet.obj (TopCat.of M)).homology N n :
      ModuleCat.{w} R)) := fun h ↦
  h.singularHomologyToLocalHomology_ne_zero hn (Classical.arbitrary M) (map_zero _)

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
  exact ⟨μ, fun x ↦ (hμ x).symm ▸ hg x,
    fun ν hν ↦ huniq ν fun x ↦ eq_of_span_localHomology_eq_top K hn (hν x) (hg x)⟩

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
