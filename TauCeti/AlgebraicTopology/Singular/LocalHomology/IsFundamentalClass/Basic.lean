/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology
import TauCeti.Geometry.Manifold.ModelTransport.Finrank

/-!
# Fundamental classes with coefficients in a ring

This module defines `TauCeti.IsFundamentalClass` — a homology class `μ ∈ Hₙ(M; N)` whose image
under `TauCeti.singularHomologyToLocalHomology` generates the local homology `Hₙ(M, M ∖ {x}; N)`
at every point `x ∈ M` — together with its basic invariance properties under unit scaling,
coefficient isomorphisms, and homeomorphisms, and the normalized rank-one equivalence
`TauCeti.IsFundamentalClass.linearEquivOfLinearEquiv` (and `TauCeti.IsFundamentalClass.linearEquiv`)
on compact connected manifolds.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe w v u

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

end Manifold

section RankOne

variable {M : Type w} {E : Type v} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

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
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  obtain ⟨x⟩ : Nonempty M := ConnectedSpace.toNonempty
  have hsurj : Function.Surjective (singularHomologyToLocalHomology R x n) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (isFundamentalClass_iff μ).1 hμ x,
      Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_range_self _ μ
  let eL := localHomologySingletonLinearEquiv R hE' eR x
  refine ⟨(LinearEquiv.ofBijective _
    ⟨singularHomologyToLocalHomology_injective R hE' x, hsurj⟩).trans eL, ?_⟩
  -- The image of `μ` generates the local homology, so its coordinate is a unit.
  exact eL.span_singleton_eq_top_iff_isUnit.1 ((isFundamentalClass_iff μ).1 hμ x)

/-- **Normalized rank-one equivalence from a fundamental class.** On a compact connected
`n`-manifold, with coefficients `eR : R ≃ₗ[k] k` over a Dedekind-finite ring `k`, a fundamental
class `μ ∈ Hₙ(M; R)` determines the `k`-linear equivalence `k ≃ₗ[k] Hₙ(M; R)` sending
`r ↦ r • μ`. -/
def IsFundamentalClass.linearEquivOfLinearEquiv [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k} (eR : R ≃ₗ[k] k)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) :
    k ≃ₗ[k] ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k) :=
  let h := hμ.exists_linearEquiv_isUnit hn eR
  let u := h.choose_spec.unit
  { toFun := fun r ↦ h.choose.symm (r * (u : k))
    invFun := fun γ ↦ h.choose γ * (↑u⁻¹ : k)
    left_inv := fun r ↦ by
      simp only [LinearEquiv.apply_symm_apply, mul_assoc, Units.mul_inv, mul_one]
    right_inv := fun γ ↦ h.choose.injective <| by
      simp only [LinearEquiv.apply_symm_apply, mul_assoc, Units.inv_mul, mul_one]
    map_add' := fun r s ↦ by simp [add_mul]
    map_smul' := fun c r ↦ by
      simp only [RingHom.id_apply, smul_eq_mul, mul_assoc]
      exact map_smul h.choose.symm c (r * (u : k)) }

@[simp]
theorem IsFundamentalClass.linearEquivOfLinearEquiv_apply [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k}
    (eR : R ≃ₗ[k] k) {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) (r : k) :
    hμ.linearEquivOfLinearEquiv hn eR r = r • μ := by
  simp only [linearEquivOfLinearEquiv, LinearEquiv.coe_mk, IsUnit.unit_spec, ← smul_eq_mul,
    map_smul, LinearEquiv.symm_apply_apply]
  rfl

/-- **Normalized rank-one equivalence from a fundamental class** for ring coefficients `R`. -/
def IsFundamentalClass.linearEquiv [T2Space M] [CompactSpace M] [ConnectedSpace M] {R : Type w}
    [Ring R] [IsDedekindFiniteMonoid R]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) :
    R ≃ₗ[R] ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R) :=
  hμ.linearEquivOfLinearEquiv hn (LinearEquiv.refl R R)

@[simp]
theorem IsFundamentalClass.linearEquiv_apply [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {R : Type w} [Ring R] [IsDedekindFiniteMonoid R]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (r : R) :
    hμ.linearEquiv hn r = r • μ :=
  hμ.linearEquivOfLinearEquiv_apply hn (LinearEquiv.refl R R) r

end RankOne

end TauCeti
