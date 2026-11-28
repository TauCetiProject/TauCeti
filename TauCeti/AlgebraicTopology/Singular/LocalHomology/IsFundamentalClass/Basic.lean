/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

/-!
# Fundamental classes with coefficients in a ring

This module defines `TauCeti.IsFundamentalClass` — a homology class `μ ∈ Hₙ(M; N)` whose image
under `TauCeti.singularHomologyToLocalHomology` generates the local homology `Hₙ(M, M ∖ {x}; N)`
at every point `x ∈ M` — together with its basic invariance properties under unit scaling,
coefficient isomorphisms, and homeomorphisms.

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

/-- A class with a fundamental multiple is fundamental: the image of `r • μ` in each local
homology module is a multiple of that of `μ`. -/
theorem IsFundamentalClass.of_smul {r : R}
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (h : IsFundamentalClass (r • μ)) : IsFundamentalClass μ :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    have hx := (isFundamentalClass_iff _).1 h x
    rw [map_smul] at hx
    exact eq_top_iff.2 (hx.symm.le.trans (Submodule.span_le.2 (Set.singleton_subset_iff.2
      (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)))))

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

end TauCeti
