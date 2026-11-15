/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Differential operators between sections of vector bundles

Let `V` and `W` be real vector bundles over a finite-dimensional Hausdorff smooth manifold `M`.
The smooth sections `Γ(V)` and `Γ(W)` are modules over `C^∞(M)`, so Grothendieck's algebraic
notion of a differential operator of order `r` (`TauCeti.differentialOperators`) applies to real
linear maps `P : Γ(V) → Γ(W)`. This file reads that notion pointwise through the ideals `I_x` of
smooth functions vanishing at `x`.

A differential operator of order `r` sends `I_x ^ (r + 1) Γ(V)` into `I_x Γ(W)`. A section that
vanishes near `x` lies in every `I_x ^ (r + 1) Γ(V)`, and a section in `I_x Γ(W)` vanishes at `x`,
so differential operators are local. For a finite-rank smooth bundle `W` the sections vanishing at
`x` are exactly `I_x Γ(W)`, and the algebraic criterion
`TauCeti.mem_differentialOperators_iff_forall_apply_mem_smul_top` shows that `P` has order `r`
exactly when `(P s) x = 0` for every `x` and every `s ∈ I_x ^ (r + 1) Γ(V)`. Neither fact needs
compactness, any assumption on `V`, or any assumption on the boundary of `M`.

Peetre's theorem (`TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Section`) supplies the
converse to locality: on a compact manifold every local operator has finite order.

The operators of order `0` are the maps linear over the smooth functions. Every smooth bundle map,
a family of fibrewise linear maps `ϕ x : V x → W x` whose map of total spaces is smooth, acts on
sections by `s ↦ (x ↦ ϕ x (s x))` (`ContMDiffSection.mapLinearMap`) as an operator of order `0`.
Conversely, when `V` has finite rank, every operator of order `0` is of this form: it is pointwise,
because a section vanishing at `x` lies in `I_x Γ(V)`, and the resulting family of fibre maps is
smooth because it sends smooth sections to smooth sections
(`TauCeti.Manifold.contMDiff_hom_iff`). This is the tensor characterization lemma, the algebraic
description of bundle homomorphisms used for the zeroth-order terms of differential operators.

The basic operators of order `1` are covariant derivatives: for a smooth covariant derivative `∇`
and a smooth vector field `X`, the operator `∇_X` (`CovariantDerivative.alongVectorField`)
satisfies the Leibniz rule `[∇_X, f] = M_{X f}`, so its commutator with every multiplication
operator has order `0`.

## Main results

* `TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`: differential operators
  between sections are local.
* `TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero`: a linear map between
  sections has order `r` exactly when it kills `I_x ^ (r + 1) Γ(V)` at every point `x`.
* `TauCeti.mapLinearMap_mem_differentialOperators_zero`: smooth bundle maps act on sections as
  operators of order `0`.
* `TauCeti.mem_differentialOperators_zero_iff_exists_eq_mapLinearMap`: for `V` of finite rank, the
  operators of order `0` are exactly the actions of smooth bundle maps, whose fibre maps are
  unique (`ContMDiffSection.mapLinearMap_inj`).
* `CovariantDerivative.smulCommutator_alongVectorField`,
  `CovariantDerivative.alongVectorField_mem_differentialOperators_one`: the Leibniz rule
  `[∇_X, f] = M_{X f}`, and `∇_X` has order at most one.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (linear differential operators between vector bundles).
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-- **Differential operators between sections are local.** If `P : Γ(V) → Γ(W)` is a differential
operator of order `r` in Grothendieck's sense and `s` vanishes near `x`, then `(P s) x = 0`. -/
theorem differentialOperators_section_apply_eq_zero_of_eventuallyEq
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    {s : Cₛ^∞⟮I; F, V⟯} {x : M} (hs : ∀ᶠ y in 𝓝 x, s y = 0) : P s x = 0 :=
  apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top (apply_mem_smul_top_of_mem_pow_smul_top hP _
    (mem_smoothVanishingIdeal_pow_smul_top_of_eventuallyEq_zero hs (r + 1)))

/-- **Differential operators between sections, pointwise.** For a smooth real vector bundle `W` of
finite rank, a linear map `P : Γ(V) → Γ(W)` is a differential operator of order `r` in
Grothendieck's sense if and only if `(P s) x = 0` for every point `x` and every
`s ∈ I_x ^ (r + 1) Γ(V)`. -/
theorem mem_differentialOperators_section_iff_forall_apply_eq_zero
    [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r ↔
      ∀ x, ∀ s ∈ smoothVanishingIdeal I x ^ (r + 1) •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), P s x = 0 := by
  rw [mem_differentialOperators_iff_forall_apply_mem_smul_top
    (fun x : M ↦ (ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ))
    ContMDiffSection.eq_zero_of_forall_mem_ker_evalAlgHom_smul_top]
  simp only [ker_evalAlgHom_eq_smoothVanishingIdeal, mem_smoothVanishingIdeal_smul_top_iff]

/-! ### Operators of order zero -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- **Bundle maps are operators of order zero.** A smooth bundle map `ϕ`, acting on sections by
`s ↦ (x ↦ ϕ x (s x))`, is linear over the smooth functions. -/
theorem mapLinearMap_mem_differentialOperators_zero (ϕ : ∀ x, V x →ₗ[ℝ] W x)
    (hϕ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
      (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace F' W))) :
    ContMDiffSection.mapLinearMap ϕ hϕ ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0 :=
  mem_differentialOperators_zero_iff.2 fun f s ↦ ContMDiffSection.mapLinearMap_smul_function _ _ f s

/-- **The tensor characterization lemma.** For a smooth bundle `V` of finite rank, a linear map
`P : Γ(V) → Γ(W)` between smooth sections is an operator of order `0`, that is linear over the
smooth functions, if and only if it is the action `s ↦ (x ↦ ϕ x (s x))` of a smooth bundle map
`ϕ`: a family of fibrewise linear maps `ϕ x : V x → W x` whose map of total spaces is smooth. -/
theorem mem_differentialOperators_zero_iff_exists_eq_mapLinearMap
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [ContMDiffVectorBundle ∞ F' W I] {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0 ↔
      ∃ (ϕ : ∀ x, V x →ₗ[ℝ] W x) (hϕ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
        (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace F' W))),
        P = ContMDiffSection.mapLinearMap ϕ hϕ := by
  refine ⟨fun hP ↦ ?_, fun ⟨ϕ, hϕ, h⟩ ↦ h ▸ mapLinearMap_mem_differentialOperators_zero ϕ hϕ⟩
  -- `P` is linear over the smooth functions, hence pointwise: it maps `I_x Γ(V)`, the sections
  -- vanishing at `x`, into `I_x Γ(W)`.
  let P' : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯ :=
    { toFun := P
      map_add' := P.map_add
      map_smul' := mem_differentialOperators_zero_iff.1 hP }
  have hpt {x : M} {s : Cₛ^∞⟮I; F, V⟯} (hs : s x = 0) : P s x = 0 :=
    apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top <| Submodule.smul_top_le_comap_smul_top _ P'
      (mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero hs)
  -- The fibre map at `x` evaluates `P` on any section through the given vector.
  choose lift hlift using fun x : M ↦
    (ContMDiffSection.evalLinearMap I F ∞ V x).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (ContMDiffSection.evalLinearMap_surjective ∞ x))
  have hlift' (x : M) (v : V x) : lift x v x = v := by
    simpa using congr($(hlift x) v)
  let ϕ (x : M) : V x →ₗ[ℝ] W x := ContMDiffSection.evalLinearMap I F' ∞ W x ∘ₗ P ∘ₗ lift x
  have hϕ (s : Cₛ^∞⟮I; F, V⟯) (x : M) : ϕ x (s x) = P s x := by
    have h := hpt (x := x) (s := lift x (s x) - s) (by simp [hlift'])
    rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h
    simpa [ϕ] using h
  -- The same fibre maps as continuous linear maps, through the finite-dimensional model fibre.
  let A (x : M) : V x →L[ℝ] W x :=
    let e := (trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    LinearMap.toContinuousLinearMap (ϕ x ∘ₗ e.symm.toLinearMap) ∘L e.toContinuousLinearMap
  have hA (x : M) (v : V x) : A x v = ϕ x v := by
    simp [A, (trivializationAt F V x).symm_apply_apply_mk
      (FiberBundle.mem_baseSet_trivializationAt' x)]
  -- `A` sends smooth sections to smooth sections, so it is a smooth section of the hom bundle,
  -- and its map of total spaces is smooth.
  have hAs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F')) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) x (A x)) := by
    refine (Manifold.contMDiff_hom_iff A).2 fun s hs ↦ ?_
    convert (P ⟨s, hs⟩).contMDiff using 2 with x
    rw [hA, ← hϕ ⟨s, hs⟩ x]
    rfl
  have htot := (contMDiff_hom_bundle_iff A).1 hAs
  refine ⟨ϕ, htot.congr fun p ↦ by simp [hA], ?_⟩
  ext s x
  rw [ContMDiffSection.mapLinearMap_apply, hϕ]

end TauCeti

/-! ### Covariant derivatives -/

namespace CovariantDerivative

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- **The Leibniz rule.** The commutator of the covariant derivative `∇_X` along a smooth vector
field with multiplication by a smooth function `f` is multiplication by the derivative `X f` of `f`
along `X`: `∇_X (f s) - f ∇_X s = (X f) s`. -/
theorem smulCommutator_alongVectorField (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    smulCommutator ℝ f (cov.alongVectorField X) s = vectorFieldDerivation X f • s := by
  ext y
  have hfs : ⇑(f • s) = (⇑f) • ⇑s := funext fun z ↦ ContMDiffSection.smul_apply ..
  rw [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply, alongVectorField_apply,
    hfs, cov.covariantDerivative_smul_section_apply
      (f.contMDiff.mdifferentiable (by simp) y) (s.mdifferentiableAt (x := y)),
    ContMDiffSection.smul_apply, alongVectorField_apply, ContMDiffSection.smul_apply,
    ContMDiffSection.vectorFieldDerivation_apply_apply]
  abel

/-- The covariant derivative along a smooth vector field is a differential operator of order at
most one. -/
theorem alongVectorField_mem_differentialOperators_one
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    cov.alongVectorField X ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_zero_iff.2
    fun g s ↦ ?_
  rw [smulCommutator_alongVectorField, smulCommutator_alongVectorField, smul_comm]

end CovariantDerivative
