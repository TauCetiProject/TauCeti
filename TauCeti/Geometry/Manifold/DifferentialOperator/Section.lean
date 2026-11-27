/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.VectorBundle.Trivialization

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
sections by `s ↦ (x ↦ ϕ x (s x))` (`ContMDiffSection.mapLinearMap`) as an operator of order `0`;
this holds for `C^n` bundle maps acting on `C^n` sections over any nontrivially normed field.
Conversely, when `V` has finite rank, every operator of order `0` is of this form: it is pointwise,
with fibre maps `TauCeti.smoothSectionFiberMap`, and this family of fibre maps is smooth because it
sends smooth sections to smooth sections (`TauCeti.Manifold.contMDiff_hom_iff`). This is the tensor
characterization lemma, the algebraic description of bundle homomorphisms used for the zeroth-order
terms of differential operators.

## Main results

* `TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`: differential operators
  between sections are local.
* `TauCeti.tsupport_apply_subset_of_local`: local operators do not enlarge the closed supports of
  sections; in particular differential operators do not
  (`TauCeti.tsupport_differentialOperators_section_apply_subset`). Composites and sums of local
  operators are local (`TauCeti.apply_eq_zero_of_local_comp`, `TauCeti.apply_eq_zero_of_local_add`).
* `TauCeti.tsupport_smulCommutator_section_apply_subset`: commutators with multiplication by
  smooth functions preserve the property of not enlarging supports.
* `TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero`: a linear map between
  sections has order `r` exactly when it kills `I_x ^ (r + 1) Γ(V)` at every point `x`.
* `TauCeti.mapLinearMap_mem_differentialOperators_zero`: `C^n` bundle maps act on `C^n` sections
  as operators of order `0`.
* `TauCeti.mem_differentialOperators_zero_iff_exists_eq_mapLinearMap`: for `V` of finite rank, the
  operators of order `0` are exactly the actions of smooth bundle maps, whose fibre maps are
  unique (`ContMDiffSection.mapLinearMap_inj`).

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

/-! ### Bundle maps -/

section BundleMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle 𝕜 F' W]

/-- **Bundle maps are operators of order zero.** A `C^n` bundle map `ϕ`, acting on `C^n` sections
by `s ↦ (x ↦ ϕ x (s x))`, is linear over the `C^n` functions. -/
theorem mapLinearMap_mem_differentialOperators_zero (ϕ : ∀ x, V x →ₗ[𝕜] W x)
    (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) n
      (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace F' W))) :
    ContMDiffSection.mapLinearMap ϕ hϕ ∈
      differentialOperators 𝕜 C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ Cₛ^n⟮I; F', W⟯ 0 :=
  mem_differentialOperators_zero_iff.2 fun f s ↦ ContMDiffSection.mapLinearMap_smul_function _ _ f s

end BundleMap

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
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  {U : M → Type*} [TopologicalSpace (TotalSpace F'' U)]
  [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)] [∀ x, TopologicalSpace (U x)]
  [FiberBundle F'' U] [VectorBundle ℝ F'' U]

/-- **Differential operators between sections are local.** If `P : Γ(V) → Γ(W)` is a differential
operator of order `r` in Grothendieck's sense and `s` vanishes near `x`, then `(P s) x = 0`. -/
theorem differentialOperators_section_apply_eq_zero_of_eventuallyEq
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    {s : Cₛ^∞⟮I; F, V⟯} {x : M} (hs : ∀ᶠ y in 𝓝 x, s y = 0) : P s x = 0 :=
  apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top (apply_mem_smul_top_of_mem_pow_smul_top hP _
    (mem_smoothVanishingIdeal_pow_smul_top_of_eventuallyEq_zero hs (r + 1)))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- A local operator does not enlarge closed supports: if `(P s) x = 0` whenever `s` vanishes near
`x`, then the closed support of `P s` lies in that of `s`. -/
theorem tsupport_apply_subset_of_local {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (s : Cₛ^∞⟮I; F, V⟯) : (P s).tsupport ⊆ s.tsupport :=
  ((P s).tsupport_subset_iff s.isClosed_tsupport).2 fun _ hx ↦ hP s _ <|
    Filter.mem_of_superset (s.isClosed_tsupport.isOpen_compl.mem_nhds hx) fun _ hy ↦
      s.eq_zero_of_notMem_tsupport hy

/-- Differential operators between sections do not enlarge supports: the closed support of `P s`
lies in that of `s`. -/
theorem tsupport_differentialOperators_section_apply_subset
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    (s : Cₛ^∞⟮I; F, V⟯) : (P s).tsupport ⊆ s.tsupport :=
  tsupport_apply_subset_of_local
    (fun _ _ hs ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP hs) s

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- A composite of local operators is local: if `Q s` and `P s` vanish at `x` whenever `s`
vanishes near `x`, then so does `(Q ∘ₗ P) s`. -/
theorem apply_eq_zero_of_local_comp {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    {Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯}
    (hQ : ∀ (s : Cₛ^∞⟮I; F', W⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → Q s x = 0)
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) (hs : ∀ᶠ y in 𝓝 x, s y = 0) : (Q ∘ₗ P) s x = 0 :=
  hQ _ x (hs.eventually_nhds.mono fun y hy ↦ hP s y hy)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- A sum of local operators is local: if `P s` and `P' s` vanish at `x` whenever `s` vanishes
near `x`, then so does `(P + P') s`. -/
theorem apply_eq_zero_of_local_add {P P' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hP' : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P' s x = 0)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) (hs : ∀ᶠ y in 𝓝 x, s y = 0) : (P + P') s x = 0 := by
  simp [hP s x hs, hP' s x hs]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- If a linear map `Q : Γ(V) → Γ(W)` does not enlarge supports, neither does its commutator
`[Q, a]` with multiplication by a smooth function `a`. -/
theorem tsupport_smulCommutator_section_apply_subset
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} (hQ : ∀ s, (Q s).tsupport ⊆ s.tsupport)
    (a : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) : (smulCommutator ℝ a Q s).tsupport ⊆ s.tsupport := by
  refine (ContMDiffSection.tsupport_subset_iff s.isClosed_tsupport).2 fun x hx ↦ ?_
  have h₁ := (Q (a • s)).eq_zero_of_notMem_tsupport fun h ↦
    hx ((hQ _).trans (ContMDiffSection.tsupport_smul_function_subset_right a s) h)
  have h₂ := (Q s).eq_zero_of_notMem_tsupport fun h ↦ hx (hQ s h)
  simp [smulCommutator_apply_apply, h₁, h₂]

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

/-- **The tensor characterization lemma.** For a smooth bundle `V` of finite rank, a linear map
`P : Γ(V) → Γ(W)` between smooth sections is an operator of order `0`, that is linear over the
smooth functions, if and only if it is the action `s ↦ (x ↦ ϕ x (s x))` of a smooth bundle map
`ϕ`: a family of fibrewise linear maps `ϕ x : V x → W x` whose map of total spaces is smooth. -/
theorem mem_differentialOperators_zero_iff_exists_eq_mapLinearMap
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ F' W I]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0 ↔
      ∃ (ϕ : ∀ x, V x →ₗ[ℝ] W x) (hϕ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
        (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace F' W))),
        P = ContMDiffSection.mapLinearMap ϕ hϕ := by
  refine ⟨fun hP ↦ ?_, fun ⟨ϕ, hϕ, h⟩ ↦ h ▸ mapLinearMap_mem_differentialOperators_zero ϕ hϕ⟩
  -- `P` is linear over the smooth functions, hence pointwise, with fibre maps
  -- `smoothSectionFiberMap x P'`.
  let P' : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯ :=
    { toFun := P
      map_add' := P.map_add
      map_smul' := mem_differentialOperators_zero_iff.1 hP }
  let ϕ (x : M) : V x →ₗ[ℝ] W x := smoothSectionFiberMap x P'
  have hϕ (s : Cₛ^∞⟮I; F, V⟯) (x : M) : ϕ x (s x) = P s x := smoothSectionFiberMap_apply x P' s
  -- The fibres of `W` are topological vector spaces, as the model fibre `F'` is.
  have := VectorBundle.isTopologicalAddGroup ℝ F' W
  have := VectorBundle.continuousSMul ℝ F' W
  -- The same fibre maps as continuous linear maps, through the finite-dimensional model fibre.
  let A (x : M) : V x →L[ℝ] W x :=
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    LinearMap.toContinuousLinearMap (ϕ x ∘ₗ e.symm.toLinearMap) ∘L e.toContinuousLinearMap
  have hA (x : M) (v : V x) : A x v = ϕ x v :=
    congrArg (ϕ x) ((VectorBundle.continuousLinearEquivAt ℝ F V x).symm_apply_apply v)
  -- `A` sends smooth sections to smooth sections, so it is a smooth section of the hom bundle,
  -- and its map of total spaces is smooth.
  have hAs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F')) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) x (A x)) := by
    refine (Manifold.contMDiff_hom_iff A).2 fun s hs ↦ ?_
    convert (P ⟨s, hs⟩).contMDiff using 2 with x
    rw [hA, ← hϕ ⟨s, hs⟩ x, ContMDiffSection.coeFn_mk]
  have htot := (contMDiff_hom_bundle_iff A).1 hAs
  refine ⟨ϕ, htot.congr fun p ↦ by simp [hA], ?_⟩
  ext s x
  rw [ContMDiffSection.mapLinearMap_apply, hϕ]

end TauCeti
