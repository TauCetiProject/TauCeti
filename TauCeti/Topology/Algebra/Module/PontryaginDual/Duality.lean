/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.Topology.Algebra.Module.Compact
public import TauCeti.Topology.Algebra.Module.PontryaginDual.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Compact–discrete Pontryagin duality for modules over a compact local ring

Let `R` be a compact, totally disconnected commutative local topological ring and let `E` be a
discrete injective `R`-module with continuous scalar action such that `Hom_R(R ⧸ 𝔪, E)` has length
one for every maximal ideal `𝔪` of `R` (for instance `R = 𝒪[L]` and `E = L ⧸ 𝒪[L]` for a
nonarchimedean local field `L`).

Under these hypotheses the single functor `TauCeti.ModulePontryaginDual R E` gives an exact
contravariant equivalence between:

* discrete `R`-modules with continuous `R`-action (meaning every element has open annihilator), and
* compact modules over `R` in the sense of `TauCeti.IsCompactModule R`.

Over any compact totally disconnected local ring `R`, the maximal ideal is open, so the residue
field is finite and finite-length `R`-modules are precisely finite `R`-modules. For discrete `M`
with continuous `R`-action, each element `m : M` has open annihilator `Iₘ`, so
`E[Iₘ] ≃ Hom_R(R ⧸ Iₘ, E)` is finite and `M^∨` embeds as a closed subspace of the profinite
product `∏ m, E[Iₘ]`. Biduality on both sides follows by reducing to finite-length modules via
`TauCeti.bijective_applyₗ_of_forall_isMaximal` and the inverse-limit property
`TauCeti.IsCompactModule.existsUnique_forall_mkQ_eq`.

## Main results

* `TauCeti.isFiniteLength_iff_finite`: over a compact totally disconnected commutative local ring,
  a module has finite length iff it is finite.
* `TauCeti.ModulePontryaginDual.isCompactModule_of_discrete`: the dual of a discrete module with
  continuous `R`-action is a compact `R`-module.
* `TauCeti.ModulePontryaginDual.exact_map_of_discrete` and
  `TauCeti.ModulePontryaginDual.exact_map_of_compact`: the dual functor is exact on both sides.
* `TauCeti.ModulePontryaginDual.evalEquivOfDiscrete` and
  `TauCeti.ModulePontryaginDual.evalEquivOfCompact`: canonical biduality `M ≃L[R] (M^∨)^∨`.
* `TauCeti.ModulePontryaginDual.bijective_map_of_discrete` and
  `TauCeti.ModulePontryaginDual.bijective_map_of_compact`: full faithfulness on continuous linear
  maps.
* `TauCeti.ModulePontryaginDual.iSup_range_map_mkQL_eq_top`,
  `TauCeti.ModulePontryaginDual.quotKerMapSubtypeEquiv`, and
  `TauCeti.ModulePontryaginDual.existsUnique_forall_restrict_fg_eq`: colimit compatibility over
  open quotients and inverse-limit compatibility over finitely generated submodules.

## References

* A. Brumer, *Pseudocompact algebras, profinite groups and class formations*, J. Algebra 4 (1966),
  §1.
* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

universe u v w w'

section FiniteLength

/-- Every finite module over any ring has finite length. -/
theorem _root_.IsFiniteLength.of_finite {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Finite M] : IsFiniteLength R M := by
  have : Finite (Submodule R M) := Finite.of_injective (fun N : Submodule R M ↦ (N : Set M))
    SetLike.coe_injective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The quotient of a compact topological module by an open submodule is finite. -/
theorem finite_quotient_of_isOpen {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [SeparatelyContinuousAdd M] [CompactSpace M]
    (U : Submodule R M) (hU : IsOpen (U : Set M)) : Finite (M ⧸ U) := by
  have : DiscreteTopology (M ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hU
  have : CompactSpace (M ⧸ U) := ⟨by
    rw [← Set.image_univ_of_surjective U.mkQ_surjective]
    exact isCompact_univ.image U.continuous_mkQ⟩
  exact finite_of_compact_of_discrete

/-- In a compact totally disconnected commutative local topological ring, the maximal ideal is
open. -/
theorem isOpen_maximalIdeal_of_compact {R : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] :
    IsOpen (IsLocalRing.maximalIdeal R : Set R) := by
  have hR : IsCompactModule R R := IsCompactModule.self
  have hnot : ¬ ∀ I : Ideal R, IsOpen (I : Set R) → (1 : R) ∈ I := fun h ↦
    one_ne_zero (hR.eq_zero_of_forall_mem_of_isOpen h)
  push Not at hnot
  obtain ⟨I, hIopen, h1⟩ := hnot
  have hIle : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal fun htop ↦ h1 (htop ▸ Submodule.mem_top)
  exact (IsLocalRing.maximalIdeal R).toAddSubgroup.isOpen_of_mem_nhds
    (mem_of_superset (hIopen.mem_nhds I.zero_mem) hIle)

/-- Over a compact totally disconnected commutative local topological ring, every module of finite
length is finite. -/
theorem finite_of_isFiniteLength {R M : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) : Finite M := by
  have hres : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    finite_quotient_of_isOpen (IsLocalRing.maximalIdeal R) isOpen_maximalIdeal_of_compact
  induction hM with
  | of_subsingleton => infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal h𝔪] at e
    have hsub : Finite N.toAddSubgroup := ih
    have hquot : Finite (M ⧸ N.toAddSubgroup) := Finite.of_equiv _ e.symm.toEquiv
    exact Finite.of_addSubgroup_quotient N.toAddSubgroup

/-- Over a compact totally disconnected commutative local topological ring, a module has finite
length if and only if it is finite. -/
theorem isFiniteLength_iff_finite {R M : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R]
    [AddCommGroup M] [Module R M] : IsFiniteLength R M ↔ Finite M :=
  ⟨finite_of_isFiniteLength, fun _ ↦ IsFiniteLength.of_finite⟩

/-- For a discrete module `M` with continuous `R`-action, the annihilator of each element is an
open ideal of `R`. -/
theorem isOpen_annihilator_elem {R M : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul R M] (m : M) :
    IsOpen (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R) := by
  have hcont : Continuous (fun r : R ↦ r • m) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  convert (isOpen_discrete {(0 : M)}).preimage hcont using 1
  ext r
  simp [LinearMap.mem_ker]

/-- Over a compact ring with separately continuous addition, every finitely generated submodule of
a discrete module with continuous scalar action is finite. -/
theorem finite_of_fg_of_discrete {R M : Type*} [CommRing R] [TopologicalSpace R]
    [SeparatelyContinuousAdd R] [CompactSpace R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M]
    {M₀ : Submodule R M} (hM₀ : M₀.FG) : Finite M₀ := by
  obtain ⟨s, hs⟩ := hM₀
  let I : Ideal R := ⨅ m ∈ s, LinearMap.ker (LinearMap.toSpanSingleton R M m)
  have hIopen : IsOpen (I : Set R) := by
    have : (I : Set R) = ⋂ m ∈ s, (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R) := by
      ext r; simp [I]
    rw [this]
    exact isOpen_biInter_finset fun m _ ↦ isOpen_annihilator_elem m
  have hRI : Finite (R ⧸ I) := finite_quotient_of_isOpen I hIopen
  let f : (s → (R ⧸ I)) → M₀ := fun c ↦
    ⟨∑ m : s, Quotient.liftOn' (c m) (fun r ↦ r • (m : M)) (fun r₁ r₂ h ↦ by
      have hmem : r₁ - r₂ ∈ I := (Submodule.quotientRel_def I).mp h
      have hm : r₁ - r₂ ∈ LinearMap.ker (LinearMap.toSpanSingleton R M m.1) := by
        simp only [I, Submodule.mem_iInf] at hmem
        exact hmem m.1 m.2
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, sub_eq_zero] at hm
      exact hm),
      Submodule.sum_mem M₀ fun m _ ↦ by
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (c m)
        rw [← hr]
        exact M₀.smul_mem r (hs ▸ Submodule.subset_span m.2)⟩
  refine Finite.of_surjective f fun ⟨x, hx⟩ ↦ ?_
  rw [← hs, Submodule.mem_span_finset] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨fun m ↦ Ideal.Quotient.mk I (c m), Subtype.ext ?_⟩
  change ∑ m ∈ s.attach, c m.1 • (m.1 : M) = x
  rw [Finset.sum_attach s (fun a ↦ c a • a)]
  exact hc.2

end FiniteLength

namespace ModulePontryaginDual

section General

variable {R : Type u} {E : Type v}
  [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E]

omit [IsTopologicalAddGroup E] [ContinuousConstSMul R E] in
/-- When `E` is discrete, the kernel of every element of `ModulePontryaginDual R E M` is an open
submodule of `M`. -/
theorem isOpen_ker [DiscreteTopology E] {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] (φ : ModulePontryaginDual R E M) :
    IsOpen (LinearMap.ker φ.toContinuousLinearMap.toLinearMap : Set M) := by
  convert (isOpen_discrete {(0 : E)}).preimage (map_continuous φ) using 1
  ext x
  simp [LinearMap.mem_ker]

/-- A surjective continuous linear map induces an injective dual map. -/
theorem map_injective_of_surjective {M N : Type*} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
    {f : M →L[R] N} (hf : Function.Surjective f) :
    Function.Injective (map (E := E) f) := by
  intro ψ₁ ψ₂ h
  refine ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_apply] using DFunLike.congr_fun h x

/-- An injective continuous linear map into a discrete module induces a surjective dual map when `E`
is injective. -/
theorem map_surjective_of_injective_of_discrete [Module.Injective R E] [Small.{v} R] {M N : Type*}
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
    {f : M →L[R] N} (hf : Function.Injective f) :
    Function.Surjective (map (E := E) f) := by
  intro φ
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R E M N f.toLinearMap hf
    φ.toContinuousLinearMap.toLinearMap
  refine ⟨⟨⟨g, continuous_of_discreteTopology⟩⟩, ext fun x ↦ ?_⟩
  simpa [map_apply] using LinearMap.congr_fun hg x

/-- Exactness of `ModulePontryaginDual R E` on continuous linear maps ending in a discrete module
when `E` is injective. -/
theorem exact_map_of_discrete [Module.Injective R E] [Small.{v} R] {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [DiscreteTopology M₃]
    {f : M₁ →L[R] M₂} {g : M₂ →L[R] M₃}
    (hex : Function.Exact f.toLinearMap g.toLinearMap) :
    Function.Exact (map (E := E) g).toLinearMap (map (E := E) f).toLinearMap := by
  rw [LinearMap.exact_iff]
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨fun hφ ↦ ?_, ?_⟩
  · have hle : LinearMap.ker g.toLinearMap ≤ LinearMap.ker φ.toContinuousLinearMap.toLinearMap := by
      rw [LinearMap.exact_iff.mp hex]
      rintro _ ⟨x, rfl⟩
      simpa [LinearMap.mem_ker, map_apply] using DFunLike.congr_fun hφ x
    let ψ₀ : LinearMap.range g.toLinearMap →ₗ[R] E :=
      (LinearMap.ker g.toLinearMap).liftQ φ.toContinuousLinearMap.toLinearMap hle ∘ₗ
        (LinearMap.quotKerEquivRange g.toLinearMap).symm.toLinearMap
    obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property R E _ M₃
      (LinearMap.range g.toLinearMap).subtype (Submodule.subtype_injective _) ψ₀
    refine ⟨⟨⟨ψ, continuous_of_discreteTopology⟩⟩, ext fun x ↦ ?_⟩
    have hx := LinearMap.congr_fun hψ ⟨g.toLinearMap x, ⟨x, rfl⟩⟩
    have hq : g.toLinearMap.quotKerEquivRange.symm ⟨g.toLinearMap x, ⟨x, rfl⟩⟩ =
        Submodule.Quotient.mk x := g.toLinearMap.quotKerEquivRange.injective (by
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext rfl)
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, ψ₀, LinearEquiv.coe_coe] at hx
    rw [hq] at hx
    simpa [map_apply] using hx
  · rintro ⟨ψ, rfl⟩
    refine ext fun x ↦ ?_
    have hgf : g (f x) = 0 := hex.apply_apply_eq_zero x
    simp [map_apply, hgf]

/-- For an open submodule `U` of `N`, the range of `map U.mkQL` consists precisely of the
continuous functionals vanishing on `U`. -/
theorem range_map_mkQL_of_isOpen {N : Type w} [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    (U : Submodule R N) (hU : IsOpen (U : Set N)) (φ : ModulePontryaginDual R E N) :
    φ ∈ LinearMap.range (map (E := E) U.mkQL).toLinearMap ↔
      U ≤ LinearMap.ker φ.toContinuousLinearMap.toLinearMap := by
  have : DiscreteTopology (N ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hU
  refine ⟨?_, fun hle ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩ x hx
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, toContinuousLinearMap_apply,
      map_apply, Submodule.mkQL_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero U).mpr hx, map_zero]
  · refine ⟨⟨⟨U.liftQ φ.toContinuousLinearMap.toLinearMap hle, continuous_of_discreteTopology⟩⟩,
      ext fun x ↦ ?_⟩
    simp [map_apply]

/-- **Colimit compatibility over open quotients**: when `E` is discrete, every element of `N^∨`
lies in the image of `(N ⧸ U)^∨` for some open submodule `U` of `N`. -/
theorem iSup_range_map_mkQL_eq_top [DiscreteTopology E] {N : Type w} [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] :
    ⨆ U : {U : Submodule R N // IsOpen (U : Set N)},
      LinearMap.range (map (E := E) U.1.mkQL).toLinearMap = ⊤ := by
  refine eq_top_iff.mpr fun φ _ ↦ ?_
  let U : {U : Submodule R N // IsOpen (U : Set N)} :=
    ⟨LinearMap.ker φ.toContinuousLinearMap.toLinearMap, isOpen_ker φ⟩
  exact Submodule.mem_iSup_of_mem U ((range_map_mkQL_of_isOpen U.1 U.2 φ).mpr le_rfl)

/-- **Inverse-limit compatibility over finitely generated submodules**: a compatible family of
elements in `K^∨` for finitely generated submodules `K` of a discrete module `M` comes from a
unique element of `M^∨`. -/
theorem existsUnique_forall_restrict_fg_eq {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M]
    (φ : ∀ K : {K : Submodule R M // K.FG}, ModulePontryaginDual R E K.1)
    (hφ : ∀ ⦃K K' : {K : Submodule R M // K.FG}⦄ (h : K.1 ≤ K'.1) (x : K.1),
      φ K' ⟨x.1, h x.2⟩ = φ K x) :
    ∃! ψ : ModulePontryaginDual R E M, ∀ K, map (E := E) K.1.subtypeL ψ = φ K := by
  let Kx : M → {K : Submodule R M // K.FG} := fun x ↦
    ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
  have hwell : ∀ (K : {K : Submodule R M // K.FG}) (x : M) (hx : x ∈ K.1),
      φ K ⟨x, hx⟩ = φ (Kx x) ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩ := fun K x hx ↦
    hφ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx))
      ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩
  let f : M →ₗ[R] E := {
    toFun := fun x ↦ φ (Kx x) ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩
    map_add' := fun x y ↦ by
      let K : {K : Submodule R M // K.FG} :=
        ⟨Submodule.span R {x, y}, Submodule.fg_span (Set.toFinite _)⟩
      have hx : x ∈ K.1 := Submodule.subset_span (by simp)
      have hy : y ∈ K.1 := Submodule.subset_span (by simp)
      rw [← hwell K (x + y) (K.1.add_mem hx hy), ← hwell K x hx, ← hwell K y hy, ← map_add]
      rfl
    map_smul' := fun r x ↦ by
      have hx : x ∈ (Kx x).1 := Submodule.subset_span (Set.mem_singleton x)
      rw [← hwell (Kx x) (r • x) ((Kx x).1.smul_mem r hx), RingHom.id_apply, ← map_smul]
      rfl }
  refine ⟨(equivLinearMap R E M).symm f, fun K ↦ ext fun x ↦ ?_, fun ψ' hψ' ↦ ext fun x ↦ ?_⟩
  · simp only [map_apply, Submodule.subtypeL_apply, equivLinearMap_symm_apply, f, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (hwell K x.1 x.2).symm
  · have h := DFunLike.congr_fun (hψ' (Kx x)) ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩
    simpa [f, map_apply] using h

/-- A discrete module is subsingleton iff its Pontryagin dual is subsingleton. -/
theorem subsingleton_iff_of_discrete [Module.Injective R E] [Small.{v} R]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] :
    Subsingleton (ModulePontryaginDual R E M) ↔ Subsingleton M := by
  refine ⟨fun h ↦ ⟨fun x y ↦ ?_⟩, fun _ ↦ ⟨fun φ ψ ↦ ext fun x ↦ by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  refine injective_applyₗ_of_forall_isMaximal hE ?_
  ext f
  have h0 := Subsingleton.elim ((equivLinearMap R E M).symm f) 0
  have hx := DFunLike.congr_fun h0 x
  have hy := DFunLike.congr_fun h0 y
  simp only [LinearMap.applyₗ_apply_apply, equivLinearMap_symm_apply, zero_apply] at hx hy ⊢
  rw [hx, hy]

end General

section CompactExact

variable {R : Type u} {E : Type v}
  [CommRing R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul R E] [Module.Injective R E] [Small.{v} R]

/-- An injective continuous linear map between compact `R`-modules induces a surjective dual map. -/
theorem map_surjective_of_injective_of_compact {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂)
    {f : N₁ →L[R] N₂} (hf : Function.Injective f) :
    Function.Surjective (map (E := E) f) := by
  have := hN₁.compactSpace
  have := hN₂.t2Space
  have := hN₂.isTopologicalAddGroup
  have := hN₂.isLinearTopology
  intro φ
  let K : Submodule R N₁ := LinearMap.ker φ.toContinuousLinearMap.toLinearMap
  have hKopen : IsOpen (K : Set N₁) := isOpen_ker φ
  have hfK : IsClosed (f '' (K : Set N₁)ᶜ) :=
    (hKopen.isClosed_compl.isCompact.image f.continuous).isClosed
  have h0 : (0 : N₂) ∈ (f '' (K : Set N₁)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hf (hfx.trans (map_zero f).symm) ▸ K.zero_mem)
  obtain ⟨U, hUopen, hUsub⟩ := (IsLinearTopology.hasBasis_open_submodule R (M := N₂)).mem_iff.mp
    (hfK.isOpen_compl.mem_nhds h0)
  have hcomap : U.comap f.toLinearMap ≤ K := by
    intro x hx
    by_contra hxK
    exact hUsub hx ⟨x, hxK, rfl⟩
  let fbar : (N₁ ⧸ U.comap f.toLinearMap) →ₗ[R] (N₂ ⧸ U) :=
    Submodule.mapQ (U.comap f.toLinearMap) U f.toLinearMap le_rfl
  have hfbar : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    simp only [Submodule.mkQ_apply, LinearMap.mem_ker, fbar, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hq
  let φbar : (N₁ ⧸ U.comap f.toLinearMap) →ₗ[R] E :=
    (U.comap f.toLinearMap).liftQ φ.toContinuousLinearMap.toLinearMap hcomap
  obtain ⟨ψbar, hψbar⟩ := Module.Injective.extension_property R E _ _ fbar hfbar φbar
  have : DiscreteTopology (N₂ ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hUopen
  refine ⟨map (E := E) U.mkQL ⟨⟨ψbar, continuous_of_discreteTopology⟩⟩, ext fun x ↦ ?_⟩
  have hx := LinearMap.congr_fun hψbar (Submodule.Quotient.mk x)
  simpa [fbar, φbar, map_apply] using hx

/-- Exactness of `ModulePontryaginDual R E` on compact `R`-modules. -/
theorem exact_map_of_compact {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂]
    [AddCommGroup N₃] [Module R N₃] [TopologicalSpace N₃]
    (hN₂ : IsCompactModule R N₂) (hN₃ : IsCompactModule R N₃)
    {f : N₁ →L[R] N₂} {g : N₂ →L[R] N₃}
    (hex : Function.Exact f.toLinearMap g.toLinearMap) :
    Function.Exact (map (E := E) g).toLinearMap (map (E := E) f).toLinearMap := by
  have := hN₂.compactSpace
  have := hN₃.t2Space
  have := hN₃.isTopologicalAddGroup
  have := hN₃.continuousSMul
  have := hN₃.totallyDisconnectedSpace
  rw [LinearMap.exact_iff]
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨fun hφ ↦ ?_, ?_⟩
  · have hle : LinearMap.ker g.toLinearMap ≤ LinearMap.ker φ.toContinuousLinearMap.toLinearMap := by
      rw [LinearMap.exact_iff.mp hex]
      rintro _ ⟨x, rfl⟩
      simpa [LinearMap.mem_ker, map_apply] using DFunLike.congr_fun hφ x
    let K : Submodule R N₃ := LinearMap.range g.toLinearMap
    let ψ₀ : K →ₗ[R] E :=
      (LinearMap.ker g.toLinearMap).liftQ φ.toContinuousLinearMap.toLinearMap hle ∘ₗ
        (LinearMap.quotKerEquivRange g.toLinearMap).symm.toLinearMap
    let g' : N₂ → K := fun x ↦ ⟨g.toLinearMap x, ⟨x, rfl⟩⟩
    have hg'_cont : Continuous g' := g.continuous.subtype_mk _
    have hg'_surj : Function.Surjective g' := fun ⟨_, x, rfl⟩ ↦ ⟨x, rfl⟩
    have hψ₀_apply : ∀ x : N₂, ψ₀ ⟨g.toLinearMap x, ⟨x, rfl⟩⟩ = φ x := fun x ↦ by
      have hq : g.toLinearMap.quotKerEquivRange.symm ⟨g.toLinearMap x, ⟨x, rfl⟩⟩ =
          Submodule.Quotient.mk x := g.toLinearMap.quotKerEquivRange.injective (by
        rw [LinearEquiv.apply_symm_apply]
        exact Subtype.ext rfl)
      simp only [ψ₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hq]
      rfl
    have hψ₀_cont : Continuous ψ₀ := by
      refine (hg'_cont.isClosedMap.isQuotientMap hg'_cont hg'_surj).continuous_iff.mpr ?_
      have heq : (ψ₀ ∘ g') = φ := funext hψ₀_apply
      rw [heq]
      exact map_continuous φ
    have hKcompact : CompactSpace K :=
      ⟨by
        rw [← Set.image_univ_of_surjective hg'_surj]
        exact isCompact_univ.image hg'_cont⟩
    have hKmod : IsCompactModule R K :=
      ⟨inferInstance, inferInstance, hKcompact, inferInstance⟩
    obtain ⟨ψ, hψ⟩ := map_surjective_of_injective_of_compact (E := E) hKmod hN₃
      (f := K.subtypeL) (Submodule.subtype_injective K) ⟨⟨ψ₀, hψ₀_cont⟩⟩
    refine ⟨ψ, ext fun x ↦ ?_⟩
    rw [map_apply]
    have hx := DFunLike.congr_fun hψ ⟨g.toLinearMap x, ⟨x, rfl⟩⟩
    have hx' : ψ (g x) = ψ₀ ⟨g.toLinearMap x, ⟨x, rfl⟩⟩ := by
      simpa only [map_apply, Submodule.subtypeL_apply, mk_apply,
        ContinuousLinearMap.coe_mk', ContinuousLinearMap.coe_coe] using hx
    exact hx'.trans (hψ₀_apply x)
  · rintro ⟨ψ, rfl⟩
    refine ext fun x ↦ ?_
    have hgf : g (f x) = 0 := hex.apply_apply_eq_zero x
    simp [map_apply, hgf]

omit [DiscreteTopology E] in
/-- Every nonzero element of a compact module is detected by a continuous functional into `E`. -/
theorem exists_apply_ne_zero_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hN : IsCompactModule R N) {x : N} (hx : x ≠ 0) :
    ∃ φ : ModulePontryaginDual R E N, φ x ≠ 0 := by
  have hnot : ¬ ∀ U : Submodule R N, IsOpen (U : Set N) → x ∈ U := fun h ↦
    hx (hN.eq_zero_of_forall_mem_of_isOpen h)
  push Not at hnot
  obtain ⟨U, hUopen, hxU⟩ := hnot
  have := hN.isTopologicalAddGroup
  have : DiscreteTopology (N ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hUopen
  obtain ⟨ψ, hψ⟩ := exists_apply_ne_zero_of_forall_isMaximal hE
    (m := U.mkQ x) (by rwa [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero])
  exact ⟨map (E := E) U.mkQL ⟨⟨ψ, continuous_of_discreteTopology⟩⟩, by simpa [map_apply] using hψ⟩

omit [DiscreteTopology E] in
/-- A compact module is subsingleton iff its Pontryagin dual is subsingleton. -/
theorem subsingleton_iff_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hN : IsCompactModule R N) :
    Subsingleton (ModulePontryaginDual R E N) ↔ Subsingleton N := by
  refine ⟨fun h ↦ ⟨fun x y ↦ ?_⟩, fun _ ↦ ⟨fun φ ψ ↦ ext fun x ↦ by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  by_contra hxy
  obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_compact hE hN (sub_ne_zero.mpr hxy)
  have h0 := Subsingleton.elim φ 0
  exact hφ (by rw [h0, zero_apply])

/-- **Biduality for compact `R`-modules**: evaluation gives a canonical continuous linear
equivalence `N ≃L[R] (N^∨)^∨`. -/
def evalEquivOfCompact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] (hN : IsCompactModule R N) :
    N ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E N) := by
  have := hN.compactSpace
  have := hN.isTopologicalAddGroup
  have hinj : Function.Injective (eval R E N) := by
    intro x y hxy
    by_contra hne
    obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_compact (nontrivial_linearMap_of_isMaximal hE) hN
      (sub_ne_zero.mpr hne)
    have h0 := DFunLike.congr_fun hxy φ
    simp only [eval_apply] at h0
    exact hφ (by rw [map_sub, sub_eq_zero]; exact h0)
  have hsurj : Function.Surjective (eval R E N) := by
    intro Φ
    have hUex : ∀ U : {U : Submodule R N // IsOpen (U : Set N)},
        ∃ xU : N ⧸ U.1, ∀ ψ : ModulePontryaginDual R E (N ⧸ U.1),
          ψ xU = Φ (map (E := E) U.1.mkQL ψ) := by
      intro U
      have : DiscreteTopology (N ⧸ U.1) :=
        Submodule.Quotient.discreteTopology_of_isOpen U.1 U.2
      have : Finite (N ⧸ U.1) := finite_quotient_of_isOpen U.1 U.2
      have hlen : IsFiniteLength R (N ⧸ U.1) := IsFiniteLength.of_finite
      let Ψ : ((N ⧸ U.1) →ₗ[R] E) →ₗ[R] E :=
        Φ.toContinuousLinearMap.toLinearMap ∘ₗ
          (map (E := E) U.1.mkQL).toLinearMap ∘ₗ (equivLinearMap R E (N ⧸ U.1)).symm.toLinearMap
      obtain ⟨xU, hxU⟩ := (bijective_applyₗ_of_forall_isMaximal hE hlen).2 Ψ
      refine ⟨xU, fun ψ ↦ ?_⟩
      have h := LinearMap.congr_fun hxU (equivLinearMap R E (N ⧸ U.1) ψ)
      simpa [Ψ, LinearMap.applyₗ_apply_apply] using h
    choose xU hxU using hUex
    have hcompat : ∀ ⦃U V : {U : Submodule R N // IsOpen (U : Set N)}⦄ (h : U.1 ≤ V.1),
        Submodule.factor h (xU U) = xU V := by
      intro U V h
      have : DiscreteTopology (N ⧸ U.1) :=
        Submodule.Quotient.discreteTopology_of_isOpen U.1 U.2
      have : DiscreteTopology (N ⧸ V.1) :=
        Submodule.Quotient.discreteTopology_of_isOpen V.1 V.2
      refine injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE) ?_
      ext f
      let ψ : ModulePontryaginDual R E (N ⧸ V.1) := (equivLinearMap R E (N ⧸ V.1)).symm f
      let factorL : (N ⧸ U.1) →L[R] (N ⧸ V.1) :=
        ⟨Submodule.factor h, continuous_of_discreteTopology⟩
      have hcomp : map (E := E) U.1.mkQL (map (E := E) factorL ψ) = map (E := E) V.1.mkQL ψ :=
        ext fun y ↦ by simp [map_apply, factorL]
      calc
        f (Submodule.factor h (xU U)) = (map (E := E) factorL ψ) (xU U) := by
          simp [map_apply, factorL, ψ]
        _ = Φ (map (E := E) U.1.mkQL (map (E := E) factorL ψ)) := hxU U _
        _ = Φ (map (E := E) V.1.mkQL ψ) := by rw [hcomp]
        _ = ψ (xU V) := (hxU V ψ).symm
        _ = f (xU V) := equivLinearMap_symm_apply f (xU V)
    obtain ⟨x, hx, -⟩ := hN.existsUnique_forall_mkQ_eq xU hcompat
    refine ⟨x, ext fun φ ↦ ?_⟩
    let U : {U : Submodule R N // IsOpen (U : Set N)} :=
      ⟨LinearMap.ker φ.toContinuousLinearMap.toLinearMap, isOpen_ker φ⟩
    obtain ⟨ψ, hψ⟩ := (range_map_mkQL_of_isOpen U.1 U.2 φ).mpr le_rfl
    have hψ' : map (E := E) U.1.mkQL ψ = φ := hψ
    rw [eval_apply, ← hψ', map_apply, Submodule.mkQL_apply, hx U, hxU U ψ]
  let e : N ≃ₗ[R] ModulePontryaginDual R E (ModulePontryaginDual R E N) :=
    LinearEquiv.ofBijective (eval R E N) ⟨hinj, hsurj⟩
  let eh : N ≃ₜ ModulePontryaginDual R E (ModulePontryaginDual R E N) :=
    (continuous_eval_of_compact (R := R) (E := E) (M := N)).homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact {
    toLinearEquiv := e
    continuous_toFun := eh.continuous_toFun
    continuous_invFun := eh.continuous_invFun }

@[simp]
theorem evalEquivOfCompact_apply
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] (hN : IsCompactModule R N)
    (x : N) (φ : ModulePontryaginDual R E N) :
    evalEquivOfCompact hE hN x φ = φ x := by
  change eval R E N x φ = φ x
  exact eval_apply x φ

/-- **Full faithfulness on compact modules**: `map` is a bijection on continuous linear maps
between compact `R`-modules. -/
theorem bijective_map_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂) :
    Function.Bijective (map (R := R) (E := E) (M := N₁) (N := N₂)) := by
  let e₁ := evalEquivOfCompact (E := E) hE hN₁
  let e₂ := evalEquivOfCompact (E := E) hE hN₂
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContinuousLinearMap.comp ((map (E := E) g).comp e₁.toContinuousLinearMap),
    fun f ↦ ?_, fun g ↦ ?_⟩
  · ext x
    apply e₂.injective
    have hnat : map (E := E) (map (E := E) f) (e₁ x) = e₂ (f x) :=
      ext fun φ ↦ by simp [e₁, e₂, map_apply]
    simpa [e₁, e₂] using hnat
  · ext φ x
    rw [map_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      ← evalEquivOfCompact_apply hE hN₂ (e₂.symm (map (E := E) g (e₁ x))) φ,
      e₂.apply_symm_apply, map_apply, evalEquivOfCompact_apply]

end CompactExact

section CompactLocalRing

variable {R : Type u} {E : Type v}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [TotallyDisconnectedSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [ContinuousSMul R E] [Module.Injective R E] [Small.{v} R]

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

omit [TopologicalSpace E] [DiscreteTopology E] [ContinuousSMul R E] in
/-- For a discrete module `M` with continuous `R`-action, the submodule of `E` killed by the
annihilator of `m : M` is finite. -/
private theorem finite_torsionBySet_annihilator {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M] (m : M) :
    Finite (Submodule.torsionBySet R E
      (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R)) := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M m)
  have hfin : Finite (R ⧸ I) := finite_quotient_of_isOpen I (isOpen_annihilator_elem m)
  have hlen : IsFiniteLength R ((R ⧸ I) →ₗ[R] E) := by
    rw [← Module.length_ne_top_iff, length_linearMap_of_forall_isMaximal hE]
    exact Module.length_ne_top_iff.mpr IsFiniteLength.of_finite
  have htor : IsFiniteLength R (Submodule.torsionBySet R E (I : Set R)) := by
    rw [← Module.length_ne_top_iff, ← (I.quotientLinearMapEquivTorsionBySet E).length_eq]
    exact Module.length_ne_top_iff.mpr hlen
  exact finite_of_isFiniteLength htor

/-- **The dual of a discrete module with continuous `R`-action is a compact `R`-module.** -/
theorem isCompactModule_of_discrete {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M] :
    IsCompactModule R (ModulePontryaginDual R E M) := by
  let T : M → Type v := fun m ↦
    Submodule.torsionBySet R E (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R)
  have hfin : ∀ m : M, Finite (T m) := fun m ↦ finite_torsionBySet_annihilator hE m
  let ι : ModulePontryaginDual R E M → ∀ m : M, T m := fun φ m ↦
    ⟨φ m, (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨r, hr⟩ ↦ by
      have hrm : r • m = 0 := LinearMap.mem_ker.mp hr
      rw [← map_smul, hrm, map_zero]⟩
  let valPi : (∀ m : M, T m) → (M → E) := fun f m ↦ (f m : E)
  have hvalPi : IsEmbedding valPi := .piMap fun _ ↦ .subtypeVal
  have hcomp : valPi ∘ ι = (⇑) := rfl
  have hclosed : IsClosedEmbedding ι := by
    have hcoe := isClosedEmbedding_coe (R := R) (E := E) (M := M)
    rw [← hcomp] at hcoe
    refine ⟨⟨hvalPi.isInducing.of_comp_iff.mp hcoe.isInducing,
      Function.Injective.of_comp hcoe.injective⟩, ?_⟩
    have hrange : Set.range ι = valPi ⁻¹' Set.range (valPi ∘ ι) := by
      ext f
      simp only [Set.mem_range, Set.mem_preimage, Function.comp_apply]
      exact ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ, congrArg valPi hφ⟩,
        fun ⟨φ, hφ⟩ ↦ ⟨φ, hvalPi.injective hφ⟩⟩
    rw [hrange]
    exact hcoe.isClosed_range.preimage hvalPi.continuous
  have : ∀ m : M, CompactSpace (T m) := fun m ↦
    have := hfin m; Finite.compactSpace
  have : ∀ m : M, TotallyDisconnectedSpace (T m) := fun m ↦
    inferInstanceAs (TotallyDisconnectedSpace {x : E // _})
  have hcompact : CompactSpace (ModulePontryaginDual R E M) :=
    hclosed.compactSpace
  have htd : TotallyDisconnectedSpace (ModulePontryaginDual R E M) :=
    ⟨fun s _ hs x hx y hy ↦ hclosed.injective <|
      TotallyDisconnectedSpace.isTotallyDisconnected_univ _ (Set.subset_univ _)
        (hs.image ι hclosed.continuous.continuousOn) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩⟩
  exact ⟨inferInstance, inferInstance, hcompact, htd⟩

/-- **Biduality for discrete modules with continuous `R`-action**: evaluation gives a canonical
continuous linear equivalence `M ≃L[R] (M^∨)^∨`. -/
def evalEquivOfDiscrete {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M] :
    M ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E M) := by
  have hDualCompact : CompactSpace (ModulePontryaginDual R E M) :=
    (isCompactModule_of_discrete hE (M := M)).compactSpace
  have hinj : Function.Injective (eval R E M) := by
    intro x y hxy
    refine injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE) ?_
    ext f
    have h := DFunLike.congr_fun hxy ((equivLinearMap R E M).symm f)
    simpa [LinearMap.applyₗ_apply_apply, eval_apply] using h
  have hsurj : Function.Surjective (eval R E M) := by
    intro Φ
    have hopen : IsOpen (LinearMap.ker Φ.toContinuousLinearMap.toLinearMap :
        Set (ModulePontryaginDual R E M)) := isOpen_ker Φ
    obtain ⟨U, hUopen, hUeq⟩ :=
      (isEmbedding_coe (R := R) (E := E) (M := M)).isInducing.isOpen_iff.mp hopen
    have h0U : (0 : M → E) ∈ U := by
      have : (0 : ModulePontryaginDual R E M) ∈ (⇑) ⁻¹' U := by
        rw [hUeq]; exact (LinearMap.ker _).zero_mem
      exact this
    rw [isOpen_pi_iff] at hUopen
    obtain ⟨s, V, hV, hsub⟩ := hUopen 0 h0U
    let M₀ : Submodule R M := Submodule.span R (s : Set M)
    have hM₀fin : Finite M₀ := finite_of_fg_of_discrete (Submodule.fg_span s.finite_toSet)
    have hM₀len : IsFiniteLength R M₀ := IsFiniteLength.of_finite
    have hker : LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap ≤
        LinearMap.ker Φ.toContinuousLinearMap.toLinearMap := by
      intro φ hφ
      have hφ_mem : (⇑φ : M → E) ∈ U := hsub fun m hm ↦ by
        have hfm : φ m = 0 := by
          have := DFunLike.congr_fun hφ ⟨m, Submodule.subset_span hm⟩
          simpa [map_apply] using this
        rw [hfm]
        exact (hV m hm).2
      have : φ ∈ (⇑) ⁻¹' U := hφ_mem
      rwa [hUeq] at this
    have hsurjM₀ : Function.Surjective (map (E := E) M₀.subtypeL) :=
      map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀)
    let eQ := LinearMap.quotKerEquivOfSurjective (map (E := E) M₀.subtypeL).toLinearMap hsurjM₀
    let Ψ : (M₀ →ₗ[R] E) →ₗ[R] E :=
      (LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap).liftQ
        Φ.toContinuousLinearMap.toLinearMap hker ∘ₗ
      eQ.symm.toLinearMap ∘ₗ (equivLinearMap R E M₀).symm.toLinearMap
    obtain ⟨x₀, hx₀⟩ := (bijective_applyₗ_of_forall_isMaximal hE hM₀len).2 Ψ
    refine ⟨x₀.1, ext fun φ ↦ ?_⟩
    have hx := LinearMap.congr_fun hx₀ (equivLinearMap R E M₀ (map (E := E) M₀.subtypeL φ))
    have hq : eQ.symm (map (E := E) M₀.subtypeL φ) = Submodule.Quotient.mk φ :=
      eQ.injective (by simp [eQ])
    simp only [LinearMap.applyₗ_apply_apply, equivLinearMap_apply, map_apply,
      Submodule.subtypeL_apply, Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at hx
    rw [eval_apply, hx, hq]
    rfl
  exact {
    toLinearEquiv := LinearEquiv.ofBijective (eval R E M) ⟨hinj, hsurj⟩
    continuous_toFun := continuous_eval_of_discrete
    continuous_invFun := continuous_of_discreteTopology }

@[simp]
theorem evalEquivOfDiscrete_apply {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M]
    (x : M) (φ : ModulePontryaginDual R E M) :
    evalEquivOfDiscrete hE x φ = φ x := by
  change eval R E M x φ = φ x
  exact eval_apply x φ

/-- **Full faithfulness on discrete modules**: `map` is a bijection on continuous linear maps
between discrete `R`-modules with continuous `R`-action. -/
theorem bijective_map_of_discrete {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
    [ContinuousSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
    [ContinuousSMul R M₂] :
    Function.Bijective (map (R := R) (E := E) (M := M₁) (N := M₂)) := by
  let e₁ := evalEquivOfDiscrete (E := E) hE (M := M₁)
  let e₂ := evalEquivOfDiscrete (E := E) hE (M := M₂)
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContinuousLinearMap.comp ((map (E := E) g).comp e₁.toContinuousLinearMap),
    fun f ↦ ?_, fun g ↦ ?_⟩
  · ext x
    apply e₂.injective
    have hnat : map (E := E) (map (E := E) f) (e₁ x) = e₂ (f x) :=
      ext fun φ ↦ by simp [e₁, e₂, map_apply]
    simpa [e₁, e₂] using hnat
  · ext φ x
    rw [map_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      ← evalEquivOfDiscrete_apply hE (e₂.symm (map (E := E) g (e₁ x))) φ,
      e₂.apply_symm_apply, map_apply, evalEquivOfDiscrete_apply]

/-- **Quotient identification on duals of discrete modules**: for any submodule `M₀` of a discrete
module `M` with continuous `R`-action, restricting to `M₀` induces a continuous linear equivalence
`M^∨ ⧸ ker(M^∨ → M₀^∨) ≃L[R] M₀^∨`. -/
def quotKerMapSubtypeEquiv {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M] (M₀ : Submodule R M) :
    (ModulePontryaginDual R E M ⧸
      LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap) ≃L[R]
      ModulePontryaginDual R E M₀ := by
  have hMcomp : IsCompactModule R (ModulePontryaginDual R E M) :=
    isCompactModule_of_discrete hE
  have hclosed : IsClosed (LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap :
      Set (ModulePontryaginDual R E M)) := by
    convert (isClosed_singleton (x := (0 : ModulePontryaginDual R E M₀))).preimage
      (map (E := E) M₀.subtypeL).continuous using 1
    ext φ
    simp [LinearMap.mem_ker]
  have hQcomp : CompactSpace (ModulePontryaginDual R E M ⧸
      LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap) :=
    (hMcomp.quotient _ hclosed).compactSpace
  have hsurj : Function.Surjective (map (E := E) M₀.subtypeL) :=
    map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀)
  let e := LinearMap.quotKerEquivOfSurjective (map (E := E) M₀.subtypeL).toLinearMap hsurj
  have hcont : Continuous e :=
    (LinearMap.ker _).isQuotientMap_mkQ.continuous_iff.mpr (map (E := E) M₀.subtypeL).continuous
  let eh := hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact {
    toLinearEquiv := e
    continuous_toFun := eh.continuous_toFun
    continuous_invFun := eh.continuous_invFun }

@[simp]
theorem quotKerMapSubtypeEquiv_mk {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul R M] (M₀ : Submodule R M)
    (φ : ModulePontryaginDual R E M) :
    quotKerMapSubtypeEquiv hE M₀ (Submodule.Quotient.mk φ) = map (E := E) M₀.subtypeL φ :=
  LinearMap.quotKerEquivOfSurjective_apply_mk (map (E := E) M₀.subtypeL).toLinearMap
    (map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀)) φ

end CompactLocalRing

end ModulePontryaginDual

end TauCeti
