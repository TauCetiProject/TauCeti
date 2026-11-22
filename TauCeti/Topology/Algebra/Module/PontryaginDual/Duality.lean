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
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import TauCeti.RingTheory.Length
import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Compact–discrete Pontryagin duality for modules over a compact local ring

For a compact totally disconnected commutative local topological ring `R` and a discrete injective
`R`-module `E` with continuous `R`-action and `length_R(Hom_R(R ⧸ 𝔪, E)) = 1`,
`TauCeti.ModulePontryaginDual R E` gives an exact contravariant equivalence between discrete
`R`-modules with continuous `R`-action and compact `R`-modules (`TauCeti.IsCompactModule R`).

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

namespace ModulePontryaginDual

section General

variable {R : Type u} {E : Type v}
  [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E]

omit [IsTopologicalAddGroup E] [ContinuousConstSMul R E] in
/-- When `E` is discrete, the kernel of every element of `ModulePontryaginDual R E M` is open. -/
theorem isOpen_ker [DiscreteTopology E] {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] (φ : ModulePontryaginDual R E M) :
    IsOpen (LinearMap.ker φ.toContinuousLinearMap.toLinearMap : Set M) :=
  (isOpen_discrete {(0 : E)}).preimage (map_continuous φ)

/-- A surjective continuous linear map induces an injective dual map. -/
theorem map_injective_of_surjective {M N : Type*} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
    {f : M →L[R] N} (hf : Function.Surjective f) :
    Function.Injective (map (E := E) f) := fun _ _ h ↦ ext fun y ↦ by
  obtain ⟨x, rfl⟩ := hf y; simpa only [map_apply] using DFunLike.congr_fun h x

/-- An injective continuous linear map into a discrete module induces a surjective dual map when `E`
is injective. -/
theorem map_surjective_of_injective_of_discrete [Module.Injective R E] [Small.{v} R] {M N : Type*}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [DiscreteTopology N] {f : M →L[R] N} (hf : Function.Injective f) :
    Function.Surjective (map (E := E) f) := fun φ ↦ by
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R E M N f.toLinearMap hf
    φ.toContinuousLinearMap.toLinearMap
  exact ⟨⟨⟨g, continuous_of_discreteTopology⟩⟩,
    ext fun x ↦ by simpa [map_apply] using LinearMap.congr_fun hg x⟩

section ExactHelper

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
  [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃]

/-- Factor a functional vanishing on `im f` through `im g` for an exact sequence `f, g`. -/
private def liftExactRange {f : M₁ →L[R] M₂} {g : M₂ →L[R] M₃}
    (hex : Function.Exact f.toLinearMap g.toLinearMap)
    (φ : ModulePontryaginDual R E M₂) (hφ : map (E := E) f φ = 0) :
    LinearMap.range g.toLinearMap →ₗ[R] E :=
  g.toLinearMap.rangeRestrict.liftOfSurjective g.toLinearMap.surjective_rangeRestrict
    ⟨φ.toContinuousLinearMap.toLinearMap, by
      rw [LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp hex]
      rintro _ ⟨x, rfl⟩
      simpa [LinearMap.mem_ker, map_apply] using DFunLike.congr_fun hφ x⟩

private theorem liftExactRange_apply {f : M₁ →L[R] M₂} {g : M₂ →L[R] M₃}
    (hex : Function.Exact f.toLinearMap g.toLinearMap)
    (φ : ModulePontryaginDual R E M₂) (hφ : map (E := E) f φ = 0) (x : M₂) :
    liftExactRange hex φ hφ ⟨g.toLinearMap x, x, rfl⟩ = φ x :=
  g.toLinearMap.rangeRestrict.equivOfSurjective_apply g.toLinearMap.surjective_rangeRestrict _

private theorem exact_map_of_lift {f : M₁ →L[R] M₂} {g : M₂ →L[R] M₃}
    (hex : Function.Exact f.toLinearMap g.toLinearMap)
    (hlift : ∀ φ : ModulePontryaginDual R E M₂, map (E := E) f φ = 0 →
      ∃ ψ : ModulePontryaginDual R E M₃, map (E := E) g ψ = φ) :
    Function.Exact (map (E := E) g).toLinearMap (map (E := E) f).toLinearMap := by
  rw [LinearMap.exact_iff]; ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  exact ⟨hlift φ, fun ⟨ψ, hψ⟩ ↦ hψ ▸ ext fun x ↦ by
    have hgf : g (f x) = 0 := hex.apply_apply_eq_zero x; simp [map_apply, hgf]⟩

end ExactHelper

/-- Exactness of `ModulePontryaginDual R E` on continuous linear maps ending in a discrete module
when `E` is injective. -/
theorem exact_map_of_discrete [Module.Injective R E] [Small.{v} R] {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [DiscreteTopology M₃]
    {f : M₁ →L[R] M₂} {g : M₂ →L[R] M₃} (hex : Function.Exact f.toLinearMap g.toLinearMap) :
    Function.Exact (map (E := E) g).toLinearMap (map (E := E) f).toLinearMap :=
  exact_map_of_lift hex fun φ hφ ↦ by
    obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property R E _ M₃
      (LinearMap.range g.toLinearMap).subtype (Submodule.subtype_injective _)
      (liftExactRange hex φ hφ)
    refine ⟨⟨⟨ψ, continuous_of_discreteTopology⟩⟩, ext fun x ↦ ?_⟩
    have hx := LinearMap.congr_fun hψ ⟨g.toLinearMap x, x, rfl⟩
    rw [LinearMap.comp_apply, Submodule.coe_subtype, liftExactRange_apply] at hx
    simpa [map_apply] using hx

/-- For an open submodule `U` of `N`, the range of `map U.mkQL` consists precisely of the
continuous functionals vanishing on `U`. -/
theorem range_map_mkQL_of_isOpen {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] (U : Submodule R N) (hU : IsOpen (U : Set N))
    (φ : ModulePontryaginDual R E N) :
    φ ∈ LinearMap.range (map (E := E) U.mkQL).toLinearMap ↔
      U ≤ LinearMap.ker φ.toContinuousLinearMap.toLinearMap := by
  have : DiscreteTopology (N ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hU
  refine ⟨fun ⟨ψ, hψ⟩ x hx ↦ by
      rw [← hψ]; simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero U).mpr hx],
    fun hle ↦ ⟨⟨⟨U.liftQ φ.toContinuousLinearMap.toLinearMap hle, continuous_of_discreteTopology⟩⟩,
      ext fun x ↦ by simp [map_apply]⟩⟩

/-- **Colimit compatibility over open quotients**: when `E` is discrete, every element of `N^∨`
lies in the image of `(N ⧸ U)^∨` for some open submodule `U` of `N`. -/
theorem iSup_range_map_mkQL_eq_top [DiscreteTopology E] {N : Type w} [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] :
    ⨆ U : {U : Submodule R N // IsOpen (U : Set N)},
      LinearMap.range (map (E := E) U.val.mkQL).toLinearMap = ⊤ :=
  eq_top_iff.mpr fun φ _ ↦
    Submodule.mem_iSup_of_mem ⟨LinearMap.ker φ.toContinuousLinearMap.toLinearMap, isOpen_ker φ⟩
      ((range_map_mkQL_of_isOpen _ (isOpen_ker φ) φ).mpr le_rfl)

/-- **Inverse-limit compatibility over finitely generated submodules**: a compatible family of
elements in `K^∨` for finitely generated submodules `K` of a discrete module `M` comes from a
unique element of `M^∨`. -/
theorem existsUnique_forall_restrict_fg_eq {M : Type w} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M]
    (φ : ∀ K : {K : Submodule R M // K.FG}, ModulePontryaginDual R E K.val)
    (hφ : ∀ ⦃K K' : {K : Submodule R M // K.FG}⦄ (h : K.val ≤ K'.val) (x : K.val),
      φ K' ⟨x.val, h x.property⟩ = φ K x) :
    ∃! ψ : ModulePontryaginDual R E M, ∀ K, map (E := E) K.val.subtypeL ψ = φ K := by
  let Kx (x : M) : {K : Submodule R M // K.FG} :=
    ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
  have hwell (K : {K : Submodule R M // K.FG}) (x : M) (hx : x ∈ K.val) :
      φ K ⟨x, hx⟩ = φ (Kx x) ⟨x, Submodule.subset_span rfl⟩ :=
    hφ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) ⟨x, Submodule.subset_span rfl⟩
  let f : M →ₗ[R] E :=
    { toFun := fun x ↦ φ (Kx x) ⟨x, Submodule.subset_span rfl⟩
      map_add' := fun x y ↦ by
        let K : {K : Submodule R M // K.FG} :=
          ⟨Submodule.span R {x, y}, Submodule.fg_span (Set.toFinite _)⟩
        have hx : x ∈ K.val := Submodule.subset_span (by simp)
        have hy : y ∈ K.val := Submodule.subset_span (by simp)
        rw [← hwell K (x + y) (K.val.add_mem hx hy), ← hwell K x hx, ← hwell K y hy, ← map_add]
        rfl
      map_smul' := fun r x ↦ by
        rw [← hwell (Kx x) (r • x) ((Kx x).val.smul_mem r (Submodule.subset_span rfl)),
          RingHom.id_apply, ← map_smul]; rfl }
  refine ⟨(equivLinearMap R E M).symm f,
    fun K ↦ ext fun x ↦ by simpa [f, map_apply] using (hwell K x.val x.property).symm,
    fun ψ' hψ' ↦ ext fun x ↦ by
      simpa [f, map_apply] using DFunLike.congr_fun (hψ' (Kx x)) ⟨x, Submodule.subset_span rfl⟩⟩

/-- A discrete module is subsingleton iff its Pontryagin dual is subsingleton. -/
theorem subsingleton_iff_of_discrete [Module.Injective R E] [Small.{v} R]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] :
    Subsingleton (ModulePontryaginDual R E M) ↔ Subsingleton M := by
  refine ⟨fun h ↦ ⟨fun x y ↦ injective_applyₗ_of_forall_isMaximal hE <| LinearMap.ext fun f ↦ ?_⟩,
    fun _ ↦ ⟨fun _ _ ↦ ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  have h0 := Subsingleton.elim ((equivLinearMap R E M).symm f) 0
  simpa [LinearMap.applyₗ_apply_apply] using
    (DFunLike.congr_fun h0 x).trans (DFunLike.congr_fun h0 y).symm

/-- Full faithfulness of `map` follows directly from continuous biduality equivalences. -/
private theorem bijective_map_of_evalEquiv {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂]
    (e₁ : M₁ ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E M₁))
    (e₂ : M₂ ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E M₂))
    (he₁ : ∀ x φ, e₁ x φ = φ x) (he₂ : ∀ x φ, e₂ x φ = φ x) :
    Function.Bijective (map (R := R) (E := E) (M := M₁) (N := M₂)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun g ↦
    e₂.symm.toContinuousLinearMap.comp ((map (E := E) g).comp e₁.toContinuousLinearMap),
    fun f ↦ ContinuousLinearMap.ext fun x ↦ e₂.injective <| by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e₂.apply_symm_apply]
      exact ext fun φ ↦ by simp [he₁, he₂],
    fun g ↦ ContinuousLinearMap.ext fun φ ↦ ext fun x ↦ by
      simp only [map_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [← he₂ _ φ, e₂.apply_symm_apply, map_apply, he₁]⟩

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
  have := hN₁.compactSpace; have := hN₂.t2Space
  have := hN₂.isTopologicalAddGroup; have := hN₂.isLinearTopology
  intro φ
  let K := LinearMap.ker φ.toContinuousLinearMap.toLinearMap
  have hfK : IsClosed (f '' (K : Set N₁)ᶜ) :=
    ((isOpen_ker φ).isClosed_compl.isCompact.image f.continuous).isClosed
  have h0 : (0 : N₂) ∈ (f '' (K : Set N₁)ᶜ)ᶜ := fun ⟨x, hx, hfx⟩ ↦
    hx (hf (hfx.trans (map_zero f).symm) ▸ K.zero_mem)
  obtain ⟨U, hUopen, hUsub⟩ := (IsLinearTopology.hasBasis_open_submodule R (M := N₂)).mem_iff.mp
    (hfK.isOpen_compl.mem_nhds h0)
  have hcomap : U.comap f.toLinearMap ≤ K := fun x hx ↦ by_contra fun hxK ↦ hUsub hx ⟨x, hxK, rfl⟩
  let fbar := Submodule.mapQ (U.comap f.toLinearMap) U f.toLinearMap le_rfl
  have hfbar : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot]
    dsimp only [fbar]
    rw [Submodule.ker_mapQ, Submodule.mkQ_map_self]
  obtain ⟨ψbar, hψbar⟩ := Module.Injective.extension_property R E _ _ fbar hfbar
    ((U.comap f.toLinearMap).liftQ φ.toContinuousLinearMap.toLinearMap hcomap)
  have : DiscreteTopology (N₂ ⧸ U) := Submodule.Quotient.discreteTopology_of_isOpen U hUopen
  exact ⟨map (E := E) U.mkQL ⟨⟨ψbar, continuous_of_discreteTopology⟩⟩, ext fun x ↦ by
    simpa [fbar, map_apply] using LinearMap.congr_fun hψbar (Submodule.Quotient.mk x)⟩

/-- Exactness of `ModulePontryaginDual R E` on compact `R`-modules. -/
theorem exact_map_of_compact {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂]
    [AddCommGroup N₃] [Module R N₃] [TopologicalSpace N₃]
    (hN₂ : IsCompactModule R N₂) (hN₃ : IsCompactModule R N₃)
    {f : N₁ →L[R] N₂} {g : N₂ →L[R] N₃} (hex : Function.Exact f.toLinearMap g.toLinearMap) :
    Function.Exact (map (E := E) g).toLinearMap (map (E := E) f).toLinearMap :=
  exact_map_of_lift hex fun φ hφ ↦ by
    have := hN₂.compactSpace; have := hN₃.t2Space; have := hN₃.isTopologicalAddGroup
    have := hN₃.continuousSMul; have := hN₃.totallyDisconnectedSpace
    let K := LinearMap.range g.toLinearMap; let ψ₀ := liftExactRange hex φ hφ
    let g' : N₂ → K := fun x ↦ ⟨g.toLinearMap x, x, rfl⟩
    have hg'_cont : Continuous g' := g.continuous.subtype_mk _
    have hg'_surj : Function.Surjective g' := fun ⟨_, x, rfl⟩ ↦ ⟨x, rfl⟩
    have hψ₀_cont : Continuous ψ₀ :=
      (hg'_cont.isClosedMap.isQuotientMap hg'_cont hg'_surj).continuous_iff.mpr <| by
        rw [show (ψ₀ ∘ g') = φ from funext (liftExactRange_apply hex φ hφ)]; exact map_continuous φ
    have hKmod : IsCompactModule R K :=
      ⟨inferInstance, inferInstance,
        ⟨Set.image_univ_of_surjective hg'_surj ▸ isCompact_univ.image hg'_cont⟩, inferInstance⟩
    obtain ⟨ψ, hψ⟩ := map_surjective_of_injective_of_compact (E := E) hKmod hN₃
      (f := K.subtypeL) (Submodule.subtype_injective K) ⟨⟨ψ₀, hψ₀_cont⟩⟩
    refine ⟨ψ, ext fun x ↦ ?_⟩
    rw [map_apply]
    exact (by simpa [map_apply] using DFunLike.congr_fun hψ ⟨g.toLinearMap x, x, rfl⟩ :
      ψ (g x) = ψ₀ ⟨g.toLinearMap x, x, rfl⟩).trans (liftExactRange_apply hex φ hφ x)

omit [DiscreteTopology E] in
/-- Every nonzero element of a compact module is detected by a continuous functional into `E`. -/
theorem exists_apply_ne_zero_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hN : IsCompactModule R N) {x : N} (hx : x ≠ 0) :
    ∃ φ : ModulePontryaginDual R E N, φ x ≠ 0 := by
  have ⟨U, hUopen, hxU⟩ : ∃ U : Submodule R N, IsOpen (U : Set N) ∧ x ∉ U := by
    by_contra h; push Not at h; exact hx (hN.eq_zero_of_forall_mem_of_isOpen h)
  have := hN.isTopologicalAddGroup
  have := Submodule.Quotient.discreteTopology_of_isOpen U hUopen
  obtain ⟨ψ, hψ⟩ := exists_apply_ne_zero_of_forall_isMaximal hE
    (m := U.mkQ x) (by rwa [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero])
  exact ⟨map (E := E) U.mkQL ⟨⟨ψ, continuous_of_discreteTopology⟩⟩, by simpa [map_apply] using hψ⟩

omit [DiscreteTopology E] in
/-- A compact module is subsingleton iff its Pontryagin dual is subsingleton. -/
theorem subsingleton_iff_of_compact
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N] (hN : IsCompactModule R N) :
    Subsingleton (ModulePontryaginDual R E N) ↔ Subsingleton N := by
  refine ⟨fun h ↦ ⟨fun x y ↦ by_contra fun hxy ↦ ?_⟩,
    fun _ ↦ ⟨fun _ _ ↦ ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_compact hE hN (sub_ne_zero.mpr hxy)
  exact hφ (by rw [Subsingleton.elim φ 0, zero_apply])

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- **Biduality for compact `R`-modules**: `N ≃L[R] (N^∨)^∨`. -/
def evalEquivOfCompact {N : Type w} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hN : IsCompactModule R N) : N ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E N) := by
  have := hN.compactSpace; have := hN.isTopologicalAddGroup
  have hinj : Function.Injective (eval R E N) := fun x y hxy ↦ by_contra fun hne ↦ by
    obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_compact (nontrivial_linearMap_of_isMaximal hE) hN
      (sub_ne_zero.mpr hne)
    exact hφ (by rw [map_sub, sub_eq_zero]; simpa [eval_apply] using DFunLike.congr_fun hxy φ)
  have hsurj : Function.Surjective (eval R E N) := fun Φ ↦ by
    choose xU hxU using fun U : {U : Submodule R N // IsOpen (U : Set N)} ↦
      show ∃ xU : N ⧸ U.val, ∀ ψ, ψ xU = Φ (map (E := E) U.val.mkQL ψ) by
        have := Submodule.Quotient.discreteTopology_of_isOpen U.val U.property
        have : Finite (N ⧸ U.val) :=
          AddSubgroup.quotient_finite_of_isOpen U.val.toAddSubgroup U.property
        obtain ⟨xU, hxU⟩ := (bijective_applyₗ_of_forall_isMaximal hE IsFiniteLength.of_finite).2
          (Φ.toContinuousLinearMap.toLinearMap ∘ₗ (map (E := E) U.val.mkQL).toLinearMap ∘ₗ
            (equivLinearMap R E (N ⧸ U.val)).symm.toLinearMap)
        exact ⟨xU, fun ψ ↦ by
          simpa [LinearMap.applyₗ_apply_apply] using
            LinearMap.congr_fun hxU (equivLinearMap R E (N ⧸ U.val) ψ)⟩
    have hcompat ⦃U V : {U : Submodule R N // IsOpen (U : Set N)}⦄ (h : U.val ≤ V.val) :
        Submodule.factor h (xU U) = xU V := by
      have := Submodule.Quotient.discreteTopology_of_isOpen U.val U.property
      have := Submodule.Quotient.discreteTopology_of_isOpen V.val V.property
      refine injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE) <|
        LinearMap.ext fun f ↦ ?_
      let ψ := (equivLinearMap R E (N ⧸ V.val)).symm f
      let fL : (N ⧸ U.val) →L[R] (N ⧸ V.val) :=
        ⟨Submodule.factor h, continuous_of_discreteTopology⟩
      have hcomp : map (E := E) U.val.mkQL (map (E := E) fL ψ) = map (E := E) V.val.mkQL ψ :=
        ext fun _ ↦ by simp [fL]
      simpa [LinearMap.applyₗ_apply_apply, fL, ψ] using
        (hxU U (map (E := E) fL ψ)).trans
          (by rw [hcomp, ← hxU V ψ]; exact equivLinearMap_symm_apply f _)
    obtain ⟨x, hx, -⟩ := hN.existsUnique_forall_mkQ_eq xU hcompat
    refine ⟨x, ext fun φ ↦ ?_⟩
    let U : {U : Submodule R N // IsOpen (U : Set N)} := ⟨_, isOpen_ker φ⟩
    obtain ⟨ψ, hψ⟩ := (range_map_mkQL_of_isOpen U.val U.property φ).mpr le_rfl
    have hψ' : map (E := E) U.val.mkQL ψ = φ := hψ
    rw [eval_apply, ← hψ', map_apply, Submodule.mkQL_apply, hx U, hxU U ψ]
  let e := LinearEquiv.ofBijective (eval R E N) ⟨hinj, hsurj⟩
  let eh := (continuous_eval_of_compact (R := R) (E := E) (M := N)).homeoOfEquivCompactToT2
    (f := e.toEquiv)
  exact ⟨e, eh.continuous_toFun, eh.continuous_invFun⟩
@[simp] theorem evalEquivOfCompact_apply {N : Type w} [AddCommGroup N] [Module R N]
    [TopologicalSpace N] (hN : IsCompactModule R N) (x : N) (φ : ModulePontryaginDual R E N) :
    evalEquivOfCompact hE hN x φ = φ x := eval_apply x φ

/-- **Full faithfulness on compact modules**: `map` is a bijection on continuous linear maps
between compact `R`-modules. -/
theorem bijective_map_of_compact {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [TopologicalSpace N₁]
    [AddCommGroup N₂] [Module R N₂] [TopologicalSpace N₂]
    (hN₁ : IsCompactModule R N₁) (hN₂ : IsCompactModule R N₂) :
    Function.Bijective (map (R := R) (E := E) (M := N₁) (N := N₂)) :=
  bijective_map_of_evalEquiv (evalEquivOfCompact hE hN₁) (evalEquivOfCompact hE hN₂)
    (evalEquivOfCompact_apply hE hN₁) (evalEquivOfCompact_apply hE hN₂)

end CompactExact

section CompactLocalRing

variable {R : Type u} {E : Type v}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [TotallyDisconnectedSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [DiscreteTopology E]
  [ContinuousSMul R E] [Module.Injective R E] [Small.{v} R]

variable (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

section SingleDiscrete

variable {M : Type w} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul R M]

omit [TopologicalSpace E] [DiscreteTopology E] [ContinuousSMul R E] in
/-- For a discrete module `M` with continuous `R`-action, the `ann(m)`-torsion in `E` is finite. -/
private theorem finite_torsionBySet_annihilator (m : M) :
    Finite (Submodule.torsionBySet R E
      (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R)) := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M m)
  have : Finite (R ⧸ I) :=
    AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup (isOpen_annihilator_elem m)
  refine IsFiniteLength.finite ((Module.length_ne_top_iff (R := R)).mp ?_)
  rw [← (I.quotientLinearMapEquivTorsionBySet E).length_eq, length_linearMap_of_forall_isMaximal hE]
  exact Module.length_ne_top_iff.mpr IsFiniteLength.of_finite

/-- **The dual of a discrete module with continuous `R`-action is a compact `R`-module.** -/
theorem isCompactModule_of_discrete : IsCompactModule R (ModulePontryaginDual R E M) := by
  let T (m : M) : Type v :=
    Submodule.torsionBySet R E (LinearMap.ker (LinearMap.toSpanSingleton R M m) : Set R)
  let ι : ModulePontryaginDual R E M → ∀ m : M, T m := fun φ m ↦
    ⟨φ m, (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨r, hr⟩ ↦ by
      dsimp only
      rw [← map_smul, show r • m = 0 from LinearMap.mem_ker.mp hr, map_zero]⟩
  let valPi : (∀ m : M, T m) → M → E := fun f m ↦ (f m : E)
  have hvalPi : IsEmbedding valPi := .piMap fun _ ↦ .subtypeVal
  have hcoe : IsClosedEmbedding (valPi ∘ ι) := isClosedEmbedding_coe (R := R) (E := E) (M := M)
  have hclosed : IsClosedEmbedding ι := IsClosedEmbedding.of_comp hvalPi hcoe
  have (m : M) : CompactSpace (T m) :=
    have := finite_torsionBySet_annihilator hE m; Finite.compactSpace
  have (m : M) : TotallyDisconnectedSpace (T m) :=
    inferInstanceAs (TotallyDisconnectedSpace {x : E // _})
  exact ⟨inferInstance, inferInstance, hclosed.compactSpace,
    hclosed.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- **Biduality for discrete modules with continuous `R`-action**: `M ≃L[R] (M^∨)^∨`. -/
def evalEquivOfDiscrete : M ≃L[R] ModulePontryaginDual R E (ModulePontryaginDual R E M) := by
  have := (isCompactModule_of_discrete hE (M := M)).compactSpace
  have hinj : Function.Injective (eval R E M) := fun x y hxy ↦
    injective_applyₗ_of_forall_isMaximal (nontrivial_linearMap_of_isMaximal hE) <|
      LinearMap.ext fun f ↦ by
        simpa [LinearMap.applyₗ_apply_apply] using
          DFunLike.congr_fun hxy ((equivLinearMap R E M).symm f)
  have hsurj : Function.Surjective (eval R E M) := fun Φ ↦ by
    obtain ⟨U, hUopen, hUeq⟩ :=
      (isEmbedding_coe (R := R) (E := E) (M := M)).isInducing.isOpen_iff.mp (isOpen_ker Φ)
    obtain ⟨s, V, hV, hsub⟩ := isOpen_pi_iff.mp hUopen 0
      (show (0 : ModulePontryaginDual R E M) ∈ (⇑) ⁻¹' U by rw [hUeq]; exact Submodule.zero_mem _)
    let M₀ := Submodule.span R (s : Set M)
    have : Finite M₀ := (Submodule.fg_span s.finite_toSet).finite_of_discrete
    have hker : LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap ≤
        LinearMap.ker Φ.toContinuousLinearMap.toLinearMap := fun φ hφ ↦ by
      rw [← SetLike.mem_coe, ← hUeq]
      exact hsub fun m hm ↦ (show φ m = 0 by
        simpa [map_apply] using DFunLike.congr_fun hφ ⟨m, Submodule.subset_span hm⟩) ▸
        (hV m hm).right
    let Φ₀ : ModulePontryaginDual R E M₀ →ₗ[R] E :=
      (map (E := E) M₀.subtypeL).toLinearMap.liftOfSurjective
        (map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀))
        ⟨Φ.toContinuousLinearMap.toLinearMap, hker⟩
    obtain ⟨x₀, hx₀⟩ := (bijective_applyₗ_of_forall_isMaximal hE IsFiniteLength.of_finite).2
      (Φ₀ ∘ₗ (equivLinearMap R E M₀).symm.toLinearMap)
    refine ⟨x₀.val, ext fun φ ↦ ?_⟩
    have hx := LinearMap.congr_fun hx₀ (equivLinearMap R E M₀ (map (E := E) M₀.subtypeL φ))
    simp only [LinearMap.applyₗ_apply_apply, equivLinearMap_apply, map_apply,
      Submodule.subtypeL_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at hx
    rw [eval_apply, hx]
    exact LinearMap.equivOfSurjective_apply
      (map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀)) hker (m := φ)
  exact ⟨LinearEquiv.ofBijective (eval R E M) ⟨hinj, hsurj⟩,
    continuous_eval_of_discrete, continuous_of_discreteTopology⟩
@[simp] theorem evalEquivOfDiscrete_apply (x : M) (φ : ModulePontryaginDual R E M) :
    evalEquivOfDiscrete hE x φ = φ x := eval_apply x φ

/-- **Quotient identification on duals of discrete modules**:
`M^∨ ⧸ ker(M^∨ → M₀^∨) ≃L[R] M₀^∨`. -/
def quotKerMapSubtypeEquiv (M₀ : Submodule R M) :
    (ModulePontryaginDual R E M ⧸
      LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap) ≃L[R] ModulePontryaginDual R E M₀ := by
  have hclosed : IsClosed (LinearMap.ker (map (E := E) M₀.subtypeL).toLinearMap :
      Set (ModulePontryaginDual R E M)) :=
    isClosed_singleton.preimage (map (E := E) M₀.subtypeL).continuous
  have := ((isCompactModule_of_discrete hE).quotient _ hclosed).compactSpace
  let e := LinearMap.quotKerEquivOfSurjective (map (E := E) M₀.subtypeL).toLinearMap
    (map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀))
  have hcont : Continuous e :=
    (LinearMap.ker _).isQuotientMap_mkQ.continuous_iff.mpr (map (E := E) M₀.subtypeL).continuous
  let eh := hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact ⟨e, eh.continuous_toFun, eh.continuous_invFun⟩
@[simp] theorem quotKerMapSubtypeEquiv_mk (M₀ : Submodule R M) (φ : ModulePontryaginDual R E M) :
    quotKerMapSubtypeEquiv hE M₀ (Submodule.Quotient.mk φ) = map (E := E) M₀.subtypeL φ :=
  LinearMap.quotKerEquivOfSurjective_apply_mk (map (E := E) M₀.subtypeL).toLinearMap
    (map_surjective_of_injective_of_discrete (Submodule.subtype_injective M₀)) φ

end SingleDiscrete

/-- **Full faithfulness on discrete modules**: `map` is a bijection on continuous linear maps
between discrete `R`-modules with continuous `R`-action. -/
theorem bijective_map_of_discrete {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [DiscreteTopology M₁]
    [ContinuousSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [DiscreteTopology M₂]
    [ContinuousSMul R M₂] :
    Function.Bijective (map (R := R) (E := E) (M := M₁) (N := M₂)) :=
  bijective_map_of_evalEquiv (evalEquivOfDiscrete hE) (evalEquivOfDiscrete hE)
    (evalEquivOfDiscrete_apply hE) (evalEquivOfDiscrete_apply hE)

end CompactLocalRing

end ModulePontryaginDual

end TauCeti
