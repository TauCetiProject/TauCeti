/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Continuity of smooth fibrewise operations on sections

A family of fibre maps `ϕ x : V x → W x` over the identity of the base, smooth as a map of
total spaces, acts on smooth sections by `s ↦ (x ↦ ϕ x (s x))` (`ContMDiffSection.map`). The
fibre maps need not be linear: pointwise polynomial operations on sections of endomorphism
bundles, such as `J ↦ J ∘ J` or `J ↦ J ∘ J₀ ∘ J`, are of this form.

This action is continuous for the compact derivative topologies on sections
(`ContMDiffSection.continuous_map_frameTopology`), for any covering frame system of the source
bundle and any frame system of the target bundle. The source model of the base is locally
compact, as for finite-dimensional manifolds; the fibres may be infinite-dimensional.

On the overlap of a source frame domain with a target frame domain, the target coefficients of
the image section are a fixed smooth map of the base point and the source coefficients. Pairing
(`ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`), composition
(`ContMDiffMap.continuous_comp_manifoldWeakWhitney`) and postcomposition with a fixed map
(`ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`) are continuous in the weak Whitney
topology, and continuity is local on the target frame domain
(`ContMDiffMap.continuous_of_forall_continuous_restrict`).

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §2, for continuity of composition
  in the compact-open `C^∞` topology.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞ω}
  {V W : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]

variable (ϕ : ∀ x, V x → W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace G W)))

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [VectorBundle 𝕜 G W]
  [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M]
  [LocallyCompactSpace E]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {κ : Type*} (e' : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (e' j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)

/-- A smooth family of fibre maps acts continuously on sections for the compact derivative
topologies, given a covering frame system of the source bundle and any frame system of the
target bundle. -/
theorem continuous_map_frameTopology (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    let _ := frameTopology (I := I) (n := n) e' U' hU'
    Continuous (ContMDiffSection.map ϕ hϕ) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology (I := I) (n := n) e' U' hU'
  apply (continuous_frameTopology_iff_frameCoordinates e' U' hU').mpr
  intro j
  -- Continuity is local on the target frame domain; cover it by the source frame domains.
  let D (i : ι) : Opens (U' j) := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (U i)
  apply ContMDiffMap.continuous_of_forall_continuous_restrict D fun x ↦ hcover x
  intro i
  have hval : ContMDiff I I n (fun y : D i ↦ ((y : U' j) : M)) :=
    (contMDiff_subtype_val (U := U' j)).comp (contMDiff_subtype_val (U := D i))
  let incl : C^n⟮I, D i; I, U i⟯ :=
    ⟨fun x ↦ ⟨((x : U' j) : M), x.2⟩, (TauCeti.ContMDiff.subtypeVal_comp_iff (U i) _).mp hval⟩
  -- On the overlap, target coefficients are a fixed smooth map of the point and the source
  -- coefficients.
  let σ : D i × F → TotalSpace F V := fun p ↦ ⟨((p.1 : U' j) : M), (e i).symm _ p.2⟩
  have hσ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) n σ := by
    intro p
    rw [(e i).contMDiffAt_iff (f := σ) ((e i).mem_source.mpr (hU i p.1.2))]
    refine ⟨(hval.comp contMDiff_fst).contMDiffAt, ?_⟩
    refine contMDiffAt_snd.congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_)
    exact congrArg Prod.snd ((e i).apply_mk_symm (hU i q.1.2) q.2)
  let g : C^n⟮I.prod 𝓘(𝕜, F), D i × F; 𝓘(𝕜, G), G⟯ :=
    ⟨fun p ↦ ((e' j) ⟨((p.1 : U' j) : M), ϕ _ ((e i).symm _ p.2)⟩).2, fun p ↦
      (((e' j).contMDiffAt_iff ((e' j).mem_source.mpr (hU' j (p.1 : U' j).2))).mp
        ((hϕ.comp hσ) p)).2⟩
  have hc : Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦
      g.comp (ContMDiffMap.id.prodMk (((e i).frameCoordinates (hU i) s).comp incl))) :=
    (ContMDiffMap.continuous_postcomp_manifoldWeakWhitney g).comp
      (ContMDiffMap.continuous_prodMk_manifoldWeakWhitney.comp (continuous_const.prodMk
        (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
          ((continuous_frameCoordinates e U hU i).prodMk continuous_const))))
  -- The bundled maps evaluate by their defining formulas.
  have hg (p : D i × F) : g p = ((e' j) ⟨((p.1 : U' j) : M), ϕ _ ((e i).symm _ p.2)⟩).2 := rfl
  have hincl (x : D i) : incl x = ⟨((x : U' j) : M), x.2⟩ := rfl
  have hid (x : D i) : (ContMDiffMap.id : C^n⟮I, D i; I, D i⟯) x = x := rfl
  refine hc.congr fun s ↦ ?_
  ext x
  simp only [ContMDiffMap.restrict_apply, ContMDiffMap.comp_apply, ContMDiffMap.prodMk_apply,
    Bundle.Trivialization.frameCoordinates_apply, map_apply, hg, hincl, hid]
  have hx : ((x : U' j) : M) ∈ (e i).baseSet := hU i x.2
  rw [(e i).symm_apply_apply_mk hx]

end ContMDiffSection
