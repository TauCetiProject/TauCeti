/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.FiberBundle.Trivialization
import TauCeti.Topology.Covering.Homeomorph
import TauCeti.Topology.Covering.Prod

/-!
# Equivariant bundle maps along covering maps

Let `projP : P → B` and `projQ : Q → B` be bundles over a base `B` equipped with right actions of
`G` and `H`, and let `φ : P → Q` cover the identity of `B` equivariantly along a covering map
`ρ : G → H` into a topological group `H`. Over the overlap `W` of equivariant trivializations
`e : Trivialization G projP` and `t : Trivialization H projQ`, reading `φ` in the two
trivializations conjugates `φ` over `projQ ⁻¹' W` to `(y, g) ↦ (y, c y * ρ g)`, where
`c : W → H` is the fibre coordinate in `t` of the image of the unit section of `e`. Since
`(y, h) ↦ (y, c y * h)` is a self-homeomorphism of `W × H` and `Prod.map id ρ` is a covering map,
`φ` is a covering map over `projQ ⁻¹' W`
(`IsCoveringMap.isCoveringMapOn_of_equivariant_trivialization`). When such equivariant
trivializations exist around every point of `Q`, `φ` is a global covering map
(`IsCoveringMap.of_equivariant_trivialization`).

## Main results

* `IsCoveringMap.isCoveringMapOn_of_equivariant_trivialization`: an equivariant map between
  bundles along a covering map `ρ : G → H` is a covering map over the overlap of equivariant
  trivializations.
* `IsCoveringMap.of_equivariant_trivialization`: an equivariant map between locally equivariantly
  trivialized bundles along a covering map `ρ : G → H` is a covering map.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (morphisms of principal bundles).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, Part I, §2
  (bundle maps in local trivializations).
-/

public section

open Bundle MulOpposite Set Topology

namespace IsCoveringMap

variable {B P Q G H : Type*}
  [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace G] [TopologicalSpace H]
  [MulOneClass G] [Group H] [IsTopologicalGroup H]
  [SMul Gᵐᵒᵖ P] [SMul Hᵐᵒᵖ Q]
  {projP : P → B} {projQ : Q → B} {φ : P → Q} {ρ : G → H}

/-- Over the overlap of equivariant trivializations `e` and `t`, a map `φ : P → Q` over `B` that
is equivariant along a covering map `ρ : G → H` is a covering map on `projQ ⁻¹' (e.baseSet ∩
t.baseSet)`. -/
theorem isCoveringMapOn_of_equivariant_trivialization (hρ : IsCoveringMap ρ)
    (e : Trivialization G projP) (t : Trivialization H projQ)
    (hφ : ContinuousOn φ (projP ⁻¹' (e.baseSet ∩ t.baseSet)))
    (hproj : ∀ p, projQ (φ p) = projP p)
    (hprojP_smul : ∀ (g : G) (p : P), projP (op g • p) = projP p)
    (hequiv : ∀ (g : G) (p : P), φ (op g • p) = op (ρ g) • φ p)
    (he : ∀ (g : G) (p : P), projP p ∈ e.baseSet → (e (op g • p)).2 = (e p).2 * g)
    (ht : ∀ (h : H) (q : Q), projQ q ∈ t.baseSet → (t (op h • q)).2 = (t q).2 * h) :
    IsCoveringMapOn φ (projQ ⁻¹' (e.baseSet ∩ t.baseSet)) := by
  let W : Set B := e.baseSet ∩ t.baseSet
  have hW : IsOpen W := e.open_baseSet.inter t.open_baseSet
  have hWe : W ⊆ e.baseSet := inter_subset_left
  have hWt : W ⊆ t.baseSet := inter_subset_right
  let V : Set Q := projQ ⁻¹' W
  have hV : IsOpen V := by
    have hV_eq : V = t.source ∩ projQ ⁻¹' W :=
      (inter_eq_right (s := t.source) (t := V) |>.2 fun _ hq ↦ t.mem_source.2 hq.2).symm
    rw [hV_eq]
    exact t.continuousOn_proj.isOpen_inter_preimage t.open_source hW
  have hpreV_eq : φ ⁻¹' V = projP ⁻¹' W := by
    ext p
    simp [V, hproj p]
  have hpreV : IsOpen (φ ⁻¹' V) := by
    have hpre_eq : projP ⁻¹' W = e.source ∩ projP ⁻¹' W :=
      (inter_eq_right (s := e.source) (t := projP ⁻¹' W) |>.2 fun _ hp ↦ e.mem_source.2 hp.1).symm
    rw [hpreV_eq, hpre_eq]
    exact e.continuousOn_proj.isOpen_inter_preimage e.open_source hW
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage V hV hpreV ?_
  have hset_coe : ∀ {s₁ s₂ : Set P} (h : s₁ = s₂) (p : s₁), (Homeomorph.setCongr h p : P) = p.1 :=
    fun h _ ↦ by cases h; rfl
  let hDom : (φ ⁻¹' V) ≃ₜ W × G :=
    (Homeomorph.setCongr hpreV_eq).trans (e.preimageHomeomorph hWe)
  let hCod : V ≃ₜ W × H := t.preimageHomeomorph hWt
  -- The local unit section `σ` of `e` maps via `t ∘ φ` to a continuous shift `c : W → H`.
  let σ : W → P := fun y ↦ e.toOpenPartialHomeomorph.symm (y.1, 1)
  have hσ_cont : Continuous σ :=
    e.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      fun y ↦ e.mem_target.2 y.2.1
  have hσ_proj (y : W) : projP (σ y) = y.1 := e.proj_symm_apply' y.2.1
  let c : W → H := fun y ↦ (t (φ (σ y))).2
  have hc_cont : Continuous c :=
    continuous_snd.comp <| t.continuousOn_toFun.comp_continuous
      (hφ.comp_continuous hσ_cont fun y ↦ by rw [mem_preimage, hσ_proj]; exact y.2)
      fun y ↦ by rw [t.mem_source, hproj, hσ_proj]; exact y.2.2
  let shift : W × H ≃ₜ W × H :=
    { toFun yh := (yh.1, c yh.1 * yh.2)
      invFun yh := (yh.1, (c yh.1)⁻¹ * yh.2)
      left_inv yh := Prod.ext rfl (inv_mul_cancel_left (c yh.1) yh.2)
      right_inv yh := Prod.ext rfl (mul_inv_cancel_left (c yh.1) yh.2)
      continuous_toFun :=
        continuous_fst.prodMk ((hc_cont.comp continuous_fst).mul continuous_snd)
      continuous_invFun :=
        continuous_fst.prodMk ((hc_cont.comp continuous_fst).inv.mul continuous_snd) }
  have hlocal : V.restrictPreimage φ = hCod.symm ∘ shift ∘ Prod.map id ρ ∘ hDom := by
    funext p
    apply hCod.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    have hpW : projP p.1 ∈ W := by simpa only [hpreV_eq, mem_preimage] using p.2
    let y : W := ⟨projP p.1, hpW⟩
    let g : G := (e p.1).2
    have hDom_p : hDom p = (y, g) := by
      rw [Homeomorph.trans_apply, e.preimageHomeomorph_apply hWe]
      exact Prod.ext (Subtype.ext (congrArg projP (hset_coe hpreV_eq p)))
        (congrArg (fun x ↦ (e x).2) (hset_coe hpreV_eq p))
    rw [hDom_p, Prod.map_apply, id_eq]
    have hp_eq : p.1 = op g • σ y := by
      have hσ_mem : projP (σ y) ∈ e.baseSet := (hσ_proj y).symm ▸ hpW.1
      have hsrc₁ : p.1 ∈ e.source := e.mem_source.2 hpW.1
      have hsrc₂ : op g • σ y ∈ e.source := e.mem_source.2 (by rw [hprojP_smul]; exact hσ_mem)
      refine e.injOn hsrc₁ hsrc₂ (Prod.ext ?_ ?_)
      · rw [e.coe_coe, e.coe_fst hsrc₁, e.coe_fst hsrc₂, hprojP_smul, hσ_proj]
      · rw [e.coe_coe, he g (σ y) hσ_mem,
          congrArg Prod.snd (e.apply_symm_apply' hpW.1), one_mul]
    have hq_mem : projQ (φ (σ y)) ∈ t.baseSet := by
      rw [hproj, hσ_proj]
      exact hpW.2
    rw [t.preimageHomeomorph_apply hWt]
    simp only [Set.restrictPreimage_coe, shift, c, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
      Prod.mk.injEq]
    refine ⟨Subtype.ext (hproj p.1), ?_⟩
    rw [hp_eq, hequiv, ht (ρ g) (φ (σ y)) hq_mem]
  rw [hlocal]
  exact ((((IsCoveringMap.id.prodMap hρ).homeomorph_comp shift).homeomorph_comp
    hCod.symm).comp_homeomorph hDom)

/-- **An equivariant bundle map along a covering map is a covering map.** If `φ : P → Q` covers
the identity of `B` equivariantly along a covering map `ρ : G → H` into a topological group `H`,
and around every point of `Q` both bundles admit equivariant local trivializations, then `φ` is a
covering map. -/
theorem of_equivariant_trivialization (hρ : IsCoveringMap ρ)
    (hφ : Continuous φ)
    (hproj : ∀ p, projQ (φ p) = projP p)
    (hprojP_smul : ∀ (g : G) (p : P), projP (op g • p) = projP p)
    (hequiv : ∀ (g : G) (p : P), φ (op g • p) = op (ρ g) • φ p)
    (hloc : ∀ q₀ : Q,
      ∃ (e : Trivialization G projP) (t : Trivialization H projQ),
        projQ q₀ ∈ e.baseSet ∧ projQ q₀ ∈ t.baseSet ∧
        (∀ (g : G) (p : P), projP p ∈ e.baseSet → (e (op g • p)).2 = (e p).2 * g) ∧
        (∀ (h : H) (q : Q), projQ q ∈ t.baseSet → (t (op h • q)).2 = (t q).2 * h)) :
    IsCoveringMap φ := fun q₀ ↦ by
  obtain ⟨e, t, he_mem, ht_mem, he, ht⟩ := hloc q₀
  exact hρ.isCoveringMapOn_of_equivariant_trivialization e t hφ.continuousOn hproj hprojP_smul
    hequiv he ht q₀ ⟨he_mem, ht_mem⟩

end IsCoveringMap
