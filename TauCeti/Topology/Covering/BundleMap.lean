/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.FiberBundle.Trivialization
import TauCeti.Topology.Algebra.Group.Shear
import TauCeti.Topology.Covering.Homeomorph
import TauCeti.Topology.Covering.Prod
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Topology.Homeomorph.SetCongr

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
  have hV : IsOpen V := t.isOpen_preimage hW hWt
  have hpreV_eq : φ ⁻¹' V = projP ⁻¹' W := by ext p; simp [V, hproj p]
  have hpreV : IsOpen (φ ⁻¹' V) := hpreV_eq ▸ e.isOpen_preimage hW hWe
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage V hV hpreV ?_
  -- Trivialize `φ ⁻¹' V` as `W × G` and `V` as `W × H`.
  let hDom : (φ ⁻¹' V) ≃ₜ W × G :=
    (Homeomorph.setCongr hpreV_eq).trans (e.preimageHomeomorph hWe)
  let hCod : V ≃ₜ W × H := t.preimageHomeomorph hWt
  -- The local unit section `σ` of `e` maps via `t ∘ φ` to a continuous shear `c : W → H`.
  let σ : W → P := fun y ↦ e.toOpenPartialHomeomorph.symm (y.val, 1)
  have hσ_cont : Continuous σ :=
    e.continuousOn_symm_prodMk_left.comp_continuous continuous_subtypeVal fun y ↦ y.property.1
  have hσ_proj (y : W) : projP (σ y) = y.val := e.proj_symm_apply' y.property.1
  let c : W → H := fun y ↦ (t (φ (σ y))).2
  have hc_cont : Continuous c :=
    continuous_snd.comp <| t.continuousOn_toFun.comp_continuous
      (hφ.comp_continuous hσ_cont fun y ↦ by rw [mem_preimage, hσ_proj]; exact y.property)
      fun y ↦ by rw [t.mem_source, hproj, hσ_proj]; exact y.property.2
  let shift : W × H ≃ₜ W × H := TauCeti.prodSMulHomeomorph c hc_cont
  -- In trivialized coordinates, `φ` is `Prod.map id ρ` followed by the left-translation shear.
  have hlocal : V.restrictPreimage φ = hCod.symm ∘ shift ∘ Prod.map id ρ ∘ hDom := by
    funext p
    apply hCod.injective
    have hpW : projP p.val ∈ W := by simpa only [hpreV_eq, mem_preimage] using p.property
    let y : W := ⟨projP p.val, hpW⟩
    let g : G := (e p.val).2
    have hDom_p : hDom p = (y, g) := by simp [hDom, y, g]
    have hp_eq : p.val = op g • σ y := (e.op_snd_smul_symm_one hprojP_smul he hpW.1).symm
    have hq_mem : projQ (φ (σ y)) ∈ t.baseSet := by rw [hproj, hσ_proj]; exact hpW.2
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply, hDom_p, Prod.map_apply, id_eq,
      shift, TauCeti.prodSMulHomeomorph_apply, smul_eq_mul]
    simp only [hCod, t.preimageHomeomorph_apply hWt, Set.restrictPreimage_coe, c, Prod.mk.injEq]
    refine ⟨Subtype.ext (hproj p.val), ?_⟩
    rw [hp_eq, hequiv, ht (ρ g) (φ (σ y)) hq_mem]
  rw [hlocal]
  exact (((IsCoveringMap.id.prodMap hρ).homeomorph_comp shift).homeomorph_comp
    hCod.symm).comp_homeomorph hDom

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
