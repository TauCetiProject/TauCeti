/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Germs of partial diffeomorphisms along a subset

Two maps out of a topological space have the same **germ along a subset `S`** when they agree
after shrinking to a neighbourhood of the whole of `S`, that is, when they are eventually equal
for the neighbourhood filter `𝓝ˢ S`. For `S` a single point this is the usual germ at a point; for
`S` the image of a submanifold it is the notion of germ in the neighbourhood theorems of
symplectic and contact geometry, where a map is only constructed on some neighbourhood of `S` and
all statements are insensitive to shrinking that neighbourhood.

This file shows that the operations on partial diffeomorphisms descend to germs along subsets of
their sources.

* **Inverse.** Near a subset `S` of the source, `Φ⁻¹ ∘ Φ` is the identity, and near a subset of
  the target `Φ ∘ Φ⁻¹` is
  (`PartialDiffeomorph.symm_comp_eventuallyEq_id`, `PartialDiffeomorph.comp_symm_eventuallyEq_id`).
  The germ of `Φ⁻¹` along `Φ(S)` depends only on the germ of `Φ` along `S`
  (`PartialDiffeomorph.symm_eventuallyEq_nhdsSet_image`).
* **Composition.** The germ of `Ψ ∘ Φ` along `S` depends only on the germ of `Φ` along `S` and the
  germ of `Ψ` along `Φ(S)` (`PartialDiffeomorph.trans_eventuallyEq_nhdsSet`), because `Φ` maps the
  neighbourhoods of `S` to those of `Φ(S)` (`PartialDiffeomorph.tendsto_nhdsSet_image`).
* **Comparison.** Two partial diffeomorphisms `Φ₁` and `Φ₂` which agree at every point of a subset
  `S` of both sources differ along `S` by the comparison `Θ = Φ₂⁻¹ ∘ Φ₁` (`Φ₁.trans Φ₂.symm`): its
  source contains `S` (`PartialDiffeomorph.subset_trans_symm_source`), it fixes every point of `S`
  (`PartialDiffeomorph.trans_symm_apply_eq_self`), and `Φ₂ ∘ Θ = Φ₁` on its whole source
  (`PartialDiffeomorph.apply_trans_symm_apply`), so `Φ₁` and `Φ₂ ∘ Θ` have the same germ along `S`
  (`PartialDiffeomorph.eventuallyEq_comp_trans_symm`). When the differentials of `Φ₁` and `Φ₂`
  agree along `S` as well, `Θ` has the identity as differential there
  (`PartialDiffeomorph.mfderiv_trans_symm_apply`).

The restriction to an open set containing `S` (`PartialDiffeomorph.restrOpen`) has the same
underlying map, hence the same germ along `S`.
-/

public section

open Filter Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : WithTop ℕ∞} {S : Set M}

namespace PartialDiffeomorph

/-! ### Inverses and composites of germs -/

/-- A partial diffeomorphism maps the neighbourhoods of a subset `S` of its source to those of
`Φ(S)`. -/
theorem tendsto_nhdsSet_image (Φ : PartialDiffeomorph I J M N n) (hS : S ⊆ Φ.source) :
    Tendsto Φ (𝓝ˢ S) (𝓝ˢ (Φ '' S)) :=
  Φ.contMDiffOn.continuousOn.tendsto_nhdsSet (Φ.open_source.mem_nhdsSet.2 hS) (mapsTo_image Φ S)

/-- **The inverse undoes a partial diffeomorphism on germs.** Near a subset `S` of the source,
`Φ⁻¹ ∘ Φ` is the identity. -/
theorem symm_comp_eventuallyEq_id (Φ : PartialDiffeomorph I J M N n) (hS : S ⊆ Φ.source) :
    ⇑Φ.symm ∘ Φ =ᶠ[𝓝ˢ S] id :=
  mem_of_superset (Φ.open_source.mem_nhdsSet.2 hS) fun _ hx ↦ Φ.left_inv hx

/-- **A partial diffeomorphism undoes its inverse on germs.** Near a subset `T` of the target,
`Φ ∘ Φ⁻¹` is the identity. -/
theorem comp_symm_eventuallyEq_id (Φ : PartialDiffeomorph I J M N n) {T : Set N}
    (hT : T ⊆ Φ.target) : ⇑Φ ∘ Φ.symm =ᶠ[𝓝ˢ T] id :=
  Φ.symm.symm_comp_eventuallyEq_id hT

/-- **The germ of the inverse depends only on the germ.** If two partial diffeomorphisms agree
near a subset `S` of both sources, their inverses agree near `Φ(S)`. -/
theorem symm_eventuallyEq_nhdsSet_image {Φ Ψ : PartialDiffeomorph I J M N n}
    (h : ⇑Φ =ᶠ[𝓝ˢ S] Ψ) (hΦ : S ⊆ Φ.source) (hΨ : S ⊆ Ψ.source) :
    ⇑Φ.symm =ᶠ[𝓝ˢ (Φ '' S)] Ψ.symm := by
  have hT : Φ '' S ⊆ Φ.target := image_subset_iff.2 fun x hx ↦ Φ.map_source (hΦ hx)
  -- `Φ⁻¹` maps the neighbourhoods of `Φ(S)` to those of `S`.
  have hsymm : Tendsto Φ.symm (𝓝ˢ (Φ '' S)) (𝓝ˢ S) :=
    Φ.symm.contMDiffOn.continuousOn.tendsto_nhdsSet (Φ.open_target.mem_nhdsSet.2 hT)
      (by rintro _ ⟨x, hx, rfl⟩; rwa [symm_toPartialEquiv, Φ.left_inv (hΦ hx)])
  filter_upwards [hsymm.eventually (h.and (Ψ.open_source.mem_nhdsSet.2 hΨ)),
    Φ.open_target.mem_nhdsSet.2 hT] with y ⟨hy, hyΨ⟩ hyT
  -- At `y = Φ x`, both inverses return `x`, since `Ψ x = Φ x = y`.
  have hΦy : Φ (Φ.symm y) = y := Φ.right_inv hyT
  calc Φ.symm y = Ψ.symm (Ψ (Φ.symm y)) := (Ψ.left_inv hyΨ).symm
    _ = Ψ.symm y := by rw [← hy, hΦy]

/-- **The germ of a composite depends only on the germs of its factors.** If `Φ` and `Φ'` agree
near a subset `S` of the source of `Φ`, and `Ψ` and `Ψ'` agree near `Φ(S)`, then `Ψ ∘ Φ` and
`Ψ' ∘ Φ'` agree near `S`. -/
theorem trans_eventuallyEq_nhdsSet {Φ Φ' : PartialDiffeomorph I J M N n}
    {Ψ Ψ' : PartialDiffeomorph J K N P n} (hΦ : ⇑Φ =ᶠ[𝓝ˢ S] Φ') (hΨ : ⇑Ψ =ᶠ[𝓝ˢ (Φ '' S)] Ψ')
    (hS : S ⊆ Φ.source) : ⇑(Φ.trans Ψ) =ᶠ[𝓝ˢ S] Φ'.trans Ψ' := by
  rw [coe_trans, coe_trans]
  exact (hΨ.comp_tendsto (Φ.tendsto_nhdsSet_image hS)).trans (hΦ.fun_comp Ψ')

/-! ### Comparing two partial diffeomorphisms which agree along a subset -/

section Comparison

variable {Φ₁ Φ₂ : PartialDiffeomorph I J M N n} {x : M}

/-- If `Φ₁` and `Φ₂` agree at a point `x` of both sources, then `x` lies in the source of the
comparison `Φ₂⁻¹ ∘ Φ₁`. -/
theorem mem_trans_symm_source (h₁ : x ∈ Φ₁.source) (h₂ : x ∈ Φ₂.source) (h : Φ₁ x = Φ₂ x) :
    x ∈ (Φ₁.trans Φ₂.symm).source := by
  rw [trans_source]
  exact ⟨h₁, by rw [mem_preimage, h]; exact Φ₂.map_source h₂⟩

/-- If `Φ₁` and `Φ₂` agree on a subset `S` of both sources, then `S` lies in the source of the
comparison `Φ₂⁻¹ ∘ Φ₁`. -/
theorem subset_trans_symm_source (h₁ : S ⊆ Φ₁.source) (h₂ : S ⊆ Φ₂.source) (h : EqOn Φ₁ Φ₂ S) :
    S ⊆ (Φ₁.trans Φ₂.symm).source :=
  fun _ hx ↦ mem_trans_symm_source (h₁ hx) (h₂ hx) (h hx)

/-- If `Φ₁` and `Φ₂` agree at a point `x` of the source of `Φ₂`, the comparison `Φ₂⁻¹ ∘ Φ₁`
fixes `x`. -/
theorem trans_symm_apply_eq_self (h₂ : x ∈ Φ₂.source) (h : Φ₁ x = Φ₂ x) :
    Φ₁.trans Φ₂.symm x = x := by
  rw [coe_trans, Function.comp_apply, h, symm_toPartialEquiv]
  exact Φ₂.left_inv h₂

/-- On its source, the comparison `Θ = Φ₂⁻¹ ∘ Φ₁` satisfies `Φ₂ ∘ Θ = Φ₁`. -/
theorem apply_trans_symm_apply (hx : x ∈ (Φ₁.trans Φ₂.symm).source) :
    Φ₂ (Φ₁.trans Φ₂.symm x) = Φ₁ x := by
  rw [trans_source] at hx
  rw [coe_trans, Function.comp_apply, symm_toPartialEquiv]
  exact Φ₂.right_inv hx.2

/-- If `Φ₁` and `Φ₂` agree on a subset `S` of both sources, then `Φ₁` and `Φ₂ ∘ Θ` have the same
germ along `S`, for the comparison `Θ = Φ₂⁻¹ ∘ Φ₁`. -/
theorem eventuallyEq_comp_trans_symm (h₁ : S ⊆ Φ₁.source) (h₂ : S ⊆ Φ₂.source)
    (h : EqOn Φ₁ Φ₂ S) : ⇑Φ₁ =ᶠ[𝓝ˢ S] Φ₂ ∘ Φ₁.trans Φ₂.symm :=
  mem_of_superset ((Φ₁.trans Φ₂.symm).open_source.mem_nhdsSet.2 (subset_trans_symm_source h₁ h₂ h))
    fun _ hx ↦ (apply_trans_symm_apply hx).symm

end Comparison

end PartialDiffeomorph
