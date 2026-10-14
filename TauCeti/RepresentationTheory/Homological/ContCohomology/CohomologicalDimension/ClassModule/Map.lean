/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Extension

/-!
# Functoriality of the pro-p class-module extension

A continuous homomorphism `f : G → H` carrying a normal subgroup `V` into `W` descends to
`G / ker(V → Vᵃᵇ(p)) → H / ker(W → Wᵃᵇ(p))`. The descended map commutes with the projections
to `G/V` and `H/W`. No surjectivity of `f`, or of its restriction to `V`, is required.

In particular, a lift from a free profinite presentation to an arithmetic Galois group gives
a comparison between their class-module extensions. This comparison can detect a generating
extension class independently of a separately constructed surjection on the kernels.

The construction uses `TopologicalAbelianization.map` followed by `maximalProPQuotient.map`
to show that the extension kernels are preserved.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

namespace TauCeti

variable (p : ℕ) {G H J : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  {V : Subgroup G} {W : Subgroup H} {U : Subgroup J}
  (f : G →* H) (hf : Continuous f) (hVW : V ≤ W.comap f)

/-- The map on pro-`p` class modules induced by a continuous homomorphism
carrying `V` into `W`. -/
noncomputable def abelianizationProPMap :
    abelianizationProP p G V →* abelianizationProP p H W := by
  let r : V →* W := (f.comp V.subtype).codRestrict W
    (fun v ↦ Subgroup.mem_comap.mp (hVW v.2))
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  exact maximalProPQuotient.map (p := p) (TopologicalAbelianization.map r hr)
    (TopologicalAbelianization.continuous_map r hr)

/-- The induced map on pro-`p` class modules is continuous. -/
theorem continuous_abelianizationProPMap : Continuous (abelianizationProPMap p f hf hVW) := by
  unfold abelianizationProPMap
  exact maximalProPQuotient.continuous_map _ _

/-- The induced class-module map sends the class of `v` to the class of `f v`. -/
@[simp]
theorem abelianizationProPMap_mk (v : V) :
    abelianizationProPMap p f hf hVW (abelianizationProPMk p G V v) =
      abelianizationProPMk p H W ⟨f v, Subgroup.mem_comap.mp (hVW v.2)⟩ := by
  let r : V →* W := (f.comp V.subtype).codRestrict W
    (fun v ↦ Subgroup.mem_comap.mp (hVW v.2))
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  simpa only [abelianizationProPMap, abelianizationProPMk_apply,
    maximalProPQuotient.mk_apply, maximalProPQuotient.map_mk, r,
    MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.subtype_apply] using
    congrArg (maximalProPQuotient.mk p (TopologicalAbelianization W))
      (TopologicalAbelianization.map_mk r hr v)

/-- The identity induces the identity on a pro-`p` class module. -/
@[simp]
theorem abelianizationProPMap_id :
    abelianizationProPMap p (MonoidHom.id G) continuous_id
        (V := V) (W := V) (by simp) =
      MonoidHom.id (abelianizationProP p G V) := by
  apply (MonoidHom.cancel_right (abelianizationProPMk_surjective p G V)).mp
  ext v
  simp

/-- Composition of ambient homomorphisms induces composition on pro-`p` class modules.
The intermediate subgroup `W` must be specified when rewriting this identity. -/
theorem abelianizationProPMap_comp (g : H →* J) (hg : Continuous g)
    (hWU : W ≤ U.comap g) :
    abelianizationProPMap p (g.comp f) (hg.comp hf) (by
        intro x hx
        rw [Subgroup.mem_comap, MonoidHom.comp_apply]
        exact Subgroup.mem_comap.mp (hWU (Subgroup.mem_comap.mp (hVW hx)))) =
      (abelianizationProPMap p g hg hWU).comp
        (abelianizationProPMap p f hf hVW) := by
  apply (MonoidHom.cancel_right (abelianizationProPMk_surjective p G V)).mp
  ext v
  simp

include hf hVW in
/-- A continuous homomorphism preserving the specified subgroups also preserves the
kernels killed in their pro-`p` class-module extensions. -/
theorem abelianizationProPExtensionKernel_le_comap :
    abelianizationProPExtensionKernel p G V ≤
      (abelianizationProPExtensionKernel p H W).comap f := by
  intro x hx
  obtain ⟨hv, hvone⟩ := (mem_abelianizationProPExtensionKernel_iff p G V x).mp hx
  refine (mem_abelianizationProPExtensionKernel_iff p H W (f x)).mpr ⟨hVW hv, ?_⟩
  simpa only [hvone, map_one] using (abelianizationProPMap_mk p f hf hVW ⟨x, hv⟩).symm

variable [V.Normal] [W.Normal] [U.Normal]

/-- The continuous map on total groups of pro-`p` class-module extensions induced by a
continuous homomorphism carrying `V` into `W`. -/
noncomputable def abelianizationProPExtensionMap :
    abelianizationProPExtensionGroup p G V →ₜ* abelianizationProPExtensionGroup p H W where
  toMonoidHom := QuotientGroup.map _ _ f
    (abelianizationProPExtensionKernel_le_comap p f hf hVW)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hf)

/-- The induced total-group map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem abelianizationProPExtensionMap_mk (x : G) :
    abelianizationProPExtensionMap p f hf hVW (QuotientGroup.mk x) =
      QuotientGroup.mk (f x) :=
  (rfl)

/-- The induced total-group map is uniquely determined by its values on representatives. -/
theorem abelianizationProPExtensionMap_unique
    (φ : abelianizationProPExtensionGroup p G V →ₜ*
      abelianizationProPExtensionGroup p H W)
    (hφ : ∀ x : G, φ (QuotientGroup.mk x) = QuotientGroup.mk (f x)) :
    φ = abelianizationProPExtensionMap p f hf hVW := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact QuotientGroup.monoidHom_ext _ (MonoidHom.ext hφ)

/-- Surjectivity of an ambient homomorphism implies surjectivity on the total groups of the
class-module extensions; surjectivity on the specified subgroups is not needed. -/
theorem abelianizationProPExtensionMap_surjective (hs : Function.Surjective f) :
    Function.Surjective (abelianizationProPExtensionMap p f hf hVW) := by
  exact QuotientGroup.map_surjective_of_surjective _ _ f
    (QuotientGroup.mk_surjective.comp hs)
    (abelianizationProPExtensionKernel_le_comap p f hf hVW)

/-- The map of total groups agrees with the induced class-module map on the kernels. -/
theorem abelianizationProPExtensionMap_comp_inl :
    (abelianizationProPExtensionMap p f hf hVW).toMonoidHom.comp
        (abelianizationProPExtension p G V).inl =
      (abelianizationProPExtension p H W).inl.comp
        (abelianizationProPMap p f hf hVW) := by
  apply MonoidHom.ext
  intro a
  obtain ⟨v, rfl⟩ := abelianizationProPMk_surjective p G V a
  simp

/-- The map of total groups covers the induced map of quotient groups. -/
theorem rightHom_comp_abelianizationProPExtensionMap :
    (abelianizationProPExtension p H W).rightHom.comp
        (abelianizationProPExtensionMap p f hf hVW).toMonoidHom =
      (QuotientGroup.map V W f hVW).comp (abelianizationProPExtension p G V).rightHom := by
  apply QuotientGroup.monoidHom_ext
  ext x
  simp [abelianizationProPExtension_rightHom, QuotientGroup.mapOfLE_mk]

/-- The identity induces the identity on the total group of a class-module extension. -/
@[simp]
theorem abelianizationProPExtensionMap_id :
    abelianizationProPExtensionMap p (MonoidHom.id G) continuous_id
        (V := V) (W := V) (by simp) =
      ContinuousMonoidHom.id (abelianizationProPExtensionGroup p G V) := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  simpa only [abelianizationProPExtensionMap, ContinuousMonoidHom.id] using
    QuotientGroup.map_id (abelianizationProPExtensionKernel p G V)
      (abelianizationProPExtensionKernel_le_comap p (MonoidHom.id G) continuous_id (by simp))

/-- Composition of ambient homomorphisms induces composition on class-module extensions.
The intermediate subgroup `W` must be specified when rewriting this identity. -/
theorem abelianizationProPExtensionMap_comp (g : H →* J) (hg : Continuous g)
    (hWU : W ≤ U.comap g) :
    abelianizationProPExtensionMap p (g.comp f) (hg.comp hf) (by
        intro x hx
        rw [Subgroup.mem_comap, MonoidHom.comp_apply]
        exact Subgroup.mem_comap.mp (hWU (Subgroup.mem_comap.mp (hVW hx)))) =
      (abelianizationProPExtensionMap p g hg hWU).comp
        (abelianizationProPExtensionMap p f hf hVW) := by
  apply ContinuousMonoidHom.toMonoidHom_injective
  simpa only [abelianizationProPExtensionMap, ContinuousMonoidHom.comp] using
    (QuotientGroup.map_comp_map _ _ _ f g
      (abelianizationProPExtensionKernel_le_comap p f hf hVW)
      (abelianizationProPExtensionKernel_le_comap p g hg hWU)).symm

end TauCeti
