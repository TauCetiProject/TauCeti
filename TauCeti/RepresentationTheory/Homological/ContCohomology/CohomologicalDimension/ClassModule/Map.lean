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
  [V.Normal] [W.Normal] [U.Normal]
  (f : G →* H) (hf : Continuous f) (hVW : V ≤ W.comap f)

omit [V.Normal] [W.Normal] in
include hf hVW in
/-- A continuous homomorphism preserving the specified normal subgroups also preserves the
kernels killed in their pro-`p` class-module extensions. -/
theorem abelianizationProPExtensionKernel_le_comap :
    abelianizationProPExtensionKernel p G V ≤
      (abelianizationProPExtensionKernel p H W).comap f := by
  let r : V →* W := (f.comp V.subtype).codRestrict W (fun v ↦ hVW v.2)
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  let a := TopologicalAbelianization.map r hr
  let b := maximalProPQuotient.map (p := p) a
    (TopologicalAbelianization.continuous_map r hr)
  have hb (v : V) : b (abelianizationProPMk p G V v) =
      abelianizationProPMk p H W (r v) := by
    simp [b, a, abelianizationProPMk_apply]
  intro x hx
  obtain ⟨hv, hvone⟩ := (mem_abelianizationProPExtensionKernel_iff p G V x).mp hx
  refine (mem_abelianizationProPExtensionKernel_iff p H W (f x)).mpr ⟨hVW hv, ?_⟩
  have hr_apply (v : V) : r v = ⟨f v, hVW v.2⟩ := (rfl)
  simpa only [hr_apply, hvone, map_one] using (hb ⟨x, hv⟩).symm

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
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  exact hφ x

/-- Surjectivity of an ambient homomorphism implies surjectivity on the total groups of the
class-module extensions; surjectivity on the specified subgroups is not needed. -/
theorem abelianizationProPExtensionMap_surjective (hs : Function.Surjective f) :
    Function.Surjective (abelianizationProPExtensionMap p f hf hVW) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨QuotientGroup.mk x, abelianizationProPExtensionMap_mk p f hf hVW x⟩

/-- The map of total groups covers the induced map of quotient groups. -/
theorem abelianizationProPExtensionMap_rightHom :
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
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [abelianizationProPExtensionMap_mk]
  rfl

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
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [abelianizationProPExtensionMap_mk]
  simp

end TauCeti
