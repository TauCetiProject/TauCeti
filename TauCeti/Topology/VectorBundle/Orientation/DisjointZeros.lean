/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Disjoint
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# Euler classes from sections with disjoint zero sets

Let `E₁`, `E₂` and `E₃` be oriented real vector bundles of rank `n + 1` over a base `B`, with
continuous sections `s₁`, `s₂` and `s₃`. Suppose that the zeros of `s₁` and `s₂` lie in disjoint
closed sets `Z₁` and `Z₂`, and that near each `Zᵢ` the section `s₃` *is* `sᵢ`: off `Z₂` an
orientation-preserving fibrewise isomorphism `E₁ ≃ E₃` carries `s₁` to `s₃`, and off `Z₁` one
`E₂ ≃ E₃` carries `s₂` to `s₃`. Then

`e(E₃) = e(E₁) + e(E₂)`

(`TauCeti.VectorBundleOrientation.eulerClass_eq_add_of_disjoint`). This is the localization of the
Euler class at the zeros of a section: the Euler class of `E` is the image of the relative class
`s^* U ∈ Hⁿ⁺¹(B, B ∖ Z)` of a section `s` nonzero off `Z`
(`TauCeti.VectorBundleOrientation.eulerClass_eq_singularCohomologyπ_thomPairMapOfNeZero`), and this
class only depends on the oriented bundle and the section near `Z`.

The motivating instance is the tensor product of complex lines. If `s₁` and `s₂` are sections of
complex lines `L₁` and `L₂` with disjoint zero sets, then off `Z₂` the map `v ↦ v ⊗ s₂` is a
complex-linear isomorphism `L₁ ≃ L₁ ⊗ L₂` carrying `s₁` to `s₁ ⊗ s₂`, and symmetrically off `Z₁`;
so the theorem gives `c₁(L₁ ⊗ L₂) = c₁(L₁) + c₁(L₂)` for lines admitting such sections.

The proof has two steps.

* **Locality**
  (`TauCeti.VectorBundleOrientation.singularCohomologyMap_interPairMapOfSubset_thomClass`).
  On a set `V` where a fibrewise isomorphism `φ : E₁ ≃ E₃` carries `s₁` to `s₃`, the relative
  classes `s₁^* U₁` and `s₃^* U₃` have the same restriction to `(V, V ∖ Z₁)`. The restriction of
  `s₁` is a section of the pullback `E₁|_V`, along which `U₁` pulls back to the Thom class of
  `E₁|_V` (`TauCeti.VectorBundleOrientation.singularCohomologyMap_pullbackThomPairMap_thomClass`),
  and `φ` pulls `U₃` back to the same class
  (`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass`).
* **Splitting.** Since `Z₁` and `Z₂` are disjoint and closed, a class of
  `Hⁿ⁺¹(B, B ∖ (Z₁ ∪ Z₂))` which agrees with `s₁^* U₁` off `Z₂` and with `s₂^* U₂` off `Z₁` is the
  sum of their restrictions (`TopCat.eq_singularCohomologyComplRestrict_add_of_disjoint`). Mapping
  to `Hⁿ⁺¹(B)` gives the sum of the Euler classes.

## Main results

* `TauCeti.VectorBundleOrientation.singularCohomologyMap_interPairMapOfSubset_thomClass`: locality
  of the relative Euler class of a section.
* `TauCeti.VectorBundleOrientation.eulerClass_eq_add_of_disjoint`: `e(E₃) = e(E₁) + e(E₂)` for
  sections with disjoint zero sets.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §12 (the Euler class as the pull-back of the Thom class along a section).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §6 and §11 (localization of the Euler class at the zeros of a section).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

universe w

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {n : ℕ}
  {F₁ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] {E₁ : B → Type w}
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  (o₁ : VectorBundleOrientation F₁ E₁ (Fin (n + 1))) (hF₁ : finrank ℝ F₁ = n + 1)
  {F₃ : Type w} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {E₃ : B → Type w}
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ b, AddCommMonoid (E₃ b)] [∀ b, Module ℝ (E₃ b)]
  [∀ b, TopologicalSpace (E₃ b)] [FiberBundle F₃ E₃] [VectorBundle ℝ F₃ E₃]
  (o₃ : VectorBundleOrientation F₃ E₃ (Fin (n + 1))) (hF₃ : finrank ℝ F₃ = n + 1)

/-- **The relative Euler class of a section is local.** Let `s₁` and `s₃` be continuous sections of
oriented bundles `E₁` and `E₃`, nonzero off `Z₁` and off `Z₃`. On a set `V` with `V ∩ Z₃ ⊆ Z₁`,
let `φ b : E₁ b ≃ E₃ b` be orientation-preserving isomorphisms, continuous on the total space over
`V`, carrying `s₁` to `s₃`. Then the relative classes `s₁^* U₁ ∈ Hⁿ⁺¹(B, B ∖ Z₁)` and
`s₃^* U₃ ∈ Hⁿ⁺¹(B, B ∖ Z₃)` have the same restriction to the pair `(V, V ∖ Z₁)`. -/
theorem singularCohomologyMap_interPairMapOfSubset_thomClass {s₁ : ∀ b, E₁ b}
    (hs₁ : Continuous fun b ↦ TotalSpace.mk' F₁ b (s₁ b)) {Z₁ : Set B} (hZ₁ : ∀ b ∉ Z₁, s₁ b ≠ 0)
    {s₃ : ∀ b, E₃ b} (hs₃ : Continuous fun b ↦ TotalSpace.mk' F₃ b (s₃ b)) {Z₃ : Set B}
    (hZ₃ : ∀ b ∉ Z₃, s₃ b ≠ 0) {V : Set B} (hV : V ∩ Z₁ᶜ ⊆ Z₃ᶜ) {φ : ∀ b, E₁ b ≃L[ℝ] E₃ b}
    (hφ : ContinuousOn (fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ v.proj (φ v.proj v.snd))
      (π F₁ E₁ ⁻¹' V))
    (ho : ∀ b ∈ V, Orientation.map (Fin (n + 1)) (φ b).toLinearEquiv (o₁ b) = o₃ b)
    (hs : ∀ b ∈ V, φ b (s₁ b) = s₃ b) :
    TopPair.singularCohomologyMap
        (TopPair.interPairMapOfSubset (X := TopCat.of B) (B := Z₁ᶜ) hV) (n + 1)
        (TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hs₃⟩ hZ₃) (n + 1)
          (o₃.thomClass hF₃)) =
      TopPair.singularCohomologyMap (TopPair.excisionMap (X := TopCat.of B) V Z₁ᶜ) (n + 1)
        (TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hs₁⟩ hZ₁) (n + 1)
          (o₁.thomClass hF₁)) := by
  -- Restrict `E₁` to `V` as the pullback along the inclusion `g`.
  let g : C(V, B) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hφ' : Continuous fun v : TotalSpace F₁ ((⇑g) *ᵖ E₁) ↦
      TotalSpace.mk' F₃ (g v.proj) (φ (g v.proj) v.snd) :=
    hφ.comp_continuous (Pullback.continuous_lift F₁ E₁ g) fun v ↦ v.proj.property
  -- The restriction of `s₁` to `V`, as a section of the pullback.
  have hσ : Continuous fun b : V ↦ TotalSpace.mk' F₁ (E := (⇑g) *ᵖ E₁) b (s₁ b) :=
    (inducing_pullbackTotalSpaceEmbedding F₁ E₁ g).continuous_iff.2
      (continuous_id.prodMk (hs₁.comp continuous_subtypeVal))
  have hσ₀ : ∀ b ∉ (⇑g ⁻¹' Z₁), (TotalSpace.mk' F₁ (E := (⇑g) *ᵖ E₁) b (s₁ b)).snd ≠ 0 :=
    fun b hb ↦ hZ₁ b hb
  -- The pullback `E₁|_V` maps to `E₁` by the identity of the fibres.
  have hι : Continuous fun v : TotalSpace F₁ ((⇑g) *ᵖ E₁) ↦
      TotalSpace.mk' F₁ (g v.proj) (ContinuousLinearEquiv.refl ℝ (E₁ (g v.proj)) v.snd) :=
    Pullback.continuous_lift F₁ E₁ g
  -- The inclusions of `(V, V ∖ Z₁)` are the maps of pairs induced by `g`.
  have hinc {C : Set B} (hC : V ∩ Z₁ᶜ ⊆ C) : TopPair.interPairMapOfSubset (X := TopCat.of B) hC =
      TopPair.ofSubsetMap (TopCat.ofHom g) fun b hb ↦ hC ⟨b.property, hb⟩ :=
    TopPair.hom_ext_of_fst _
      ((TopPair.interPairMapOfSubset_fst hC).trans (TopPair.ofSubsetMap_fst _ _).symm)
  -- Both relative classes are pulled back from the Thom class of `E₁|_V` along that section.
  have h₁ : TopPair.excisionMap (X := TopCat.of B) V Z₁ᶜ ≫ thomPairMapOfNeZero ⟨_, hs₁⟩ hZ₁ =
      thomPairMapOfNeZero ⟨_, hσ⟩ hσ₀ ≫
        thomPairMapOfFiberwise (g := g) (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (E₁ (g b)))
          hι := by
    rw [← TopPair.interPairMapOfSubset_eq_excisionMap, hinc]
    exact (ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq ⟨_, hs₁⟩ hZ₁ g _ rfl hσ₀).trans
      (thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_comp_eq ⟨_, hσ⟩ hσ₀ hι
        (ContinuousMap.ext fun b ↦ congrArg (TotalSpace.mk' F₁ b.val)
          (ContinuousLinearEquiv.refl_apply ℝ (E₁ b.val) _)) _).symm
  have h₃ : TopPair.interPairMapOfSubset (X := TopCat.of B) (B := Z₁ᶜ) hV ≫
      thomPairMapOfNeZero ⟨_, hs₃⟩ hZ₃ =
      thomPairMapOfNeZero ⟨_, hσ⟩ hσ₀ ≫ thomPairMapOfFiberwise (φ := fun b ↦ φ (g b)) hφ' := by
    rw [hinc]
    exact (ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq ⟨_, hs₃⟩ hZ₃ g _ rfl
      fun b hb ↦ hZ₃ b (hV ⟨b.property, hb⟩)).trans
      (thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_comp_eq ⟨_, hσ⟩ hσ₀ hφ'
        (ContinuousMap.ext fun b ↦ congrArg (TotalSpace.mk' F₃ b.val) (hs b.val b.property)) _).symm
  have hU₁ := o₁.singularCohomologyMap_thomPairMapOfFiberwise_thomClass hF₁ (o₁.pullback g) hF₁
    (g := g) (φ := fun b ↦ ContinuousLinearEquiv.refl ℝ (E₁ (g b))) hι fun b ↦ by
      rw [pullback_apply]
      exact DFunLike.congr_fun (Orientation.map_refl (R := ℝ) (M := E₁ (g b)) (Fin (n + 1))) _
  -- Term-mode steps: `rw` with the composition law has to guess the intermediate pairs.
  refine (TopPair.singularCohomologyMap_comp_apply _ _ _ _).symm.trans <|
    (congrArg (fun f ↦ TopPair.singularCohomologyMap f (n + 1) (o₃.thomClass hF₃)) h₃).trans ?_
  refine (TopPair.singularCohomologyMap_comp_apply _ _ _ _).trans ?_
  refine (congrArg (TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hσ⟩ hσ₀) (n + 1))
    ((o₃.singularCohomologyMap_thomPairMapOfFiberwise_thomClass hF₃ (o₁.pullback g) hF₁ hφ'
      fun b ↦ by rw [pullback_apply]; exact ho b b.property).trans hU₁.symm)).trans ?_
  refine (TopPair.singularCohomologyMap_comp_apply _ _ _ _).symm.trans <|
    (congrArg (fun f ↦ TopPair.singularCohomologyMap f (n + 1) (o₁.thomClass hF₁)) h₁.symm).trans ?_
  exact TopPair.singularCohomologyMap_comp_apply _ _ _ _

variable {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {E₂ : B → Type w}
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  (o₂ : VectorBundleOrientation F₂ E₂ (Fin (n + 1))) (hF₂ : finrank ℝ F₂ = n + 1)

/-- **Euler classes from sections with disjoint zero sets.** Let `s₁`, `s₂` and `s₃` be continuous
sections of oriented bundles `E₁`, `E₂` and `E₃` of rank `n + 1`, with `s₁` nonzero off `Z₁` and
`s₂` nonzero off `Z₂`, for disjoint closed sets `Z₁` and `Z₂`. Suppose that off `Z₂`
orientation-preserving fibrewise isomorphisms `φ₁ b : E₁ b ≃ E₃ b`, continuous on the total space
there, carry `s₁` to `s₃`, and that off `Z₁` such isomorphisms `φ₂ b : E₂ b ≃ E₃ b` carry `s₂` to
`s₃`. Then `e(E₃) = e(E₁) + e(E₂)`. -/
theorem eulerClass_eq_add_of_disjoint {Z₁ Z₂ : Set B} (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (hZ : Disjoint Z₁ Z₂) {s₁ : ∀ b, E₁ b} (hs₁ : Continuous fun b ↦ TotalSpace.mk' F₁ b (s₁ b))
    (hs₁₀ : ∀ b ∉ Z₁, s₁ b ≠ 0) {s₂ : ∀ b, E₂ b}
    (hs₂ : Continuous fun b ↦ TotalSpace.mk' F₂ b (s₂ b)) (hs₂₀ : ∀ b ∉ Z₂, s₂ b ≠ 0)
    {s₃ : ∀ b, E₃ b} (hs₃ : Continuous fun b ↦ TotalSpace.mk' F₃ b (s₃ b))
    {φ₁ : ∀ b, E₁ b ≃L[ℝ] E₃ b}
    (hφ₁ : ContinuousOn (fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ v.proj (φ₁ v.proj v.snd))
      (π F₁ E₁ ⁻¹' Z₂ᶜ))
    (ho₁ : ∀ b ∉ Z₂, Orientation.map (Fin (n + 1)) (φ₁ b).toLinearEquiv (o₁ b) = o₃ b)
    (hs₁₃ : ∀ b ∉ Z₂, φ₁ b (s₁ b) = s₃ b) {φ₂ : ∀ b, E₂ b ≃L[ℝ] E₃ b}
    (hφ₂ : ContinuousOn (fun v : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₃ v.proj (φ₂ v.proj v.snd))
      (π F₂ E₂ ⁻¹' Z₁ᶜ))
    (ho₂ : ∀ b ∉ Z₁, Orientation.map (Fin (n + 1)) (φ₂ b).toLinearEquiv (o₂ b) = o₃ b)
    (hs₂₃ : ∀ b ∉ Z₁, φ₂ b (s₂ b) = s₃ b) :
    o₃.eulerClass hF₃ = o₁.eulerClass hF₁ + o₂.eulerClass hF₂ := by
  -- Off `Z₁ ∪ Z₂` the section `s₃` is the image of `s₁ ≠ 0` under `φ₁`.
  have hs₃₀ : ∀ b ∉ Z₁ ∪ Z₂, s₃ b ≠ 0 := fun b hb ↦ hs₁₃ b (fun h ↦ hb (Or.inr h)) ▸
    (φ₁ b).toLinearEquiv.map_ne_zero_iff.2 (hs₁₀ b fun h ↦ hb (Or.inl h))
  -- Off `Z₂` the class of `s₃` agrees with that of `s₁`, and off `Z₁` with that of `s₂`.
  have hV₁ : (Z₂ᶜ ∩ Z₁ᶜ : Set B) ⊆ (Z₁ ∪ Z₂)ᶜ :=
    ((Set.inter_comm Z₂ᶜ Z₁ᶜ).trans (Set.compl_union Z₁ Z₂).symm).subset
  have hV₂ : (Z₁ᶜ ∩ Z₂ᶜ : Set B) ⊆ (Z₁ ∪ Z₂)ᶜ := (Set.compl_union Z₁ Z₂).symm.subset
  have h₁ := o₁.singularCohomologyMap_interPairMapOfSubset_thomClass hF₁ o₃ hF₃ hs₁ hs₁₀ hs₃ hs₃₀
    hV₁ hφ₁ (fun b hb ↦ ho₁ b hb) fun b hb ↦ hs₁₃ b hb
  have h₂ := o₂.singularCohomologyMap_interPairMapOfSubset_thomClass hF₂ o₃ hF₃ hs₂ hs₂₀ hs₃ hs₃₀
    hV₂ hφ₂ (fun b hb ↦ ho₂ b hb) fun b hb ↦ hs₂₃ b hb
  have hsplit := TopCat.eq_singularCohomologyComplRestrict_add_of_disjoint (X := TopCat.of B)
    hZ₁ hZ₂ hZ _ _ _ h₁ h₂
  -- Each Euler class is the image in `Hⁿ⁺¹(B)` of the relative class of its section.
  rw [o₁.eulerClass_eq_singularCohomologyπ_thomPairMapOfNeZero hF₁ hs₁ hs₁₀,
    o₂.eulerClass_eq_singularCohomologyπ_thomPairMapOfNeZero hF₂ hs₂ hs₂₀,
    o₃.eulerClass_eq_singularCohomologyπ_thomPairMapOfNeZero hF₃ hs₃ hs₃₀, hsplit, map_add,
    TopCat.singularCohomologyπ_singularCohomologyComplRestrict_apply,
    TopCat.singularCohomologyπ_singularCohomologyComplRestrict_apply]
  -- The two sides differ only in reading subsets of `B` as subsets of `TopCat.of B`.
  rfl

end TauCeti.VectorBundleOrientation
