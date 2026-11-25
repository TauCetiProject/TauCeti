/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Cube
public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Homotopy.Extension.Proper.Basic
import TauCeti.Topology.Homotopy.Proper
import TauCeti.Topology.Homotopy.Trans
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper NDR pairs, products of proper cofibrations, and proper retracing

In the ordinary theory (`TauCeti.nonempty_ndrPair_iff`), closed subsets with the homotopy extension
property are characterized by Strøm's NDR data `(u, H)`. Adding properness of the deformation
`H : I × X → X` gives the exact counterpart in the proper category:

* if `r : I × X → I × X` is a proper retraction onto `{0} × X ∪ I × A`, then the deformation
  `(t, x) ↦ (r (t, x)).2` of `TauCeti.NDRPair.ofRetraction` is proper
  (`TauCeti.NDRPair.isProperMap_ofRetraction_deformation`);
* conversely, if `N : NDRPair A` has proper deformation `N.deformation`, then the cylinder
  deformation `N.cylinderDeformation : I × (I × X) → I × X` is proper
  (`TauCeti.NDRPair.isProperMap_cylinderDeformation`), hence `A` has the proper homotopy extension
  property (`TauCeti.NDRPair.hasProperHomotopyExtensionProperty`);
* if `N : NDRPair A` and `M : NDRPair B` both have proper deformations, then so does their product
  `N.prod M` (`TauCeti.NDRPair.isProperMap_prod_deformation`).

This yields **Strøm's product theorem for closed proper cofibrations**
(`TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`) on arbitrary topological
spaces with no local compactness or separation assumptions on `X` or `Y`. Specializing the first
factor to `{0, 1} ⊆ I` gives the proper homotopy extension property for
`{0, 1} × X ∪ I × A ⊆ I × X`
(`TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`), which upgrades
any proper homotopy `F` concatenated with a proper homotopy `G` that retraces `F` on `A` to a
proper homotopy *relative* to `A`
(`TauCeti.HasProperHomotopyExtensionProperty.exists_homotopyRel_isProperMap_of_retracing`).

## Main declarations

* `TauCeti.NDRPair.isProperMap_cylinderDeformation`,
  `TauCeti.NDRPair.hasProperHomotopyExtensionProperty`,
  `TauCeti.exists_ndrPair_isProperMap_iff`: **Strøm's characterization of closed proper
  cofibrations** by NDR pairs with proper deformation.
* `TauCeti.NDRPair.isProperMap_prod_deformation`,
  `TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`: **Strøm's product
  theorem** for closed proper cofibrations, together with
  `TauCeti.HasProperHomotopyExtensionProperty.univ_prod`.
* `TauCeti.hasProperHomotopyExtensionProperty_cubeBoundary`,
  `TauCeti.hasProperHomotopyExtensionProperty_singleton_unitInterval`,
  `TauCeti.hasProperHomotopyExtensionProperty_zero_one`, and
  `TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: cube boundaries,
  singletons in `I`, and cylinder ends-and-wall subspaces have the proper homotopy extension
  property.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_homotopyRel_isProperMap_of_retracing`:
  **proper retracing**, turning a proper concatenation `F.trans G` that retraces itself on a closed
  proper cofibration `A` into a proper homotopy relative to `A`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1 (Theorem 1.6).
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Proposition 0.19.
-/

public section

open Filter Set Topology unitInterval

universe u v

namespace TauCeti

namespace NDRPair

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- If a retraction `r` of `I × X` onto `{0} × X ∪ I × A` is proper, then the deformation of the
resulting NDR pair `NDRPair.ofRetraction` is proper. -/
theorem isProperMap_ofRetraction_deformation {r : C(I × X, I × X)} (hrp : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A) (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (hA : IsClosed A) :
    IsProperMap (ofRetraction hr hr' hA).deformation := by
  convert isProperMap_snd_of_compactSpace.comp hrp using 1
  funext p
  exact ofRetraction_deformation hr hr' hA p

/-- Ultrafilter convergence for an NDR deformation evaluated at a `projIcc`-rescaled time
`s z * projIcc 0 1 zero_le_one (v z / N.control (q z))`. -/
private lemma exists_tendsto_of_tendsto_deformation_mul_projIcc {Z : Type*} [TopologicalSpace Z]
    (N : NDRPair A) (hN : IsProperMap N.deformation) {s : Z → I} {v : Z → I} {q : Z → X}
    (hs : Continuous s) (hv : Continuous v) (hq : Continuous q) {𝒰 : Ultrafilter Z} {x₀ : X}
    (hw : Tendsto (fun z ↦ N.deformation
      (s z * projIcc 0 1 zero_le_one ((v z : ℝ) / N.control (q z)), q z)) 𝒰 (𝓝 x₀)) :
    ∃ x₁, Tendsto q 𝒰 (𝓝 x₁) ∧
      ∀ z₁ : Z, q z₁ = x₁ → (𝒰 : Filter Z) ≤ 𝓝 z₁ →
        N.deformation (s z₁ * projIcc 0 1 zero_le_one ((v z₁ : ℝ) / N.control (q z₁)), q z₁) = x₀ :=
  hN.exists_tendsto_of_tendsto_apply_prodMk
    (fun t₁ t₂ _ hx ↦ (N.deformation_of_mem t₁ hx).trans (N.deformation_of_mem t₂ hx).symm)
    (q := q) (φ := fun z ↦ s z * projIcc 0 1 zero_le_one ((v z : ℝ) / N.control (q z)))
    (fun _ hz ↦ hs.continuousAt.mul
      (N.control.continuousAt_projIcc_div_of_notMem N.control_eq_zero_iff hv hq hz))
    hw

/-- If the deformation of an NDR pair `N` is proper, then so is its cylinder deformation
`N.cylinderDeformation : I × (I × X) → I × X`. -/
theorem isProperMap_cylinderDeformation (N : NDRPair A) (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderDeformation := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨N.cylinderDeformation.continuous, fun 𝒰 ⟨t₀, x₀⟩ hw ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hw
  have hw₂ := hw.2.congr fun w : I × (I × X) ↦ N.cylinderDeformation_snd w.1 w.2.1 w.2.2
  obtain ⟨x₁, hx₁, hx₁_eq⟩ := N.exists_tendsto_of_tendsto_deformation_mul_projIcc hN
    continuous_fst (by fun_prop) (by fun_prop) hw₂
  obtain ⟨s₁, -, hs₁⟩ := isCompact_univ.ultrafilter_le_nhds (Ultrafilter.map Prod.fst 𝒰) (by simp)
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (Ultrafilter.map (fun w : I × (I × X) ↦ w.2.1) 𝒰) (by simp)
  rw [Ultrafilter.coe_map] at hs₁ ht₁
  have hle : (𝒰 : Filter (I × (I × X))) ≤ 𝓝 (s₁, t₁, x₁) :=
    tendsto_id'.1 (Tendsto.prodMk_nhds hs₁ (Tendsto.prodMk_nhds ht₁ hx₁))
  have ht₀_eq : (N.cylinderDeformation (s₁, t₁, x₁)).1 = t₀ :=
    tendsto_nhds_unique
      (((continuous_fst.comp N.cylinderDeformation.continuous).tendsto _).mono_left hle) hw.1
  have hx₀_eq : (N.cylinderDeformation (s₁, t₁, x₁)).2 = x₀ := by
    rw [cylinderDeformation_snd]
    exact hx₁_eq (s₁, t₁, x₁) rfl hle
  exact ⟨(s₁, t₁, x₁), Prod.ext ht₀_eq hx₀_eq, hle⟩

/-- If the deformation of an NDR pair `N` is proper, then so is its cylinder retraction
`N.cylinderRetraction : I × X → {0} × X ∪ I × A`. -/
theorem isProperMap_cylinderRetraction (N : NDRPair A) (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderRetraction := by
  refine isProperMap_of_comp_of_inj N.cylinderRetraction.continuous continuous_subtypeVal ?_
    Subtype.val_injective
  convert (N.isProperMap_cylinderDeformation hN).comp (isProperMap_prodMk_left (1 : I)) using 1
  funext z
  exact N.coe_cylinderRetraction_apply z

/-- The subset of an NDR pair with proper deformation has the proper homotopy extension property. -/
protected theorem hasProperHomotopyExtensionProperty (N : NDRPair A)
    (hN : IsProperMap N.deformation) :
    HasProperHomotopyExtensionProperty A := by
  have hval : ((ContinuousMap.subtypeVal (cylinderExtensionDomain A)).comp N.cylinderRetraction :
      I × X → I × X) = Subtype.val ∘ N.cylinderRetraction := by
    funext z
    simp
  refine hasProperHomotopyExtensionProperty_of_retraction
    (r := (ContinuousMap.subtypeVal _).comp N.cylinderRetraction)
    (hval ▸ (isClosed_cylinderExtensionDomain N.isClosed).isProperMap_subtypeVal.comp
      (N.isProperMap_cylinderRetraction hN))
    (fun z ↦ (N.cylinderRetraction z).property)
    fun z hz ↦ ?_
  simpa using congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

/-- If two NDR pairs `N` and `M` have proper deformations, then so does their product `N.prod M`. -/
theorem isProperMap_prod_deformation {Y : Type v} [TopologicalSpace Y] {B : Set Y}
    (N : NDRPair A) (M : NDRPair B) (hN : IsProperMap N.deformation)
    (hM : IsProperMap M.deformation) :
    IsProperMap (N.prod M).deformation := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨(N.prod M).deformation.continuous, fun 𝒰 ⟨x₀, y₀⟩ hw ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hw
  have hw₁ := hw.1.congr fun w : I × (X × Y) ↦
    congrArg Prod.fst (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  have hw₂ := hw.2.congr fun w : I × (X × Y) ↦
    congrArg Prod.snd (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  obtain ⟨x₁, hx₁, hx₁_eq⟩ := N.exists_tendsto_of_tendsto_deformation_mul_projIcc hN
    continuous_fst (by fun_prop) (by fun_prop) hw₁
  obtain ⟨y₁, hy₁, hy₁_eq⟩ := M.exists_tendsto_of_tendsto_deformation_mul_projIcc hM
    continuous_fst (by fun_prop) (by fun_prop) hw₂
  obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.ultrafilter_le_nhds (Ultrafilter.map Prod.fst 𝒰) (by simp)
  rw [Ultrafilter.coe_map] at ht₁
  have hle : (𝒰 : Filter (I × (X × Y))) ≤ 𝓝 (t₁, x₁, y₁) :=
    tendsto_id'.1 (Tendsto.prodMk_nhds ht₁ (Tendsto.prodMk_nhds hx₁ hy₁))
  refine ⟨(t₁, x₁, y₁), ?_, hle⟩
  rw [prod_deformation_apply]
  exact Prod.ext (hx₁_eq (t₁, x₁, y₁) rfl hle) (hy₁_eq (t₁, x₁, y₁) rfl hle)

end NDRPair

/-- **Strøm's characterization of closed proper cofibrations**: a subset `A ⊆ X` admits NDR data
with proper deformation if and only if `A` is closed and has the proper homotopy extension
property. -/
theorem exists_ndrPair_isProperMap_iff {X : Type u} [TopologicalSpace X] {A : Set X} :
    (∃ N : NDRPair A, IsProperMap N.deformation) ↔
      IsClosed A ∧ HasProperHomotopyExtensionProperty A :=
  ⟨fun ⟨N, hN⟩ ↦ ⟨N.isClosed, N.hasProperHomotopyExtensionProperty hN⟩, fun ⟨hA, h⟩ ↦
    let ⟨_, hrp, hr, hr'⟩ := h.exists_proper_retraction hA
    ⟨NDRPair.ofRetraction hr hr' hA, NDRPair.isProperMap_ofRetraction_deformation hrp hr hr' hA⟩⟩

section Products

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- **Strøm's product theorem for closed proper cofibrations**: if closed subsets `A ⊆ X` and
`B ⊆ Y` have the proper homotopy extension property, then so does
`A × Y ∪ X × B ⊆ X × Y`. -/
theorem HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod
    (hA : HasProperHomotopyExtensionProperty A) (hA' : IsClosed A)
    (hB : HasProperHomotopyExtensionProperty B) (hB' : IsClosed B) :
    HasProperHomotopyExtensionProperty (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) := by
  obtain ⟨N, hN⟩ := exists_ndrPair_isProperMap_iff.2 ⟨hA', hA⟩
  obtain ⟨M, hM⟩ := exists_ndrPair_isProperMap_iff.2 ⟨hB', hB⟩
  exact (N.prod M).hasProperHomotopyExtensionProperty (N.isProperMap_prod_deformation M hN hM)

/-- A closed proper cofibration remains a proper cofibration after taking its product with any
topological space. -/
theorem HasProperHomotopyExtensionProperty.univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  simpa using hasProperHomotopyExtensionProperty_empty.prod_univ_union_univ_prod isClosed_empty h hA

/-- The boundary `Cube.boundary N` of a finite-dimensional cube `I^N` has the proper homotopy
extension property in `I^N`. -/
theorem hasProperHomotopyExtensionProperty_cubeBoundary {N : Type*} [Finite N] :
    HasProperHomotopyExtensionProperty (Cube.boundary N) :=
  hasHomotopyExtensionProperty_cubeBoundary.hasProperHomotopyExtensionProperty

/-- Every singleton `{t₀}` in the unit interval `I` (in particular `{0}` and `{1}`) has the proper
homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_singleton_unitInterval (t₀ : I) :
    HasProperHomotopyExtensionProperty ({t₀} : Set I) :=
  (hasHomotopyExtensionProperty_singleton_unitInterval t₀).hasProperHomotopyExtensionProperty

/-- The endpoints `{0, 1}` of the unit interval have the proper homotopy extension property in
`I`. -/
theorem hasProperHomotopyExtensionProperty_zero_one :
    HasProperHomotopyExtensionProperty ({0, 1} : Set I) :=
  hasHomotopyExtensionProperty_zero_one.hasProperHomotopyExtensionProperty

/-- **The cylinder on a closed proper cofibration**: if a closed subset `A ⊆ X` has the proper
homotopy extension property, then so does `{0, 1} × X ∪ I × A ⊆ I × X`. -/
theorem HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) :=
  hasProperHomotopyExtensionProperty_zero_one.prod_univ_union_univ_prod (toFinite _).isClosed h hA

end Products

section Retracing

/-- Cutoff of `TauCeti.tent t` by `s`, clamped to `[0, 1]`. -/
private noncomputable def retraceTime (s t : I) : I :=
  projIcc 0 1 zero_le_one ((tent t : ℝ) - s)

private lemma continuous_retraceTime : Continuous (Function.uncurry retraceTime) := by
  unfold Function.uncurry retraceTime
  fun_prop

private lemma retraceTime_zero_left (t : I) : retraceTime 0 t = tent t := by
  rw [retraceTime, Icc.coe_zero, sub_zero, projIcc_val]

private lemma retraceTime_zero_right (s : I) : retraceTime s 0 = 0 :=
  projIcc_eq_zero.2 (by simp [s.property.1])

private lemma retraceTime_one_right (s : I) : retraceTime s 1 = 0 :=
  projIcc_eq_zero.2 (by simp [s.property.1])

private lemma retraceTime_one_left (t : I) : retraceTime 1 t = 0 :=
  projIcc_eq_zero.2 (by rw [Icc.coe_one]; linarith [(tent t).property.2])

/-- Boundary data on `I × ({0, 1} × X ∪ I × A)` contracting the tent-reparametrised loop on `A`
to the stationary path `f₀` while keeping the endpoints `t = 0` and `t = 1` fixed at `f₀` and
`f₂`. -/
private noncomputable def retraceBoundary {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f₀ f₁ f₂ : C(X, Y)}
    (F : f₀.Homotopy f₁) :
    I × ↥(({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) → Y := fun q ↦
  if q.2.val.1 = 0 then f₀ q.2.val.2
  else if q.2.val.1 = 1 then f₂ q.2.val.2
  else F (retraceTime q.1 q.2.val.1, q.2.val.2)

private lemma retraceBoundary_of_mem {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {f₀ f₁ f₂ : C(X, Y)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hG : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x))
    (q : I × ↥(({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A)) (hq : q.2.val.2 ∈ A) :
    retraceBoundary (f₂ := f₂) F q = F (retraceTime q.1 q.2.val.1, q.2.val.2) := by
  by_cases h0 : q.2.val.1 = 0
  · simp [retraceBoundary, h0, retraceTime_zero_right]
  · by_cases h1 : q.2.val.1 = 1
    · have hf₂ : f₂ q.2.val.2 = F (0, q.2.val.2) := by
        simpa using (G.apply_one q.2.val.2).symm.trans (hG 1 q.2.val.2 hq)
      simp [retraceBoundary, h1, retraceTime_one_right, hf₂]
    · simp [retraceBoundary, h0, h1]

private lemma isProperMap_retraceBoundary {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : IsClosed A)
    {f₀ f₁ f₂ : C(X, Y)} {F : f₀.Homotopy f₁} (hF : IsProperMap F)
    {G : f₁.Homotopy f₂} (hG : IsProperMap G) (hretrace : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    IsProperMap (retraceBoundary (A := A) (f₂ := f₂) F) := by
  let B : Set (I × X) := ({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A
  have hB : IsClosed B :=
    ((toFinite ({0, 1} : Set I)).isClosed.prod isClosed_univ).union (isClosed_univ.prod hA)
  -- Cover `I × B` by the two end slices (`t = 0`, `t = 1`) and the wall (`x ∈ A`).
  let C : Fin 3 → Set (I × B) := fun i ↦
    match i with
    | ⟨0, _⟩ => {q | q.2.val.1 = 0}
    | ⟨1, _⟩ => {q | q.2.val.1 = 1}
    | ⟨2, _⟩ => {q | q.2.val.2 ∈ A}
  have hC : ∀ i, IsClosed (C i) := by
    rintro ⟨_ | _ | _ | n, hn⟩
    · exact (isClosed_singleton (x := (0 : I))).preimage (by fun_prop)
    · exact (isClosed_singleton (x := (1 : I))).preimage (by fun_prop)
    · exact hA.preimage (by fun_prop)
    · omega
  have hcov : ⋃ i, C i = univ := eq_univ_of_forall fun q ↦ by
    rcases q.2.property with ⟨h0 | h1, -⟩ | ⟨-, hx⟩
    · exact mem_iUnion.2 ⟨0, h0⟩
    · exact mem_iUnion.2 ⟨1, h1⟩
    · exact mem_iUnion.2 ⟨2, hx⟩
  -- Proper inclusion `ι : I × B ↪ I × (I × X)` and projection `I × B → X`.
  let ι : I × B → I × (I × X) := Prod.map id Subtype.val
  have hι : IsProperMap ι := isProperMap_id.prodMap hB.isProperMap_subtypeVal
  have hproj : IsProperMap (Prod.snd ∘ Prod.snd ∘ ι) :=
    isProperMap_snd_of_compactSpace.comp (isProperMap_snd_of_compactSpace.comp hι)
  rw [isProperMap_iff_domRestrict_of_iUnion_eq_univ hC hcov]
  rintro ⟨_ | _ | _ | n, hn⟩
  · have h₀ : (C 0).domRestrict (retraceBoundary (A := A) (f₂ := f₂) F) =
        (C 0).domRestrict (f₀ ∘ Prod.snd ∘ Prod.snd ∘ ι) := by
      funext q; have hq : q.val.2.val.1 = 0 := q.property; simp [retraceBoundary, ι, hq]
    exact h₀ ▸ ((F.isProperMap_left hF).comp hproj).restrict (hC 0)
  · have h₁ : (C 1).domRestrict (retraceBoundary (A := A) (f₂ := f₂) F) =
        (C 1).domRestrict (f₂ ∘ Prod.snd ∘ Prod.snd ∘ ι) := by
      funext q; have hq : q.val.2.val.1 = 1 := q.property; simp [retraceBoundary, ι, hq]
    exact h₁ ▸ ((G.isProperMap_right hG).comp hproj).restrict (hC 1)
  · have h₂ : (C 2).domRestrict (retraceBoundary (A := A) (f₂ := f₂) F) =
        (C 2).domRestrict (F ∘ Prod.map (Function.uncurry retraceTime) id ∘
          (Homeomorph.prodAssoc I I X).symm ∘ ι) := by
      funext ⟨⟨s, ⟨⟨t, x⟩, hb⟩⟩, hx⟩
      simp only [domRestrict_apply, Function.comp_apply, ι, Prod.map_apply, id_eq,
        ← Homeomorph.coe_symm_toEquiv, Homeomorph.prodAssoc_toEquiv, Equiv.prodAssoc_symm_apply,
        Function.uncurry_apply_pair]
      exact retraceBoundary_of_mem F G hretrace (s, ⟨(t, x), hb⟩) hx
    exact h₂ ▸ (hF.comp ((continuous_retraceTime.isProperMap.prodMap isProperMap_id).comp
      ((Homeomorph.prodAssoc I I X).symm.isProperMap.comp hι))).restrict (hC 2)
  · omega

/-- **Proper retracing**: if `F : f₀.Homotopy f₁` and `G : f₁.Homotopy f₂` are proper homotopies
and `G` runs backwards along `F` on a closed subset `A ⊆ X` with the proper homotopy extension
property, then there is a proper homotopy `H : f₀.HomotopyRel f₂ A` relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_homotopyRel_isProperMap_of_retracing
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}
    (hA : HasProperHomotopyExtensionProperty A) (hA' : IsClosed A) {f₀ f₁ f₂ : C(X, Y)}
    {F : f₀.Homotopy f₁} (hF : IsProperMap F) {G : f₁.Homotopy f₂} (hG : IsProperMap G)
    (hretrace : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    ∃ H : f₀.HomotopyRel f₂ A, IsProperMap H := by
  let B : Set (I × X) := ({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A
  have hB : IsClosed B :=
    ((toFinite ({0, 1} : Set I)).isClosed.prod isClosed_univ).union (isClosed_univ.prod hA')
  have hBp := isProperMap_retraceBoundary hA' hF hG hretrace
  obtain ⟨E, hEp, -, hE₁⟩ :=
    (hA.zero_one_prod_univ_union_univ_prod hA').exists_extension_of_isClosed hB
      (F.trans G).toContinuousMap (F.isProperMap_trans hF hG)
      ⟨retraceBoundary (A := A) (f₂ := f₂) F, hBp.continuous⟩ hBp fun b ↦ by
        obtain ⟨⟨t, x⟩, hb⟩ := b
        rcases hb with ⟨h0 | h1, -⟩ | ⟨-, hx⟩
        · obtain rfl : t = 0 := h0
          simp [retraceBoundary]
        · obtain rfl : t = 1 := h1
          simp [retraceBoundary]
        · rw [ContinuousMap.coe_mk,
            retraceBoundary_of_mem F G hretrace (0, ⟨(t, x), Or.inr ⟨mem_univ t, hx⟩⟩) hx,
            retraceTime_zero_left]
          exact (F.trans_apply_of_retracing G (hretrace · x hx) t).symm
  refine ⟨{ toContinuousMap := E.comp ⟨Prod.mk (1 : I), .prodMk_right 1⟩
            map_zero_left := fun x ↦ by
              simpa [retraceBoundary] using hE₁ 1 ⟨(0, x), Or.inl ⟨Or.inl rfl, mem_univ x⟩⟩
            map_one_left := fun x ↦ by
              simpa [retraceBoundary] using hE₁ 1 ⟨(1, x), Or.inl ⟨Or.inr rfl, mem_univ x⟩⟩
            prop' := fun t x hx ↦ by
              have h := hE₁ 1 ⟨(t, x), Or.inr ⟨mem_univ t, hx⟩⟩
              simp only [ContinuousMap.coe_mk] at h
              rw [retraceBoundary_of_mem F G hretrace (1, ⟨(t, x), Or.inr ⟨mem_univ t, hx⟩⟩) hx,
                retraceTime_one_left, F.apply_zero] at h
              simpa using h },
    hEp.comp (isProperMap_prodMk_left (1 : I))⟩

end Retracing

end TauCeti
