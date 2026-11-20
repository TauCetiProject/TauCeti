/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# Local continuous sections of the universal cover

Continuous sections `X → UniversalCover x₀` of the universal cover over a subset `U : Set X`
(with `x₀ : U`) arise when restricting maps defined on `UniversalCover x₀` to ambient-space
functions `X → E` on a simply connected subset `V ⊆ U`.

* `TauCeti.UniversalCover.exists_continuousOn_proj_eq_of_isSimplyConnected` and
  `TauCeti.UniversalCover.exists_continuousOn_proj_eq_of_isSimplyConnected_of_isOpen`: existence
  of a continuous section `sec : X → UniversalCover x₀` over a simply connected subset `V ⊆ U`
  passing through a prescribed lift `p₀` over `w₀ ∈ V`.
* `TauCeti.UniversalCover.eqOn_of_continuousOn_proj_eq` and
  `TauCeti.UniversalCover.eqOn_of_continuousOn_proj_eq_of_isOpen`: uniqueness of continuous lifts
  into `UniversalCover x₀` on a preconnected set agreeing at one point.
-/

public section

namespace TauCeti.UniversalCover

/-- **Existence of a continuous section over a simply connected, locally path-connected subset
`V ⊆ U`.** -/
theorem exists_continuousOn_proj_eq_of_isSimplyConnected {X : Type*} [TopologicalSpace X]
    {U V : Set X} [LocallyPathConnectedSpace U] [SemilocallySimplyConnectedSpace U]
    [LocallyPathConnectedSpace V] (hVc : IsSimplyConnected V) (hVU : V ⊆ U) {x₀ : U}
    {w₀ : X} (hw₀ : w₀ ∈ V) (p₀ : UniversalCover x₀) (hp₀ : (p₀.proj : X) = w₀) :
    ∃ sec : X → UniversalCover x₀,
      ContinuousOn sec V ∧ (∀ x ∈ V, ((sec x).proj : X) = x) ∧ sec w₀ = p₀ := by
  have : SimplyConnectedSpace V := hVc.simplyConnectedSpace
  classical
  let incl : C(V, U) := ⟨Set.inclusion hVU, continuous_inclusion hVU⟩
  obtain ⟨s, ⟨hs0, hsproj⟩, -⟩ := existsUnique_continuousMap_lifts x₀ incl ⟨w₀, hw₀⟩ p₀
    (Subtype.ext hp₀)
  refine ⟨fun x => if hx : x ∈ V then s ⟨x, hx⟩ else p₀,
    continuousOn_iff_continuous_domRestrict.mpr (s.continuous.congr fun x => by simp [x.property]),
    fun x hx => by simpa [hx, incl] using congrArg Subtype.val (congrFun hsproj ⟨x, hx⟩),
    by simp [hw₀, hs0]⟩

/-- **Existence of a continuous section over a simply connected open subset `V ⊆ U`** of a
strongly locally contractible space `X`. -/
theorem exists_continuousOn_proj_eq_of_isSimplyConnected_of_isOpen {X : Type*} [TopologicalSpace X]
    [StronglyLocallyContractibleSpace X] {U V : Set X} (hUo : IsOpen U) (hVo : IsOpen V)
    (hVc : IsSimplyConnected V) (hVU : V ⊆ U) {x₀ : U} {w₀ : X} (hw₀ : w₀ ∈ V)
    (p₀ : UniversalCover x₀) (hp₀ : (p₀.proj : X) = w₀) :
    ∃ sec : X → UniversalCover x₀,
      ContinuousOn sec V ∧ (∀ x ∈ V, ((sec x).proj : X) = x) ∧ sec w₀ = p₀ := by
  have : StronglyLocallyContractibleSpace U := hUo.stronglyLocallyContractibleSpace
  have : LocallyPathConnectedSpace V := hVo.locallyPathConnectedSpace
  exact exists_continuousOn_proj_eq_of_isSimplyConnected hVc hVU hw₀ p₀ hp₀

/-- **Uniqueness of continuous lifts on a preconnected set.** Two continuous maps on a
preconnected set `V ⊆ A` into `UniversalCover x₀` (for `x₀ : U`) with matching ambient projections
into `X` and agreeing at one point `w₀ ∈ V` agree on all of `V`. -/
theorem eqOn_of_continuousOn_proj_eq {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    {U : Set X} [LocallyPathConnectedSpace U] [SemilocallySimplyConnectedSpace U]
    {V : Set A} (hVc : IsPreconnected V) {x₀ : U} {sec₁ sec₂ : A → UniversalCover x₀}
    (hsec₁ : ContinuousOn sec₁ V) (hsec₂ : ContinuousOn sec₂ V)
    (hproj : Set.EqOn (fun a => ((sec₁ a).proj : X)) (fun a => ((sec₂ a).proj : X)) V)
    {w₀ : A} (hw₀ : w₀ ∈ V) (heq : sec₁ w₀ = sec₂ w₀) : Set.EqOn sec₁ sec₂ V :=
  (isCoveringMap x₀).eqOn_of_comp_eqOn hVc hsec₁ hsec₂
    (fun _ hz => Subtype.ext (hproj hz)) hw₀ heq

/-- **Uniqueness of continuous lifts on a preconnected set** over an open subset `U` of a
strongly locally contractible space `X`. -/
theorem eqOn_of_continuousOn_proj_eq_of_isOpen {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [StronglyLocallyContractibleSpace X] {U : Set X} (hUo : IsOpen U)
    {V : Set A} (hVc : IsPreconnected V) {x₀ : U} {sec₁ sec₂ : A → UniversalCover x₀}
    (hsec₁ : ContinuousOn sec₁ V) (hsec₂ : ContinuousOn sec₂ V)
    (hproj : Set.EqOn (fun a => ((sec₁ a).proj : X)) (fun a => ((sec₂ a).proj : X)) V)
    {w₀ : A} (hw₀ : w₀ ∈ V) (heq : sec₁ w₀ = sec₂ w₀) : Set.EqOn sec₁ sec₂ V := by
  have : StronglyLocallyContractibleSpace U := hUo.stronglyLocallyContractibleSpace
  exact eqOn_of_continuousOn_proj_eq hVc hsec₁ hsec₂ hproj hw₀ heq

end TauCeti.UniversalCover
