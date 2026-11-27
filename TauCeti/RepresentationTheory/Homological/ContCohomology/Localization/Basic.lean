/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.Topology.Algebra.Module.ContinuousMapLocalization

/-!
# Continuous cohomology commutes with localization of the coefficients

Let `G` be a compact group, `S` a submonoid of the coefficient ring `k` and `f : X ⟶ Y` a
morphism of topological representations of `G` which is a localization at `S` in the following
topological sense:

* its kernel is killed by a single `s₀ ∈ S`;
* it lifts continuous maps from compact spaces up to `S`: for every continuous `y : Z → Y` with
  `Z` compact there are `s ∈ S` and a continuous `x : Z → X` with `f ∘ x = s • y`;
* every `s ∈ S` acts invertibly on `Y`, through a morphism of representations.

Then `Hⁿ(G, f) : Hⁿ(G, X) → Hⁿ(G, Y)` is a localization at `S`
(`TauCeti.ContinuousCohomology.isLocalizedModule_coeffMap`).

The two lifting conditions pass from `X → Y` to every term `C(G, C(G, …, X)) → C(G, C(G, …, Y))`
of Mathlib's coinduced resolution, with the same `s₀`. For the kernel this is pointwise. For the
lifting this is currying: a continuous map `Z → C(G, Y)` is a continuous map `Z × G → Y`, and
`Z × G` is again compact. On the homogeneous cochains, the `G`-invariant elements of the
resolution, a lift `x` of `s • y` need not be invariant, but `g • x - x` lies in the kernel, so
`s₀ • x` is invariant. The same device turns a lift of a cocycle into a cocycle and a lift of a
coboundary relation into one. Neither flatness of the localization nor any comparison of
complexes is used.

For a compact space `X`, `C(X, T) → C(X, V)` is a localization when `T` is an open absorbing
submodule of `V` (`TauCeti.isLocalizedModule_compLeftContinuous_subtypeL`).
`TauCeti.ContinuousCohomology.lift_of_isOpen` supplies the lifting hypothesis in that situation,
given a continuous section of `f` over the open submodule.

## Main results

* `TauCeti.ContinuousCohomology.exists_coeffMap_eq_smul`: every class of `Hⁿ(G, Y)` times some
  `s ∈ S` comes from `Hⁿ(G, X)`.
* `TauCeti.ContinuousCohomology.exists_smul_eq_zero_of_coeffMap_eq_zero`: a class of `Hⁿ(G, X)`
  mapping to zero is killed by some `s ∈ S`.
* `TauCeti.ContinuousCohomology.isLocalizedModule_coeffMap`: `Hⁿ(G, f)` is a localization at `S`.
* `TauCeti.ContinuousCohomology.lift_of_isOpen`: the lifting hypothesis from a continuous section
  over an open absorbing submodule.

## References

* K. Rubin, *Euler Systems*, Appendix B, §2, Proposition 2.4.
-/

public section

open CategoryTheory TopRep

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology

universe v

section Ring

variable {k : Type*} [Ring k] [TopologicalSpace k] (S : Submonoid k)
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y : TopRep.{v} k G} (f : X ⟶ Y)

/-- If a single `s ∈ S` kills the kernel of `f`, it kills the kernel of the map induced by `f` on
every term of the coinduced resolution. -/
theorem smul_resolutionMap_eq_zero (hker : ∃ s ∈ S, ∀ a, f.hom a = 0 → s • a = 0) :
    ∃ s ∈ S, ∀ (n : ℕ) (a : (resolutionX X n).V),
      (resolutionMap (ContinuousMonoidHom.id G) f n).hom a = 0 → s • a = 0 := by
  obtain ⟨s, hs, h⟩ := hker
  refine ⟨s, hs, fun n ↦ ?_⟩
  induction n with
  | zero => exact h
  | succ n ih =>
    intro F hF
    exact ContinuousMap.ext fun g ↦ ih (F g) (congr($hF g))

variable [CompactSpace G]

/-- If `f` lifts continuous maps from compact spaces up to `S`, so does the map it induces on
every term of the coinduced resolution of a compact group. -/
theorem exists_resolutionMap_eq_smul
    (hlift : ∀ (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, Y.V)),
      ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z) (n : ℕ)
    (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, (resolutionX Y n).V)) :
    ∃ s ∈ S, ∃ x : C(Z, (resolutionX X n).V),
      ∀ z, (resolutionMap (ContinuousMonoidHom.id G) f n).hom (x z) = s • y z := by
  induction n generalizing Z with
  | zero => exact hlift Z y
  | succ n ih =>
    -- a continuous map `Z → C(G, -)` is a continuous map on the compact space `Z × G`
    obtain ⟨s, hs, x, hx⟩ := ih (Z × G)
      (ContinuousMap.uncurry (y : C(Z, C(G, (resolutionX Y n).V))))
    exact ⟨s, hs, (x.curry : C(Z, C(G, (resolutionX X n).V))), fun z ↦
      ContinuousMap.ext fun g ↦ hx (z, g)⟩

variable {S f}

/-- **Homogeneous cochains lift up to `S`.** Under the two lifting hypotheses on `f`, every
homogeneous cochain of `Y` times some `s ∈ S` is the image of a homogeneous cochain of `X`. -/
theorem exists_cochainsMap_eq_smul (hker : ∃ s ∈ S, ∀ a, f.hom a = 0 → s • a = 0)
    (hlift : ∀ (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, Y.V)),
      ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z) (n : ℕ)
    (y : (homogeneousCochains Y).X n) :
    ∃ s ∈ S, ∃ x, (cochainsMap (ContinuousMonoidHom.id G) f).f n x = s • y := by
  set r := resolutionMap (ContinuousMonoidHom.id G) f (n + 1)
  obtain ⟨s, hs, x, hx⟩ := exists_resolutionMap_eq_smul S f hlift (n + 1) PUnit
    (ContinuousMap.const _ y.val)
  obtain ⟨s₀, hs₀, h₀⟩ := smul_resolutionMap_eq_zero S f hker
  set F := x PUnit.unit
  have hF : r.hom F = s • y.val := hx PUnit.unit
  -- the lift `F` need not be invariant, but `g • F - F` lies in the kernel
  have hinv : ∀ g : G, (resolutionX X (n + 1)).ρ g (s₀ • F) = s₀ • F := fun g ↦ by
    have hρ : r.hom ((resolutionX X (n + 1)).ρ g F) = (resolutionX Y (n + 1)).ρ g (r.hom F) :=
      resolutionMap_ρ_apply (ContinuousMonoidHom.id G) f (n + 1) g F
    have h := h₀ (n + 1) ((resolutionX X (n + 1)).ρ g F - F) (by
      rw [map_sub, hρ, hF, _root_.map_smul, y.property g, sub_self])
    rw [smul_sub, sub_eq_zero] at h
    rw [_root_.map_smul, h]
  refine ⟨s₀ * s, S.mul_mem hs₀ hs, ⟨s₀ • F, hinv⟩, Subtype.ext ?_⟩
  change r.hom (s₀ • F) = (s₀ * s) • y.val
  rw [_root_.map_smul, hF, smul_smul]

/-- **Classes lift up to `S`.** Under the two lifting hypotheses on `f`, every class of
`Hⁿ(G, Y)` times some `s ∈ S` is the image of a class of `Hⁿ(G, X)`. -/
theorem exists_coeffMap_eq_smul (hker : ∃ s ∈ S, ∀ a, f.hom a = 0 → s • a = 0)
    (hlift : ∀ (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, Y.V)),
      ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z) (n : ℕ)
    (c : continuousCohomology n Y) :
    ∃ s ∈ S, ∃ a, (coeffMap f n).hom a = s • c := by
  set K := homogeneousCochains Y
  set KX := homogeneousCochains X
  set φ := cochainsMap (ContinuousMonoidHom.id G) f
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective n c
  obtain ⟨s, hs, x, hx⟩ := exists_cochainsMap_eq_smul hker hlift n (K.iCycles n z)
  obtain ⟨s₀, hs₀, h₀⟩ := smul_resolutionMap_eq_zero S f hker
  -- the coboundary of `x` maps to `s • d z = 0`, so it is killed by `s₀`
  have hd : φ.f (n + 1) ((KX.d n (n + 1)).hom x) = 0 := by
    have h := ConcreteCategory.congr_hom (φ.comm n (n + 1)) x
    simp only [ConcreteCategory.comp_apply] at h
    rw [← h, hx, _root_.map_smul, K.d_iCycles_apply (n + 1) z, smul_zero]
  have hdx : (KX.d n (n + 1)).hom (s₀ • x) = 0 := by
    rw [_root_.map_smul]
    exact Subtype.ext (h₀ (n + 2) _ (congrArg Subtype.val hd))
  refine ⟨s₀ * s, S.mul_mem hs₀ hs,
    KX.homologyπ n (KX.cyclesMkOfEq (s₀ • x) (n + 1) (CochainComplex.next ℕ n) hdx), ?_⟩
  rw [coeffMap_def]
  refine (map_π_apply _ _ n _).trans ?_
  rw [mul_smul, ← _root_.map_smul (K.homologyπ n).hom, ← _root_.map_smul (K.homologyπ n).hom]
  refine congrArg (K.homologyπ n).hom (K.iCycles_injective n ?_)
  refine (iCycles_cocyclesMap_apply _ _ n _).trans ?_
  rw [HomologicalComplex.iCycles_cyclesMkOfEq, _root_.map_smul, _root_.map_smul,
    _root_.map_smul, hx]

/-- **The kernel is `S`-torsion.** Under the two lifting hypotheses on `f`, every class of
`Hⁿ(G, X)` mapping to zero in `Hⁿ(G, Y)` is killed by some `s ∈ S`. -/
theorem exists_smul_eq_zero_of_coeffMap_eq_zero (hker : ∃ s ∈ S, ∀ a, f.hom a = 0 → s • a = 0)
    (hlift : ∀ (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, Y.V)),
      ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z) {n : ℕ}
    (a : continuousCohomology n X) (ha : (coeffMap f n).hom a = 0) :
    ∃ s ∈ S, s • a = 0 := by
  set K := homogeneousCochains Y
  set KX := homogeneousCochains X
  set φ := cochainsMap (ContinuousMonoidHom.id G) f
  obtain ⟨z, rfl⟩ := KX.homologyπ_surjective n a
  obtain ⟨m, hm⟩ : ∃ m, (ComplexShape.up ℕ).prev n = m := ⟨_, rfl⟩
  rw [coeffMap_def] at ha
  -- the image of the cocycle is the coboundary of some cochain `w`, whose multiple lifts to `u`
  obtain ⟨w, hw⟩ := (K.homologyπ_eq_zero_iff n hm).1 ((map_π_apply _ _ n z).symm.trans ha)
  obtain ⟨s, hs, u, hu⟩ := exists_cochainsMap_eq_smul hker hlift m w
  obtain ⟨s₀, hs₀, h₀⟩ := smul_resolutionMap_eq_zero S f hker
  -- `s • z - d u` maps to zero, so it is killed by `s₀`
  have hzero : φ.f n (s • KX.iCycles n z - (KX.d m n).hom u) = 0 := by
    have h := ConcreteCategory.congr_hom (φ.comm m n) u
    simp only [ConcreteCategory.comp_apply] at h
    have hc : φ.f n (KX.iCycles n z) =
        K.iCycles n (cocyclesMap (ContinuousMonoidHom.id G) f n z) :=
      (iCycles_cocyclesMap_apply _ _ n z).symm
    rw [map_sub, _root_.map_smul, ← h, hu, _root_.map_smul, hc, ← hw,
      K.iCycles_toCycles_apply, sub_self]
  have h0 : s₀ • (s • KX.iCycles n z - (KX.d m n).hom u) = 0 :=
    Subtype.ext (h₀ (n + 1) _ (congrArg Subtype.val hzero))
  rw [smul_sub, sub_eq_zero] at h0
  refine ⟨s₀ * s, S.mul_mem hs₀ hs, ?_⟩
  rw [← _root_.map_smul]
  refine (KX.homologyπ_eq_zero_iff n hm).2 ⟨s₀ • u, KX.iCycles_injective n ?_⟩
  rw [KX.iCycles_toCycles_apply, _root_.map_smul, _root_.map_smul, mul_smul, h0]

end Ring

section CommRing

variable {k : Type*} [CommRing k] [TopologicalSpace k] {S : Submonoid k}
  {G : Type v} [Group G] {X Y : TopRep.{v} k G} {f : X ⟶ Y}

/-- **The lifting hypothesis from an open section.** If `W` is an open submodule of `Y` absorbing
`Y` along `S`, and `f` has a continuous section over `W`, then `f` lifts continuous maps from
compact spaces up to `S`. -/
theorem lift_of_isOpen [ContinuousConstSMul k Y.V] (W : Submodule k Y.V)
    (hW : IsOpen (W : Set Y.V)) (habs : ∀ y, ∃ s ∈ S, s • y ∈ W) (σ : C(W, X.V))
    (hσ : ∀ w, f.hom (σ w) = w) (Z : Type*) [TopologicalSpace Z] [CompactSpace Z]
    (y : C(Z, Y.V)) : ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z := by
  obtain ⟨s, hs, h⟩ := exists_smul_apply_mem_of_compactSpace S W hW habs y
  exact ⟨s, hs, σ.comp ⟨fun z ↦ ⟨s • y z, h z⟩, (y.continuous.const_smul s).subtype_mk _⟩,
    fun z ↦ hσ _⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **Continuous cohomology commutes with localization of the coefficients.** Let `G` be compact
and `f : X ⟶ Y` a morphism of topological representations whose kernel is killed by one element
of `S`, which lifts continuous maps from compact spaces up to `S`, and such that every `s ∈ S`
acts invertibly on `Y` through a morphism `u` with `s • u = 𝟙 Y`. Then
`Hⁿ(G, f) : Hⁿ(G, X) → Hⁿ(G, Y)` is a localization at `S`. -/
theorem isLocalizedModule_coeffMap (hker : ∃ s ∈ S, ∀ a, f.hom a = 0 → s • a = 0)
    (hlift : ∀ (Z : Type v) [TopologicalSpace Z] [CompactSpace Z] (y : C(Z, Y.V)),
      ∃ s ∈ S, ∃ x : C(Z, X.V), ∀ z, f.hom (x z) = s • y z)
    (hunit : ∀ s ∈ S, ∃ u : Y ⟶ Y, s • u = 𝟙 Y) (n : ℕ) :
    IsLocalizedModule S (coeffMap f n).hom.toLinearMap where
  map_units s := by
    obtain ⟨u, hu⟩ := hunit s s.property
    -- `Hⁿ(G, -)` is linear, so `s • Hⁿ(G, u)` is the identity
    have h : (s : k) • coeffMap u n = 𝟙 _ := by
      rw [← coeffMap_id Y n, ← hu]
      exact ((continuousCohomologyFunctor k G n).map_smul (s : k) u).symm
    have h' : ∀ c, (s : k) • (coeffMap u n).hom c = c := fun c ↦ congr($h c)
    refine (Module.End.isUnit_iff _).2 ⟨fun c₁ c₂ hc ↦ ?_, fun c ↦ ⟨(coeffMap u n).hom c, ?_⟩⟩
    · rw [← h' c₁, ← h' c₂]
      simp only [Module.algebraMap_end_apply] at hc
      rw [← _root_.map_smul, ← _root_.map_smul, hc]
    · simpa only [Module.algebraMap_end_apply] using h' c
  surj c := by
    obtain ⟨s, hs, a, ha⟩ := exists_coeffMap_eq_smul hker hlift n c
    exact ⟨(a, ⟨s, hs⟩), ha.symm⟩
  exists_of_eq {a₁ a₂} h := by
    obtain ⟨s, hs, ha⟩ := exists_smul_eq_zero_of_coeffMap_eq_zero hker hlift (a₁ - a₂)
      (by simpa [sub_eq_zero] using h)
    exact ⟨⟨s, hs⟩, by simpa [smul_sub, sub_eq_zero] using ha⟩

end CommRing

end TauCeti.ContinuousCohomology
