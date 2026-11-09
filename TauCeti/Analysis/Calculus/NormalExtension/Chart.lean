/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.NormalExtension.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Frame
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Coordinates adapted to a totally real submanifold

Let `γ : V → W` parametrize a submanifold `L` of `W` near `x₀`, and let `J : W → End W` be an
almost complex structure along `L`. The adapted normal extension
`Φ (x, y) = γ x + J (γ x) (Dγ x y)` (`TauCeti.adaptedNormalExtension`) sends the real locus
`V × {0}` onto `L`, and its derivative along the real locus carries the standard structure
`(u, v) ↦ (-v, u)` of `V × V` (`LinearEquiv.skewSwap`) to `J`. When the tangent space of `L` at
`γ x₀` is maximal totally real for `J (γ x₀)`, the derivative of `Φ` at `(x₀, 0)` is invertible,
and the inverse function theorem makes the inverse of `Φ` a chart `ψ` of `W` near `γ x₀`. This
is McDuff–Salamon, Exercise B.4.10. The chart `ψ`

* sends the points of `L` in its domain to the real locus, and only those points, provided the
  parametrization `γ` induces the topology of `L`;
* sends `γ x` to `(x, 0)`;
* has derivative intertwining `J` with the standard structure at every point of `L` in its
  domain, so that the structure read in the chart is the standard one along the real locus.

If `γ` is `C^(n+1)` and `J` is `C^n` with `n ≥ 1`, then `ψ` and its inverse are `C^n`. The
structure read in the chart, `dψ ∘ J ∘ dψ⁻¹`, is then only `C^(n-1)`: this is the derivative
that the boundary regularity theory for pseudoholomorphic curves loses in such charts.

The properties of the chart are collected in the predicate `OpenPartialHomeomorph.IsAdaptedChart`,
and `TauCeti.exists_isAdaptedChart` constructs such a chart.

## Main declarations

* `OpenPartialHomeomorph.IsAdaptedChart`: a chart sending a parametrized submanifold to the real
  locus, with derivative carrying the ambient structure to the standard one along it.
* `OpenPartialHomeomorph.IsAdaptedChart.restrOpen`: adapted charts restrict to open subsets.
* `TauCeti.exists_hasFDerivAt_adaptedNormalExtension_zero_iff`: the adapted normal extension has
  an invertible derivative at `(x₀, 0)` exactly when the derivative of `γ` at `x₀` is injective
  and the tangent space at `γ x₀` is maximal totally real.
* `TauCeti.exists_isAdaptedChart`: the existence of a `C^n` adapted chart near a point of a
  submanifold whose tangent space there is maximal totally real.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications **52**, 2012, Exercise B.4.10.
-/

public section

noncomputable section

open Function Set Topology
open scoped ContDiff

namespace OpenPartialHomeomorph

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A chart `ψ` of `W` is **adapted** to the submanifold parametrized by `γ` on `U` and to the
field of endomorphisms `J` if

* a point of the domain of `ψ` lies on `γ '' U` exactly when `ψ` sends it to the real locus
  `V × {0}`;
* `ψ` sends `γ x` to `(x, 0)`;
* at every point `γ x` of its domain, the derivative of `ψ` carries `J (γ x)` to the standard
  structure `(u, v) ↦ (-v, u)` of `V × V`.

No regularity of `ψ`, `γ` or `J` is part of the predicate. -/
structure IsAdaptedChart (ψ : OpenPartialHomeomorph W (V × V)) (γ : V → W)
    (J : W → W →L[𝕜] W) (U : Set V) : Prop where
  /-- The chart detects the submanifold: a point of its domain lies on it exactly when its image
  lies on the real locus. -/
  mem_image_iff : ∀ y ∈ ψ.source, y ∈ γ '' U ↔ (ψ y).2 = 0
  /-- The chart inverts the parametrization along the real locus. -/
  apply_eq : ∀ x ∈ U, γ x ∈ ψ.source → ψ (γ x) = (x, 0)
  /-- Along the submanifold, the derivative of the chart is complex linear from `J` to the
  standard structure of `V × V`. -/
  fderiv_apply : ∀ x ∈ U, γ x ∈ ψ.source → ∀ v : W,
    fderiv 𝕜 ψ (γ x) (J (γ x) v) = LinearEquiv.skewSwap 𝕜 V V (fderiv 𝕜 ψ (γ x) v)

/-- Restricting an adapted chart to an open subset of its domain gives an adapted chart. -/
theorem IsAdaptedChart.restrOpen {ψ : OpenPartialHomeomorph W (V × V)} {γ : V → W}
    {J : W → W →L[𝕜] W} {U : Set V} (h : ψ.IsAdaptedChart γ J U) {s : Set W} (hs : IsOpen s) :
    (ψ.restrOpen s hs).IsAdaptedChart γ J U :=
  ⟨fun y hy ↦ h.mem_image_iff y hy.1, fun x hx hxs ↦ h.apply_eq x hx hxs.1,
    fun x hx hxs ↦ h.fderiv_apply x hx hxs.1⟩

end OpenPartialHomeomorph

namespace TauCeti

variable {𝕂 V W : Type*} [RCLike 𝕂]
  [NormedAddCommGroup V] [NormedSpace 𝕂 V] [NormedAddCommGroup W] [NormedSpace 𝕂 W]

/-- A local inverse of the adapted normal extension is complex linear, from `J` to the standard
structure of `V × V`, at a point `γ x` of the submanifold whose preimage `(x, 0)` lies in its
domain, provided it is differentiable there. -/
private theorem fderiv_symm_apply_of_coe_eq {γ : V → W} {J : W → W →L[𝕂] W}
    (Θ : OpenPartialHomeomorph (V × V) W) (hΘ : ⇑Θ = adaptedNormalExtension γ J) {x : V}
    (hp : (x, 0) ∈ Θ.source) (hγ : ContDiffAt 𝕂 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hdΘs : DifferentiableAt 𝕂 Θ.symm (γ x)) (v : W) :
    fderiv 𝕂 Θ.symm (γ x) (J (γ x) v) =
      LinearEquiv.skewSwap 𝕂 V V (fderiv 𝕂 Θ.symm (γ x) v) := by
  have hΘx : Θ (x, 0) = γ x := by rw [hΘ, adaptedNormalExtension_zero]
  have hdΘ : DifferentiableAt 𝕂 Θ (x, 0) :=
    hΘ ▸ (hasFDerivAt_adaptedNormalExtension_zero hγ hJ).differentiableAt
  -- The derivatives of `Θ` at `(x, 0)` and of its inverse at `γ x` are mutually inverse.
  have hleft := Θ.fderiv_symm_comp_fderiv (hΘx ▸ Θ.map_source hp)
    (by rwa [← hΘx, Θ.left_inv hp]) hdΘs
  have hright := Θ.symm.fderiv_symm_comp_fderiv (𝕜 := 𝕂) (p := (x, 0))
    (by rwa [Θ.symm_target]) (by simpa [hΘx] using hdΘs) (by simpa using hdΘ)
  rw [← hΘx, Θ.left_inv hp, hΘx] at hleft
  simp only [OpenPartialHomeomorph.symm_symm, hΘx] at hright
  have hv : fderiv 𝕂 Θ (x, 0) (fderiv 𝕂 Θ.symm (γ x) v) = v := by
    simpa using congrArg (fun T ↦ T v) hright
  -- The derivative of `Θ` at `(x, 0)` carries the standard structure to `J (γ x)`.
  have hJv : J (γ x) v = fderiv 𝕂 Θ (x, 0)
      (-(fderiv 𝕂 Θ.symm (γ x) v).2, (fderiv 𝕂 Θ.symm (γ x) v).1) := by
    rw [hΘ, fderiv_adaptedNormalExtension_intertwines hγ hJ hsq, ← hΘ, Prod.mk.eta, hv]
  rw [hJv, ← ContinuousLinearMap.comp_apply, hleft]
  simp

variable [CompleteSpace V] [CompleteSpace W]

/-- **The adapted normal extension has invertible derivative exactly at maximal totally real
points.** Let `γ` be `C^1` at `x₀` and `J` continuous at `γ x₀`, with `J (γ x₀)` injective on the
range of the derivative of `γ` at `x₀`. The derivative of the adapted normal extension at
`(x₀, 0)` is a continuous linear equivalence if and only if the derivative of `γ` at `x₀` is
injective with maximal totally real range for `J (γ x₀)`. -/
theorem exists_hasFDerivAt_adaptedNormalExtension_zero_iff {γ : V → W} {J : W → W →L[𝕂] W}
    {x₀ : V} (hγ : ContDiffAt 𝕂 1 γ x₀) (hJ : ContinuousAt J (γ x₀))
    (hJ₀ : Injective (J (γ x₀) ∘ fderiv 𝕂 γ x₀)) :
    (∃ e : (V × V) ≃L[𝕂] W,
        HasFDerivAt (adaptedNormalExtension γ J) (e : V × V →L[𝕂] W) (x₀, 0)) ↔
      Injective (fderiv 𝕂 γ x₀) ∧ IsMaximalTotallyReal (J (γ x₀) : W →ₗ[𝕂] W)
        (LinearMap.range (fderiv 𝕂 γ x₀ : V →ₗ[𝕂] W)) := by
  have hΦ := hasFDerivAt_adaptedNormalExtension_zero hγ hJ
  constructor
  · rintro ⟨e, he⟩
    have hb : Bijective ((fderiv 𝕂 γ x₀).coprod ((J (γ x₀)).comp (fderiv 𝕂 γ x₀))) :=
      he.unique hΦ ▸ e.bijective
    refine ⟨fun v w hvw ↦ ?_, isMaximalTotallyReal_range_of_bijective_coprod hb⟩
    have h := @hb.1 (v, 0) (w, 0) (by simpa using hvw)
    exact congrArg Prod.fst h
  · rintro ⟨hD, htr⟩
    have hb : Bijective ((fderiv 𝕂 γ x₀).coprod ((J (γ x₀)).comp (fderiv 𝕂 γ x₀))) :=
      htr.bijective_coprod hD hJ₀
    refine ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hb.1)
      (LinearMap.range_eq_top.2 hb.2), ?_⟩
    rwa [ContinuousLinearEquiv.coe_ofBijective]

/-- **Coordinates adapted to a totally real submanifold** (McDuff–Salamon, Exercise B.4.10).

Let `γ` be `C^(n+1)` on an open set `U`, with `1 ≤ n`, inducing the topology of `γ '' U`, and let
`J` be `C^n` on an open set containing `γ '' U` and square to `-1` along `γ '' U`. If at `x₀ ∈ U`
the derivative of `γ` is injective with maximal totally real range for `J (γ x₀)`, then the
inverse of the adapted normal extension `(x, y) ↦ γ x + J (γ x) (Dγ x y)` restricts to an adapted
chart `ψ` (`OpenPartialHomeomorph.IsAdaptedChart`) around `γ x₀` with image in `U × V`, and `ψ`
and its inverse are `C^n`. -/
theorem exists_isAdaptedChart {γ : V → W} {J : W → W →L[𝕂] W} {U : Set V} {Ω : Set W}
    {n : ℕ∞ω} {x₀ : V} (hn : 1 ≤ n) (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕂 (n + 1) γ U) (hγi : IsInducing (U.domRestrict γ))
    (hJ : ContDiffOn 𝕂 n J Ω) (hγΩ : MapsTo γ U Ω)
    (hsq : ∀ x ∈ U, ∀ v, J (γ x) (J (γ x) v) = -v) (hD : Injective (fderiv 𝕂 γ x₀))
    (htr : IsMaximalTotallyReal (J (γ x₀) : W →ₗ[𝕂] W)
      (LinearMap.range (fderiv 𝕂 γ x₀ : V →ₗ[𝕂] W))) :
    ∃ ψ : OpenPartialHomeomorph W (V × V), ψ.IsAdaptedChart γ J U ∧ γ x₀ ∈ ψ.source ∧
      ψ.target ⊆ U ×ˢ univ ∧ ⇑ψ.symm = adaptedNormalExtension γ J ∧
      ContDiffOn 𝕂 n ψ ψ.source ∧ ContDiffOn 𝕂 n ψ.symm ψ.target := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  have hγ1 : ∀ x ∈ U, ContDiffAt 𝕂 1 γ x := fun x hx ↦
    (hγ.contDiffAt (hU.mem_nhds hx)).of_le (hn.trans le_self_add)
  have hJc : ∀ x ∈ U, ContinuousAt J (γ x) := fun x hx ↦
    hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hx))
  have hJinj : Injective (J (γ x₀)) := fun v w hvw ↦ by
    simpa [hsq x₀ hx₀] using congrArg (fun u ↦ -J (γ x₀) u) hvw
  -- The inverse function theorem for the adapted normal extension.
  obtain ⟨e, he⟩ := (exists_hasFDerivAt_adaptedNormalExtension_zero_iff (hγ1 x₀ hx₀)
    (hJc x₀ hx₀) (hJinj.comp hD)).2 ⟨hD, htr⟩
  have hΦ : ContDiffOn 𝕂 n (adaptedNormalExtension γ J) (U ×ˢ univ) :=
    contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ
  obtain ⟨Θ, hΘ, hx₀Θ, hΘU, hΘs⟩ := ContDiffOn.exists_openPartialHomeomorph hΦ
    (hU.prod isOpen_univ) ⟨hx₀, trivial⟩ hn he.fderiv.symm
  -- An open set `O` cutting out of `γ '' U` the part parametrized by the real locus of `Θ`.
  have hA : IsOpen {x : U | ((x : V), (0 : V)) ∈ Θ.source} :=
    Θ.open_source.preimage (by fun_prop)
  obtain ⟨O, hO, hOeq⟩ := hγi.isOpen_iff.1 hA
  have hmemO : ∀ x ∈ U, γ x ∈ O ↔ (x, 0) ∈ Θ.source := fun x hx ↦ by
    simpa only [mem_preimage, domRestrict_apply, mem_ofPred_eq] using Set.ext_iff.1 hOeq ⟨x, hx⟩
  have hΘzero : ∀ x, Θ (x, 0) = γ x := fun x ↦ by
    rw [hΘ, adaptedNormalExtension_zero]
  -- The chart.
  refine ⟨Θ.symm.restrOpen O hO, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have happly : ∀ x ∈ U, γ x ∈ (Θ.symm.restrOpen O hO).source →
        Θ.symm.restrOpen O hO (γ x) = (x, 0) := fun x hx hxs ↦ by
      rw [OpenPartialHomeomorph.coe_restrOpen, ← hΘzero, Θ.left_inv ((hmemO x hx).1 hxs.2)]
    refine ⟨fun y hy ↦ ⟨?_, fun h ↦ ?_⟩, happly, fun x hx hxs v ↦ ?_⟩
    · rintro ⟨x, hx, rfl⟩
      rw [happly x hx hy]
    · have hp := Θ.map_target hy.1
      rw [OpenPartialHomeomorph.coe_restrOpen] at h
      refine ⟨(Θ.symm y).1, (hΘU hp).1, ?_⟩
      rw [← hΘzero, ← h, Prod.mk.eta, Θ.right_inv hy.1]
    · have hxs' : γ x ∈ Θ.target := hxs.1
      simp only [OpenPartialHomeomorph.coe_restrOpen]
      exact fderiv_symm_apply_of_coe_eq Θ hΘ ((hmemO x hx).1 hxs.2) (hγ1 x hx) (hJc x hx)
        (hsq x hx) ((hΘs.contDiffAt (Θ.open_target.mem_nhds hxs')).differentiableAt hn0) v
  · refine ⟨?_, (hmemO x₀ hx₀).2 hx₀Θ⟩
    rw [← hΘzero]
    exact Θ.map_source hx₀Θ
  · exact fun p hp ↦ hΘU hp.1
  · rw [OpenPartialHomeomorph.coe_restrOpen_symm, Θ.symm_symm, hΘ]
  · exact hΘs.mono inter_subset_left
  · rw [OpenPartialHomeomorph.coe_restrOpen_symm, Θ.symm_symm, hΘ]
    exact hΦ.mono fun p hp ↦ hΘU hp.1

end TauCeti
