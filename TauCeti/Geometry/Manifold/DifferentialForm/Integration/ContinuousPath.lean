/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.Topology
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Integrals of `1`-forms with local primitives along continuous paths

A `1`-form `φ` with local primitives on a `C¹` manifold `M` over any real model with corners
induces a covering map `TauCeti.PrimitiveSpace.proj φ` from its space of local primitives to `M`
(`TauCeti.PrimitiveSpace.isCoveringMap_proj_of_localPrimitives`). Consequently, `φ` can be
integrated along every continuous path `γ : Path x y` in `M` by lifting `γ` to `PrimitiveSpace φ`
and taking the change of its value (`TauCeti.continuousPathIntegral`). No regularity of `φ`,
completeness of the coefficient space `F`, finite dimensionality, or Hausdorff property is needed
for the definition or its topological properties.

The integral does not depend on the chosen lift (`TauCeti.continuousPathIntegral_eq_sub_of_lift`),
agrees with the endpoint difference of any primitive covering the path
(`TauCeti.continuousPathIntegral_eq_sub_of_isPrimitiveOn`), and equals the telescoping sum of
endpoint differences of local primitives along any finite subdivision of `[0, 1]` whose pieces map
into primitive domains (`TauCeti.continuousPathIntegral_eq_sum_sub_of_subdivision`). It is
additive under concatenation (`TauCeti.continuousPathIntegral_trans`), negated under reversal
(`TauCeti.continuousPathIntegral_symm`), invariant under homotopy relative to the endpoints
(`TauCeti.continuousPathIntegral_eq_of_homotopic`), natural under differentiable maps
(`TauCeti.continuousPathIntegral_mpullback`), and covariant under continuous real-linear maps of
coefficients (`TauCeti.continuousPathIntegral_mapCoeff`).

When `F` is complete and `φ` is continuous, the integral along a continuous path following a `C¹`
curve agrees with `TauCeti.pathIntegral` (`TauCeti.continuousPathIntegral_eq_pathIntegral`), and on
a normed space or open subset of one it agrees with Mathlib's `curveIntegral`
(`TauCeti.continuousPathIntegral_ofSubsingleton_eq_curveIntegral`,
`TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral`). Finally,
`φ` admits a global primitive if and only if its integral along every continuous loop vanishes
(`TauCeti.exists_isPrimitiveOn_univ_iff_forall_continuousPathIntegral_loop_eq_zero`), and on a
preconnected manifold vanishing of loops at a single base point suffices, with integration from the
base point supplying the global primitive
(`TauCeti.exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_iff`).

## Main declarations

* `TauCeti.continuousPathIntegral φ γ`: the integral of a `1`-form with local primitives along a
  continuous path `γ`.
* `TauCeti.continuousPathIntegral_eq_sub_of_lift`: independence of the chosen lift to
  `PrimitiveSpace φ`.
* `TauCeti.continuousPathIntegral_eq_sub_of_isPrimitiveOn`,
  `TauCeti.continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ`,
  `TauCeti.continuousPathIntegral_mextDeriv_ofFunction`: evaluation via primitives.
* `TauCeti.continuousPathIntegral_eq_sum_sub_of_subdivision`: evaluation by summing local
  primitive increments along any finite subdivision.
* `TauCeti.continuousPathIntegral_trans`, `TauCeti.continuousPathIntegral_symm`,
  `TauCeti.continuousPathIntegral_eq_of_homotopic`: additivity, reversal, and homotopy invariance.
* `TauCeti.continuousPathIntegral_mpullback`, `TauCeti.continuousPathIntegral_mapCoeff`:
  naturality under differentiable maps and coefficient maps.
* `TauCeti.continuousPathIntegral_eq_pathIntegral`,
  `TauCeti.continuousPathIntegral_ofSubsingleton_eq_curveIntegral`,
  `TauCeti.continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral`:
  agreement with `TauCeti.pathIntegral` and Mathlib's `curveIntegral` for continuous forms along
  `C¹` curves with complete coefficients.
* `TauCeti.exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_iff`,
  `TauCeti.exists_isPrimitiveOn_univ_iff_forall_continuousPathIntegral_loop_eq_zero`:
  characterization of global primitives by vanishing loop integrals (both unbased and with a
  fixed base point on preconnected manifolds).

## References

* Allen Hatcher, *Algebraic Topology*, Section 1.3, Propositions 1.30 and 1.34 (homotopy lifting
  and uniqueness of lifts).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M]
  {φ ψ : RoughForm I M F 1} {x y z : M}

/-! ### Definition and lift characterization -/

open Classical in
/-- The integral of a `1`-form `φ` with local primitives on a `C¹` manifold along a continuous path
`γ` from `x` to `y`: the value at the endpoint of the lift of `γ` to `TauCeti.PrimitiveSpace φ`
starting at `x` with value `0`. It is `0` by convention when `φ` does not have local primitives. -/
def continuousPathIntegral (φ : RoughForm I M F 1) (γ : Path x y) : F :=
  if hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U then
    PrimitiveSpace.value φ
      ((PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ).liftPath
        γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
        (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph]) 1)
  else 0

/-- By convention, `continuousPathIntegral` is `0` when `φ` does not have local primitives. -/
theorem continuousPathIntegral_undef
    (h : ¬ ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) : continuousPathIntegral φ γ = 0 :=
  dite_eq_right h

/-- **Integration along any lift.** If `Γ` is any continuous lift of `γ` to `PrimitiveSpace φ`,
then `continuousPathIntegral φ γ` is the change `value (Γ 1) - value (Γ 0)`. -/
theorem continuousPathIntegral_eq_sub_of_lift
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {γ : Path x y} {Γ : unitInterval → PrimitiveSpace φ} (hΓ : Continuous Γ)
    (hΓγ : ∀ t, PrimitiveSpace.proj φ (Γ t) = γ t) :
    continuousPathIntegral φ γ = PrimitiveSpace.value φ (Γ 1) - PrimitiveSpace.value φ (Γ 0) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  let Γ' : unitInterval → PrimitiveSpace φ :=
    fun t ↦ PrimitiveSpace.translate φ (-PrimitiveSpace.value φ (Γ 0)) (Γ t)
  have hΓ'_eq : Γ' = hp.liftPath γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
      (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph]) :=
    (hp.eq_liftPath_iff _).mpr ⟨(PrimitiveSpace.continuous_translate _).comp hΓ,
      funext fun t ↦ by simp [Γ', hΓγ],
      PrimitiveSpace.ext (by simp [Γ', hΓγ]) (by simp [Γ'])⟩
  rw [continuousPathIntegral, dite_eq_left hφ, ← hΓ'_eq]
  simp [Γ', sub_eq_add_neg]

/-- Lifting a path to `PrimitiveSpace φ` starting from `e` translates the value by
`continuousPathIntegral φ γ`. -/
theorem PrimitiveSpace.value_liftPath_of_localPrimitives
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) (e : PrimitiveSpace φ) (he : γ.toContinuousMap 0 = PrimitiveSpace.proj φ e) :
    PrimitiveSpace.value φ
        ((PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ).liftPath
          γ.toContinuousMap e he 1) =
      PrimitiveSpace.value φ e + continuousPathIntegral φ γ := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  rw [continuousPathIntegral_eq_sub_of_lift hφ (hp.liftPath γ.toContinuousMap e he).continuous
    (fun t ↦ congrFun (hp.liftPath_lifts γ.toContinuousMap e he) t), hp.liftPath_zero]
  abel

/-- **Integration inside a primitive domain.** If `g` is a primitive of `φ` on an open set `U`
containing the image of `γ`, then `continuousPathIntegral φ γ = g y - g x`. -/
theorem continuousPathIntegral_eq_sub_of_isPrimitiveOn
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {g : M → F} {U : Set M} (hgU : IsPrimitiveOn φ g U) (γ : Path x y)
    (hγU : ∀ t, γ t ∈ U) :
    continuousPathIntegral φ γ = g y - g x := by
  rw [continuousPathIntegral_eq_sub_of_lift hφ
    ((PrimitiveSpace.continuousOn_graph hgU).comp_continuous γ.continuous hγU)
    (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp

/-- If `g` is a global primitive of `φ`, then `continuousPathIntegral φ γ = g y - g x`. -/
theorem continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ
    {g : M → F} (hg : IsPrimitiveOn φ g univ) (γ : Path x y) :
    continuousPathIntegral φ γ = g y - g x :=
  continuousPathIntegral_eq_sub_of_isPrimitiveOn
    (fun p ↦ ⟨g, univ, mem_univ p, hg⟩) hg γ (fun _ ↦ mem_univ _)

/-- **Fundamental theorem of calculus for differentiable functions along continuous paths.**
For any differentiable function `g : M → F` (not necessarily `C¹`), the continuous path integral
of `dg` along `γ` is `g y - g x`. -/
theorem continuousPathIntegral_mextDeriv_ofFunction
    {g : M → F} (hg : MDifferentiable I 𝓘(ℝ, F) g) (γ : Path x y) :
    continuousPathIntegral (mextDeriv (RoughForm.ofFunction I g)) γ = g y - g x :=
  continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ
    (isPrimitiveOn_univ_of_mextDeriv_eq hg rfl) γ

/-! ### Finite subdivisions -/

/-- Along any subinterval mapped into the domain `U` of a local primitive `g`, the change of value
of a continuous lift `Γ` of `γ` equals `g (γ b) - g (γ a)`. -/
theorem PrimitiveSpace.value_sub_eq_of_isPrimitiveOn
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    {γ : Path x y} {Γ : unitInterval → PrimitiveSpace φ} (hΓ : Continuous Γ)
    (hΓγ : ∀ s, PrimitiveSpace.proj φ (Γ s) = γ s)
    {g : M → F} {U : Set M} (hgU : IsPrimitiveOn φ g U) {a b : unitInterval}
    (hγU : ∀ s ∈ uIcc a b, γ s ∈ U) :
    PrimitiveSpace.value φ (Γ b) - PrimitiveSpace.value φ (Γ a) = g (γ b) - g (γ a) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  let S : Set unitInterval := uIcc a b
  have hpre : IsPreconnected S := by
    have himg : (Subtype.val : unitInterval → ℝ) '' S = uIcc (a : ℝ) (b : ℝ) := by
      ext r
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hs
      · intro hr
        exact ⟨⟨r, uIcc_subset_Icc a.property b.property hr⟩, hr, rfl⟩
    exact (Topology.IsInducing.subtypeVal.isPreconnected_image (s := S)).mp
      (himg.symm ▸ isPreconnected_uIcc)
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hpre
  let c : F := PrimitiveSpace.value φ (Γ a) - g (γ a)
  let f₁ : S → PrimitiveSpace φ := fun s ↦ Γ s
  let f₂ : S → PrimitiveSpace φ := fun s ↦ PrimitiveSpace.graph φ (fun p ↦ g p + c) (γ s)
  have hf₁ : Continuous f₁ := hΓ.comp continuous_subtypeVal
  have hf₂ : Continuous f₂ :=
    (PrimitiveSpace.continuousOn_graph (hgU.add_const c)).comp_continuous
      (γ.continuous.comp continuous_subtypeVal) (fun s ↦ hγU s s.property)
  have heq : f₁ = f₂ := hp.eq_of_comp_eq hf₁ hf₂
    (funext fun s ↦ by simp [f₁, f₂, hΓγ]) ⟨a, left_mem_uIcc⟩
    (PrimitiveSpace.ext (by simp [f₁, f₂, hΓγ]) (by simp [f₁, f₂, c]))
  have hb := congrArg (PrimitiveSpace.value φ) (congrFun heq ⟨b, right_mem_uIcc⟩)
  simp only [f₁, f₂, PrimitiveSpace.value_graph, c] at hb
  rw [hb]
  abel

/-- **Subdivision formula.** Along any finite subdivision of `[0, 1]` whose pieces map into domains
of local primitives `g i`, `continuousPathIntegral φ γ` equals the sum of endpoint differences
`g i (γ (t (i + 1))) - g i (γ (t i))`. -/
theorem continuousPathIntegral_eq_sum_sub_of_subdivision
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (ht₀ : t 0 = 0) (ht₁ : t (Fin.last n) = 1)
    (g : Fin n → M → F) (U : Fin n → Set M)
    (hg : ∀ i, IsPrimitiveOn φ (g i) (U i))
    (hγ : ∀ i, ∀ s ∈ uIcc (t i.castSucc) (t i.succ), γ s ∈ U i) :
    continuousPathIntegral φ γ =
      ∑ i : Fin n, (g i (γ (t i.succ)) - g i (γ (t i.castSucc))) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  let Γ := hp.liftPath γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
    (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph])
  have hΓγ (s : unitInterval) : PrimitiveSpace.proj φ (Γ s) = γ s :=
    congrFun (hp.liftPath_lifts _ _ _) s
  have hterm (i : Fin n) :
      g i (γ (t i.succ)) - g i (γ (t i.castSucc)) =
        PrimitiveSpace.value φ (Γ (t i.succ)) - PrimitiveSpace.value φ (Γ (t i.castSucc)) :=
    (PrimitiveSpace.value_sub_eq_of_isPrimitiveOn hφ Γ.continuous hΓγ (hg i) (hγ i)).symm
  rw [continuousPathIntegral_eq_sub_of_lift hφ Γ.continuous hΓγ,
    Finset.sum_congr rfl fun i _ ↦ hterm i,
    Fin.sum_univ_succ_sub_castSucc (fun k : Fin (n + 1) ↦ PrimitiveSpace.value φ (Γ (t k))),
    ht₀, ht₁]

/-! ### Path operations and homotopy invariance -/

/-- The integral along a constant path vanishes. -/
@[simp]
theorem continuousPathIntegral_refl (x : M) :
    continuousPathIntegral φ (Path.refl x) = 0 := by
  by_cases hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · rw [continuousPathIntegral_eq_sub_of_lift hφ continuous_const
      (Γ := fun _ ↦ PrimitiveSpace.graph φ 0 x) (fun _ ↦ PrimitiveSpace.proj_graph x), sub_self]
  · exact continuousPathIntegral_undef hφ _

/-- Casting the endpoints of a path does not change its integral. -/
@[simp]
theorem continuousPathIntegral_cast (γ : Path x y) {x' y' : M} (hx : x' = x) (hy : y' = y) :
    continuousPathIntegral φ (γ.cast hx hy) = continuousPathIntegral φ γ := by
  subst hx hy
  rfl

/-- Paths agreeing pointwise have the same integral, even with different endpoint expressions. -/
theorem continuousPathIntegral_eq_of_apply_eq {x' y' : M} (γ : Path x y) (γ' : Path x' y')
    (h : ∀ t, γ t = γ' t) : continuousPathIntegral φ γ = continuousPathIntegral φ γ' := by
  obtain rfl : x = x' := by simpa using h 0
  obtain rfl : y = y' := by simpa using h 1
  rw [Path.ext (funext h)]

/-- **Homotopy invariance.** Paths homotopic relative to their endpoints have the same integral. -/
theorem continuousPathIntegral_eq_of_homotopic {γ₁ γ₂ : Path x y} (h : γ₁.Homotopic γ₂) :
    continuousPathIntegral φ γ₁ = continuousPathIntegral φ γ₂ := by
  by_cases hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · rw [continuousPathIntegral, dite_eq_left hφ, continuousPathIntegral, dite_eq_left hφ]
    congr 1
    have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
    exact hp.liftPath_apply_one_eq_of_homotopicRel h (PrimitiveSpace.graph φ 0 x)
      (by rw [Path.coe_toContinuousMap, γ₁.source, PrimitiveSpace.proj_graph])
      (by rw [Path.coe_toContinuousMap, γ₂.source, PrimitiveSpace.proj_graph])
  · simp [continuousPathIntegral_undef hφ]

/-- **Additivity under concatenation.** The integral along `γ.trans γ'` is the sum of the
integrals along `γ` and `γ'`. -/
@[simp]
theorem continuousPathIntegral_trans (γ : Path x y) (γ' : Path y z) :
    continuousPathIntegral φ (γ.trans γ') =
      continuousPathIntegral φ γ + continuousPathIntegral φ γ' := by
  by_cases hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
    have h0 : γ.toContinuousMap 0 = PrimitiveSpace.proj φ (PrimitiveSpace.graph φ 0 x) := by
      rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph]
    let Γ₁ : Path (PrimitiveSpace.graph φ 0 x) (hp.liftPath γ.toContinuousMap _ h0 1) :=
      ⟨hp.liftPath γ.toContinuousMap _ h0, hp.liftPath_zero _ _ h0, rfl⟩
    have h1 : γ'.toContinuousMap 0 = PrimitiveSpace.proj φ (Γ₁ 1) := by
      have := congrFun (hp.liftPath_lifts γ.toContinuousMap _ h0) 1
      simpa [Γ₁] using this.symm
    let Γ₂ : Path (Γ₁ 1) (hp.liftPath γ'.toContinuousMap (Γ₁ 1) h1 1) :=
      ⟨hp.liftPath γ'.toContinuousMap (Γ₁ 1) h1, hp.liftPath_zero _ _ h1, rfl⟩
    have hproj (t : unitInterval) : PrimitiveSpace.proj φ ((Γ₁.trans Γ₂) t) = (γ.trans γ') t := by
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact congrFun (hp.liftPath_lifts γ.toContinuousMap _ h0) _
      · exact congrFun (hp.liftPath_lifts γ'.toContinuousMap _ h1) _
    rw [continuousPathIntegral_eq_sub_of_lift hφ (Γ₁.trans Γ₂).continuous hproj,
      Path.source, Path.target, PrimitiveSpace.value_graph, Pi.zero_apply, sub_zero,
      PrimitiveSpace.value_liftPath_of_localPrimitives hφ γ' (Γ₁ 1) h1]
    have hval1 := PrimitiveSpace.value_liftPath_of_localPrimitives hφ γ
      (PrimitiveSpace.graph φ 0 x) h0
    simpa [Γ₁] using congrArg (· + continuousPathIntegral φ γ') hval1
  · simp [continuousPathIntegral_undef hφ]

/-- **Reversal.** The integral along the reversed path `γ.symm` is the negative of the integral
along `γ`. -/
@[simp]
theorem continuousPathIntegral_symm (γ : Path x y) :
    continuousPathIntegral φ γ.symm = -continuousPathIntegral φ γ := by
  rw [eq_neg_iff_add_eq_zero, ← continuousPathIntegral_trans,
    continuousPathIntegral_eq_of_homotopic (Path.Homotopic.symm_trans γ),
    continuousPathIntegral_refl]

/-! ### Naturality and linearity -/

section Naturality

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']

/-- **Naturality under differentiable maps.** The continuous path integral of the pullback `f^* θ`
along `γ` equals the integral of `θ` along `f ∘ γ`, for any differentiable map `f : M → M'`. -/
theorem continuousPathIntegral_mpullback {θ : RoughForm I' M' F 1}
    (hθ : ∀ p : M', ∃ (g : M' → F) (U : Set M'), p ∈ U ∧ IsPrimitiveOn θ g U)
    {f : M → M'} (hf : MDifferentiable I I' f) (γ : Path x y) :
    continuousPathIntegral (mpullback I I' f θ) γ =
      continuousPathIntegral θ (γ.map hf.continuous) := by
  have hfθ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧
      IsPrimitiveOn (mpullback I I' f θ) g U := fun p ↦
    let ⟨g, U, hpU, hgU⟩ := hθ (f p)
    ⟨g ∘ f, f ⁻¹' U, hpU, hgU.mpullback hf⟩
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hθ
  let Γ := hp.liftPath (γ.map hf.continuous).toContinuousMap (PrimitiveSpace.graph θ 0 (f x))
    (by simp)
  have hΓγ (t : unitInterval) : PrimitiveSpace.proj θ (Γ t) = f (γ t) :=
    congrFun (hp.liftPath_lifts _ _ _) t
  let Λ (t : unitInterval) : PrimitiveSpace (mpullback I I' f θ) :=
    PrimitiveSpace.graph _ (fun _ ↦ PrimitiveSpace.value θ (Γ t)) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hθ
        (Γ.continuous.continuousAt (x := t₀))
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      ((hgU.mpullback hf).add_const c)
      (by simpa only [Λ, PrimitiveSpace.proj_graph, mem_preimage, ← hΓγ] using hxU) ?_
    filter_upwards [hc] with s hs
    simp only [Λ, PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, hs.2, hΓγ,
      Function.comp_apply]
  rw [continuousPathIntegral_eq_sub_of_lift hfθ hΛ (fun t ↦ PrimitiveSpace.proj_graph (γ t)),
    continuousPathIntegral_eq_sub_of_lift hθ Γ.continuous hΓγ]
  simp [Λ]

end Naturality

/-- **Covariance in the coefficients.** For a continuous real-linear map `L : F →L[ℝ] G`,
integrating `RoughForm.mapCoeff L φ` applies `L` to the integral of `φ`. -/
theorem continuousPathIntegral_mapCoeff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G)
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) :
    continuousPathIntegral (RoughForm.mapCoeff L φ) γ = L (continuousPathIntegral φ γ) := by
  have hLφ : ∀ p : M, ∃ (g : M → G) (U : Set M), p ∈ U ∧
      IsPrimitiveOn (RoughForm.mapCoeff L φ) g U := fun p ↦
    let ⟨g, U, hpU, hgU⟩ := hφ p
    ⟨L ∘ g, U, hpU, hgU.mapCoeff L⟩
  have hp := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  let Γ := hp.liftPath γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
    (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph])
  have hΓγ (t : unitInterval) : PrimitiveSpace.proj φ (Γ t) = γ t :=
    congrFun (hp.liftPath_lifts _ _ _) t
  let Λ (t : unitInterval) : PrimitiveSpace (RoughForm.mapCoeff L φ) :=
    PrimitiveSpace.graph _ (fun _ ↦ L (PrimitiveSpace.value φ (Γ t))) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hφ
        (Γ.continuous.continuousAt (x := t₀))
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      ((hgU.mapCoeff L).add_const (L c))
      (by simpa only [Λ, PrimitiveSpace.proj_graph, ← hΓγ] using hxU) ?_
    filter_upwards [hc] with s hs
    simp only [Λ, PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, hs.2, hΓγ,
      Function.comp_apply, map_add]
  rw [continuousPathIntegral_eq_sub_of_lift hLφ hΛ (fun t ↦ PrimitiveSpace.proj_graph (γ t)),
    continuousPathIntegral_eq_sub_of_lift hφ Γ.continuous hΓγ]
  simp [Λ, map_sub]

/-- The integral of the zero form vanishes. -/
@[simp]
theorem continuousPathIntegral_zero (γ : Path x y) :
    continuousPathIntegral (0 : RoughForm I M F 1) γ = 0 := by
  rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ (isPrimitiveOn_zero isOpen_univ)]
  simp

/-- The continuous path integral is additive in forms with local primitives. -/
theorem continuousPathIntegral_add
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn ψ g U)
    (γ : Path x y) :
    continuousPathIntegral (φ + ψ) γ =
      continuousPathIntegral φ γ + continuousPathIntegral ψ γ := by
  have hφψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (φ + ψ) g U := fun p ↦
    let ⟨g, U, hpU, hgU⟩ := hφ p
    let ⟨h, V, hpV, hhV⟩ := hψ p
    ⟨g + h, U ∩ V, ⟨hpU, hpV⟩, hgU.add hhV⟩
  have hpφ := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hφ
  have hpψ := PrimitiveSpace.isCoveringMap_proj_of_localPrimitives hψ
  let Γ := hpφ.liftPath γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
    (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph])
  let Δ := hpψ.liftPath γ.toContinuousMap (PrimitiveSpace.graph ψ 0 x)
    (by rw [Path.coe_toContinuousMap, γ.source, PrimitiveSpace.proj_graph])
  have hΓγ (t : unitInterval) : PrimitiveSpace.proj φ (Γ t) = γ t :=
    congrFun (hpφ.liftPath_lifts _ _ _) t
  have hΔγ (t : unitInterval) : PrimitiveSpace.proj ψ (Δ t) = γ t :=
    congrFun (hpψ.liftPath_lifts _ _ _) t
  let Λ (t : unitInterval) : PrimitiveSpace (φ + ψ) :=
    PrimitiveSpace.graph _ (fun _ ↦ PrimitiveSpace.value φ (Γ t) + PrimitiveSpace.value ψ (Δ t))
      (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hφ
        (Γ.continuous.continuousAt (x := t₀))
    obtain ⟨h, V, hxV, hhV, d, hd⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq_of_localPrimitives hψ
        (Δ.continuous.continuousAt (x := t₀))
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      ((hgU.add hhV).add_const (c + d))
      (by simp only [Λ, PrimitiveSpace.proj_graph]; rw [hΓγ] at hxU; rw [hΔγ] at hxV
          exact ⟨hxU, hxV⟩) ?_
    filter_upwards [hc, hd] with s hcs hds
    simp only [Λ, PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, hcs.2, hds.2, hΓγ, hΔγ,
      Pi.add_apply]
    abel
  rw [continuousPathIntegral_eq_sub_of_lift hφψ hΛ (fun t ↦ PrimitiveSpace.proj_graph (γ t)),
    continuousPathIntegral_eq_sub_of_lift hφ Γ.continuous hΓγ,
    continuousPathIntegral_eq_sub_of_lift hψ Δ.continuous hΔγ]
  simp only [Λ, PrimitiveSpace.value_graph]
  abel

/-- Scalar multiplication by any commuting scalar action commutes with the continuous path integral
for forms with local primitives. -/
theorem continuousPathIntegral_smul_of_localPrimitives {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (c : S)
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) :
    continuousPathIntegral (c • φ) γ = c • continuousPathIntegral φ γ := by
  rw [RoughForm.smul_eq_mapCoeff, continuousPathIntegral_mapCoeff _ hφ]
  rfl

/-- Scalar multiplication by a division ring acting continuously and commuting with `ℝ` commutes
unconditionally with `continuousPathIntegral`. -/
@[simp]
theorem continuousPathIntegral_smul {S : Type*} [DivisionRing S] [Module S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (c : S) (γ : Path x y) :
    continuousPathIntegral (c • φ) γ = c • continuousPathIntegral φ γ := by
  by_cases hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U
  · exact continuousPathIntegral_smul_of_localPrimitives c hφ γ
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hcφ : ¬ ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (c • φ) g U := by
        intro h
        apply hφ
        intro p
        obtain ⟨g, U, hpU, hgU⟩ := h p
        have hg' := hgU.mapCoeff (c⁻¹ • ContinuousLinearMap.id ℝ F)
        rw [← RoughForm.smul_eq_mapCoeff, inv_smul_smul₀ hc] at hg'
        exact ⟨_, U, hpU, hg'⟩
      rw [continuousPathIntegral_undef hφ, continuousPathIntegral_undef hcφ, smul_zero]

/-- Negating the form negates the continuous path integral unconditionally. -/
@[simp]
theorem continuousPathIntegral_neg (γ : Path x y) :
    continuousPathIntegral (-φ) γ = -continuousPathIntegral φ γ := by
  simpa using continuousPathIntegral_smul (φ := φ) (-1 : ℝ) γ

/-- The continuous path integral is subtractive in forms with local primitives. -/
theorem continuousPathIntegral_sub
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hψ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn ψ g U)
    (γ : Path x y) :
    continuousPathIntegral (φ - ψ) γ =
      continuousPathIntegral φ γ - continuousPathIntegral ψ γ := by
  have hneg : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn (-ψ) g U := fun p ↦
    let ⟨h, V, hpV, hhV⟩ := hψ p
    ⟨-h, V, hpV, hhV.neg⟩
  rw [sub_eq_add_neg, continuousPathIntegral_add hφ hneg, continuousPathIntegral_neg,
    ← sub_eq_add_neg]

/-! ### Comparison with `TauCeti.pathIntegral` and `curveIntegral` -/

section Comparison

/-- **Comparison with smooth path integrals.** For a continuous `1`-form `φ` with local primitives
and complete coefficients `F`, the continuous path integral along a path `γ` following a `C¹` curve
`c` agrees with `TauCeti.pathIntegral φ c 0 1`. -/
theorem continuousPathIntegral_eq_pathIntegral [CompleteSpace F]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hφ₀ : IsSmoothForm I 0 φ) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    {γ : Path x y} (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral φ γ = pathIntegral φ c 0 1 := by
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU⟩ := hφ (c t₀)
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp (hgU.isOpen.preimage hc.continuous) (t₀ : ℝ) hxU
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Γ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (hgU.add_const (pathIntegral φ c 0 t₀ - g (c t₀)))
      (by simp only [Γ, PrimitiveSpace.proj_graph, hγ]; exact hxU) ?_
    filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (t₀ : ℝ) hδ)] with s hs
    have hsub : uIcc (t₀ : ℝ) s ⊆ c ⁻¹' U := by
      refine (Set.OrdConnected.uIcc_subset ?_ (Metric.mem_ball_self (x := (t₀ : ℝ)) hδ) hs).trans
        hball
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Γ, hγ]
    rw [← pathIntegral_add_adjacent (hint 0 t₀) (hint t₀ s),
      pathIntegral_eq_sub_of_isPrimitiveOn hgU (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero)
        (fun t ht ↦ hsub ht) (hint t₀ s)]
    abel
  rw [continuousPathIntegral_eq_sub_of_lift hφ hΓ (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp [Γ]

/-- On a real normed space `E`, for a continuous covector field `α : E → E →L[ℝ] F` with local
primitives and complete coefficients, `continuousPathIntegral` along a path following a `C¹` curve
agrees with Mathlib's `curveIntegral α γ`. -/
theorem continuousPathIntegral_ofSubsingleton_eq_curveIntegral [CompleteSpace F]
    {α : E → E →L[ℝ] F} (hα : Continuous α)
    (hφ : ∀ p : E, ∃ (g : E → F) (U : Set E), p ∈ U ∧
      IsPrimitiveOn (I := 𝓘(ℝ, E))
        ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
          RoughForm 𝓘(ℝ, E) E F 1) g U)
    {c : ℝ → E} (hc : ContDiff ℝ 1 c) {a b : E} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral (I := 𝓘(ℝ, E))
        ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
          RoughForm 𝓘(ℝ, E) E F 1) γ =
      curveIntegral α γ := by
  let ψ : RoughForm 𝓘(ℝ, E) E F 1 :=
    fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)
  have hsmooth : IsSmoothForm 𝓘(ℝ, E) 0 ψ :=
    (isSmoothForm_modelSpace_iff (φ := ψ)).mpr <| contDiff_zero.mpr <|
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
        (0 : Fin 1)).continuous.comp hα
  exact (continuousPathIntegral_eq_pathIntegral hφ hsmooth hc.contMDiff hγ).trans
    (pathIntegral_ofSubsingleton_eq_curveIntegral α hγ)

/-- On an open submanifold `U : TopologicalSpace.Opens E` of a real normed space, for a covector
field `α : E → E →L[ℝ] F` continuous on `U` with local primitives on `U` and complete coefficients,
`continuousPathIntegral` along a path `γ` in `U` following a `C¹` curve agrees with Mathlib's
`curveIntegral α (γ.map continuous_subtypeVal)`. -/
theorem continuousPathIntegral_mpullback_subtypeVal_ofSubsingleton_eq_curveIntegral
    [CompleteSpace F] {U : TopologicalSpace.Opens E} {α : E → E →L[ℝ] F}
    (hα : ContinuousOn α U)
    (hφ : ∀ p : U, ∃ (g : U → F) (V : Set U), p ∈ V ∧
      IsPrimitiveOn
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun q ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) :
            RoughForm 𝓘(ℝ, E) E F 1)) g V)
    {c : ℝ → U} (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c) {a b : U} {γ : Path a b}
    (hγ : ∀ t : unitInterval, γ t = c t) :
    continuousPathIntegral
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E)
          ((fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)) :
            RoughForm 𝓘(ℝ, E) E F 1)) γ =
      curveIntegral α (γ.map continuous_subtypeVal) := by
  let ψ : RoughForm 𝓘(ℝ, E) E F 1 :=
    fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α p)
  have hsmooth : IsSmoothForm 𝓘(ℝ, E) 0 (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) ψ) := by
    rw [isSmoothForm_def]
    intro p
    have hψp : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) 0
        (fun q ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) q (ψ q)) (p : E) := by
      refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
      rw [RoughForm.inChartAt_modelSpace]
      have hcont : ContinuousOn (fun q : E ↦
          ContinuousAlternatingMap.ofSubsingleton ℝ E F (0 : Fin 1) (α q)) (U : Set E) :=
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
          (0 : Fin 1)).continuous.comp_continuousOn hα
      exact (contDiffAt_zero.mpr ⟨U, U.isOpen.mem_nhds p.property, hcont⟩).contDiffWithinAt
    exact hψp.mpullback_form (contMDiff_subtypeVal (n := 1) p) le_rfl
  rw [continuousPathIntegral_eq_pathIntegral hφ hsmooth hc hγ,
    pathIntegral_mpullback ψ (fun _ _ ↦ contMDiff_subtypeVal.mdifferentiable one_ne_zero _)
      (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero),
    pathIntegral_ofSubsingleton_eq_curveIntegral α (c := Subtype.val ∘ c)
      (γ := γ.map continuous_subtypeVal) (fun t ↦ congrArg Subtype.val (hγ t))]

end Comparison

/-! ### Loop criteria for global primitives -/

section LoopCriterion

/-- A global primitive constructed from continuous path integrals when every loop integral
vanishes, on any `C¹` manifold (without assuming connectedness). -/
private theorem exists_isPrimitiveOn_univ_of_forall_loop_eq_zero
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U)
    (hloop : ∀ (x : M) (γ : Path x x), continuousPathIntegral φ γ = 0) :
    ∃ g : M → F, IsPrimitiveOn φ g univ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  let baseOf : ∀ (S : Set M), S.Nonempty → M := fun _ hS ↦ hS.choose
  let base (x : M) : M := baseOf (pathComponent x) ⟨x, mem_pathComponent_self x⟩
  have hjoined (x : M) : Joined (base x) x :=
    (mem_pathComponent_iff.mp
      (⟨x, mem_pathComponent_self x⟩ : (pathComponent x).Nonempty).choose_spec).symm
  let g (x : M) : F := continuousPathIntegral φ (hjoined x).somePath
  have hg_eq {x y : M} (hxy : base x = base y) (γ : Path (base x) y) :
      g y = continuousPathIntegral φ γ := by
    let γ₀ : Path (base x) y := (hjoined y).somePath.cast hxy rfl
    have h0 := hloop (base x) (γ₀.trans γ.symm)
    rw [continuousPathIntegral_trans, continuousPathIntegral_symm, add_neg_eq_zero] at h0
    simpa [g, γ₀] using h0
  have hloc (p : M) : ∃ V : Set M, p ∈ V ∧ IsPrimitiveOn φ g V := by
    obtain ⟨h, U, hpU, hhU⟩ := hφ p
    have hprim := (hhU.add_const (g p - h p)).mono (hhU.isOpen.pathComponentIn p)
      pathComponentIn_subset
    have heqOn : EqOn g (fun q ↦ h q + (g p - h p)) (pathComponentIn U p) := by
      intro q hq
      obtain ⟨δ, hδU⟩ := hq
      have hbase : base p = base q := by
        have hpc : pathComponent p = pathComponent q :=
          Set.ext fun r ↦ ⟨fun hr ↦ (Joined.symm ⟨δ⟩).trans hr, fun hr ↦ Joined.trans ⟨δ⟩ hr⟩
        simp only [base, hpc]
      rw [hg_eq hbase ((hjoined p).somePath.trans δ), continuousPathIntegral_trans,
        continuousPathIntegral_eq_sub_of_isPrimitiveOn hφ hhU δ hδU]
      simp only [g]
      abel
    refine ⟨pathComponentIn U p, mem_pathComponentIn_self hpU, hprim.isOpen,
      hprim.mdifferentiableOn.congr heqOn, fun q hq ↦ ?_⟩
    have heq : g =ᶠ[𝓝 q] fun r ↦ h r + (g p - h p) :=
      eventuallyEq_of_mem (hprim.isOpen.mem_nhds hq) heqOn
    rw [mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (g := fun r ↦ h r + (g p - h p))
      (c := 0) (heq.mono fun r hr ↦ by simp [hr])]
    exact hprim.mextDeriv_eq q hq
  refine ⟨g, isOpen_univ, fun p _ ↦ ?_, fun p _ ↦ ?_⟩
  · obtain ⟨V, hpV, hV⟩ := hloc p
    exact ((hV.mdifferentiableOn p hpV).mdifferentiableAt
      (hV.isOpen.mem_nhds hpV)).mdifferentiableWithinAt
  · obtain ⟨V, hpV, hV⟩ := hloc p
    exact hV.mextDeriv_eq p hpV

/-- **Loop criterion for global primitives.** A `1`-form with local primitives on a `C¹` manifold
has a global primitive if and only if its continuous path integral vanishes along every continuous
loop. No connectedness assumption is required. -/
theorem exists_isPrimitiveOn_univ_iff_forall_continuousPathIntegral_loop_eq_zero
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U) :
    (∃ g : M → F, IsPrimitiveOn φ g univ) ↔
      ∀ (x : M) (γ : Path x x), continuousPathIntegral φ γ = 0 :=
  ⟨fun ⟨_, hg⟩ _ γ ↦ by rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ hg γ, sub_self],
    exists_isPrimitiveOn_univ_of_forall_loop_eq_zero hφ⟩

/-- **Basepoint loop criterion on a preconnected manifold.** On a preconnected `C¹` manifold,
a `1`-form `φ` with local primitives has a global primitive vanishing at `x₀` whose values are the
continuous path integrals from `x₀` if and only if every continuous loop at `x₀` has integral `0`.
-/
theorem exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_iff [PreconnectedSpace M]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U) (x₀ : M) :
    (∃ g : M → F, IsPrimitiveOn φ g univ ∧
        ∀ (y : M) (γ : Path x₀ y), g y = continuousPathIntegral φ γ) ↔
      ∀ γ : Path x₀ x₀, continuousPathIntegral φ γ = 0 := by
  constructor
  · rintro ⟨g, hg, _⟩ γ
    rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ hg γ, sub_self]
  · intro hloop
    have := I.locallyPathConnectedSpace
    have := ChartedSpace.locallyPathConnectedSpace H M
    have : Nonempty M := ⟨x₀⟩
    have : ConnectedSpace M := ⟨inferInstance⟩
    have : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    have hall : ∀ (x : M) (γ : Path x x), continuousPathIntegral φ γ = 0 := fun x γ ↦ by
      let δ := PathConnectedSpace.somePath x₀ x
      have h0 := hloop ((δ.trans γ).trans δ.symm)
      rw [continuousPathIntegral_trans, continuousPathIntegral_trans,
        continuousPathIntegral_symm] at h0
      simpa using h0
    obtain ⟨g, hg⟩ := exists_isPrimitiveOn_univ_of_forall_loop_eq_zero hφ hall
    refine ⟨fun y ↦ g y - g x₀, ?_, fun y γ ↦ ?_⟩
    · simpa only [sub_eq_add_neg] using hg.add_const (-g x₀)
    · exact (continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ hg γ).symm

/-- On a preconnected `C¹` manifold with basepoint `x₀`, a `1`-form with local primitives has a
global primitive if and only if its integral vanishes along every continuous loop at `x₀`. -/
theorem
    exists_isPrimitiveOn_univ_iff_forall_continuousPathIntegral_loop_eq_zero_of_preconnectedSpace
    [PreconnectedSpace M]
    (hφ : ∀ p : M, ∃ (g : M → F) (U : Set M), p ∈ U ∧ IsPrimitiveOn φ g U) (x₀ : M) :
    (∃ g : M → F, IsPrimitiveOn φ g univ) ↔
      ∀ γ : Path x₀ x₀, continuousPathIntegral φ γ = 0 :=
  ⟨fun ⟨_, hg⟩ γ ↦ by rw [continuousPathIntegral_eq_sub_of_isPrimitiveOn_univ hg γ, sub_self],
    fun h ↦
      let ⟨g, hg, _⟩ := (exists_isPrimitiveOn_univ_and_eq_continuousPathIntegral_iff hφ x₀).mpr h
      ⟨g, hg⟩⟩

end LoopCriterion

end TauCeti
