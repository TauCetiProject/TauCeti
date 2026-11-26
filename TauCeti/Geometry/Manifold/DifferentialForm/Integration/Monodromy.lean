/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.Topology
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrals of `1`-forms with local primitives along continuous paths

A `1`-form `φ` *has local primitives* when every point lies in an open set carrying a primitive of
`φ` (`TauCeti.IsPrimitiveOn`). Such a form can be integrated along every continuous path, with no
regularity of the form, of the path or of the coefficients: the projection of the space
`TauCeti.PrimitiveSpace φ` of points and values is then a covering map, and the integral
`TauCeti.monodromyIntegral φ γ` of `φ` along a path `γ` is the change of value along a lift of `γ`
to this covering. It is built from values of primitives and never from a derivative of the path.

The integral does not depend on the lift (`TauCeti.monodromyIntegral_eq_sub`). It is the sum of the
increments of local primitives along any subdivision of the parameter interval into pieces mapped
into their domains (`TauCeti.monodromyIntegral_eq_sum`), additive under concatenation, negated under
reversal, invariant under homotopy relative to the endpoints, and natural under differentiable maps.
For a continuous form with complete coefficients it is the line integral `TauCeti.pathIntegral`
along `C¹` curves (`TauCeti.monodromyIntegral_eq_pathIntegral`). On a connected manifold a form with
local primitives has a global primitive exactly when its integrals along loops at a base point
vanish (`TauCeti.exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero`).

Only a `C¹` manifold over a real model with corners is used: neither finite dimensionality, the
Hausdorff property nor completeness of the coefficients. For closed `C¹` forms on finite-dimensional
Hausdorff manifolds with complete coefficients, where the local primitives come from the Poincaré
lemma, the integral is `TauCeti.pathClassIntegral` (`TauCeti.monodromyIntegral_eq_pathClassIntegral`
in `TauCeti.Geometry.Manifold.DeRham.Period`).

## Main declarations

* `TauCeti.monodromyIntegral φ γ`: the integral of a `1`-form with local primitives along a
  continuous path.
* `TauCeti.monodromyIntegral_eq_sub`: it is the change of value along any continuous lift.
* `TauCeti.monodromyIntegral_eq_sum`: it is the sum of the increments of local primitives along a
  subdivision.
* `TauCeti.monodromyIntegral_trans`, `TauCeti.monodromyIntegral_symm`,
  `TauCeti.monodromyIntegral_eq_of_homotopic`, `TauCeti.monodromyIntegral_mpullback`:
  concatenation, reversal, homotopy invariance and naturality.
* `TauCeti.monodromyIntegral_eq_pathIntegral`: agreement with line integrals along `C¹` curves.
* `TauCeti.exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero`: global primitives and
  loop integrals.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
* Allen Hatcher, *Algebraic Topology*, Propositions 1.30 (homotopy lifting) and 1.34 (uniqueness
  of lifts).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold I 1 M]
  {φ : RoughForm I M F 1} {g : M → F} {U : Set M} {x y z : M}

open Classical in
/-- The integral of a `1`-form `φ` along a continuous path `γ` from `x` to `y`: when every point
lies in an open set carrying a primitive of `φ`, the value at the end of the lift of `γ` to the
covering space `TauCeti.PrimitiveSpace φ` of local primitives which starts at `x` with value `0`.
It is `0` when `φ` does not have local primitives. -/
def monodromyIntegral (φ : RoughForm I M F 1) (γ : Path x y) : F :=
  if hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U then
    PrimitiveSpace.value φ
      ((PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ).liftPath
        γ.toContinuousMap (PrimitiveSpace.graph φ 0 x) (by simp) 1)
  else 0

/-- The integral of a form without local primitives is `0` by convention. -/
theorem monodromyIntegral_undef (hφ : ¬∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) : monodromyIntegral φ γ = 0 :=
  dite_eq_right hφ

/-- **The integral is the change of value along any lift.** If `Γ` is a continuous lift of the
path `γ` to the covering space of local primitives of `φ`, the integral of `φ` along `γ` is the
change of the value of `Γ`. -/
theorem monodromyIntegral_eq_sub (hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U)
    {γ : Path x y} {Γ : unitInterval → PrimitiveSpace φ} (hΓ : Continuous Γ)
    (hΓγ : ∀ t, PrimitiveSpace.proj φ (Γ t) = γ t) :
    monodromyIntegral φ γ = PrimitiveSpace.value φ (Γ 1) - PrimitiveSpace.value φ (Γ 0) := by
  have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
  -- translating `Γ` so that it starts with value `0` gives the lift of the definition
  let Γ' : C(unitInterval, PrimitiveSpace φ) :=
    ⟨fun t ↦ PrimitiveSpace.translate φ (-PrimitiveSpace.value φ (Γ 0)) (Γ t),
      (PrimitiveSpace.continuous_translate _).comp hΓ⟩
  have h := (hp.eq_liftPath_iff' (Γ := Γ') (γ := γ.toContinuousMap)
    (e := PrimitiveSpace.graph φ 0 x) (by simp)).mpr
    ⟨funext fun t ↦ by simp [Γ', hΓγ], PrimitiveSpace.ext (by simp [Γ', hΓγ]) (by simp [Γ'])⟩
  rw [monodromyIntegral, dite_eq_left hφ, ← h]
  simp [Γ', sub_eq_add_neg]

/-- **Integration inside the domain of a primitive.** The integral of `φ` along a path inside the
domain `U` of a primitive `g` of `φ` is the increment of `g`. -/
theorem IsPrimitiveOn.monodromyIntegral_eq_sub
    (hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U) (hg : IsPrimitiveOn φ g U)
    {γ : Path x y} (hγU : ∀ t, γ t ∈ U) : monodromyIntegral φ γ = g y - g x := by
  -- the graph of `g` along `γ` is a lift of `γ`
  rw [TauCeti.monodromyIntegral_eq_sub hφ
    ((PrimitiveSpace.continuousOn_graph hg).comp_continuous γ.continuous hγU)
    fun t ↦ PrimitiveSpace.proj_graph (γ t)]
  simp

/-- **Integration along a subdivision.** If `0 = t₀, t₁, …, tₙ = 1` subdivide the parameter
interval so that `γ` maps the interval between `tᵢ` and `tᵢ₊₁` into the domain of a primitive `gᵢ`
of `φ`, then the integral of `φ` along `γ` is the sum of the increments of the `gᵢ`. The choice of
the primitives does not matter, and the `tᵢ` need not be monotone. -/
theorem monodromyIntegral_eq_sum (hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U)
    (γ : Path x y) {n : ℕ} {t : ℕ → unitInterval} (ht₀ : t 0 = 0) (htn : t n = 1) {g : ℕ → M → F}
    {U : ℕ → Set M} (hg : ∀ i < n, IsPrimitiveOn φ (g i) (U i))
    (hγU : ∀ i < n, ∀ s ∈ uIcc (t i) (t (i + 1)), γ s ∈ U i) :
    monodromyIntegral φ γ = ∑ i ∈ Finset.range n, (g i (γ (t (i + 1))) - g i (γ (t i))) := by
  obtain ⟨Γ, hΓγ, -⟩ := (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
    hφ).exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph φ 0 x) (by simp)
  have hΓγ' (s : unitInterval) : PrimitiveSpace.proj φ (Γ s) = γ s := congrFun hΓγ s
  rw [monodromyIntegral_eq_sub hφ Γ.continuous hΓγ', ← ht₀, ← htn,
    ← Finset.sum_range_sub (fun i ↦ PrimitiveSpace.value φ (Γ (t i)))]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  simpa only [hΓγ'] using PrimitiveSpace.value_sub_value_eq_of_isPreconnected Γ.continuous (hg i hi)
    isPreconnected_uIcc (fun s hs ↦ (hΓγ' s).symm ▸ hγU i hi s hs) left_mem_uIcc right_mem_uIcc

/-- The integral along a constant path vanishes. -/
@[simp]
theorem monodromyIntegral_refl (x : M) : monodromyIntegral φ (.refl x) = 0 := by
  by_cases hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U
  · obtain ⟨g, U, hxU, hg⟩ := hφ x
    simpa using hg.monodromyIntegral_eq_sub hφ (γ := .refl x) fun _ ↦ hxU
  · exact monodromyIntegral_undef hφ _

/-- The integral along a concatenation of paths is the sum of the integrals. -/
@[simp]
theorem monodromyIntegral_trans (γ : Path x y) (γ' : Path y z) :
    monodromyIntegral φ (γ.trans γ') = monodromyIntegral φ γ + monodromyIntegral φ γ' := by
  by_cases hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U
  · have hp := PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn hφ
    obtain ⟨Γ, hΓγ, -⟩ := hp.exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
      (by simp)
    obtain ⟨Γ', hΓ'γ', hΓ'0⟩ := hp.exists_path_lifts γ'.toContinuousMap (Γ 1)
      (by simpa using (congrFun hΓγ 1).symm)
    -- the lift of `γ` followed by the lift of `γ'` is a lift of `γ.trans γ'`
    let L : Path (Γ 0) (Γ' 1) := (⟨Γ, rfl, rfl⟩ : Path (Γ 0) (Γ 1)).trans ⟨Γ', hΓ'0, rfl⟩
    rw [monodromyIntegral_eq_sub hφ L.continuous fun t ↦ ?_, Path.source, Path.target,
      monodromyIntegral_eq_sub hφ Γ.continuous (congrFun hΓγ),
      monodromyIntegral_eq_sub hφ Γ'.continuous (congrFun hΓ'γ'), hΓ'0]
    · abel
    · simp only [L, Path.trans_apply]
      split_ifs
      exacts [congrFun hΓγ _, congrFun hΓ'γ' _]
  · simp [monodromyIntegral_undef hφ]

/-- The integral along the reversed path is the negative of the integral. -/
@[simp]
theorem monodromyIntegral_symm (γ : Path x y) :
    monodromyIntegral φ γ.symm = -monodromyIntegral φ γ := by
  by_cases hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U
  · obtain ⟨Γ, hΓγ, -⟩ := (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
      hφ).exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph φ 0 x) (by simp)
    -- the lift of `γ` run backwards is a lift of the reversed path
    rw [monodromyIntegral_eq_sub hφ Γ.continuous (congrFun hΓγ),
      monodromyIntegral_eq_sub hφ (Γ.continuous.comp unitInterval.continuous_symm)
        fun t ↦ by rw [Path.symm_apply]; exact congrFun hΓγ _]
    simp
  · simp [monodromyIntegral_undef hφ]

/-- **Homotopy invariance.** Paths that are homotopic relative to their endpoints have the same
integral. -/
theorem monodromyIntegral_eq_of_homotopic {γ γ' : Path x y} (h : γ.Homotopic γ') :
    monodromyIntegral φ γ = monodromyIntegral φ γ' := by
  by_cases hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U
  · rw [monodromyIntegral, monodromyIntegral, dite_eq_left hφ, dite_eq_left hφ,
      (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
        hφ).liftPath_apply_one_eq_of_homotopicRel h]
  · rw [monodromyIntegral_undef hφ, monodromyIntegral_undef hφ]

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {θ : RoughForm I' M' F 1} {f : M → M'}

/-- **Naturality.** The integral of the pullback of a form `θ` with local primitives along a
differentiable map `f` over a path `γ` is the integral of `θ` over the image of `γ`. -/
theorem monodromyIntegral_mpullback
    (hθ : ∀ z, ∃ g : M' → F, ∃ U, z ∈ U ∧ IsPrimitiveOn θ g U) (hf : MDifferentiable I I' f)
    (γ : Path x y) :
    monodromyIntegral (mpullback I I' f θ) γ = monodromyIntegral θ (γ.map hf.continuous) := by
  have hfθ (z : M) : ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn (mpullback I I' f θ) g U :=
    let ⟨g, U, hzU, hgU⟩ := hθ (f z)
    ⟨g ∘ f, f ⁻¹' U, hzU, hgU.mpullback hf⟩
  -- a lift of the image path `f ∘ γ`
  obtain ⟨Γ, hΓγ, -⟩ := (PrimitiveSpace.isCoveringMap_proj_of_forall_exists_isPrimitiveOn
    hθ).exists_path_lifts (γ.map hf.continuous).toContinuousMap (PrimitiveSpace.graph θ 0 (f x))
      (by simp)
  have hΓγ' (t : unitInterval) : PrimitiveSpace.proj θ (Γ t) = f (γ t) := congrFun hΓγ t
  -- the same values over `γ` give a lift of `γ` for the pullback
  let Λ (t : unitInterval) : PrimitiveSpace (mpullback I I' f θ) :=
    PrimitiveSpace.graph _ (fun _ ↦ PrimitiveSpace.value θ (Γ t)) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU⟩ := hθ (PrimitiveSpace.proj θ (Γ t₀))
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      ((hgU.mpullback hf).add_const
        (PrimitiveSpace.value θ (Γ t₀) - g (PrimitiveSpace.proj θ (Γ t₀))))
      (by simpa only [Λ, PrimitiveSpace.proj_graph, mem_preimage, ← hΓγ'] using hxU) ?_
    filter_upwards [PrimitiveSpace.eventually_value_eq_add_const Γ.continuous.continuousAt hgU hxU]
      with s hs
    simp only [Λ, PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, hs.2, hΓγ',
      Function.comp_apply]
  rw [monodromyIntegral_eq_sub hfθ hΛ fun t ↦ PrimitiveSpace.proj_graph (γ t),
    monodromyIntegral_eq_sub hθ Γ.continuous hΓγ']
  simp [Λ]

end Pullback

/-! ### Line integrals along `C¹` curves -/

section PathIntegral

variable [CompleteSpace F]

/-- **The fundamental theorem of calculus inside the domain of a primitive.** The line integral of
a continuous `1`-form `φ` along a `C¹` curve `c` over an interval mapped into the domain of a
primitive `g` of `φ` is the increment of `g`. The primitive need only be differentiable. -/
theorem IsPrimitiveOn.pathIntegral_eq_sub (hg : IsPrimitiveOn φ g U) (hφ : IsSmoothForm I 0 φ)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {a b : ℝ} (hab : ∀ t ∈ uIcc a b, c t ∈ U) :
    pathIntegral φ c a b = g (c b) - g (c a) := by
  rw [pathIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g ∘ c) (fun t ht ↦ ?_)
    (hφ.intervalIntegrable_apply_curveVelocity hc a b)
  rw [← hg.mextDeriv_eq _ (hab t ht), mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  exact Manifold.hasDerivAt_comp_curve
    ((hg.mdifferentiableOn _ (hab t ht)).mdifferentiableAt (hg.isOpen.mem_nhds (hab t ht)))
    (Manifold.hasMFDerivAt_curveVelocity ((hc t).mdifferentiableAt one_ne_zero))

/-- **Paths following smooth curves.** The integral of a continuous `1`-form with local primitives
along a path which follows a `C¹` curve `c` is the line integral along `c`. -/
theorem monodromyIntegral_eq_pathIntegral
    (hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U) (hφ₀ : IsSmoothForm I 0 φ)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {γ : Path x y} (hγ : ∀ t : unitInterval, γ t = c t) :
    monodromyIntegral φ γ = pathIntegral φ c 0 1 := by
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  -- the lift: follow `γ`, with value the line integral from `0`
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, U, hxU, hgU⟩ := hφ (c t₀)
    -- near `t₀`, the curve stays in `U`, where `φ = dg`
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
      hgU.pathIntegral_eq_sub hφ₀ hc hsub]
    abel
  rw [monodromyIntegral_eq_sub hφ hΓ fun t ↦ PrimitiveSpace.proj_graph (γ t)]
  simp [Γ]

end PathIntegral

/-! ### Global primitives -/

/-- **Global primitives and loop integrals.** On a connected manifold, a `1`-form with local
primitives has a primitive on the whole manifold exactly when its integrals along all loops at a
base point `x₀` vanish. The integral from `x₀` is then such a primitive. -/
theorem exists_isPrimitiveOn_univ_iff_forall_monodromyIntegral_eq_zero [PreconnectedSpace M]
    (hφ : ∀ z, ∃ g : M → F, ∃ U, z ∈ U ∧ IsPrimitiveOn φ g U) (x₀ : M) :
    (∃ g : M → F, IsPrimitiveOn φ g univ) ↔ ∀ γ : Path x₀ x₀, monodromyIntegral φ γ = 0 := by
  refine ⟨fun ⟨g, hg⟩ γ ↦ by simp [hg.monodromyIntegral_eq_sub hφ fun t ↦ mem_univ (γ t)],
    fun h ↦ ?_⟩
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have : ConnectedSpace M := { toNonempty := ⟨x₀⟩ }
  have : PathConnectedSpace M := .of_locallyPathConnectedSpace
  -- the integral does not depend on the path between two points
  have hindep {y : M} (γ γ' : Path x₀ y) : monodromyIntegral φ γ = monodromyIntegral φ γ' := by
    have := h (γ.trans γ'.symm)
    rwa [monodromyIntegral_trans, monodromyIntegral_symm, ← sub_eq_add_neg, sub_eq_zero] at this
  refine ⟨fun y ↦ monodromyIntegral φ (PathConnectedSpace.somePath x₀ y),
    isPrimitiveOn_of_forall_eventuallyEq_add_const isOpen_univ fun x _ ↦ ?_⟩
  obtain ⟨g, U, hxU, hgU⟩ := hφ x
  refine ⟨g, U, hxU, hgU, monodromyIntegral φ (PathConnectedSpace.somePath x₀ x) - g x, ?_⟩
  -- near `x`, join `x` to `y` by a path inside `U`
  obtain ⟨V, hV, hVc, hVU⟩ := (pathConnected_subset_basis hgU.isOpen hxU).ex_mem
  filter_upwards [hV] with y hy
  have hxy := hVc.joinedIn x (mem_of_mem_nhds hV) y hy
  rw [hindep _ ((PathConnectedSpace.somePath x₀ x).trans hxy.somePath), monodromyIntegral_trans,
    hgU.monodromyIntegral_eq_sub hφ fun t ↦ hVU (hxy.somePath_mem t)]
  abel

end TauCeti
