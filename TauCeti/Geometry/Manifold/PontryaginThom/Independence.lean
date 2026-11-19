/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.Homotopy.Isotopy.Linearization
import TauCeti.Topology.Homotopy.Isotopy.RadialShrink

/-!
# Independence of the Pontryagin–Thom collapse from the tube

The Pontryagin–Thom collapse `M → OnePoint V` of a framed submanifold is built from a chosen
framed tube `τ : S × V → M` around it (`TauCeti.pontryaginThomCollapse`). This file shows that, up
to homotopy, it depends on the tube only through the framing it induces along the core.

Let `τ₀` and `τ₁` be framed tubes around the same map `f : S → M`, with `S` compact, `M`
Hausdorff and `V` a real normed space. Suppose that near the core `τ₁` reads in `τ₀` as
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`, for a continuous family `A` of linear
automorphisms of `V` (`TauCeti.HasTransitionFDeriv`). For tubes whose transition is `C¹` in the
fibre direction, `A x` is the fibre derivative of the normal coordinate of `τ₀⁻¹ ∘ τ₁` at `(x, 0)`
(`TauCeti.HasTransitionFDeriv.of_hasFDerivAt`). Then:

* the collapse of `τ₁` is homotopic to the collapse of `τ₀` reframed by `A`, the tube
  `(x, v) ↦ τ₀ (x, A x v)`
  (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph`);
* if `A` is homotopic to the identity through linear automorphisms, the collapses of `τ₁` and `τ₀`
  are homotopic (`TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic`), and so are their
  collapses onto the sphere `Sᵏ` for `V = ℝᵏ`
  (`TauCeti.IsFramedTube.pontryaginThomSphereMap_homotopic`).

Together with the invariance under homotopies of the framing
(`TauCeti.pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic`), the homotopy class of
the collapse depends only on the homotopy class of the framing of the core read to first order.
Some condition on `A` is needed: reframing a tube with fibre `ℝᵏ`, `k ≥ 1`, by a reflection of
`ℝᵏ` in a hyperplane composes its collapse with a reflection of `Sᵏ`, which has degree `-1`.

The proof has two steps.

* **Shrinking.** The radial compressions `v ↦ (1 + s ‖v‖ / r)⁻¹ • v`, `s ∈ [0, 1]`, form an
  isotopy of tubes from `τ₁` to its reparametrized restriction to `S × B(0, r)`
  (`TauCeti.isOpenEmbedding_radialShrink_family`), so the collapse does not change up to
  homotopy. For small `r` the shrunk tube lies in the image of `τ₀`, and it is `τ₀ ∘ g` for an
  open embedding `g` of `S × V` fixing the zero section.
* **The Alexander trick.** The rescalings `g_t (x, v) = ((g (x, t v)).1, t⁻¹ (g (x, t v)).2)`,
  `t ∈ (0, 1]`, extended at `t = 0` by the linearization `(x, v) ↦ (x, A x v)`, form an isotopy
  of open embeddings of `S × V` (`TauCeti.isOpenEmbedding_zeroSectionRescale`). Continuity at
  `t = 0` is the uniform first-order estimate for `g`, and for its inverse, which follows from it
  by compactness of `S`. So `τ₀ ∘ g` is isotopic to the reframed tube, and their collapses are
  homotopic (`TauCeti.pontryaginThomCollapseMap_homotopic`).

Only the topology of the tubes and the first-order estimate along the core are used; no smooth
structure on `S` or `M` is needed.

## Main definitions and results

* `TauCeti.HasTransitionFDeriv τ₀ τ₁ A`: the transition from `τ₁` to `τ₀` has fibre derivative
  `A` along the core.
* `TauCeti.HasTransitionFDeriv.refl`, `TauCeti.HasTransitionFDeriv.comp_prodUnitsHomeomorph`: the
  transition from a tube to itself has fibre derivative the identity, and from a tube reframed by
  `A` to the tube, fibre derivative `A`.
* `TauCeti.HasTransitionFDeriv.of_hasFDerivAt`: a transition that is `C¹` in the fibre direction
  has a fibre derivative along the core.
* `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph`: the collapse
  of `τ₁` is that of `τ₀` reframed by `A`, up to homotopy.
* `TauCeti.IsFramedTube.pontryaginThomCollapseMap_homotopic`,
  `TauCeti.IsFramedTube.pontryaginThomSphereMap_homotopic`: tubes whose transition derivative is
  homotopic to the identity have homotopic collapses.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §7.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5 (uniqueness of tubular neighbourhoods, through the rescaling of an embedding to
  its derivative along the zero section).
-/

public section

open Function Set Topology Metric

namespace TauCeti

variable {S M V : Type*} [TopologicalSpace S] [TopologicalSpace M] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {r : ℝ}

/-! ### Shrinking a tube into a ball -/

/-- **Shrinking a tube into a ball does not change its collapse up to homotopy.** The tube
`(x, v) ↦ τ (x, (1 + ‖v‖ / r)⁻¹ • v)`, the restriction of `τ` to `S × B(0, r)` reparametrized by a
radial homeomorphism `V ≃ B(0, r)`, has a collapse homotopic to that of `τ`. -/
private theorem pontryaginThomCollapseMap_homotopic_comp_radialShrink [CompactSpace S]
    [T2Space M] {τ : S × V → M} (hτ : IsOpenEmbedding τ) (hr : 0 < r) :
    (pontryaginThomCollapseMap hτ).Homotopic
      (pontryaginThomCollapseMap (hτ.comp (isOpenEmbedding_prodMap_radialShrink (X := S) hr
        zero_le_one))) := by
  -- The isotopy `q ↦ (q.1, τ (q.2.1, radialShrink r q.1 q.2.2))` is `(id × τ) ∘ family`, by
  -- unfolding `Prod.map` and `∘`.
  refine pontryaginThomCollapseMap_homotopic _ _
    (τ := fun q ↦ τ (q.2.1, radialShrink r q.1 q.2.2))
    ((IsOpenEmbedding.id.prodMap hτ).comp (isOpenEmbedding_radialShrink_family hr))
    (fun p ↦ by simp) fun p ↦ by simp [Prod.map_apply']

/-! ### The derivative of the transition between two tubes -/

/-- The transition from a tube `τ₁` to a tube `τ₀` has **fibre derivative `A` along the core**:
near the core, `τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`. Explicitly, for every
`ε > 0` there is `δ > 0` such that for `‖v‖ < δ` the point `τ₁ (x, v)` is `τ₀ p` for some `p` with
`‖p.2 - A x v‖ ≤ ε ‖v‖`. When the transition `τ₀⁻¹ ∘ τ₁` is `C¹` in the fibre direction near the
core and `S` is compact, this holds with `A x` the fibre derivative of its normal coordinate at
`(x, 0)` (`TauCeti.HasTransitionFDeriv.of_hasFDerivAt`). -/
@[expose] def HasTransitionFDeriv (τ₀ τ₁ : S × V → M) (A : S → V →L[ℝ] V) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x (v : V), ‖v‖ < δ →
    ∃ p : S × V, τ₁ (x, v) = τ₀ p ∧ ‖p.2 - A x v‖ ≤ ε * ‖v‖

omit [TopologicalSpace S] [TopologicalSpace M] in
/-- The transition from a tube to itself has fibre derivative the identity along the core. -/
theorem HasTransitionFDeriv.refl (τ : S × V → M) :
    HasTransitionFDeriv τ τ fun _ ↦ ContinuousLinearMap.id ℝ V :=
  fun _ hε ↦ ⟨1, one_pos, fun x v _ ↦ ⟨(x, v), rfl, by
    rw [ContinuousLinearMap.id_apply, sub_self, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg v)⟩⟩

omit [TopologicalSpace M] in
/-- **Reframing a tube.** The transition from the tube `(x, v) ↦ τ (x, A x v)`, reframed by a
continuous family `A` of linear automorphisms of `V`, to `τ` has fibre derivative `A` along the
core. -/
theorem HasTransitionFDeriv.comp_prodUnitsHomeomorph (τ : S × V → M) {A : S → (V →L[ℝ] V)ˣ}
    (hA : Continuous A) :
    HasTransitionFDeriv τ (τ ∘ prodUnitsHomeomorph A hA) fun x ↦ (A x : V →L[ℝ] V) :=
  fun _ hε ↦ ⟨1, one_pos, fun x v _ ↦ ⟨(x, (A x : V →L[ℝ] V) v),
    by rw [comp_apply, prodUnitsHomeomorph_apply], by
      rw [sub_self, norm_zero]
      exact mul_nonneg hε.le (norm_nonneg v)⟩⟩

omit [TopologicalSpace M] in
/-- **A transition that is `C¹` in the fibre direction has a fibre derivative along the core.**
Suppose that `τ₁ (x, v) = τ₀ (φ (x, v))` for `‖v‖ < r`, where `φ` fixes the normal coordinate
`0` and its normal coordinate `w ↦ (φ (x, w)).2` has derivative `D (x, w)` at every `w` of the
ball `B(0, r)`, with `D` continuous on `S × B(0, r)`. If `S` is compact, the transition from `τ₁`
to `τ₀` has fibre derivative `x ↦ D (x, 0)` along the core. -/
theorem HasTransitionFDeriv.of_hasFDerivAt [CompactSpace S] {τ₀ τ₁ : S × V → M}
    {φ : S × V → S × V} {D : S × V → V →L[ℝ] V} (hr : 0 < r)
    (hφ : ∀ x (v : V), ‖v‖ < r → τ₁ (x, v) = τ₀ (φ (x, v))) (hφ0 : ∀ x, (φ (x, 0)).2 = 0)
    (hD : ∀ x (v : V), ‖v‖ < r → HasFDerivAt (fun w ↦ (φ (x, w)).2) (D (x, v)) v)
    (hDc : ContinuousOn D (univ ×ˢ ball 0 r)) :
    HasTransitionFDeriv τ₀ τ₁ fun x ↦ D (x, 0) := by
  intro ε hε
  have h0 (x : S) : (x, (0 : V)) ∈ univ ×ˢ ball (0 : V) r := ⟨trivial, mem_ball_self hr⟩
  -- Near the core, `D` stays within `ε` of its value on the core.
  have hO : IsOpen (univ ×ˢ ball (0 : V) r ∩ (fun p ↦ D p - D (p.1, 0)) ⁻¹' ball 0 ε) :=
    (hDc.sub (hDc.comp (continuous_fst.prodMk continuous_const).continuousOn
      fun p _ ↦ h0 p.1)).isOpen_inter_preimage (isOpen_univ.prod isOpen_ball) isOpen_ball
  obtain ⟨δ, hδ, hδO⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (v : V) (x : S) ↦
      (x, v) ∈ univ ×ˢ ball (0 : V) r ∩ (fun p ↦ D p - D (p.1, 0)) ⁻¹' ball 0 ε)
    fun x _ ↦ (hO.preimage continuous_swap).mem_nhds ⟨h0 x, by simpa using hε⟩
  refine ⟨δ, hδ, fun x v hv ↦ ⟨φ (x, v), hφ x v (mem_ball_zero_iff.1 (hδO hv x trivial).1.2), ?_⟩⟩
  have hball (w : V) (hw : w ∈ ball (0 : V) δ) := hδO (mem_ball_zero_iff.1 hw) x (mem_univ x)
  -- The mean value inequality on the ball `B(0, δ)` bounds the deviation from `D (x, 0)`.
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun w ↦ (φ (x, w)).2) (φ := D (x, 0))
    (fun w hw ↦ (hD x w (mem_ball_zero_iff.1 (hball w hw).1.2)).hasFDerivWithinAt)
    (fun w hw ↦ (mem_ball_zero_iff.1 (hball w hw).2).le) (convex_ball (0 : V) δ)
    (mem_ball_self hδ) (mem_ball_zero_iff.2 hv)
  simpa [hφ0] using this

/-! ### Independence of the tube -/

omit [TopologicalSpace M] in
/-- After shrinking `τ₁` into a ball, its transition `g` into `τ₀` keeps the fibre derivative
`A` of the transition of `τ₁` along the core. -/
private theorem exists_norm_transition_sub_le [CompactSpace S] {τ₀ τ₁ : S × V → M}
    (hτ₀ : Injective τ₀) {g : S × V → S × V} (hr : 0 < r)
    (hg : ∀ p, τ₀ (g p) = τ₁ (p.1, radialShrink r 1 p.2)) {A : S → (V →L[ℝ] V)ˣ}
    (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : V →L[ℝ] V))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (Units.continuous_val.comp hA).continuousOn
  set K := max C 1
  have hK : 0 < K := lt_max_of_lt_right one_pos
  have hAK (x : S) : ‖(A x : V →L[ℝ] V)‖ ≤ K := (hC x (mem_univ x)).trans (le_max_left _ _)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hτ (ε / 2) (half_pos hε)
  refine ⟨min δ₁ (ε * r / (2 * K)), by positivity, fun x v hv ↦ ?_⟩
  have hvδ₁ : ‖v‖ < δ₁ := hv.trans_le (min_le_left _ _)
  have hvK : ‖v‖ ≤ ε * r / (2 * K) := hv.le.trans (min_le_right _ _)
  obtain ⟨p, hp, hpe⟩ := h₁ x (radialShrink r 1 v)
    ((norm_radialShrink_le hr zero_le_one v).trans_lt hvδ₁)
  rw [show g (x, v) = p from hτ₀ ((hg _).trans hp)]
  have hlin : ‖(A x : V →L[ℝ] V) (radialShrink r 1 v) - (A x : V →L[ℝ] V) v‖ ≤
      ε / 2 * ‖v‖ := by
    rw [← map_sub]
    calc _ ≤ K * (1 * ‖v‖ ^ 2 / r) := ((A x : V →L[ℝ] V).le_opNorm _).trans
          (mul_le_mul (hAK x) (norm_radialShrink_sub_le hr zero_le_one v) (norm_nonneg _) hK.le)
      _ = K / r * ‖v‖ * ‖v‖ := by ring
      _ ≤ K / r * (ε * r / (2 * K)) * ‖v‖ := by gcongr
      _ = ε / 2 * ‖v‖ := by field_simp
  calc ‖p.2 - (A x : V →L[ℝ] V) v‖
      ≤ ‖p.2 - (A x : V →L[ℝ] V) (radialShrink r 1 v)‖ +
        ‖(A x : V →L[ℝ] V) (radialShrink r 1 v) - (A x : V →L[ℝ] V) v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 * ‖v‖ + ε / 2 * ‖v‖ :=
        add_le_add (hpe.trans (by gcongr; exact norm_radialShrink_le hr zero_le_one v)) hlin
    _ = ε * ‖v‖ := by ring

/-- **The collapse of a framed tube is the collapse of another one, reframed by the derivative of
the transition.** Let `τ₀` and `τ₁` be framed tubes around the same map `f : S → M`, with compact
`S` and Hausdorff `M`. Suppose that near the core `τ₁` reads in `τ₀` as
`τ₁ (x, v) = τ₀ (x', A x v + o(‖v‖))`, uniformly in `x`, for a continuous family `A` of linear
automorphisms of `V`: the transition from `τ₁` to `τ₀` has fibre derivative `A` along the core.
Then the collapse of `τ₁` is homotopic to that of the tube `(x, v) ↦ τ₀ (x, A x v)`. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph
    [CompactSpace S] [T2Space M] {f : S → M} {τ₀ τ₁ : S × V → M} (h₁ : IsFramedTube f τ₁)
    (h₀ : IsFramedTube f τ₀) {A : S → (V →L[ℝ] V)ˣ} (hA : Continuous A)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (A x : V →L[ℝ] V)) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap
        (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph A hA).isOpenEmbedding)) := by
  -- First shrink `τ₁` into the domain of `τ₀`, along a radial compression `ρ` onto `B(0, r)`.
  obtain ⟨r, hr, hτr⟩ := hτ 1 one_pos
  have hρ := isOpenEmbedding_prodMap_radialShrink (X := S) (V := V) hr zero_le_one
  refine (pontryaginThomCollapseMap_homotopic_comp_radialShrink h₁.isOpenEmbedding hr).trans ?_
  have hmem (p : S × V) : τ₁ (p.1, radialShrink r 1 p.2) ∈ range τ₀ := by
    obtain ⟨q, hq, -⟩ := hτr p.1 _ (by simpa using mul_norm_radialShrink_lt hr zero_le_one p.2)
    exact ⟨q, hq.symm⟩
  -- Then `τ₁ ∘ ρ = τ₀ ∘ g` for the transition `g`, an open embedding of `S × V`.
  set g : S × V → S × V := fun p ↦ (hmem p).choose
  have hτ₀g (p : S × V) : τ₀ (g p) = τ₁ (p.1, radialShrink r 1 p.2) := (hmem p).choose_spec
  have hg : IsOpenEmbedding g := (IsOpenEmbedding.of_comp_iff g h₀.isOpenEmbedding).1 <| by
    convert h₁.isOpenEmbedding.comp hρ using 1
    exact funext hτ₀g
  have hg0 (x : S) : g (x, 0) = (x, 0) :=
    h₀.isOpenEmbedding.injective (by simp [hτ₀g, h₀.apply_zero, h₁.apply_zero])
  -- The Alexander isotopy deforms `τ₀ ∘ g` into the reframed tube `τ₀ ∘ (id × A)`. As a map
  -- `q ↦ (q.1, τ₀ (zeroSectionRescale g A q))` it is `(id × τ₀) ∘ (q ↦ (q.1, …))`, by unfolding
  -- `Prod.map` and `∘`.
  refine (pontryaginThomCollapseMap_homotopic _ _
    (τ := fun q ↦ τ₀ (zeroSectionRescale g (fun x ↦ (A x : V →L[ℝ] V)) q))
    ((IsOpenEmbedding.id.prodMap h₀.isOpenEmbedding).comp (isOpenEmbedding_zeroSectionRescale hg
      hg0 hA (exists_norm_transition_sub_le h₀.isOpenEmbedding.injective hr hτ₀g hA hτ)))
    (fun p ↦ ?_) fun p ↦ ?_).symm
  · simp
  · simp [hτ₀g, Prod.map_apply']

/-- **Independence of the Pontryagin–Thom collapse from the tube.** Let `τ₀` and `τ₁` be framed
tubes around the same map `f : S → M`, with compact `S` and Hausdorff `M`, such that near the core
`τ₁ (x, v) = τ₀ (x', B (0, x) v + o(‖v‖))` uniformly in `x`, for a homotopy `B` through linear
automorphisms of `V` ending at the identity (so the transition derivative `B (0, ·)` is homotopic
to the identity). Then their Pontryagin–Thom collapses are homotopic. -/
theorem IsFramedTube.pontryaginThomCollapseMap_homotopic [CompactSpace S] [T2Space M]
    {f : S → M} {τ₀ τ₁ : S × V → M} (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀)
    {B : unitInterval × S → (V →L[ℝ] V)ˣ} (hB : Continuous B)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (B (0, x) : V →L[ℝ] V)) (hB₁ : ∀ x, B (1, x) = 1) :
    (pontryaginThomCollapseMap h₁.isOpenEmbedding).Homotopic
      (pontryaginThomCollapseMap h₀.isOpenEmbedding) := by
  have e₁ : pontryaginThomCollapseMap (h₀.isOpenEmbedding.comp (prodUnitsHomeomorph
      (fun x ↦ B (1, x)) (hB.comp (Continuous.prodMk_right 1))).isOpenEmbedding) =
      pontryaginThomCollapseMap h₀.isOpenEmbedding := by
    ext m
    simp only [hB₁, coe_pontryaginThomCollapseMap]
    congr 1
    funext p
    simp
  rw [← e₁]
  exact (h₁.pontryaginThomCollapseMap_homotopic_comp_prodUnitsHomeomorph h₀
    (hB.comp (Continuous.prodMk_right 0)) hτ).trans
    (pontryaginThomCollapseMap_comp_prodUnitsHomeomorph_homotopic h₀.isOpenEmbedding hB)

/-- **Independence of the collapse onto the sphere from the tube.** For `V = ℝᵏ`, two framed tubes
around the same map whose transition has fibre derivative `B (0, ·)` along the core, for a homotopy
`B` through linear automorphisms ending at the identity, have homotopic collapses onto `Sᵏ`. -/
theorem IsFramedTube.pontryaginThomSphereMap_homotopic {k : ℕ} [CompactSpace S] [T2Space M]
    {f : S → M} {τ₀ τ₁ : S × (Fin k → ℝ) → M} (h₁ : IsFramedTube f τ₁) (h₀ : IsFramedTube f τ₀)
    {B : unitInterval × S → ((Fin k → ℝ) →L[ℝ] (Fin k → ℝ))ˣ} (hB : Continuous B)
    (hτ : HasTransitionFDeriv τ₀ τ₁ fun x ↦ (B (0, x) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)))
    (hB₁ : ∀ x, B (1, x) = 1)
    (s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (pontryaginThomSphereMap h₁.isOpenEmbedding s₀).Homotopic
      (pontryaginThomSphereMap h₀.isOpenEmbedding s₀) := by
  have e {τ : S × (Fin k → ℝ) → M} (hτ : IsOpenEmbedding τ) : pontryaginThomSphereMap hτ s₀ =
      (onePointHomeomorphSphere k s₀ : C(OnePoint (Fin k → ℝ), _)).comp
        (pontryaginThomCollapseMap hτ) :=
    ContinuousMap.ext fun m ↦ by simp [coe_pontryaginThomSphereMap]
  rw [e, e]
  exact (ContinuousMap.Homotopic.refl _).comp
    (h₁.pontryaginThomCollapseMap_homotopic h₀ hB hτ hB₁)

end TauCeti
