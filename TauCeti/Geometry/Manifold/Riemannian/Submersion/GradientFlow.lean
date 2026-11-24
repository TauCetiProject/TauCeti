/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Flow.Related
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Negative gradient trajectories of a pullback along a Riemannian submersion

Let `f : M → N` be a Riemannian submersion and `g : N → ℝ` a `C²` function. The gradient of the
pullback `g ∘ f` is the horizontal lift of the gradient of `g`
(`TauCeti.IsRiemannianSubmersion.mgradient_comp`). This file draws the consequences for the
negative gradient flows `V = -grad (g ∘ f)` on `M` and `W = -grad g` on `N`. For a Morse function
`g` on the base of a fibre bundle, `g ∘ f` is the Morse–Bott function whose critical submanifolds
are the fibres over the critical points of `g`, used to compare Morse–Bott and Morse homology of
fibre bundles. The results here describe its trajectories: each is determined by its projection,
a trajectory of `W`, and its value at time `0` in a fibre. A trajectory of `V` over a trajectory
of `W` running from a nondegenerate critical point `x` of `g` to another one `y` converges
exponentially fast to a point of the fibre over `y` as `t → ∞` when it stays in a compact set,
and to a point of the fibre over `x` as `t → -∞` when `M` is compact.

* **Projection.** `f` maps integral curves of `V` to integral curves of `W`
  (`TauCeti.IsRiemannianSubmersion.isMIntegralCurveOn_comp`), so the maximal flow of `V` covers
  that of `W` (`TauCeti.IsRiemannianSubmersion.apply_maximalIntegralCurve`). Since `df` is an
  isometry on horizontal vectors, a trajectory of `V` and its projection have the same speed, so
  the same Riemannian length on every time interval
  (`TauCeti.IsRiemannianSubmersion.pathELength_maximalIntegralCurve`).
* **Lifting.** When `V` is complete, as on a compact `M`, the global trajectories of `V`
  correspond bijectively to the pairs of a global trajectory `c` of `W` and a point of the fibre
  over `c 0` (`TauCeti.IsRiemannianSubmersion.liftIntegralCurveEquiv`): a trajectory `γ` of `V`
  goes to `(f ∘ γ, γ 0)`, and `(c, z)` to the trajectory of `V` through `z`, which lies over `c`.
* **Convergence into the critical fibres.** If the trajectory of `W` through `f z` converges to a
  nondegenerate critical point `x` of `g` and the forward trajectory of `V` through `z` stays in a
  compact set, then the latter converges to a point of `f ⁻¹' {x}`, exponentially fast in the
  Riemannian distance (`TauCeti.IsRiemannianSubmersion.` +
  `exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp`), and on
  a compact `M` the same holds in backward time (`TauCeti.IsRiemannianSubmersion.` +
  `exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp`).
  The critical fibre need not be a single point, so the Morse decay estimates do not apply to `V`
  directly. Instead the tail length of the lift equals that of the base trajectory, which the
  Łojasiewicz inequality at `x` bounds by `K * sqrt (g (c t) - g x)` (`TauCeti.` +
  `IsRiemannianSubmersion.exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient_comp`),
  and a curve whose tail lengths tend to zero converges to each of its cluster points
  (`TauCeti.Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le`).
* **Stable and unstable sets of the critical fibres.** On a compact `M`, the points whose
  trajectory converges in forward, respectively backward, time into the fibre over a nondegenerate
  critical point `x` are exactly the preimage of the stable, respectively unstable, set of `x`
  (`TauCeti.IsRiemannianSubmersion.setOf_exists_tendsto_maximalIntegralCurve_neg_mgradient_comp`,
  `TauCeti.IsRiemannianSubmersion.` +
  `setOf_exists_tendsto_atBot_maximalIntegralCurve_neg_mgradient_comp`).

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the Morse–Bott function pulled back from the base of a
  fibre bundle).
* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
-/

public section

open Bundle Filter Function Set Topology TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti

namespace IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {g : N → ℝ}

/-! ### Projection of trajectories -/

section Projection

variable [IsManifold I 1 M] [IsManifold J 1 N] (h : IsRiemannianSubmersion I J f)
include h

/-- **Trajectories project to trajectories.** A Riemannian submersion `f` maps every integral
curve of `-grad (g ∘ f)` to an integral curve of `-grad g`. -/
theorem isMIntegralCurveOn_comp (hg : MDifferentiable J 𝓘(ℝ) g) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (-mgradient I (g ∘ f)) s) :
    IsMIntegralCurveOn (f ∘ γ) (-mgradient J g) s :=
  hγ.map_of_mfderiv_eq (W := -mgradient J g)
    (fun _ _ ↦ h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
    fun _ _ ↦ h.mfderiv_neg_mgradient_comp (hg _)

/-- A Riemannian submersion `f` maps every global integral curve of `-grad (g ∘ f)` to a global
integral curve of `-grad g`. -/
theorem isMIntegralCurve_comp (hg : MDifferentiable J 𝓘(ℝ) g) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (-mgradient I (g ∘ f))) :
    IsMIntegralCurve (f ∘ γ) (-mgradient J g) :=
  isMIntegralCurve_iff_isMIntegralCurveOn.2
    (h.isMIntegralCurveOn_comp hg (isMIntegralCurve_iff_isMIntegralCurveOn.1 hγ))

/-- The maximal trajectory of `-grad (g ∘ f)` through `z` exists at most as long as the maximal
trajectory of `-grad g` through `f z`. -/
theorem maximalIntegralCurveInterval_subset (hg : MDifferentiable J 𝓘(ℝ) g) (z : M) :
    maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z ⊆
      maximalIntegralCurveInterval (-mgradient J g) (f z) :=
  (h.isSubmersion.contMDiff.mdifferentiable (by simp)).maximalIntegralCurveInterval_subset
    (X := -mgradient I (g ∘ f)) (Y := -mgradient J g)
    (fun _ ↦ h.mfderiv_neg_mgradient_comp (hg _)) z

end Projection

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The pullback of a `C²` function along a Riemannian submersion is `C²`. -/
private theorem contMDiff_comp (h : IsRiemannianSubmersion I J f) (hg : ContMDiff J 𝓘(ℝ) 2 g) :
    ContMDiff I 𝓘(ℝ) 2 (g ∘ f) :=
  hg.comp (h.isSubmersion.contMDiff.of_le (by simp))

section Flow

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [T2Space N] [BoundarylessManifold J N]
  (h : IsRiemannianSubmersion I J f)
include h

/-- **The flow of the lifted field covers the flow on the base.** Along the maximal trajectory of
`-grad (g ∘ f)` through `z`, the projection `f` agrees with the maximal trajectory of `-grad g`
through `f z`. -/
theorem apply_maximalIntegralCurve (hg : ContMDiff J 𝓘(ℝ) 2 g) {z : M} {t : ℝ}
    (ht : t ∈ maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z) :
    f (maximalIntegralCurve (-mgradient I (g ∘ f)) z t) =
      maximalIntegralCurve (-mgradient J g) (f z) t := by
  have : IsManifold J 1 N := IsManifold.of_le one_le_two
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hg1 : MDifferentiable J 𝓘(ℝ) g := hg.mdifferentiable (by norm_num)
  simpa only [flowOf_apply] using
    (h.isSubmersion.contMDiff.mdifferentiable (by simp)).apply_flowOf
      (X := -mgradient I (g ∘ f)) (contMDiff_neg_mgradient_one hg)
      (fun _ ↦ h.mfderiv_neg_mgradient_comp (hg1 _)) (mem_flowDomain.2 ht)

/-- **Trajectories of a complete lifted field lie over trajectories on the base.** If
`-grad (g ∘ f)` is complete, the projection of its maximal trajectory through `z` is the maximal
trajectory of `-grad g` through `f z`. -/
theorem comp_maximalIntegralCurve (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f))) (z : M) :
    f ∘ maximalIntegralCurve (-mgradient I (g ∘ f)) z =
      maximalIntegralCurve (-mgradient J g) (f z) :=
  funext fun t ↦ h.apply_maximalIntegralCurve hg (hV.mem_maximalIntegralCurveInterval z t)

/-- **Lifting a trajectory through a point of the fibre.** If `-grad (g ∘ f)` is complete, then
for every global trajectory `c` of `-grad g` and every point `z` of the fibre over `c 0`, the
maximal trajectory of `-grad (g ∘ f)` through `z` lies over `c`. -/
theorem comp_maximalIntegralCurve_of_isMIntegralCurve (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f))) {c : ℝ → N}
    (hc : IsMIntegralCurve c (-mgradient J g)) {z : M} (hz : f z = c 0) :
    f ∘ maximalIntegralCurve (-mgradient I (g ∘ f)) z = c := by
  have : IsManifold J 1 N := IsManifold.of_le one_le_two
  rw [h.comp_maximalIntegralCurve hg hV, hz]
  exact funext (hc.maximalIntegralCurve_eq (contMDiff_neg_mgradient_one hg))

/-- **Limits of lifted trajectories project to limits on the base.** If `-grad (g ∘ f)` is
complete and its maximal trajectory through `z` tends to `z'` along a filter `l`, then the maximal
trajectory of `-grad g` through `f z` tends to `f z'` along `l`. -/
theorem tendsto_maximalIntegralCurve_of_tendsto (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f))) {l : Filter ℝ} {z z' : M}
    (hγ : Tendsto (maximalIntegralCurve (-mgradient I (g ∘ f)) z) l (𝓝 z')) :
    Tendsto (maximalIntegralCurve (-mgradient J g) (f z)) l (𝓝 (f z')) := by
  rw [← h.comp_maximalIntegralCurve hg hV]
  exact (h.isSubmersion.contMDiff.continuous.tendsto z').comp hγ

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [T2Space M] [BoundarylessManifold I M]

/-- **A lifted trajectory has the length of its projection.** On every time interval within its
interval of existence, the maximal trajectory of `-grad (g ∘ f)` through `z` has the same
Riemannian length as the maximal trajectory of `-grad g` through `f z`: their speeds are the
lengths of the gradients, which agree since `df` is isometric on horizontal vectors. -/
theorem pathELength_maximalIntegralCurve (hg : ContMDiff J 𝓘(ℝ) 2 g) {z : M} {a b : ℝ}
    (hab : Icc a b ⊆ maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z) :
    Manifold.pathELength I (maximalIntegralCurve (-mgradient I (g ∘ f)) z) a b =
      Manifold.pathELength J (maximalIntegralCurve (-mgradient J g) (f z)) a b := by
  have : IsManifold J 1 N := IsManifold.of_le one_le_two
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hg1 : MDifferentiable J 𝓘(ℝ) g := hg.mdifferentiable (by norm_num)
  rw [pathELength_eq_setLIntegral_enorm_curveVelocity_Ioo,
    pathELength_eq_setLIntegral_enorm_curveVelocity_Ioo]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have htV : t ∈ maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z :=
    hab (Ioo_subset_Icc_self ht)
  have htW := h.maximalIntegralCurveInterval_subset hg1 z htV
  simp only [curveVelocity_maximalIntegralCurve_neg_mgradient (h.contMDiff_comp hg) htV,
    curveVelocity_maximalIntegralCurve_neg_mgradient hg htW, ← ofReal_norm, norm_neg,
    h.norm_mgradient_comp (hg1 _)]
  rw [h.apply_maximalIntegralCurve hg htV]

/-! ### Lifting trajectories -/

/-- **Horizontal lifting of trajectories.** If `-grad (g ∘ f)` is complete, as on a compact
manifold, its global trajectories correspond to the pairs of a global trajectory `c` of
`-grad g` and a point of the fibre of `f` over `c 0`: a trajectory `γ` corresponds to
`(f ∘ γ, γ 0)`, and `(c, z)` to the maximal trajectory through `z`, which lies over `c`. -/
def liftIntegralCurveEquiv (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f))) :
    {γ : ℝ → M // IsMIntegralCurve γ (-mgradient I (g ∘ f))} ≃
      Σ c : {c : ℝ → N // IsMIntegralCurve c (-mgradient J g)}, f ⁻¹' {c.val 0} where
  toFun γ := ⟨⟨f ∘ γ.val, by
    have : IsManifold J 1 N := IsManifold.of_le one_le_two
    have : IsManifold I 1 M := IsManifold.of_le one_le_two
    exact h.isMIntegralCurve_comp (hg.mdifferentiable (by norm_num)) γ.property⟩,
    ⟨γ.val 0, rfl⟩⟩
  invFun p := ⟨maximalIntegralCurve (-mgradient I (g ∘ f)) p.2,
    have : IsManifold I 1 M := IsManifold.of_le one_le_two
    isMIntegralCurve_maximalIntegralCurve_of_eq_univ
      (contMDiff_neg_mgradient_one (h.contMDiff_comp hg))
      (hV.maximalIntegralCurveInterval_eq_univ _)⟩
  left_inv γ := by
    have : IsManifold I 1 M := IsManifold.of_le one_le_two
    exact Subtype.ext (funext (γ.property.maximalIntegralCurve_eq
      (contMDiff_neg_mgradient_one (h.contMDiff_comp hg))))
  right_inv p := Sigma.subtype_ext
    (Subtype.ext
      (h.comp_maximalIntegralCurve_of_isMIntegralCurve hg hV p.1.property p.2.property))
    maximalIntegralCurve_zero

/-- The trajectory on the base attached to a lifted trajectory is its projection. -/
@[simp]
theorem coe_liftIntegralCurveEquiv_fst (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f)))
    (γ : {γ : ℝ → M // IsMIntegralCurve γ (-mgradient I (g ∘ f))}) :
    ((h.liftIntegralCurveEquiv hg hV γ).1 : ℝ → N) = f ∘ γ :=
  (rfl)

/-- The fibre point attached to a lifted trajectory is its value at time `0`. -/
@[simp]
theorem coe_liftIntegralCurveEquiv_snd (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f)))
    (γ : {γ : ℝ → M // IsMIntegralCurve γ (-mgradient I (g ∘ f))}) :
    ((h.liftIntegralCurveEquiv hg hV γ).2 : M) = γ.val 0 :=
  (rfl)

/-- The lift of a trajectory `c` on the base through a point `z` of the fibre over `c 0` is the
maximal trajectory of `-grad (g ∘ f)` through `z`. -/
@[simp]
theorem coe_liftIntegralCurveEquiv_symm (hg : ContMDiff J 𝓘(ℝ) 2 g)
    (hV : IsCompleteVectorField (-mgradient I (g ∘ f)))
    (p : Σ c : {c : ℝ → N // IsMIntegralCurve c (-mgradient J g)}, f ⁻¹' {c.val 0}) :
    ((h.liftIntegralCurveEquiv hg hV).symm p : ℝ → M) =
      maximalIntegralCurve (-mgradient I (g ∘ f)) p.2 :=
  (rfl)

end Flow

/-! ### Convergence into the critical fibres -/

section Convergence

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [T2Space M] [BoundarylessManifold I M] [T2Space N] [BoundarylessManifold J N]
  (h : IsRiemannianSubmersion I J f)
include h

/-- **The tail length of a lifted trajectory is controlled by the energy on the base.** If the
maximal trajectory `c` of `-grad g` through `f z` converges to a nondegenerate critical point `x`
of `g`, and the maximal trajectory `γ` of `-grad (g ∘ f)` through `z` exists for all positive
time, then for some `K > 0` and all large `t`, every piece of `γ` starting at time `t` has
Riemannian length at most `K * sqrt (g (c t) - g x)`. -/
theorem exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient_comp
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : N} (hx : IsManifoldNondegenerateCriticalPoint J g x)
    {z : M} (hconv : Tendsto (maximalIntegralCurve (-mgradient J g) (f z)) atTop (𝓝 x))
    (hIci : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z) :
    ∃ K > 0, ∀ᶠ t in atTop, ∀ s,
      Manifold.pathELength I (maximalIntegralCurve (-mgradient I (g ∘ f)) z) t s ≤
        ENNReal.ofReal (K * √(g (maximalIntegralCurve (-mgradient J g) (f z) t) - g x)) := by
  have : IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := 1)
  obtain ⟨K, hK, hlen⟩ :=
    exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient hx.mem_criticalPoints
      hx.exists_mul_abs_sub_le_norm_mgradient_sq hconv hg
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlen, eventually_ge_atTop 0] with t ht ht0 s
  rw [h.pathELength_maximalIntegralCurve hg fun r hr ↦ hIci (ht0.trans hr.1)]
  exact ht s

/-- **Lifted trajectories converge exponentially fast into the critical fibre.** Let the maximal
trajectory `c` of `-grad g` through `f z` converge to a nondegenerate critical point `x` of `g`,
and let the forward maximal trajectory `γ` of `-grad (g ∘ f)` through `z` stay in a compact set
`K`. Then `γ` converges to a point `z'` of `K` in the fibre over `x`, and the Riemannian distance
from `γ t` to `z'` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`. -/
theorem exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : N} (hx : IsManifoldNondegenerateCriticalPoint J g x)
    {z : M} (hconv : Tendsto (maximalIntegralCurve (-mgradient J g) (f z)) atTop (𝓝 x))
    {K : Set M} (hK : IsCompact K)
    (hmem : MapsTo (maximalIntegralCurve (-mgradient I (g ∘ f)) z)
      (maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z ∩ Ici 0) K) :
    ∃ z' ∈ K, f z' = x ∧
      Tendsto (maximalIntegralCurve (-mgradient I (g ∘ f)) z) atTop (𝓝 z') ∧
      ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
        Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I (g ∘ f)) z t) z' ≤
          ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsContinuousRiemannianBundle F (fun y : N ↦ TangentSpace J y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I (g ∘ f)) z
  set c := maximalIntegralCurve (-mgradient J g) (f z)
  have hgf := h.contMDiff_comp hg
  have hIci : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I (g ∘ f)) z :=
    Ici_subset_maximalIntegralCurveInterval_of_isCompact_of_mapsTo
      (contMDiff_neg_mgradient_one hgf) hK hmem
  have hγC : CMDiff[Ici 0] 1 γ := (contMDiffOn_maximalIntegralCurve_neg_mgradient hgf).mono hIci
  -- The tail lengths of `γ` tend to zero with the energy of `c`.
  obtain ⟨L, hL, hlen⟩ :=
    h.exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient_comp hg hx hconv hIci
  have henergy : Tendsto (fun t ↦ ENNReal.ofReal (L * √(g (c t) - g x))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ g (c t) - g x) atTop (𝓝 (g x - g x)) :=
      ((hg.continuous.tendsto x).comp hconv).sub_const _
    rw [sub_self] at hlim
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_const_nhds (x := L)).mul ((Real.continuous_sqrt.tendsto 0).comp hlim))
  have htail : ∀ ε > 0, ∀ᶠ t in atTop, ∀ s, Manifold.pathELength I γ t s ≤ ε := fun ε hε ↦ by
    filter_upwards [hlen, ENNReal.tendsto_nhds_zero.1 henergy ε hε] with t ht hε s
    exact (ht s).trans hε
  -- A cluster point of `γ` in `K` is its limit, and it lies over `x`.
  obtain ⟨z', hz'K, hz'⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (tendsto_principal.2
    (by filter_upwards [eventually_ge_atTop 0] with t ht using hmem ⟨hIci ht, ht⟩))
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have hγz' : Tendsto γ atTop (𝓝 z') :=
    Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le hγC hz' htail
  have hfz' : f z' = x := by
    refine tendsto_nhds_unique ((h.isSubmersion.contMDiff.continuous.tendsto z').comp hγz') ?_
    refine hconv.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (h.apply_maximalIntegralCurve hg (hIci ht)).symm
  refine ⟨z', hz'K, hfz', hγz', ?_⟩
  -- The rate: the distance to `z'` is at most the tail length, and the energy decays.
  obtain ⟨μ, hμ, C, hC, hdecay⟩ :=
    exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient hg hx.mem_criticalPoints
      hx.exists_mul_abs_sub_le_norm_mgradient_sq hconv
  refine ⟨μ / 2, by positivity, L * √C, by positivity, ?_⟩
  filter_upwards [hlen, hdecay, eventually_ge_atTop 0] with t ht hte ht0
  refine (Manifold.riemannianEDist_le_of_tendsto_of_forall_pathELength_le
    (hγC.mono (Ici_subset_Ici.2 ht0)) hγz' ht).trans (ENNReal.ofReal_le_ofReal ?_)
  calc L * √(g (c t) - g x) ≤ L * √(C * Real.exp (-(μ * t))) := by gcongr
    _ = L * √C * Real.exp (-(μ / 2 * t)) := by
        rw [Real.sqrt_mul hC.le, ← Real.exp_half, mul_assoc]
        ring_nf

/-- **Lifted trajectories converge into the critical fibre in backward time too.** On a compact
manifold, if the trajectory of `-grad g` through `f z` converges as `t → -∞` to a nondegenerate
critical point `x` of `g`, then the trajectory `γ` of `-grad (g ∘ f)` through `z` converges as
`t → -∞` to a point `z'` of the fibre over `x`, and the Riemannian distance from `γ t` to `z'` is
at most `C * exp (μ * t)` for some `μ, C > 0` and all `t` near `-∞`. -/
theorem exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp
    [CompactSpace M] (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : N}
    (hx : IsManifoldNondegenerateCriticalPoint J g x) {z : M}
    (hconv : Tendsto (maximalIntegralCurve (-mgradient J g) (f z)) atBot (𝓝 x)) :
    ∃ z' ∈ f ⁻¹' {x},
      Tendsto (maximalIntegralCurve (-mgradient I (g ∘ f)) z) atBot (𝓝 z') ∧
      ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot,
        Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I (g ∘ f)) z t) z' ≤
          ENNReal.ofReal (C * Real.exp (μ * t)) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold J 1 N := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I (g ∘ f)) z
  set c := maximalIntegralCurve (-mgradient J g) (f z)
  have hV1 := contMDiff_neg_mgradient_one (h.contMDiff_comp hg)
  have hγ : IsMIntegralCurve γ (-mgradient I (g ∘ f)) := isMIntegralCurve_maximalIntegralCurve hV1
  have hc : IsMIntegralCurve c (-mgradient J g) := by
    have hfc : f ∘ γ = c :=
      h.comp_maximalIntegralCurve hg (isCompleteVectorField_of_compactSpace hV1) z
    rw [← hfc]
    exact h.isMIntegralCurve_comp (hg.mdifferentiable (by norm_num)) hγ
  -- Reversing time turns trajectories of `-grad φ` into trajectories of `-grad (-φ)`.
  have hg' : ContMDiff J 𝓘(ℝ) 2 (-g) := hg.neg
  have hγrev : maximalIntegralCurve (-mgradient I ((-g) ∘ f)) z = γ ∘ (· * -1) :=
    maximalIntegralCurve_neg_mgradient_neg (h.contMDiff_comp hg) hγ
  have hcrev : maximalIntegralCurve (-mgradient J (-g)) (f z) = c ∘ (· * -1) :=
    maximalIntegralCurve_neg_mgradient_neg hg hc
  have htop : Tendsto (fun t : ℝ ↦ t * -1) atTop atBot := by
    simpa only [mul_neg_one] using tendsto_neg_atTop_atBot
  have hbot : Tendsto (fun t : ℝ ↦ t * -1) atBot atTop := by
    simpa only [mul_neg_one] using tendsto_neg_atBot_atTop
  obtain ⟨z', -, hz', hlim, μ, hμ, C, hC, hrate⟩ :=
    h.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp
      hg' hx.neg (z := z) (by rw [hcrev]; exact hconv.comp htop) isCompact_univ
      (mapsTo_univ _ _)
  rw [hγrev] at hlim hrate
  refine ⟨z', hz', ?_, μ, hμ, C, hC, ?_⟩
  · simpa [Function.comp_def] using hlim.comp hbot
  · filter_upwards [hbot.eventually hrate] with t ht
    simpa [Function.comp_def, mul_comm μ t] using ht

/-- **The stable set of a nondegenerate critical fibre.** On a compact manifold, the points whose
trajectory under `-grad (g ∘ f)` converges to a point of the fibre over a nondegenerate critical
point `x` of `g` are exactly the preimage under `f` of the stable set of `x` for `-grad g`. -/
theorem setOf_exists_tendsto_maximalIntegralCurve_neg_mgradient_comp [CompactSpace M]
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : N} (hx : IsManifoldNondegenerateCriticalPoint J g x) :
    {z | ∃ z' ∈ f ⁻¹' {x},
        Tendsto (maximalIntegralCurve (-mgradient I (g ∘ f)) z) atTop (𝓝 z')} =
      f ⁻¹' {y | Tendsto (maximalIntegralCurve (-mgradient J g) y) atTop (𝓝 x)} := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hV : IsCompleteVectorField (-mgradient I (g ∘ f)) :=
    isCompleteVectorField_of_compactSpace (contMDiff_neg_mgradient_one (h.contMDiff_comp hg))
  ext z
  refine ⟨fun ⟨z', hz', hγ⟩ ↦ ?_, fun hconv ↦ ?_⟩
  · exact mem_singleton_iff.1 hz' ▸ h.tendsto_maximalIntegralCurve_of_tendsto hg hV hγ
  · obtain ⟨z', -, hz', hγ, -⟩ :=
      h.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp hg
        hx hconv isCompact_univ (mapsTo_univ _ _)
    exact ⟨z', hz', hγ⟩

/-- **The unstable set of a nondegenerate critical fibre.** On a compact manifold, the points
whose trajectory under `-grad (g ∘ f)` converges in backward time to a point of the fibre over a
nondegenerate critical point `x` of `g` are exactly the preimage under `f` of the unstable set of
`x` for `-grad g`. -/
theorem setOf_exists_tendsto_atBot_maximalIntegralCurve_neg_mgradient_comp [CompactSpace M]
    (hg : ContMDiff J 𝓘(ℝ) 2 g) {x : N} (hx : IsManifoldNondegenerateCriticalPoint J g x) :
    {z | ∃ z' ∈ f ⁻¹' {x},
        Tendsto (maximalIntegralCurve (-mgradient I (g ∘ f)) z) atBot (𝓝 z')} =
      f ⁻¹' {y | Tendsto (maximalIntegralCurve (-mgradient J g) y) atBot (𝓝 x)} := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hV : IsCompleteVectorField (-mgradient I (g ∘ f)) :=
    isCompleteVectorField_of_compactSpace (contMDiff_neg_mgradient_one (h.contMDiff_comp hg))
  ext z
  refine ⟨fun ⟨z', hz', hγ⟩ ↦ ?_, fun hconv ↦ ?_⟩
  · exact mem_singleton_iff.1 hz' ▸ h.tendsto_maximalIntegralCurve_of_tendsto hg hV hγ
  · obtain ⟨z', hz', hγ, -⟩ :=
      h.exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_comp
        hg hx hconv
    exact ⟨z', hz', hγ⟩

end Convergence

end IsRiemannianSubmersion

end TauCeti
