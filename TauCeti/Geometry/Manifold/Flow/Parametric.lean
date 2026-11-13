/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.NondegenerateOrbit
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.FixedPoint
import TauCeti.Geometry.Manifold.Flow.Related
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Flows of families of vector fields

Let `v a` be a family of vector fields on a manifold `M`, indexed by the points `a` of a
parameter manifold `N`. Adjoining the trivial equation `a' = 0` turns it into the single
*vertical* vector field `(a, x) ↦ (0, v a x)` on `N × M` (`TauCeti.verticalField J v`), which is
`C^n` when the family is jointly `C^n` (`TauCeti.contMDiff_verticalField`). Its trajectories keep
the parameter fixed and move in `M` along the field of that parameter: the maximal interval of the
vertical field through `(a, x)` is that of `v a` through `x`
(`TauCeti.maximalIntegralCurveInterval_verticalField`, which needs no regularity of the family),
and when `M` is Hausdorff and boundaryless and `v a` is `C¹`,
`flowOf (verticalField J v) t (a, x) = (a, flowOf (v a) t x)` for all `t`
(`TauCeti.flowOf_verticalField`, which needs no regularity in the parameter). So results about one
vector field, applied to the vertical field, become results about the family which are uniform in
the parameter.

The main application is the **continuation of nondegenerate closed orbits**
(`TauCeti.exists_contMDiffAt_closedOrbit_continuation`). Let `M` be a Hausdorff boundaryless
manifold modelled on a finite-dimensional space, `N` a Hausdorff boundaryless manifold modelled on
a Banach space, and `v` a jointly `C^n` family with `1 ≤ n ≤ ∞` (`n : ℕ∞`). Let `p` be a point on a
closed orbit of `v a₀` with return time `T₀`, let `{g = g p}` be a local section through `p`
transverse to `v a₀`, with `g` `C^n` at `p`, and suppose the orbit is nondegenerate: `1` is not an
eigenvalue of the linearized return map. Then for parameters `a` near `a₀` the field `v a` has a
closed orbit through a point `c a` of the same section, with return time `τ a`, where `c` and `τ`
are `C^n` at `a₀` with `c a₀ = p` and `τ a₀ = T₀`; this orbit is again nondegenerate, and it is the
only closed orbit through the section near `(T₀, p)`. The proof applies the hitting time of the
section to the vertical field: its transition map `flowTransition` is a `C^n` family of return
branches of the fields `v a`, and the continuation of nondegenerate fixed points of families of
maps (`TauCeti.IsNondegenerateFixedPt.exists_contMDiffAt_fixedPt_continuation`) continues the
fixed point `p` of the return branch of `v a₀`. The only additional point is that the transition
map of the vertical field restricts to the transition maps of the single fields `v a`, by the
local uniqueness of hitting times
(`TauCeti.eventually_eventuallyEq_snd_flowTransition_verticalField`).

In the Kupka–Smale theorem, continuation is the input to the proof that nondegeneracy of the closed
orbits of bounded period in a compact window is an open condition on the vector field.

## Main definitions

* `TauCeti.verticalField J v`: the vector field `(a, x) ↦ (0, v a x)` on `N × M`.

## Main results

* `TauCeti.contMDiffAt_verticalField`, `TauCeti.contMDiff_verticalField`: the vertical field of a
  `C^n` family is `C^n`.
* `IsMIntegralCurveOn.prodMk_verticalField`, `IsMIntegralCurveOn.fst_eq_of_verticalField`,
  `IsMIntegralCurveOn.snd_of_verticalField`: integral curves of the vertical field are integral
  curves of the fields of the family, paired with a constant parameter.
* `TauCeti.maximalIntegralCurveInterval_verticalField`, `TauCeti.mem_flowDomain_verticalField_iff`,
  `TauCeti.flowOf_verticalField`: the flow of the vertical field is the flow of the fields of the
  family, with the parameter fixed.
* `TauCeti.eventually_contMDiffAt_and_mvfderiv_apply_ne_zero`: transversality of a function to
  the fields of a continuous family is an open condition in the parameter and the point.
* `TauCeti.eventually_eventuallyEq_snd_flowTransition_verticalField`: near `(T₀, (a₀, p))`, the
  transition map of the vertical field restricts to the transition maps of the individual fields.
* `TauCeti.exists_contMDiffAt_closedOrbit_continuation`: a nondegenerate closed orbit of `v a₀`
  continues to a unique `C^n` family of nondegenerate closed orbits of the fields `v a`.

## References

* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §3
  (persistence of hyperbolic closed orbits) and §4 (the Kupka–Smale theorem).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]

/-! ### The vertical field of a family -/

variable (J) in
/-- The **vertical field** of a family `v` of vector fields on `M` indexed by `N`: the vector
field `(a, x) ↦ (0, v a x)` on `N × M`. Its trajectories keep the parameter `a` fixed and follow
the field `v a` in `M`. -/
def verticalField (v : N → (x : M) → TangentSpace I x) :
    (z : N × M) → TangentSpace (J.prod I) z :=
  fun z ↦ (0, v z.1 z.2)

/-- The vertical field at `(a, x)` is `(0, v a x)`. -/
theorem verticalField_apply (v : N → (x : M) → TangentSpace I x) (z : N × M) :
    verticalField J v z = (0, v z.1 z.2) :=
  (rfl)

/-- The parameter component of the vertical field is `0`. -/
@[simp]
theorem verticalField_fst (v : N → (x : M) → TangentSpace I x) (z : N × M) :
    (verticalField J v z).1 = 0 :=
  (rfl)

/-- The component of the vertical field at `(a, x)` along `M` is `v a x`. -/
@[simp]
theorem verticalField_snd (v : N → (x : M) → TangentSpace I x) (z : N × M) :
    (verticalField J v z).2 = v z.1 z.2 :=
  (rfl)

/-- The vertical field of a family which is `C^n` at `z` is `C^n` at `z`. -/
theorem contMDiffAt_verticalField [IsManifold J 1 N] [IsManifold I 1 M] {n : ℕ∞ω}
    {v : N → (x : M) → TangentSpace I x} {z : N × M}
    (hv : ContMDiffAt (J.prod I) I.tangent n
      (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)) z) :
    ContMDiffAt (J.prod I) (J.prod I).tangent n
      (fun z : N × M ↦ (⟨z, verticalField J v z⟩ : TangentBundle (J.prod I) (N × M))) z := by
  -- The vertical field is the zero section of `TN` paired with `v`, read through
  -- `TangentBundle (J.prod I) (N × M) ≃ TangentBundle J N × TangentBundle I M`.
  have h : (fun z : N × M ↦ (⟨z, verticalField J v z⟩ : TangentBundle (J.prod I) (N × M))) =
      (equivTangentBundleProd J N I M).symm ∘
        fun z ↦ (Bundle.zeroSection F (TangentSpace J) z.1, ⟨z.2, v z.1 z.2⟩) :=
    funext fun _ ↦ rfl
  rw [h]
  exact contMDiff_equivTangentBundleProd_symm.contMDiffAt.comp z
    ((((Bundle.contMDiff_zeroSection ℝ (TangentSpace J (M := N))).comp contMDiff_fst).contMDiffAt
      ).prodMk hv)

/-- **The vertical field of a `C^n` family is `C^n`.** If the family `v` is jointly `C^n` on
`N × M`, the vertical field `(a, x) ↦ (0, v a x)` is a `C^n` vector field on `N × M`. -/
theorem contMDiff_verticalField [IsManifold J 1 N] [IsManifold I 1 M] {n : ℕ∞ω}
    {v : N → (x : M) → TangentSpace I x}
    (hv : ContMDiff (J.prod I) I.tangent n
      (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M))) :
    ContMDiff (J.prod I) (J.prod I).tangent n
      (fun z : N × M ↦ (⟨z, verticalField J v z⟩ : TangentBundle (J.prod I) (N × M))) :=
  fun z ↦ contMDiffAt_verticalField (hv z)

/-- The map `x ↦ (a, x)` carries `v a` to the vertical field. -/
theorem mfderiv_prodMk_apply_verticalField (v : N → (x : M) → TangentSpace I x) (a : N)
    (x : M) : mfderiv I (J.prod I) (Prod.mk a) x (v a x) = verticalField J v (a, x) := by
  rw [mfderiv_prod_right]
  -- `inr` sends `v a x` to `(0, v a x)` in `T_a N × T_x M = T_(a, x) (N × M)`.
  rfl

/-- An integral curve of `v a` on a set, paired with the constant parameter `a`, is an integral
curve of the vertical field on that set. -/
theorem _root_.IsMIntegralCurveOn.prodMk_verticalField {v : N → (x : M) → TangentSpace I x}
    {a : N} {γ : ℝ → M} {s : Set ℝ} (hγ : IsMIntegralCurveOn γ (v a) s) :
    IsMIntegralCurveOn (fun t ↦ (a, γ t)) (verticalField J v) s :=
  hγ.map_of_mfderiv_eq (fun _ _ ↦ mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    (fun _ _ ↦ mfderiv_prodMk_apply_verticalField v a _)

/-- Along an integral curve of the vertical field on an open preconnected set of times, the
parameter is constant. -/
theorem _root_.IsMIntegralCurveOn.fst_eq_of_verticalField [IsManifold J 1 N]
    {v : N → (x : M) → TangentSpace I x} {γ : ℝ → N × M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (verticalField J v) s) (hs : IsOpen s) (hs' : IsPreconnected s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) : (γ t).1 = (γ t₀).1 :=
  hγ.apply_eq_of_mfderiv_apply_eq_zero hs hs' (fun _ _ ↦ mdifferentiableAt_fst)
    (fun _ _ ↦ by
      rw [mfderiv_fst]
      -- The first projection sends `(0, v a x)` to `0`.
      rfl) ht₀ ht

/-- Along an integral curve of the vertical field on an open preconnected set of times, the
component in `M` is an integral curve of the field of the (constant) parameter. -/
theorem _root_.IsMIntegralCurveOn.snd_of_verticalField [IsManifold J 1 N]
    {v : N → (x : M) → TangentSpace I x} {γ : ℝ → N × M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (verticalField J v) s) (hs : IsOpen s) (hs' : IsPreconnected s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) : IsMIntegralCurveOn (fun t ↦ (γ t).2) (v (γ t₀).1) s :=
  hγ.map_of_mfderiv_eq (fun _ _ ↦ mdifferentiableAt_snd) fun t ht ↦ by
    rw [mfderiv_snd, ← hγ.fst_eq_of_verticalField hs hs' ht₀ ht]
    -- The second projection sends `(0, v a x)` to `v a x`.
    rfl

/-- **The maximal interval of the vertical field** through `(a, x)` is the maximal interval of
`v a` through `x`. No regularity of the family is needed. -/
@[simp]
theorem maximalIntegralCurveInterval_verticalField [IsManifold J 1 N]
    (v : N → (x : M) → TangentSpace I x) (a : N) (x : M) :
    maximalIntegralCurveInterval (verticalField J v) (a, x) = maximalIntegralCurveInterval (v a) x
    := by
  ext t
  constructor
  · intro h
    obtain ⟨γ, α, β, hγ, hγ0, h0, ht, -⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq h
    have h2 := hγ.snd_of_verticalField isOpen_Ioo isPreconnected_Ioo h0
    simp only [hγ0] at h2
    exact h2.subset_maximalIntegralCurveInterval h0 (by simp [hγ0]) ht
  · exact fun h ↦ (mdifferentiable_const.prodMk mdifferentiable_id
      ).maximalIntegralCurveInterval_subset (mfderiv_prodMk_apply_verticalField v a) x h

/-- **The domain of the flow of the vertical field.** The flow of the vertical field is defined at
`(t, (a, x))` exactly when the flow of `v a` is defined at `(t, x)`. No regularity of the family
is needed. -/
theorem mem_flowDomain_verticalField_iff [IsManifold J 1 N] {v : N → (x : M) → TangentSpace I x}
    {t : ℝ} {a : N} {x : M} :
    (t, (a, x)) ∈ flowDomain (verticalField J v) ↔ (t, x) ∈ flowDomain (v a) := by
  rw [mem_flowDomain, mem_flowDomain, maximalIntegralCurveInterval_verticalField]

/-- **The flow of the vertical field** keeps the parameter fixed and follows the flow of the
field of that parameter: if `M` is Hausdorff and boundaryless and `v a` is `C¹`, then
`flowOf (verticalField J v) t (a, x) = (a, flowOf (v a) t x)` for all `t` and `x`. No regularity
in the parameter is needed. -/
theorem flowOf_verticalField [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
    [IsManifold J 1 N] {v : N → (x : M) → TangentSpace I x} {a : N}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v a y⟩ : TangentBundle I M))) (t : ℝ) (x : M) :
    flowOf (verticalField J v) t (a, x) = (a, flowOf (v a) t x) := by
  by_cases h : t ∈ maximalIntegralCurveInterval (v a) x
  · rw [← maximalIntegralCurveInterval_verticalField (J := J)] at h
    obtain ⟨γ, α, β, hγ, hγ0, h0, ht, heq⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq h
    have h1 := hγ.fst_eq_of_verticalField isOpen_Ioo isPreconnected_Ioo h0 ht
    have h2 := hγ.snd_of_verticalField isOpen_Ioo isPreconnected_Ioo h0
    simp only [hγ0] at h1 h2
    rw [flowOf_apply, flowOf_apply, heq,
      h2.eqOn_maximalIntegralCurve hv h0 (by simp [hγ0]) ht]
    exact Prod.ext h1 rfl
  · -- Outside the maximal intervals, both flows take the junk value at the initial point.
    rw [flowOf_apply, flowOf_apply, maximalIntegralCurve_eq_of_not_mem h,
      maximalIntegralCurve_eq_of_not_mem (by rwa [maximalIntegralCurveInterval_verticalField])]

/-- The derivative of a function of the second coordinate along the vertical field at `(a, x)` is
its derivative along `v a` at `x`. -/
theorem mvfderiv_comp_snd_verticalField {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {v : N → (x : M) → TangentSpace I x} {g : M → F'} {z : N × M} :
    mvfderiv (J.prod I) (g ∘ Prod.snd) z (verticalField J v z) = mvfderiv I g z.2 (v z.1 z.2) := by
  rw [mvfderiv_comp_snd_apply, verticalField_snd]

/-- **Transversality is open in the parameter.** If `g` is `C¹` at `q` and its derivative along
`v a₀` does not vanish there, then for `(a, x)` near `(a₀, q)` the function `g` is still `C¹` at `x`
and its derivative along `v a` does not vanish at `x`, provided the family `v` is continuous at
`(a₀, q)` as a map to the tangent bundle. -/
theorem eventually_contMDiffAt_and_mvfderiv_apply_ne_zero [IsManifold I 1 M] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {v : N → (x : M) → TangentSpace I x} {g : M → F'}
    {a₀ : N} {q : M}
    (hv : ContinuousAt (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)) (a₀, q))
    (hg : ContMDiffAt I 𝓘(ℝ, F') 1 g q) (hgv : mvfderiv I g q (v a₀ q) ≠ 0) :
    ∀ᶠ z in 𝓝 (a₀, q), ContMDiffAt I 𝓘(ℝ, F') 1 g z.2 ∧ mvfderiv I g z.2 (v z.1 z.2) ≠ 0 :=
  (continuousAt_snd.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hg)).and
    (((hg.contMDiffAt_mvfderiv_apply (p := ⟨q, v a₀ q⟩) (m := 0) (by simp)).continuousAt.comp
      (f := fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)) (x := (a₀, q)) hv).eventually_ne
        hgv)

/-! ### Continuation of nondegenerate closed orbits -/

section Continuation

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace F] [T2Space N]
  [BoundarylessManifold J N] {v : N → (x : M) → TangentSpace I x} {g : M → ℝ} {a₀ : N} {T₀ : ℝ}
  {p : M}

/-- **Transition maps of the vertical field restrict to transition maps of the fields.** Let `M`
and `N` be Hausdorff boundaryless manifolds modelled on Banach spaces, let `v` be a jointly `C¹`
family of vector fields on `M`, let the flow of `v a₀` be defined at `(T₀, p)`, and let
`{g = g q₀}` be a section through `q₀ = flowOf (v a₀) T₀ p` with `g` `C¹` at `q₀` and transverse to
`v a₀` there. Then for every `(t, (a, q))` close to `(T₀, (a₀, p))` such that the flow of `v a`
carries `q` into the section at time `t`, the map
`x ↦ (flowTransition (verticalField J v) (g ∘ Prod.snd) T₀ (a₀, p) (a, x)).2` agrees near `q` with
the transition map `flowTransition (v a) g t q` of the single field `v a`. -/
theorem eventually_eventuallyEq_snd_flowTransition_verticalField [CompleteSpace E]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (hv : ContMDiff (J.prod I) I.tangent 1
      (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)))
    (hP : (T₀, p) ∈ flowDomain (v a₀)) (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf (v a₀) T₀ p))
    (hgv : mvfderiv I g (flowOf (v a₀) T₀ p) (v a₀ (flowOf (v a₀) T₀ p)) ≠ 0) :
    ∀ᶠ y in 𝓝 (T₀, (a₀, p)), g (flowOf (v y.2.1) y.1 y.2.2) = g (flowOf (v a₀) T₀ p) →
      (fun x ↦ (flowTransition (verticalField J v) (g ∘ Prod.snd) T₀ (a₀, p) (y.2.1, x)).2)
        =ᶠ[𝓝 y.2.2] flowTransition (v y.2.1) g y.1 y.2.2 := by
  set q₀ := flowOf (v a₀) T₀ p
  have hva (a : N) : CMDiff 1 (fun y ↦ (⟨y, v a y⟩ : TangentBundle I M)) :=
    hv.comp (contMDiff_const.prodMk contMDiff_id)
  have hV := contMDiff_verticalField hv
  have hT : (T₀, (a₀, p)) ∈ flowDomain (verticalField J v) :=
    mem_flowDomain_verticalField_iff.2 hP
  have hflow : flowOf (verticalField J v) T₀ (a₀, p) = (a₀, q₀) :=
    flowOf_verticalField (hva a₀) T₀ p
  -- Near `(a₀, q₀)`, `g` is still `C¹` and transverse to the fields of the family.
  have hgnear :=
    eventually_contMDiffAt_and_mvfderiv_apply_ne_zero hv.continuous.continuousAt hg hgv
  have hflowNear : Tendsto (fun y : ℝ × N × M ↦ flowOf (verticalField J v) y.1 y.2)
      (𝓝 (T₀, (a₀, p))) (𝓝 (a₀, q₀)) := by
    rw [← hflow]
    exact (contMDiffAt_flowOf_comp le_rfl hV contMDiffAt_fst contMDiffAt_snd hT).continuousAt
  have huniq := eventually_eq_flowHittingTime_iff hV hT
    (by rw [hflow]; exact hg.comp (a₀, q₀) contMDiffAt_snd)
    (by rwa [hflow, mvfderiv_comp_snd_verticalField])
  simp only [hflow, comp_apply] at huniq
  -- An open neighbourhood of `(T₀, (a₀, p))` on which reaching the section at time `t` means
  -- that `t` is the hitting time of the vertical field.
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.1 huniq
  filter_upwards [hWopen.mem_nhds hWmem, (isOpen_flowDomain hV).mem_nhds hT,
    hflowNear.eventually hgnear] with ⟨t, a, q⟩ hW hdom hgq hlevel
  dsimp only at hW hdom hgq hlevel ⊢
  rw [mem_flowDomain_verticalField_iff] at hdom
  rw [flowOf_verticalField (hva a)] at hgq
  -- Near `q`, the hitting time of the section along `v a` is the hitting time of the vertical
  -- field: it is continuous at `q` with value `t`, so the points `(h x, (a, x))` stay in `W`.
  have hlev := eventually_flowHittingTime (hva a) hdom hgq.1 hgq.2
  have hhW : ∀ᶠ x in 𝓝 q, (flowHittingTime (v a) g t q x, (a, x)) ∈ W := by
    have h := (continuousAt_flowHittingTime (v := v a) (g := g) (T := t) (p := q)).tendsto
      |>.prodMk_nhds ((continuous_const.prodMk continuous_id).tendsto (f := fun x : M ↦ (a, x)) q)
    rw [flowHittingTime_self] at h
    exact h.eventually (hWopen.mem_nhds hW)
  filter_upwards [hlev, hhW] with x hx hxW
  have hσ : flowHittingTime (v a) g t q x =
      flowHittingTime (verticalField J v) (g ∘ Prod.snd) T₀ (a₀, p) (a, x) :=
    (hWsub hxW).1 (by rw [flowOf_verticalField (hva a), hx.2, hlevel])
  rw [flowTransition_apply, flowTransition_apply, ← hσ, flowOf_verticalField (hva a)]

/-- **Continuation of nondegenerate closed orbits.** Let `M` be a Hausdorff boundaryless manifold
modelled on a finite-dimensional space, `N` a Hausdorff boundaryless manifold modelled on a Banach
space, and `v` a jointly `C^n` family of vector fields on `M` indexed by `N`, with `1 ≤ n ≤ ∞`
(`n : ℕ∞`). Suppose `p` returns to itself at time `T₀` under the flow of `v a₀`, that `g` is
`C^n` at `p` with `dg_p (v a₀ p) ≠ 0`, so that `{g = g p}` is a local section through `p`
transverse to `v a₀`, and that the closed orbit is nondegenerate: `1` is not an eigenvalue of its
linearized return map. Then there are a return time `τ a` and a point `c a`, both `C^n` at `a₀`
with `τ a₀ = T₀` and `c a₀ = p`, such that for every parameter `a` near `a₀`:

* the flow of `v a` is defined at `(τ a, c a)`, and `c a` returns to itself at time `τ a` and lies
  on the section `{g = g p}`, which is still transverse to `v a` there;
* this closed orbit of `v a` is nondegenerate.

Moreover, near `(a₀, T₀, p)` these are exactly the closed orbits through the section: for
`(a, t, x)` close to `(a₀, T₀, p)`, the point `x` lies on the section and returns to itself at
time `t` under the flow of `v a` if and only if `t = τ a` and `x = c a`. -/
theorem exists_contMDiffAt_closedOrbit_continuation [FiniteDimensional ℝ E] [IsManifold I 1 M]
    {n : ℕ∞} [IsManifold I n M] [IsManifold J n N] (hn : 1 ≤ n)
    (hv : ContMDiff (J.prod I) I.tangent n
      (fun z : N × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)))
    (hP : (T₀, p) ∈ flowDomain (v a₀)) (hp : flowOf (v a₀) T₀ p = p)
    (hg : ContMDiffAt I 𝓘(ℝ) n g p) (hgv : mvfderiv I g p (v a₀ p) ≠ 0)
    (hnd : ¬(returnDerivative (v a₀) g T₀ p).HasEigenvalue 1) :
    ∃ (τ : N → ℝ) (c : N → M), τ a₀ = T₀ ∧ c a₀ = p ∧
      ContMDiffAt J 𝓘(ℝ) n τ a₀ ∧ ContMDiffAt J I n c a₀ ∧
      (∀ᶠ a in 𝓝 a₀, (τ a, c a) ∈ flowDomain (v a) ∧ flowOf (v a) (τ a) (c a) = c a ∧
        g (c a) = g p ∧ mvfderiv I g (c a) (v a (c a)) ≠ 0 ∧
        ¬(returnDerivative (v a) g (τ a) (c a)).HasEigenvalue 1) ∧
      ∀ᶠ y in 𝓝 (a₀, T₀, p), flowOf (v y.1) y.2.1 y.2.2 = y.2.2 ∧ g y.2.2 = g p ↔
        y.2.1 = τ y.1 ∧ y.2.2 = c y.1 := by
  have hn1 : ((1 : ℕ∞) : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have : IsManifold J 1 N := .of_le hn1
  have hg1 : ContMDiffAt I 𝓘(ℝ) 1 g p := hg.of_le hn1
  have hagree := eventually_eventuallyEq_snd_flowTransition_verticalField (J := J)
    (hv.of_le hn1) hP (by rwa [hp]) (by rwa [hp])
  set V := verticalField J v
  have hV : CMDiff n (fun z : N × M ↦ (⟨z, V z⟩ : TangentBundle (J.prod I) (N × M))) :=
    contMDiff_verticalField hv
  have hva (a : N) : CMDiff 1 (fun y ↦ (⟨y, v a y⟩ : TangentBundle I M)) :=
    (hv.comp (contMDiff_const.prodMk contMDiff_id)).of_le hn1
  -- The closed orbit of `v a₀` through `p` is a closed orbit of the vertical field through
  -- `(a₀, p)`, and `g ∘ Prod.snd` cuts out a transverse section through it.
  have hT : (T₀, (a₀, p)) ∈ flowDomain V := mem_flowDomain_verticalField_iff.2 hP
  have hflow : flowOf V T₀ (a₀, p) = (a₀, p) := by rw [flowOf_verticalField (hva a₀), hp]
  have hG : ContMDiffAt (J.prod I) 𝓘(ℝ) n (g ∘ Prod.snd) (flowOf V T₀ (a₀, p)) := by
    rw [hflow]
    exact hg.comp _ contMDiffAt_snd
  have hGV : mvfderiv (J.prod I) (g ∘ Prod.snd) (flowOf V T₀ (a₀, p))
      (V (flowOf V T₀ (a₀, p))) ≠ 0 := by
    rwa [hflow, mvfderiv_comp_snd_verticalField]
  obtain ⟨σ, hσ_def⟩ : ∃ σ, σ = flowHittingTime V (g ∘ Prod.snd) T₀ (a₀, p) := ⟨_, rfl⟩
  have hσC : ContMDiffAt (J.prod I) 𝓘(ℝ) n σ (a₀, p) := by
    rw [hσ_def]
    exact contMDiffAt_flowHittingTime hn hV hT hG hGV
  -- The return branches `f a` of the fields `v a` near `p`, read off the return branch of `V`.
  obtain ⟨f, hf_def⟩ : ∃ f : N → M → M,
      uncurry f = Prod.snd ∘ flowTransition V (g ∘ Prod.snd) T₀ (a₀, p) :=
    ⟨curry _, uncurry_curry _⟩
  have hf_apply (a : N) (x : M) : f a x = (flowTransition V (g ∘ Prod.snd) T₀ (a₀, p) (a, x)).2 :=
    congrFun hf_def (a, x)
  have hf : ContMDiffAt (J.prod I) I n (uncurry f) (a₀, p) := by
    rw [hf_def]
    exact contMDiffAt_snd.comp _ (contMDiffAt_flowTransition hn hV hT hG hGV)
  have hlev := eventually_flowHittingTime (hV.of_le hn1) hT (hG.of_le hn1) hGV
  have huniq := eventually_eq_flowHittingTime_iff (hV.of_le hn1) hT (hG.of_le hn1) hGV
  simp only [hflow, comp_apply, ← hσ_def] at hlev huniq
  have hfV (a : N) (x : M) : f a x = flowOf (v a) (σ (a, x)) x := by
    rw [hf_apply, flowTransition_apply, ← hσ_def, flowOf_verticalField (hva a)]
  simp only [← hf_apply, hp] at hagree
  -- The fixed point `p` of `f a₀` is nondegenerate, so it continues to fixed points `c a` of
  -- `f a`, with return times `τ a`.
  have hnd₀ : IsNondegenerateFixedPt I (f a₀) p :=
    ((isNondegenerateFixedPt_flowTransition_iff (hva a₀) hP hp hg1 hgv).2 hnd).congr_of_eventuallyEq
      (hagree.self_of_nhds (by dsimp only; rw [hp]))
  obtain ⟨c, hc0, hcC, hcnd, hcuniq⟩ :=
    hnd₀.exists_contMDiffAt_fixedPt_continuation (n := (n : ℕ∞ω))
      (by exact_mod_cast (zero_lt_one.trans_le hn).ne') hf
  obtain ⟨τ, hτ_def⟩ : ∃ τ : N → ℝ, ∀ a, τ a = σ (a, c a) := ⟨_, fun _ ↦ rfl⟩
  have hcpair : ContMDiffAt J (J.prod I) n (fun a ↦ (a, c a)) a₀ := contMDiffAt_id.prodMk hcC
  have hτC : ContMDiffAt J 𝓘(ℝ) n τ a₀ := by
    rw [funext hτ_def]
    exact hσC.comp_of_eq hcpair (by rw [hc0])
  have hτ0 : τ a₀ = T₀ := by rw [hτ_def, hc0, hσ_def, flowHittingTime_self]
  have hpair : Tendsto (fun a ↦ (a, c a)) (𝓝 a₀) (𝓝 (a₀, p)) := by
    simpa only [hc0] using hcpair.continuousAt.tendsto
  have hτpair : Tendsto (fun a ↦ (τ a, (a, c a))) (𝓝 a₀) (𝓝 (T₀, (a₀, p))) := by
    simpa only [hτ0] using hτC.continuousAt.tendsto.prodMk_nhds hpair
  -- Near `(a₀, p)`, `g` is still `C¹` and transverse to the fields of the family.
  have hgnear :=
    eventually_contMDiffAt_and_mvfderiv_apply_ne_zero hv.continuous.continuousAt hg1 hgv
  -- Each `c a` is a closed orbit of `v a` through the section, where `f a` is the return branch
  -- of `v a`; so nondegeneracy as a fixed point of `f a` is nondegeneracy of the orbit.
  have horbit : ∀ᶠ a in 𝓝 a₀, (τ a, c a) ∈ flowDomain (v a) ∧
      flowOf (v a) (τ a) (c a) = c a ∧ g (c a) = g p ∧ mvfderiv I g (c a) (v a (c a)) ≠ 0 ∧
      ¬(returnDerivative (v a) g (τ a) (c a)).HasEigenvalue 1 := by
    filter_upwards [hcnd, hpair.eventually hlev, hpair.eventually hgnear,
      hτpair.eventually hagree] with a hnda hleva hgna hagreea
    rw [← hτ_def] at hleva
    have hdom : (τ a, c a) ∈ flowDomain (v a) := mem_flowDomain_verticalField_iff.1 hleva.1
    have hclosed : flowOf (v a) (τ a) (c a) = c a := by
      rw [hτ_def, ← hfV]
      exact hnda.isFixedPt
    have hgc : g (c a) = g p := by
      have h := hleva.2
      rwa [flowOf_verticalField (hva a), hclosed] at h
    exact ⟨hdom, hclosed, hgc, hgna.2, (isNondegenerateFixedPt_flowTransition_iff (hva a) hdom
      hclosed hgna.1 hgna.2).1
        (hnda.congr_of_eventuallyEq (hagreea (by rw [hclosed, hgc])).symm)⟩
  refine ⟨τ, c, hτ0, hc0, hτC, hcC, horbit, ?_⟩
  -- A closed orbit through the section near `(T₀, p)` reaches it at the hitting time of `V`,
  -- so its point is a fixed point of `f a`, which is `c a`; conversely the continued orbits are
  -- closed orbits through the section.
  have hmap : Tendsto (fun y : N × ℝ × M ↦ (y.2.1, (y.1, y.2.2))) (𝓝 (a₀, T₀, p))
      (𝓝 (T₀, (a₀, p))) :=
    ((continuous_snd.fst).prodMk (continuous_fst.prodMk continuous_snd.snd)).tendsto _
  have hmap₂ : Tendsto (fun y : N × ℝ × M ↦ (y.1, y.2.2)) (𝓝 (a₀, T₀, p)) (𝓝 (a₀, p)) :=
    (continuous_fst.prodMk continuous_snd.snd).tendsto _
  filter_upwards [hmap.eventually huniq, hmap₂.eventually hcuniq,
    (continuous_fst.tendsto _).eventually horbit] with y hu hcu hy
  refine ⟨fun ⟨hfix, hgy⟩ ↦ ?_, fun ⟨ht, hx⟩ ↦ ?_⟩
  · have hVflow : flowOf V y.2.1 (y.1, y.2.2) = (y.1, y.2.2) := by
      rw [flowOf_verticalField (hva y.1), hfix]
    have ht : y.2.1 = σ (y.1, y.2.2) := hu.1 (by rw [hVflow, hgy])
    have hfx : IsFixedPt (f y.1) y.2.2 := by
      rw [IsFixedPt, hfV, ← ht, hfix]
    have hcx : c y.1 = y.2.2 := hcu.1 hfx
    exact ⟨by rw [ht, hτ_def, hcx], hcx.symm⟩
  · rw [ht, hx]
    exact ⟨hy.2.1, hy.2.2.1⟩

end Continuation

end TauCeti
