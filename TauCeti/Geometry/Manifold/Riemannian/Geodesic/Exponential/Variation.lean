/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Analysis.Calculus.FDeriv.InitialPositivity
import TauCeti.Geometry.Manifold.MFDeriv.Chart.EndpointVariation

/-!
# Exponential variations of a curve

Let `γ : ℝ → M` be a curve in a Riemannian manifold and `V` a tangent field along `γ`. The
**exponential variation** `TauCeti.Manifold.exponentialVariation I γ V` is the two-parameter
family `(s, t) ↦ exp_(γ t) (s • V t)`. Its central curve is `γ` and its variation field is `V`.
It is jointly `C^n` at every point `(s, t)` with `s • V t` in the domain of the exponential map
at `γ t`, as soon as the lift of `V` to the tangent bundle is `C^n` at `t`. In particular it is
`C^n` along the central curve. Neither completeness nor a normal neighbourhood containing the
curve is needed.

For each `t`, the transverse curve `s ↦ exp_(γ t) (s • V t)` is the maximal geodesic from `γ t`
with initial velocity `V t`. Over an open set `S` of parameters `t` on which the lift of `V` is
continuous, the pairs `(s, t)` with `s • V t` in the domain of the exponential map at `γ t` form an
open subset of the plane, on which the exponential variation is as regular as the lift of `V`.
When `γ` is a curve in a surface and `V` a unit normal field along it, this is the map of the
Fermi coordinates of `γ`. If `γ` lies on the zero set of a function `ρ` whose derivative is
positive on `V`, the transverse geodesics from all the points of `γ` near a given one enter
`{ρ > 0}` at once and stay there on a common initial interval: for instance, normal geodesics
leaving the boundary of a domain inwards enter the domain.

Combined with an endpoint correction in a chart, the exponential variation realizes every `C^n`
field `V` along `γ` on `[a, b]` as the variation field of a `C^n` variation whose left endpoint
follows a prescribed curve `σ` with `σ 0 = γ a` and velocity `V a`, and whose right endpoint
follows the geodesic `s ↦ exp_(γ b) (s • V b)`, which is fixed when `V b = 0`.
For two fields `V, W` on adjacent intervals `[a, c]` and `uIcc c b` with `V c = W c`,
the two variation branches can be chosen with matching moving vertices at `c`, while the
left endpoint follows `σ` near `0` and the right endpoint is fixed when `W b = 0`.
The assembled family agrees with each branch on its closed interval. This realizes fields
with a corner as piecewise curve variations for variational arguments.

## Main definitions and results

* `TauCeti.Manifold.exponentialVariation`: the exponential variation of a curve along a field.
* `TauCeti.Manifold.exponentialVariation_zero`: its central curve is the original curve.
* `TauCeti.Manifold.variationField_exponentialVariation`: its variation field is the given field.
* `TauCeti.Manifold.contMDiffAt_exponentialVariation`: its joint regularity on the domain of the
  exponential map.
* `TauCeti.Manifold.contMDiffAt_exponentialVariation_zero`: its joint regularity along the
  central curve.
* `TauCeti.Manifold.isGeodesicCurveOnFrom_exponentialVariation`: its transverse curves are the
  geodesics leaving the curve with the velocities given by the field.
* `TauCeti.Manifold.isOpen_setOfPred_smul_mem_expDomain`: its natural domain over an open set of
  parameters is open.
* `TauCeti.Manifold.contMDiffOn_exponentialVariation`: its joint regularity on that domain.
* `TauCeti.Manifold.eventually_pos_on_initial_interval_comp_exponentialVariation`: its transverse
  geodesics from a zero set of `ρ` enter `{ρ > 0}` on a common initial interval.
* `TauCeti.Manifold.exists_contMDiffAt_variationField_eq`: every `C^n` field along a curve is the
  variation field of a `C^n` variation with a prescribed moving left endpoint.
* `TauCeti.Manifold.exists_contMDiffAt_variationField_pair_eq`: two fields agreeing at their
  join are realized by a piecewise family with regular branches and matching moving vertices.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5 (tubular neighbourhoods and Fermi coordinates) and Chapter 6 (variations of curves).
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))

variable (I) in
/-- The exponential variation `(s, t) ↦ exp_(γ t) (s • V t)` of the curve `γ` along the tangent
field `V`. -/
def exponentialVariation (s t : ℝ) : M :=
  riemannianExp I M (γ t) (s • V t)

omit [I.Boundaryless] [T2Space M] in
/-- The defining formula of the exponential variation. -/
@[simp]
theorem exponentialVariation_apply (s t : ℝ) :
    exponentialVariation I γ V s t = riemannianExp I M (γ t) (s • V t) :=
  (rfl)

/-- The central curve of the exponential variation is the original curve. -/
@[simp]
theorem exponentialVariation_zero : exponentialVariation I γ V 0 = γ := by
  funext t
  simp only [exponentialVariation_apply, zero_smul, riemannianExp_zero]

/-- The variation field of the exponential variation is the given field. -/
@[simp]
theorem variationField_exponentialVariation (t : ℝ) :
    variationField I (exponentialVariation I γ V) t = V t := by
  rw [variationField_apply]
  exact curveVelocity_riemannianExp_smul_zero (γ t) (V t)

/-- The exponential variation is jointly `C^n` at every `(s, t)` with `s • V t` in the domain of
the exponential map at `γ t`, when the lift of `V` to the tangent bundle is `C^n` at `t`. -/
theorem contMDiffAt_exponentialVariation {n : ℕ∞} {s t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t)
    (hv : s • V t ∈ expDomain I M (γ t)) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (s, t) := by
  have hinput : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent n
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (γ z.2) (z.1 • V z.2)) (s, t) :=
    contDiff_fst.contMDiff.contMDiffAt.smul_totalSpace
      (hV.comp (s, t) contDiff_snd.contMDiff.contMDiffAt)
  have hexp : ContMDiffAt I.tangent I n
      (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      (TotalSpace.mk' E (γ t) (s • V t)) :=
    (contMDiffOn_riemannianExp_tangentBundle.contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds hv)).of_le (by exact_mod_cast le_top)
  exact hexp.comp (s, t) hinput

/-- The exponential variation is jointly `C^n` at every point `(0, t)` of the central curve where
the lift of `V` to the tangent bundle is `C^n`. -/
theorem contMDiffAt_exponentialVariation_zero {n : ℕ∞} {t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
  contMDiffAt_exponentialVariation γ V hV (by simp)

omit [I.Boundaryless] [T2Space M] in
/-- Replacing the field `V` by `-V` reverses the variation parameter of the exponential
variation. -/
@[simp]
theorem exponentialVariation_neg (s : ℝ) :
    exponentialVariation I γ (-V) s = exponentialVariation I γ V (-s) := by
  funext t
  simp only [exponentialVariation_apply, Pi.neg_apply, smul_neg, neg_smul]

/-- For each `t`, the transverse curve `s ↦ exp_(γ t) (s • V t)` of the exponential variation is a
geodesic on the maximal geodesic interval of `V t`, leaving `γ t` with velocity `V t`. -/
theorem isGeodesicCurveOnFrom_exponentialVariation (t : ℝ) :
    IsGeodesicCurveOnFrom I (fun s ↦ exponentialVariation I γ V s t)
      (geodesicInterval I M (γ t) (V t)) (γ t) (V t) := by
  have hcurve : (fun s ↦ exponentialVariation I γ V s t) = maximalGeodesic I M (γ t) (V t) :=
    funext fun s ↦ riemannianExp_smul (γ t) (V t) s
  rw [hcurve]
  exact isGeodesicCurveOnFrom_maximalGeodesic (γ t) (V t)

/-- Let `S` be an open set of parameters on which the lift of `V` to the tangent bundle is
continuous. The pairs `(s, t)` with `t ∈ S` and `s • V t` in the domain of the exponential map at
`γ t` form an open subset of the plane. -/
theorem isOpen_setOfPred_smul_mem_expDomain {S : Set ℝ} (hS : IsOpen S)
    (hV : ContinuousOn (fun t ↦ TotalSpace.mk' E (γ t) (V t)) S) :
    IsOpen {z : ℝ × ℝ | z.2 ∈ S ∧ z.1 • V z.2 ∈ expDomain I M (γ z.2)} := by
  have hinput : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent 0
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (γ z.2) (z.1 • V z.2)) (Prod.snd ⁻¹' S) :=
    contDiff_fst.contMDiff.contMDiffOn.smul_totalSpace
      ((contMDiffOn_zero_iff.2 hV).comp contDiff_snd.contMDiff.contMDiffOn (mapsTo_preimage _ _))
  exact hinput.continuousOn.isOpen_inter_preimage (hS.preimage continuous_snd)
    isOpen_setOfPred_mem_expDomain

/-- If the lift of `V` to the tangent bundle is `C^n` on a set `S` of parameters, the exponential
variation is jointly `C^n` on the set of pairs `(s, t)` with `t ∈ S` and `s • V t` in the domain of
the exponential map at `γ t`. -/
theorem contMDiffOn_exponentialVariation {n : ℕ∞} {S : Set ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (V t)) S) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2)
      {z : ℝ × ℝ | z.2 ∈ S ∧ z.1 • V z.2 ∈ expDomain I M (γ z.2)} := by
  have hinput : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent n
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (γ z.2) (z.1 • V z.2))
      {z : ℝ × ℝ | z.2 ∈ S ∧ z.1 • V z.2 ∈ expDomain I M (γ z.2)} :=
    contDiff_fst.contMDiff.contMDiffOn.smul_totalSpace
      (hV.comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hz ↦ hz.1 : MapsTo Prod.snd
          {z : ℝ × ℝ | z.2 ∈ S ∧ z.1 • V z.2 ∈ expDomain I M (γ z.2)} S))
  have hexp : ContMDiffOn I.tangent I n
      (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      {z | z.2 ∈ expDomain I M z.proj} :=
    contMDiffOn_riemannianExp_tangentBundle.of_le (by exact_mod_cast le_top)
  exact hexp.comp hinput fun _ hz ↦ hz.2

/-- The derivative at `s = 0` of a function `f` along the transverse geodesic
`s ↦ exp_(γ t) (s • V t)` is the derivative of `f` at `γ t` in the direction `V t`. -/
theorem hasDerivAt_comp_exponentialVariation_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : M → F} {t : ℝ} (hf : MDifferentiableAt I 𝓘(ℝ, F) f (γ t)) :
    HasDerivAt (fun s ↦ f (exponentialVariation I γ V s t)) (mvfderiv I f (γ t) (V t)) 0 := by
  have key (x : M) (hx : exponentialVariation I γ V 0 t = x)
      (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) :
      HasDerivAt (fun s ↦ f (exponentialVariation I γ V s t)) (mvfderiv I f x (V t)) 0 := by
    subst hx
    exact hasDerivAt_comp_curve hf
      ((isGeodesicCurveOnFrom_exponentialVariation γ V t).hasMFDerivAt_zero
        (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval))
  exact key (γ t) (by simp) hf

/-- **Transverse geodesics enter a superlevel set at once.** Let `ρ` be a `C¹` function vanishing
on `γ` near `t`, whose derivative at `γ t` is positive on `V t`, and let the lift of `V` be `C¹` at
`t`. Then there is `τ > 0` such that `ρ (exp_(γ u) (s • V u)) > 0` for all `u` near `t` and all
`s ∈ (0, τ]`. -/
theorem eventually_pos_on_initial_interval_comp_exponentialVariation {t : ℝ} {ρ : M → ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t)
    (hρ : ContMDiffAt I 𝓘(ℝ, ℝ) 1 ρ (γ t)) (hzero : ∀ᶠ u in 𝓝 t, ρ (γ u) = 0)
    (hpos : 0 < mvfderiv I ρ (γ t) (V t)) :
    ∃ τ > 0, ∀ᶠ u in 𝓝 t, ∀ s ∈ Ioc 0 τ, 0 < ρ (exponentialVariation I γ V s u) := by
  have hρ' : ContMDiffAt I 𝓘(ℝ, ℝ) 1 ρ (exponentialVariation I γ V 0 t) := by
    simpa only [exponentialVariation_zero] using hρ
  have hG : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.2 z.1) (t, 0) :=
    (contMDiffAt_exponentialVariation_zero γ V hV).comp (t, 0)
      (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffAt
  have hφ : ContDiffAt ℝ 1 (fun z : ℝ × ℝ ↦ ρ (exponentialVariation I γ V z.2 z.1)) (t, 0) :=
    contMDiffAt_iff_contDiffAt.1 (hρ'.comp (t, 0) hG)
  have hline : HasDerivAt (fun s : ℝ ↦ (t, s)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id (0 : ℝ))
  have hd := (hφ.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  rw [← hd.unique (hasDerivAt_comp_exponentialVariation_zero γ V
    (hρ.mdifferentiableAt one_ne_zero))] at hpos
  obtain ⟨τ, hτ, -, h⟩ := TauCeti.eventually_pos_on_initial_interval_of_partial_deriv_pos
    zero_lt_one hφ hpos (hzero.mono fun u hu ↦ by simpa only [exponentialVariation_zero] using hu)
  exact ⟨τ, hτ, h.mono fun u hu s hs ↦ hu s (by rwa [zero_add])⟩

/-- **Realization of a field with a moving endpoint.** Let `V` be a field along `γ` whose lift to
the tangent bundle is `C^n`, `1 ≤ n`, on `[a, b]`, with `a < b`, and let `σ` be a curve which is
`C^n` at `0`, with `σ 0 = γ a` and velocity `V a` at `0`. Then there is a `C^n` variation of `γ`
with variation field `V` on `[a, b]`, whose curves start at `σ s` for `s` near `0` and end at
`exp_(γ b) (s • V b)`. In particular the right endpoint is fixed when `V b = 0`. -/
theorem exists_contMDiffAt_variationField_eq {n : ℕ∞} (hn : 1 ≤ n) {σ : ℝ → M} {a b : ℝ}
    (hab : a < b)
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : γ a = σ 0) (hvel : curveVelocity I σ 0 = V a) :
    ∃ F : ℝ → ℝ → M, F 0 = γ ∧
      (∀ t ∈ uIcc a b,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, F s a = σ s) ∧ (∀ s, F s b = exponentialVariation I γ V s b) ∧
      ∀ t ∈ uIcc a b, variationField I F t = V t := by
  obtain ⟨F, hF₀, hF, hFa, hFb, hFV⟩ := exists_contMDiffAt_endpointCorrection hn hab
    (fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)) hσ
    (by rw [exponentialVariation_zero]; exact hbase)
    (by rw [variationField_exponentialVariation]; exact hvel)
  exact ⟨F, hF₀.trans (exponentialVariation_zero γ V), hF, hFa, hFb,
    fun t ht ↦ (hFV t ht).trans (variationField_exponentialVariation γ V t)⟩

/-- Two fields `V, W` whose tangent-bundle lifts are `C^n`, `1 ≤ n`, on `uIcc a c` and
`uIcc c b`, respectively, with `a < c` and `V c = W c`, are realized by variation branches
jointly `C^n` along `{0} × uIcc a c` and `{0} × uIcc c b`, with matching moving vertices.
If `σ` is `C^n` at `0`, starts at `γ a` and has velocity `V a`, the left endpoint follows
`σ s` for `s` near `0`. The second branch ends at `exp_(γ b) (s • W b)`, so its terminal
value is fixed when `W b = 0`. The central curves and both variation fields remain exact.
The assembled family `F` agrees with the branches on `Icc a c` and `Icc c b`, respectively. -/
theorem exists_contMDiffAt_variationField_pair_eq (W : ∀ t, TangentSpace I (γ t))
    {n : ℕ∞} (hn : 1 ≤ n) {σ : ℝ → M} {a c b : ℝ} (hac : a < c)
    (hV : ∀ t ∈ uIcc a c, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t)
    (hW : ∀ t ∈ uIcc c b, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun t ↦ TotalSpace.mk' E (γ t) (W t)) t)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : γ a = σ 0)
    (hvel : curveVelocity I σ 0 = V a) (hjoin : V c = W c) :
    ∃ F G₁ G₂ : ℝ → ℝ → M, F 0 = γ ∧ G₁ 0 = γ ∧ G₂ 0 = γ ∧
      (∀ s, EqOn (F s) (G₁ s) (Icc a c)) ∧
      (∀ s, EqOn (F s) (G₂ s) (Icc c b)) ∧
      (∀ t ∈ uIcc a c,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G₁ z.1 z.2) (0, t)) ∧
      (∀ t ∈ uIcc c b,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G₂ z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G₁ s a = σ s) ∧ (∀ s, G₁ s c = G₂ s c) ∧
      (∀ s, G₂ s b = exponentialVariation I γ W s b) ∧
      (∀ t ∈ uIcc a c, variationField I G₁ t = V t) ∧
      (∀ t ∈ uIcc c b, variationField I G₂ t = W t) := by
  obtain ⟨G₁, hG₁₀, hG₁, hG₁a, hG₁c, hG₁V⟩ :=
    exists_contMDiffAt_variationField_eq γ V hn hac hV hσ hbase hvel
  have hmatch (s : ℝ) : G₁ s c = exponentialVariation I γ W s c := by
    rw [hG₁c]
    simp only [exponentialVariation_apply, hjoin]
  let F : ℝ → ℝ → M := fun s t ↦ if t ≤ c then G₁ s t else exponentialVariation I γ W s t
  refine ⟨F, G₁, exponentialVariation I γ W, ?_, hG₁₀, exponentialVariation_zero γ W,
    ?_, ?_, hG₁, fun t ht ↦ contMDiffAt_exponentialVariation_zero γ W (hW t ht),
    hG₁a, hmatch, fun _ ↦ rfl, hG₁V, fun t _ ↦ variationField_exponentialVariation γ W t⟩
  · funext t
    simp only [F, hG₁₀, exponentialVariation_zero, ite_self]
  · intro s t ht
    simp only [F, ite_eq_left ht.2]
  · intro s t ht
    rcases ht.1.eq_or_lt with h | h
    · subst t
      simpa only [F, le_refl, ↓reduceIte] using hmatch s
    · simp only [F, ite_eq_right (not_le.mpr h)]

end TauCeti.Manifold
