/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Analysis.Calculus.LocalOperator
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt

/-!
# Peetre's theorem on manifolds

Let `M` be a finite-dimensional Hausdorff boundaryless real manifold and `P` a linear map from the
smooth functions `M → ℝ` to functions `M → G`. Suppose that on an open set `U` the operator `P` is
*local*, that is `(P f) x = 0` whenever `f` vanishes on a neighbourhood of `x ∈ U`, and that every
`P f` is continuous on `U`. No continuity of `P` itself is assumed. Peetre's theorem says that `P`
then has locally finite order: for every compact `K ⊆ U` there is `r` such that `(P f) x = 0`
whenever `x ∈ K` and `f` lies in the `(r + 1)`-st power of the ideal `I_x` of smooth functions
vanishing at `x` (`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`). Equivalently,
`(P f) x = (P g) x` whenever the chart expressions of `f` and `g` have the same derivatives of
order at most `r` at `x`, that is, whenever `f` and `g` have the same `r`-jet at `x`
(`LinearMap.exists_apply_eq_apply_of_iteratedFDeriv_comp_extChartAt_symm_eq`).

The proof reduces to the Euclidean theorem
`LinearMap.exists_apply_eq_zero_of_iteratedFDeriv_eq_zero`. Near a point `x₀ ∈ U`, a smooth
function `g` on the model space becomes the smooth function `y ↦ β y • g (φ y)` on `M`, where
`φ = extChartAt I x₀` and `β` is a bump function at `x₀`; applying `P` and reading the result in
the chart gives a local operator on the model space. Its finite order near `φ x₀` gives a common
order at all points of a neighbourhood of `x₀`, and a function in `I_y ^ (r + 1)` has a chart
expression in `φ` whose `r`-jet vanishes at `φ y`
(the `_of_mem_source` form of
`TauCeti.iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow`). A finite
cover of `K` gives the uniform order.

On a compact manifold the order is therefore bounded, and the algebraic criterion
`TauCeti.mem_differentialOperators_iff_forall_apply_mem_smul_top` turns the vanishing on
`I_x ^ (r + 1)` at every point into the vanishing of all `(r + 1)`-fold commutators with
multiplication operators. So for compact `M`, a linear endomorphism of `C^∞(M)` is local if
and only if it is a differential operator of finite order in Grothendieck's sense
(`LinearMap.exists_mem_differentialOperators_iff_apply_eq_zero_of_eventuallyEq`). On a noncompact
manifold the order need not be bounded: on a disjoint union of circles, the operator acting by the
`j`-th derivative on the `j`-th circle is local but has no finite order.

## Main results

* `LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`,
  `LinearMap.exists_apply_eq_apply_of_iteratedFDeriv_comp_extChartAt_symm_eq`: **Peetre's
  theorem** on manifolds.
* `LinearMap.exists_mem_differentialOperators_iff_apply_eq_zero_of_eventuallyEq`: on a compact
  manifold the local operators on `C^∞(M)` are exactly the differential operators.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Theorem 19.1.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Set Filter Metric
open scoped ContDiff Manifold Topology

noncomputable section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Multiplication by a bump function `β` at `x₀` turns a smooth function `g` on the model space
into the smooth function `y ↦ β y • g (extChartAt I x₀ y)` on `M`. -/
private def chartLift {x₀ : M} (β : SmoothBumpFunction I x₀) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun g := ⟨fun y ↦ β y • g (extChartAt I x₀ y),
    β.contMDiff_smul (g.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt)⟩
  map_add' g h := by ext y; exact smul_add (β y) (g _) (h _)
  map_smul' c g := by ext y; exact smul_comm (β y) c (g _)

private theorem chartLift_apply {x₀ : M} (β : SmoothBumpFunction I x₀) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (y : M) : chartLift β g y = β y • g (extChartAt I x₀ y) :=
  (rfl)

variable [BoundarylessManifold I M]

/-- **Peetre's theorem**, local form: near each point `x₀` of `U` there is a common order `r` such
that `(P f) y = 0` for every `y` near `x₀` and every `f ∈ I_y ^ (r + 1)`. -/
private theorem exists_mem_nhds_forall_apply_eq_zero (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] M → G)
    {U : Set M} (hU : IsOpen U)
    (hloc : ∀ f : C^∞⟮I, M; ℝ⟯, ∀ x ∈ U, (f : M → ℝ) =ᶠ[𝓝 x] 0 → P f x = 0)
    (hcont : ∀ f, ContinuousOn (P f) U) {x₀ : M} (hx₀ : x₀ ∈ U) :
    ∃ N ∈ 𝓝 x₀, ∃ r : ℕ, ∀ y ∈ N, ∀ f ∈ TauCeti.smoothVanishingIdeal I y ^ (r + 1),
      P f y = 0 := by
  set e := extChartAt I x₀
  let β : SmoothBumpFunction I x₀ := Classical.choice inferInstance
  -- An open neighbourhood `W` of `x₀` in the chart source on which `β = 1`.
  obtain ⟨W₀, hW₀β, hW₀o, hx₀W₀⟩ := _root_.eventually_nhds_iff.1 β.eventuallyEq_one
  set W := W₀ ∩ e.source
  have hWo : IsOpen W := hW₀o.inter (isOpen_extChartAt_source x₀)
  -- The operator `P` read in the chart `e`, as an operator on functions on the model space.
  let Q : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] E → G := funLeft ℝ G e.symm ∘ₗ P ∘ₗ chartLift β
  have hQ (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (z : E) : Q g z = P (chartLift β g) (e.symm z) := (rfl)
  set U' := interior e.target ∩ e.symm ⁻¹' (W ∩ U)
  have hU' : IsOpen U' := ((continuousOn_extChartAt_symm x₀).mono interior_subset)
    |>.isOpen_inter_preimage isOpen_interior (hWo.inter hU)
  have hQloc (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (z : E) (hz : z ∈ U') (hg : (g : E → ℝ) =ᶠ[𝓝 z] 0) :
      Q g z = 0 := by
    rw [hQ]
    refine hloc _ _ hz.2.2 ?_
    have he : Tendsto e (𝓝 (e.symm z)) (𝓝 z) := by
      have h := (continuousAt_extChartAt' (I := I) (e.map_target (interior_subset hz.1))).tendsto
      rwa [e.right_inv (interior_subset hz.1)] at h
    filter_upwards [he.eventually hg] with y hy
    rw [Pi.zero_apply] at hy
    rw [chartLift_apply, hy, smul_zero, Pi.zero_apply]
  have hQcont (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : ContinuousOn (Q g) U' :=
    (hcont _).comp
      ((continuousOn_extChartAt_symm x₀).mono (inter_subset_left.trans interior_subset))
      fun z hz ↦ hz.2.2
  have hx₀U' : e x₀ ∈ U' :=
    ⟨I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint, by
      rw [mem_preimage, extChartAt_to_inv]
      exact ⟨⟨hx₀W₀, mem_extChartAt_source x₀⟩, hx₀⟩⟩
  obtain ⟨δ, hδ, hδU'⟩ := Metric.isOpen_iff.1 hU' _ hx₀U'
  -- The Euclidean theorem on a closed ball around `e x₀`.
  obtain ⟨r, hr⟩ := exists_apply_eq_zero_of_iteratedFDeriv_eq_zero Q hU' hQloc hQcont
    (isCompact_closedBall (e x₀) (δ / 2))
    ((closedBall_subset_ball (by linarith)).trans hδU')
  refine ⟨e.source ∩ e ⁻¹' ball (e x₀) (δ / 2), inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds _ (by linarith))), r, ?_⟩
  rintro y ⟨hys, hyb⟩ f hf
  have hz : e y ∈ U' := hδU' (ball_subset_ball (by linarith) hyb)
  have hy : e.symm (e y) = y := e.left_inv hys
  have hyW : y ∈ W := hy ▸ hz.2.1
  have hint : e y ∈ interior e.target := hz.1
  -- Near `y`, `f` is the lift of a smooth function `g` on the model space.
  obtain ⟨g, hg, hfg⟩ := TauCeti.exists_contDiff_comp_extChartAt_symm_eventuallyEq hint f
  set g' : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨g, hg.contMDiff⟩ with hg'
  have hcoe : (g' : E → ℝ) = g := by rw [hg', ContMDiffMap.coeFn_mk]
  have hlift : (f - chartLift β g' : C^∞⟮I, M; ℝ⟯) =ᶠ[𝓝 y] 0 := by
    filter_upwards [hWo.mem_nhds hyW, (continuousAt_extChartAt' hys).tendsto.eventually hfg]
      with w hw hfw
    rw [Function.comp_apply, e.left_inv hw.2] at hfw
    rw [ContMDiffMap.coe_sub, Pi.sub_apply, chartLift_apply, hW₀β w hw.1, Pi.one_apply, one_smul,
      hcoe, hfw, sub_self, Pi.zero_apply]
  have hPf : P f y = P (chartLift β g') y := by
    have h := hloc _ y (hy ▸ hz.2.2) hlift
    rwa [map_sub, Pi.sub_apply, sub_eq_zero] at h
  rw [hPf, ← hy, ← hQ]
  refine hr (e y) (ball_subset_closedBall hyb) g' fun k hk ↦ ?_
  rw [hcoe, ← (hfg.iteratedFDeriv ℝ k).eq_of_nhds]
  open TauCeti in
  exact iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow_of_mem_source
    hys hint hf hk

/-- **Peetre's theorem** on manifolds. Let `P` be a linear map from smooth functions `M → ℝ` to
functions `M → G`, local on the open set `U` (`(P f) x = 0` whenever `f` vanishes near `x ∈ U`)
and with `P f` continuous on `U` for every `f`. Then `P` has locally finite order: for every
compact `K ⊆ U` there is `r` such that `(P f) x = 0` whenever `x ∈ K` and `f` is a finite sum of
products of `r + 1` smooth functions vanishing at `x`. No continuity of `P` is assumed. -/
theorem exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] M → G)
    {U : Set M} (hU : IsOpen U)
    (hloc : ∀ f : C^∞⟮I, M; ℝ⟯, ∀ x ∈ U, (f : M → ℝ) =ᶠ[𝓝 x] 0 → P f x = 0)
    (hcont : ∀ f, ContinuousOn (P f) U) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ f ∈ TauCeti.smoothVanishingIdeal I x ^ (r + 1), P f x = 0 := by
  choose! N hN r hr using fun x (hx : x ∈ U) ↦
    exists_mem_nhds_forall_apply_eq_zero P hU hloc hcont hx
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover N fun x hx ↦ hN x (hKU hx)
  refine ⟨t.sup r, fun x hx f hf ↦ ?_⟩
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (hKt hx)
  exact hr c (hKU (htK c hct)) x hxc f
    (Ideal.pow_le_pow_right (Nat.succ_le_succ (Finset.le_sup hct)) hf)

/-- **Peetre's theorem** on manifolds, in jet form: for every compact `K ⊆ U` there is `r` such
that `(P f) x = (P g) x` whenever `x ∈ K` and the chart expressions of `f` and `g` in the extended
chart at `x` have the same derivatives of order at most `r` at the image of `x`. -/
theorem exists_apply_eq_apply_of_iteratedFDeriv_comp_extChartAt_symm_eq
    (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] M → G) {U : Set M} (hU : IsOpen U)
    (hloc : ∀ f : C^∞⟮I, M; ℝ⟯, ∀ x ∈ U, (f : M → ℝ) =ᶠ[𝓝 x] 0 → P f x = 0)
    (hcont : ∀ f, ContinuousOn (P f) U) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ f g : C^∞⟮I, M; ℝ⟯,
      (∀ k ≤ r,
        iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) =
          iteratedFDeriv ℝ k ((g : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x)) →
        P f x = P g x := by
  obtain ⟨r, hr⟩ := exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow P hU hloc hcont hK hKU
  refine ⟨r, fun x hx f g hfg ↦ ?_⟩
  have hmem : f - g ∈ TauCeti.smoothVanishingIdeal I x ^ (r + 1) := by
    rw [← Ideal.Quotient.eq]
    exact (TauCeti.quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff
      BoundarylessManifold.isInteriorPoint r f g).mpr hfg
  have h := hr x hx _ hmem
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at h

/-- **Local operators on a compact manifold are differential operators.** On a compact
finite-dimensional Hausdorff boundaryless manifold, a linear endomorphism `P` of `C^∞(M)` is local,
that is `(P f) x = 0` whenever `f` vanishes near `x`, if and only if it is a differential operator
of some finite order in Grothendieck's sense: for some `r`, all its `(r + 1)`-fold commutators with
multiplication operators vanish. No continuity of `P` is assumed. -/
theorem exists_mem_differentialOperators_iff_apply_eq_zero_of_eventuallyEq [CompactSpace M]
    (P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :
    (∃ r, P ∈ TauCeti.differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ r) ↔
      ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M), (f : M → ℝ) =ᶠ[𝓝 x] 0 → P f x = 0 := by
  constructor
  · rintro ⟨r, hP⟩ f x hf
    simpa using TauCeti.differentialOperators_apply_eq_of_eventuallyEq hP (g := 0) hf
  · intro hloc
    obtain ⟨r, hr⟩ := exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow
      (ContMDiffMap.coeFnLinearMap ∘ₗ P) isOpen_univ (fun f x _ ↦ hloc f x)
      (fun f ↦ (P f).contMDiff.continuous.continuousOn) isCompact_univ subset_rfl
    have hsep := ContMDiffMap.eq_zero_of_forall_mem_ker_evalAlgHom_smul_top (I := I) (M := M)
      (𝕜 := ℝ) (n := ∞)
    refine ⟨r, (TauCeti.mem_differentialOperators_iff_forall_apply_mem_smul_top
      (fun x : M ↦ (ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ)) hsep).2
      fun x g hg ↦ ?_⟩
    -- The kernel of evaluation at `x` is the vanishing ideal `I_x`, and `I_x • C^∞(M) = I_x`.
    rw [smul_eq_mul, Ideal.mul_top, TauCeti.ker_evalAlgHom_eq_smoothVanishingIdeal] at hg ⊢
    exact TauCeti.mem_smoothVanishingIdeal_iff.2 (hr x (mem_univ x) g hg)

end LinearMap
