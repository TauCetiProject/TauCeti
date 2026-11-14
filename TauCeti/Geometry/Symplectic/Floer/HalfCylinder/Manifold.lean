/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Complex.Tietze
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Instances.AddCircle.PeriodicExtension

/-!
# Periodic orbits at the ends of finite-energy Floer half-cylinders in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a symplectic manifold,
`H : ℝ → M → ℝ` a `C¹` Hamiltonian, `1`-periodic in time, and `u` a `C¹` solution of the Floer
equation

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set `K ⊆ M`, for
the cylindrical perturbation `K = H_t dt` and almost complex structures `J z` on the tangent
spaces `T_{u z} M`. This file shows that if `u` has finite energy, there are `s_n → ∞` such that
the loops `t ↦ u(s_n, t)` converge uniformly to a `1`-periodic orbit `x` of the Hamiltonian vector
field in `K`, along which the `L²` norms of the defects `∂_t u - X_{H_t}(u)` tend to `0`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, in the
namespace `TauCeti.SmoothTwoForm`). On a compact manifold `K` can be the whole manifold
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer`).
This is the first step of Floer breaking at an end of a Floer cylinder or a pair of pants in a
closed manifold; `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic` proves it for a symplectic
vector space.

When the derivative of `e ∘ u` is bounded on the strip `(a, ∞) × [0, 1]` and each `1`-periodic
orbit of `H` in `K` is isolated — in particular when `H` is `C²` on a Hausdorff boundaryless
manifold and each orbit in `K` starts at a nondegenerate fixed point of the time-one map
`timeDependentFlowOf X_H 0 1` — the loops `t ↦ u(s, t)` converge along the whole end `s → ∞` to a
single `1`-periodic orbit, uniformly after applying `e` and pointwise in `M`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated`,
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`, and
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`).

Measuring the convergence needs a metric near `K`. It is measured through a `C¹` map `e : M → F`
into a finite-dimensional normed space, injective on `K` and with injective differential at the
points of `K`; on a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`. Since `K` is compact, `e` restricts to a closed embedding
of `K`, so uniform convergence of the loops `e ∘ u(s_n, ·)` is uniform convergence in `K`, and it
gives pointwise convergence `u(s_n, t) → x(t)` in `M`. Uniform tameness and the defects are also
measured through `e`: `c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0`.

The proof transports the problem to `F`, where the vector-space theory applies.

* The pushforward `d e (X_{H_t})` of the Hamiltonian vector field is a continuous periodic field
  on the image `e(K)`, and extends to a continuous periodic field `Y` on all of `F` by the Tietze
  extension theorem (`Topology.IsClosedEmbedding.exists_continuous_periodic_extension`).
* The defect `∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` is `d e (∂_t u - X_{H_t}(u))`
  (`TauCeti.sliceDefect_comp_eq_mvfderiv_sub`). By the Floer equation, the energy density is
  `ω(η, J η)` for `η = ∂_t u - X_{H_t}(u)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_eq_symplecticFormAt`), so
  the squared norm of the defect is at most the energy density divided by `c`, and has finite
  integral (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`).
* Loops with square-integrable defect in the compact set `e(K)` accumulate at a periodic solution
  `y` of `y' = Y(t, y)`
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`).
  The limit lies in the closed set `e(K)`, so `y = e ∘ x` for a continuous periodic loop `x` in
  `K`, and there `y' = d e (X_{H_t}(x))`.
* Since `d e` is injective, `x` is differentiable with velocity `X_{H_t}(x)`
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), so `x` is a `1`-periodic orbit.
* When the derivative of `e ∘ u` is bounded on `(a, ∞) × [0, 1]`, `1`-periodicity bounds it on the
  whole half-cylinder `(a, ∞) × ℝ`, and isolation of the `1`-periodic orbits of `H` in `K` makes
  the `1`-periodic solutions of `Y` in `e(K)` isolated, so `e ∘ u(s, ·)` converges as `s → ∞` by
  `TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped Manifold ENNReal

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F}

/-- Let `e : M → F` be differentiable at `u z`, and let `Y` be a time-dependent field on `F` whose
value at `e (u z)` is the pushforward `d e v` of a tangent vector `v` at `u z`. Then the defect
`∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` at `z` is `d e (∂_t u - v)`. -/
theorem sliceDefect_comp_eq_mvfderiv_sub {u : ℝ × ℝ → M} {z : ℝ × ℝ} {Y : ℝ → F → F}
    {v : TangentSpace I (u z)} (he : MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hY : Y z.2 (e (u z)) = mvfderiv I e (u z) v) :
    sliceDefect Y (e ∘ u) z =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - v) := by
  -- The chain rule for `e ∘ u`, read as a map between vector spaces.
  have hd : fderiv ℝ (e ∘ u) z stdComplexLineImag =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) :=
    (mvfderiv_eq_fderiv_apply (e ∘ u) z stdComplexLineImag).symm.trans
      (mvfderiv_comp_apply z he hu _)
  rw [sliceDefect_def, ← stdComplexLineImag_eq, hd, comp_apply, hY, map_sub]

/-- A derivative bound on the strip `(a, ∞) × [0, 1]` extends to `(a, ∞) × ℝ` when the slices
`t ↦ v(s, t)` are `1`-periodic. -/
private theorem norm_fderiv_le_of_periodic {v : ℝ × ℝ → F} {a C : ℝ}
    (hper : ∀ s, a < s → Periodic (fun t ↦ v (s, t)) 1)
    (hC : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ v z‖ ≤ C) {z : ℝ × ℝ}
    (hz : z ∈ Ioi a ×ˢ (univ : Set ℝ)) : ‖fderiv ℝ v z‖ ≤ C := by
  set n : ℤ := ⌊z.2⌋
  have heq : (fun w : ℝ × ℝ ↦ v (w + (0, -(n : ℝ)))) =ᶠ[𝓝 z] v := by
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hz] with ⟨s, t⟩ hw
    simpa only [Prod.mk_add_mk, add_zero, ← sub_eq_add_neg, mul_one] using
      (hper s hw.1).sub_int_mul_eq n
  rw [← heq.fderiv_eq, fderiv_comp_add_right]
  refine hC _ ⟨by simpa only [Prod.fst_add, add_zero] using hz.1, ?_, ?_⟩ <;>
    simp only [Prod.snd_add] <;> linarith [Int.floor_le z.2, Int.lt_floor_add_one z.2]

namespace SmoothTwoForm

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}

/-- **The energy controls the defect, measured through `e`.** Let `u` solve the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a measurable set `U`, where `e : M → F` and `u` are
differentiable, with almost complex structures satisfying `c ‖d e v‖² ≤ ω(v, J z v)`, and let `Y`
be a time-dependent field on `F` agreeing with the pushforward `d e (X_{H_t})` at the points of
`e ∘ u` over `U`. Then the integral over `U` of the squared defect `‖∂_t (e ∘ u) - Y(e ∘ u)‖²` of
the loops of `e ∘ u` is at most `1 / c` times the energy over `U`. -/
theorem IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → M} {Y : ℝ → F → F}
    (he : ∀ z ∈ U, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hY : ∀ z ∈ U, Y z.2 (e (u z)) = mvfderiv I e (u z) (ω.hamiltonianVectorField (H z.2) (u z)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ∫⁻ z in U, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≤
      ENNReal.ofReal c⁻¹ *
        ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hU fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sliceDefect_comp_eq_mvfderiv_sub (he z hz) (hu z hz) (hY z hz),
    hω.floerEnergyDensity_zero_left_eq_symplecticFormAt (hfloer z hz), le_inv_mul_iff₀ hc]
  exact hJc z hz _

/-- **Finite energy gives a square-integrable defect, measured through `e`.** Under the hypotheses
of `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`, if the energy
over `U` is finite, then so is the integral over `U` of `‖∂_t (e ∘ u) - Y(e ∘ u)‖²`. -/
theorem IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_ne_top (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) {u : ℝ × ℝ → M} {Y : ℝ → F → F}
    (he : ∀ z ∈ U, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hY : ∀ z ∈ U, Y z.2 (e (u z)) = mvfderiv I e (u z) (ω.hamiltonianVectorField (H z.2) (u z)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in U,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∫⁻ z in U, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ :=
  ((hω.lintegral_norm_sq_sliceDefect_comp_le hU he hu hY J hc hJc hfloer).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE.lt_top)).ne

variable [FiniteDimensional ℝ F]

/-- A `1`-periodic solution of `y' = Y(t, y)` in `e(K)` lifts uniquely to a `1`-periodic orbit of
`X_{H_t}` in `K` when `e` embeds `K` with injective differential and `Y` extends `d e (X_{H_t})`. -/
private theorem exists_mem_periodicSolutions_of_periodic_hasDerivAt {K : Set M}
    (he_inj : InjOn e K) (hemb : IsClosedEmbedding fun p : K ↦ e p)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {Y : ℝ → F → F}
    (hYe : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    {x' : ℝ → F} (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
    (hx'K : ∀ t, x' t ∈ e '' K) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ e ∘ x = x' := by
  have hmem : ∀ t, ∃ p ∈ K, e p = x' t := hx'K
  choose x hxK hx using hmem
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := by
    have h : Continuous fun t ↦ (⟨x t, hxK t⟩ : K) :=
      hemb.isEmbedding.continuous_iff.2 <| hex ▸
        continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt
    exact continuous_subtype_val.comp h
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_,
    fun t ↦ he_inj (hxK _) (hxK _) (by rw [hx, hx, hx'per t])⟩, hxK, hex⟩
  refine hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t)) ?_
  rw [hex, ← hYe t _ (hxK t), hx]
  exact hx' t

variable [FiniteDimensional ℝ E]

/-- Extend the pushforward `d e (X_{H_t})` from `e(K)` to a continuous `1`-periodic field on `F`. -/
private theorem IsNondegenerate.exists_continuous_periodic_extension_mvfderiv
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M}
    (hemb : IsClosedEmbedding fun p : K ↦ e p) :
    ∃ Y : ℝ → F → F, Continuous (uncurry Y) ∧ (∀ v, Periodic (fun t ↦ Y t v) 1) ∧
      ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) := by
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hXe.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  exact ⟨Y, hYc, hYper, fun t p hp ↦ hYe t ⟨p, hp⟩⟩

omit [FiniteDimensional ℝ E] in
/-- Isolation of `1`-periodic orbits of `X_{H_t}` in `K` at `t = 0` transfers through the embedding
`e` to uniform isolation of `1`-periodic solutions of `y' = Y(t, y)` in `e(K)`. -/
private theorem exists_pos_forall_eq_of_isolated {K : Set M}
    (he_inj : InjOn e K) (hemb : IsClosedEmbedding fun p : K ↦ e p)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {Y : ℝ → F → F}
    (hYe : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ y in 𝓝 (x 0), ∀ x' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, x' t ∈ K) → x' 0 = y → x' = x)
    {x' : ℝ → F} (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
    (hx'K : ∀ t, x' t ∈ e '' K) :
    ∃ ε > 0, ∀ y' : ℝ → F, Periodic y' 1 → (∀ t, HasDerivAt y' (Y t (y' t)) t) →
      (∀ t, y' t ∈ e '' K) → (∀ t, dist (y' t) (x' t) < ε) → y' = x' := by
  obtain ⟨x, hx, hxK, hex⟩ := exists_mem_periodicSolutions_of_periodic_hasDerivAt he_inj hemb hde
    hYe hx'per hx' hx'K
  have hnhds : ∀ᶠ p : K in 𝓝 ⟨x 0, hxK 0⟩,
      ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → y 0 = p.1 → y = x :=
    (continuous_subtype_val.tendsto ⟨x 0, hxK 0⟩).eventually (hiso x hx hxK)
  rw [hemb.isEmbedding.nhds_eq_comap] at hnhds
  obtain ⟨V, hV, hpV⟩ := mem_comap.1 hnhds
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ε, hε, fun y' hy'per hy' hy'K hy'x' ↦ ?_⟩
  obtain ⟨y, hy, hyK, hey⟩ := exists_mem_periodicSolutions_of_periodic_hasDerivAt he_inj hemb hde
    hYe hy'per hy' hy'K
  have hy0 : e (y 0) ∈ V := hball
    (Metric.mem_ball.2 (by simpa only [← hex, ← hey, comp_apply] using hy'x' 0))
  have hyx : y = x := hpV (a := ⟨y 0, hyK 0⟩) hy0 y hy hyK rfl
  rw [← hex, ← hey, hyx]

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder in a manifold.** Let `ω`
be a nondegenerate two-form on a manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in time, and
let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact
set `K`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]`. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `K` and with
injective differential at the points of `K`, and suppose that the almost complex structures are
uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u`
over `(a, ∞) × [0, 1]` is finite, then there are `s_n → ∞`, with `s_n > a`, such that the loops
`t ↦ u(s_n, t)` converge to a `1`-periodic orbit `x` of the Hamiltonian vector field in `K`,
pointwise in `M` and uniformly after applying `e`, and the `L²` norms of their defects
`d e (∂_t u - X_{H_t}(u))` tend to `0`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  obtain ⟨Y, hYc, hYper, hYe'⟩ :=
    hω.exists_continuous_periodic_extension_mvfderiv hH hHper he hemb
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmd : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ :=
    hω.lintegral_norm_sq_sliceDefect_comp_ne_top (measurableSet_Ioi.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero) (fun z hz ↦ hmd z ⟨hz.1, mem_univ _⟩)
      (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc hfloer hE
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)`.
  obtain ⟨x', hx'per, hx', φ, hφa, hφ, hconv, hL2⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
  -- The limit lies in the closed set `e(K)`.
  obtain ⟨x, hx, hxK, hex⟩ := exists_mem_periodicSolutions_of_periodic_hasDerivAt he_inj hemb hde
    hYe' hx'per hx' fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto (hconv.tendsto_at t)
      (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  refine ⟨x, hx, hxK, φ, hφa, hφ, hex ▸ hconv, fun t ↦ ?_,
    hL2.congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  · -- Inside `K`, convergence is measured by `e`.
    have h : Tendsto (fun n ↦ (⟨u (φ n, t), huK _ (hφa n) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) :=
      hemb.isEmbedding.tendsto_nhds_iff.2 <| by
        simpa only [comp_def, ← hex] using hconv.tendsto_at t
    exact (continuous_subtype_val.tendsto _).comp h
  · rw [sliceDefect_comp_eq_mvfderiv_sub (he.mdifferentiableAt one_ne_zero)
      (hmd (φ n, t) ⟨hφa n, mem_univ t⟩) (hYe' t _ (huK _ (hφa n) t))]

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder in a closed manifold.** Let
`ω` be a nondegenerate two-form on a compact manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in
time, and let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)`,
solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]`. Let
`e : M → F` be a `C¹` injective map with injective differential into a finite-dimensional normed
space, and suppose that the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `(a, ∞) × [0, 1]` is finite,
then there are `s_n → ∞`, with `s_n > a`, such that the loops `t ↦ u(s_n, t)` converge to a
`1`-periodic orbit `x` of the Hamiltonian vector field, pointwise in `M` and uniformly after
applying `e`, and the `L²` norms of their defects `d e (∂_t u - X_{H_t}(u))` tend to `0`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hx, -, h⟩ := hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
    hH hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper
    (fun _ _ _ ↦ mem_univ _) J hc hJc hfloer hE
  exact ⟨x, hx, h⟩

/-- **Convergence of a finite-energy Floer half-cylinder in a manifold to an isolated orbit.**
Under the hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose
moreover that the derivative of `e ∘ u` is bounded on the strip `(a, ∞) × [0, 1]` and that each
`1`-periodic orbit `x` of `H` in `K` is isolated among the `1`-periodic orbits in `K`: for `y`
close enough to `x 0`, `x` is the only `1`-periodic orbit in `K` starting at `y`. Then the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single `1`-periodic orbit `x` in `K`, uniformly after
applying `e` and pointwise in `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ y in 𝓝 (x 0), ∀ x' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, x' t ∈ K) → x' 0 = y → x' = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  obtain ⟨Y, hYc, hYper, hYe'⟩ :=
    hω.exists_continuous_periodic_extension_mvfderiv hH hHper he hemb
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ :=
    hω.lintegral_norm_sq_sliceDefect_comp_ne_top (measurableSet_Ioi.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
      (fun z hz ↦ (hu.contMDiffAt (hU.mem_nhds ⟨hz.1, mem_univ _⟩)).mdifferentiableAt one_ne_zero)
      (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc hfloer hE
  obtain ⟨x', hx'per, hx', hconv⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
    (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
    (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
    (fun z hz ↦ norm_fderiv_le_of_periodic
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) hC hz)
    fun _ hx'per hx' hx'K ↦
      exists_pos_forall_eq_of_isolated he_inj hemb hde hYe' hiso hx'per hx' hx'K
  obtain ⟨x, hx, hxK, hex⟩ := exists_mem_periodicSolutions_of_periodic_hasDerivAt he_inj hemb hde
    hYe' hx'per hx' fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop a).mono fun s hs ↦ mem_image_of_mem e (huK s hs t))
  refine ⟨x, hx, hxK, hex ▸ hconv, fun t ↦ ?_⟩
  -- Truncate to `K` beyond `a` so convergence in `K` can be read through `e`.
  set g : ℝ → K := fun s ↦ if hs : a < s then ⟨u (s, t), huK s hs t⟩ else ⟨x t, hxK t⟩
  have hge : (fun s ↦ e (g s).1) =ᶠ[atTop] fun s ↦ e (u (s, t)) :=
    (eventually_gt_atTop a).mono fun s hs ↦ by simp only [g, hs, ↓reduceDIte]
  have hg : Tendsto g atTop (𝓝 ⟨x t, hxK t⟩) :=
    hemb.isEmbedding.tendsto_nhds_iff.2
      ((hex ▸ hconv.tendsto_at t).congr' hge.symm)
  exact ((continuous_subtype_val.tendsto _).comp hg).congr'
    ((eventually_gt_atTop a).mono fun s hs ↦ by simp only [comp_apply, g, hs, ↓reduceDIte])

/-- **Convergence of a finite-energy Floer half-cylinder in a manifold to a nondegenerate orbit.**
Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `H` a `C²`
Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)` in a compact set `K`, solving the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `(a, ∞) × [0, 1]` with finite energy. Let `e : M → F` be a
`C¹` map into a finite-dimensional normed space, injective on `K` and with injective differential at
the points of `K`, suppose that `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0` and `‖d(e ∘ u)‖ ≤ C` on
`(a, ∞) × [0, 1]`, and suppose that every `1`-periodic orbit `x` of `H` in `K` is nondegenerate:
`x 0` is a nondegenerate fixed point of `timeDependentFlowOf X_H 0 1`. Then the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single `1`-periodic orbit `x` in `K`, uniformly after
applying `e` and pointwise in `M`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
    (hH.of_le one_le_two) hHper he hK he_inj hde hu hper huK J hc hJc hfloer hE hC
    fun x hx hxK ↦ ?_
  have hiso := IsNondegenerateFixedPt.eventually_forall_mem_periodicSolutions_eq (s := 0)
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num)))
    (fun t ↦ by rw [hHper t]) one_ne_zero hx (by simpa only [zero_add] using hnd x hx hxK)
  exact hiso.mono fun y hy x' hx' _ hx'0 ↦ hy x' hx' hx'0

/-- **Convergence of a finite-energy Floer half-cylinder in a closed manifold to a nondegenerate
orbit.** Specialization of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` when `M`
is compact and `K = univ`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
      hH hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper
      (fun _ _ _ ↦ mem_univ _) J hc hJc hfloer hE hC fun x hx _ ↦ hnd x hx
  exact ⟨x, hx, h⟩

end SmoothTwoForm

end TauCeti
