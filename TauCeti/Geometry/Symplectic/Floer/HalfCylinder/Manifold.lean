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
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Connected.TotallyDisconnected
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Instances.AddCircle.PeriodicExtension
import TauCeti.Topology.OmegaLimit

/-!
# Periodic orbits at the ends of finite-energy Floer half-cylinders in a manifold

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a symplectic manifold,
`H : ℝ → M → ℝ` a `C¹` Hamiltonian, `1`-periodic in time, and `u` a `C¹` solution of the Floer
equation

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set `K ⊆ M`, for
the cylindrical perturbation `K = H_t dt` and almost complex structures `J z` on the tangent spaces
`T_{u z} M`. This file shows:

* **Accumulation along a sequence.** If `u` has finite energy on `(a, ∞) × [0, 1]`, there are
  `s_n → ∞` such that the loops `t ↦ u(s_n, t)` converge uniformly (as measured through an
  immersion `e : M → F` injective on `K`) to a `1`-periodic orbit `x` of `X_{H_t}` in `K`, along
  which the `L²` norms of the defects `d e (∂_t u - X_{H_t}(u))` tend to `0`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, and
  `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer` on a compact manifold).
  When some slice `u(s₀, ·)` (`s₀ > a`) is null-homotopic on `AddCircle 1`, the sequential limit
  orbit is contractible
  (`IsNondegenerate.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact`
  and `IsNondegenerate.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer`).
* **Convergence along the whole end.** When `e ∘ u` has bounded derivative on `(a, ∞) × ℝ` and the
  `1`-periodic orbits (or, when a slice of `u` is null-homotopic, only the contractible
  `1`-periodic orbits) in `K` are isolated in the uniform distance induced by `e`, the loops
  `t ↦ u(s, t)` converge uniformly as `s → ∞` to a single orbit
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact`
  and `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact`).
  For a jointly `C²` Hamiltonian on a Hausdorff boundaryless manifold, nondegeneracy of the
  time-one map isolates its `1`-periodic orbits
  (`TauCeti.exists_pos_forall_eq_of_isNondegenerateFixedPt`), giving whole-end convergence on both
  the full sector (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`
  and its `_of_isCompact` version) and the contractible sector
  (`IsNondegenerate.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer` and
  its `_of_isCompact` version).

Measuring the convergence needs a metric near `K`. It is measured through a `C¹` map `e : M → F`
into a finite-dimensional normed space, injective on `K` and with injective differential at the
points of `K`; on a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`. Since `K` is compact, `e` restricts to a closed embedding
of `K`, so uniform convergence of the loops `e ∘ u(s, ·)` is uniform convergence in `K`, and it
gives pointwise convergence `u(s, t) → x(t)` in `M`. Uniform tameness and the defects are also
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
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`), and when `e ∘ u` has
  bounded derivative their ω-limit set in the compact Arzelà–Ascoli space of `1`-periodic
  `C`-Lipschitz loops in `e(K)` consists of periodic solutions
  (`TauCeti.periodic_and_hasDerivAt_of_mapClusterPt`).
* Since `d e` is injective, each limit `y = e ∘ x` lifts to a `1`-periodic orbit `x` in `K`
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), preserving contractibility by
  `TauCeti.mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp`; isolation of those
  orbits makes the ω-limit set discrete, hence a singleton.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, American Mathematical
  Society, 2012, on asymptotic convergence of Floer cylinders.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped Manifold ENNReal UniformConvergence

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

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

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
  -- The pushforward `(t, p) ↦ d e_p (X_{H_t}(p))` of the Hamiltonian vector field is continuous.
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  -- Extend it from `e(K)` to a continuous periodic field on `F`.
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hXe.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  have hYe' : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) :=
    fun t p hp ↦ hYe t ⟨p, hp⟩
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
  have hmem : ∀ t, ∃ p ∈ K, e p = x' t := fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto
    (hconv.tendsto_at t) (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  choose x hxK hx using hmem
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := by
    have h : Continuous fun t ↦ (⟨x t, hxK t⟩ : K) :=
      hemb.isEmbedding.continuous_iff.2 <| hex ▸
        continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt
    exact continuous_subtype_val.comp h
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (hxK _) (hxK _)
    (by rw [hx, hx, hx'per t])⟩, hxK, φ, hφa, hφ, hex ▸ hconv, fun t ↦ ?_,
    hL2.congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  · refine hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t)) ?_
    rw [hex, ← hYe' t _ (hxK t), hx]
    exact hx' t
  · -- Inside `K`, convergence is measured by `e`.
    have h : Tendsto (fun n ↦ (⟨u (φ n, t), huK _ (hφa n) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) :=
      hemb.isEmbedding.tendsto_nhds_iff.2 <| by
        simpa only [comp_def, hx] using hconv.tendsto_at t
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

namespace IsNondegenerate

/-- **Contractible periodic orbits at the end of a finite-energy Floer half-cylinder.** Under the
hypotheses of `exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, if some slice
`u(s₀, ·)` (`s₀ > a`) is null-homotopic as a map `AddCircle 1 → M`, then the sequential limit orbit
`x` is contractible (`x ∈ contractiblePeriodicSolutions _ 1`). -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hx, hxK, φ, hφa, hφ, hconv, hpt, hL2⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact hH hHper he hK he_inj hde
      hu hper huK J hc hJc hfloer hE
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have hxc : x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1 :=
    (mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp hK he.continuous.continuousOn
      he_inj one_pos hx hxK
      (Eventually.of_forall fun n ↦ hu.continuousOn.comp_continuous
        (continuous_const.prodMk continuous_id) fun t ↦ ⟨hφa n, mem_univ t⟩)
      (Eventually.of_forall fun n ↦ hper (φ n) (hφa n))
      (Eventually.of_forall fun n ↦ huK (φ n) (hφa n)) hconv).2 <|
      Eventually.of_forall fun n ↦ (exists_nullhomotopic_slice_iff_of_isPreconnected I
        isPreconnected_Ioi hu.continuousOn one_pos hper hs₀ (hφa n)).1 hnull₀
  exact ⟨x, hxc, hxK, φ, hφa, hφ, hconv, hpt, hL2⟩

/-- **Contractible periodic orbits at the end of a finite-energy Floer half-cylinder on a closed
manifold.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact` to `[CompactSpace
M]`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (φ n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (φ n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact hH hHper he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) hnull J hc hJc
      hfloer hE
  exact ⟨x, hx, h⟩

/-! ### Convergence along the whole half-cylinder -/

/-- Shared ω-limit convergence engine on `(a, ∞)`: given a property `P` of periodic curves in `K`
that passes to uniform limits along nontrivial filters, if the loops of `u` satisfy `P` for
`s ≥ a + 1`, have square-integrable defect for any continuous periodic extension of `d e (X_H)`,
bounded derivative of `e ∘ u`, and isolated `1`-periodic orbits among those satisfying `P`, then
the loops converge as `s → ∞` to a single `1`-periodic orbit satisfying `P`. -/
private theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hfin : ∀ Y : ℝ → F → F,
      (∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p)) →
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    {P : (ℝ → M) → Prop}
    (hPlim : ∀ {l : Filter ℝ} [NeBot l] {x : ℝ → M},
      x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1 → (∀ t, x t ∈ K) →
      (∀ᶠ s in l, a + 1 ≤ s) →
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) l → P x)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) → P x →
      ∃ ε > 0, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → P y → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧ P x ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hXe.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  have hYe' : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) :=
    fun t p hp ↦ hYe t ⟨p, hp⟩
  have hfinY := hfin Y hYe'
  have heu : ContDiffOn ℝ 1 (e ∘ u) (Ioi a ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu)
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (a + 1, 0) ⟨lt_add_one a, trivial⟩)
  have hL : LipschitzOnWith C.toNNReal (e ∘ u) (Ioi a ×ˢ univ) :=
    ((convex_Ioi a).prod convex_univ).lipschitzOnWith_of_nnNorm_fderiv_le
      (fun z hz ↦ (heu.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz))
      fun z hz ↦ (Real.le_toNNReal_iff_coe_le hC0).2 (hC z hz)
  set ℓ : ℝ → ℝ →ᵤ F := fun s ↦ UniformFun.ofFun fun t ↦ (e ∘ u) (s, t)
  set S : Set (ℝ →ᵤ F) := {f | Periodic (UniformFun.toFun f) 1 ∧
    (∀ t, UniformFun.toFun f t ∈ e '' K) ∧ LipschitzWith C.toNNReal (UniformFun.toFun f)}
  have hScpt : IsCompact S :=
    isCompact_setOf_periodic_lipschitzWith (hK.image he.continuous) C.toNNReal
  have hmaps : MapsTo ℓ (Ici (a + 1)) S := fun s hs ↦ by
    have has : a < s := (lt_add_one a).trans_le hs
    have hlip : LipschitzWith C.toNNReal (UniformFun.toFun (ℓ s)) := by
      have h := hL.comp (LipschitzWith.prodMk_left s).lipschitzOnWith
        fun t (_ : t ∈ univ) ↦ ⟨has, trivial⟩
      rwa [lipschitzOnWith_univ, mul_one] at h
    exact ⟨fun t ↦ by simp only [ℓ, UniformFun.toFun_ofFun, comp_apply, hper s has t],
      fun t ↦ mem_image_of_mem e (huK s has t), hlip⟩
  have hcont : ContinuousOn ℓ (Ici (a + 1)) := by
    refine LipschitzOnWith.continuousOn (K := C.toNNReal) fun s hs s' hs' ↦
      UniformFun.edist_le.2 fun t ↦ ?_
    have hLs : LipschitzOnWith C.toNNReal (fun s ↦ (e ∘ u) (s, t)) (Ioi a) := by
      simpa [Function.comp_def] using
        hL.comp (LipschitzWith.prodMk_right t).lipschitzOnWith fun s hs ↦ ⟨hs, trivial⟩
    exact hLs ((lt_add_one a).trans_le hs) ((lt_add_one a).trans_le hs')
  let X := fun t ↦ ω.hamiltonianVectorField (H t)
  set O : Set (ℝ →ᵤ F) := {f | ∃ x ∈ periodicSolutions X 1, (∀ t, x t ∈ K) ∧ P x ∧
    e ∘ x = UniformFun.toFun f}
  have hsub : {f | MapClusterPt f atTop ℓ} ⊆ O := by
    intro f hf
    have hfS : f ∈ S := by
      have h := (setOf_mapClusterPt_atTop_eq_iInter ℓ (a + 1)).subset hf
      exact closure_minimal hmaps.image_subset hScpt.isClosed
        (mem_iInter.1 h ⟨a + 1, mem_Ici.2 le_rfl⟩)
    choose γ hγK heγ' using hfS.2.1
    have heγ : e ∘ γ = UniformFun.toFun f := funext heγ'
    obtain ⟨hfper, hf'⟩ := periodic_and_hasDerivAt_of_mapClusterPt heu
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfinY hC hf
    have hγc : Continuous γ := by
      have h : Continuous fun t ↦ (⟨γ t, hγK t⟩ : K) :=
        hemb.isEmbedding.continuous_iff.2 <| heγ ▸
          continuous_iff_continuousAt.2 fun t ↦ (hf' t).continuousAt
      exact continuous_subtype_val.comp h
    have hγsol : γ ∈ periodicSolutions X 1 := mem_periodicSolutions.2
      ⟨fun t ↦ by
        refine hγc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hγK t)) ?_
        rw [heγ, ← hYe' t _ (hγK t), heγ' t]
        exact hf' t,
      fun t ↦ he_inj (hγK _) (hγK _) (by rw [heγ', heγ', hfper t])⟩
    let l : Filter ℝ := comap ℓ (𝓝 f) ⊓ atTop
    have : NeBot l := (map_neBot_iff ℓ).1 (by rwa [Filter.push_pull'])
    have hlim_l : Tendsto ℓ l (𝓝 f) := tendsto_comap.mono_left inf_le_left
    have hconv_l : TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ γ) l := by
      rw [heγ]
      exact UniformFun.tendsto_iff_tendstoUniformly.1 hlim_l
    exact ⟨γ, hγsol, hγK, hPlim hγsol hγK ((eventually_ge_atTop (a + 1)).filter_mono inf_le_right)
      hconv_l, heγ⟩
  have hdisc : IsDiscrete O := by
    refine isDiscrete_iff_forall_mem_exists_isOpen.2 ?_
    rintro f ⟨x, hx, hxK, hPx, hex⟩
    obtain ⟨ε, hε, hxε⟩ := hiso x hx hxK hPx
    refine ⟨Metric.eball f (ENNReal.ofReal ε), Metric.isOpen_eball, Subset.antisymm ?_ ?_⟩
    · rintro g ⟨hgf, y, hy, hyK, hPy, hey⟩
      have hyx : y = x := hxε y hy hyK hPy fun t ↦ by
        have hdist := edist_lt_ofReal.1 ((UniformFun.edist_le.1 le_rfl t).trans_lt hgf)
        rwa [← congrFun hey t, ← congrFun hex t] at hdist
      exact UniformFun.toFun.injective (hey.symm.trans (hyx ▸ hex))
    · rintro g rfl
      exact ⟨Metric.mem_eball_self (ENNReal.ofReal_pos.2 hε), x, hx, hxK, hPx, hex⟩
  obtain ⟨f, ⟨x, hx, hxK, hPx, hex⟩, hlim⟩ :=
    exists_tendsto_atTop_of_setOf_mapClusterPt_subset_of_isTotallyDisconnected hScpt hcont hmaps
      hdisc.isTotallyDisconnected hsub
  have hconv : TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop := by
    rw [hex]
    exact UniformFun.tendsto_iff_tendstoUniformly.1 hlim
  refine ⟨x, hx, hxK, hPx, hconv, fun t ↦ ?_⟩
  have hKconv : Tendsto (fun s ↦ (⟨u (max s (a + 1), t),
      huK _ ((lt_add_one a).trans_le (le_max_right _ _)) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) :=
    hemb.isEmbedding.tendsto_nhds_iff.2 <| by
      have hmax : Tendsto (fun s ↦ max s (a + 1)) atTop atTop :=
        tendsto_atTop_mono (fun s ↦ le_max_left s (a + 1)) tendsto_id
      simpa only [comp_def] using (hconv.tendsto_at t).comp hmax
  exact ((continuous_subtype_val.tendsto _).comp hKconv).congr'
    ((eventually_ge_atTop (a + 1)).mono fun s hs ↦ by simp only [comp_apply, max_eq_left hs])

/-- **Convergence of a finite-energy Floer half-cylinder to an isolated periodic orbit.** Under the
hypotheses of `exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose
moreover that `e ∘ u` has bounded derivative on `(a, ∞) × ℝ` and that the `1`-periodic orbits of
`X_{H_t}` in `K` are isolated in the uniform distance induced by `e`. Then the loops `t ↦ u(s, t)`
converge as `s → ∞` to a single `1`-periodic orbit `x` in `K`, pointwise in `M` and uniformly
after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
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
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmd : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  obtain ⟨x, hx, hxK, -, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly hH hHper he hK
      he_inj hde hu hper huK
      (fun Y hYe' ↦ hω.lintegral_norm_sq_sliceDefect_comp_ne_top
        (measurableSet_Ioi.prod measurableSet_Icc) (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
        (fun z hz ↦ hmd z ⟨hz.1, mem_univ _⟩) (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc
        hfloer hE)
      hC (fun _ _ _ _ ↦ trivial)
      fun x hx hxK _ ↦ by
        obtain ⟨ε, hε, h⟩ := hiso x hx hxK
        exact ⟨ε, hε, fun y hy hyK _ hyx ↦ h y hy hyK hyx⟩
  exact ⟨x, hx, hxK, hconv, hpt⟩

/-- **Convergence of a contractible Floer half-cylinder to an isolated contractible orbit.** Under
the hypotheses of `exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose
that `e ∘ u` has bounded derivative on `(a, ∞) × ℝ`, that at least one slice `u(s₀, ·)` (`s₀ > a`)
is null-homotopic as a map `AddCircle (1 : ℝ) → M`, and that the *contractible* `1`-periodic orbits
of `X_{H_t}` in `K` are isolated in the uniform distance induced by `e`. Then the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single contractible `1`-periodic orbit `x` in `K`.
Noncontractible orbits in `K` need not be isolated. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hiso : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmd : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have huP (s : ℝ) (hs : a + 1 ≤ s) :
      ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s, t) :=
    (exists_nullhomotopic_slice_iff_of_isPreconnected I isPreconnected_Ioi hu.continuousOn one_pos
      hper hs₀ ((lt_add_one a).trans_le hs)).1 hnull₀
  obtain ⟨x, hx, hxK, hPx, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly hH hHper he hK
      he_inj hde hu hper huK
      (fun Y hYe' ↦ hω.lintegral_norm_sq_sliceDefect_comp_ne_top
        (measurableSet_Ioi.prod measurableSet_Icc) (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
        (fun z hz ↦ hmd z ⟨hz.1, mem_univ _⟩) (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc
        hfloer hE)
      hC
      (fun {l} _ {x} hx hxK hsl hconv ↦
        (mem_contractiblePeriodicSolutions.1
          ((mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp hK
            he.continuous.continuousOn he_inj one_pos hx hxK
            (hsl.mono fun s hs ↦ hu.continuousOn.comp_continuous
              (continuous_const.prodMk continuous_id) fun t ↦ ⟨(lt_add_one a).trans_le hs, trivial⟩)
            (hsl.mono fun s hs ↦ hper s ((lt_add_one a).trans_le hs))
            (hsl.mono fun s hs ↦ huK s ((lt_add_one a).trans_le hs)) hconv).2
            (hsl.mono huP))).2)
      fun x hx hxK hPx ↦ by
        obtain ⟨ε, hε, h⟩ := hiso x (mem_contractiblePeriodicSolutions.2 ⟨hx, hPx⟩) hxK
        exact ⟨ε, hε, fun y hy hyK hPy hyx ↦
          h y (mem_contractiblePeriodicSolutions.2 ⟨hy, hPy⟩) hyK hyx⟩
  exact ⟨x, mem_contractiblePeriodicSolutions.2 ⟨hx, hPx⟩, hxK, hconv, hpt⟩

section NondegenerateOrbits

variable [T2Space M] [BoundarylessManifold I M]

/-- **Convergence of a finite-energy Floer half-cylinder to a nondegenerate periodic orbit.** Let
`ω` be a nondegenerate two-form on a Hausdorff boundaryless finite-dimensional manifold `M`, `H` a
jointly `C²` Hamiltonian, `1`-periodic in time, and `u` a finite-energy `C¹` Floer half-cylinder on
`s > a` with `1`-periodic loops in a compact set `K`, measured through a `C¹` map `e : M → F`
injective on `K` with injective differential on `K`. Suppose that `e ∘ u` has bounded derivative on
`(a, ∞) × ℝ` and that every `1`-periodic orbit `x` of `X_{H_t}` in `K` is nondegenerate: `x 0` is
a nondegenerate fixed point of `timeDependentFlowOf X_H 0 1`. Then the loops `t ↦ u(s, t)` converge
as `s → ∞` to a single `1`-periodic orbit `x` in `K`, pointwise in `M` and uniformly after applying
`e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
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
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num))
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hH.of_le (by norm_num)) hHper he hK he_inj hde hu hper huK J hc hJc hfloer hE hC
    fun x hx hxK ↦ ?_
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt (s := 0) hX
    (fun t ↦ by rw [hHper t]) one_ne_zero hK he.continuous.continuousOn he_inj hx hxK
    (by simpa only [zero_add] using hnd x hx hxK)
  exact ⟨ε, hε, fun y hy hyK hyx ↦ h y hy hyK (hyx 0)⟩

/-- **Convergence of a finite-energy Floer half-cylinder on a closed manifold to a nondegenerate
periodic orbit.** The specialization of
`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` to `[CompactSpace
M]`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
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
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH hHper he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) J hc hJc
      hfloer hE hC fun x hx _ ↦ hnd x hx
  exact ⟨x, hx, hconv, hpt⟩

/-- **Convergence of a contractible Floer half-cylinder to a nondegenerate contractible orbit.**
Under the hypotheses of
`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`, suppose that at least
one slice `u(s₀, ·)` (`s₀ > a`) is null-homotopic as a map `AddCircle (1 : ℝ) → M`, and assume
nondegeneracy only for the *contractible* `1`-periodic orbits of `X_{H_t}` in `K`. Then the loops
`t ↦ u(s, t)` converge as `s → ∞` to a single contractible `1`-periodic orbit `x` in `K`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num))
  refine
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
      (hH.of_le (by norm_num)) hHper he hK he_inj hde hu hper huK hnull J hc hJc hfloer hE hC
      fun x hx hxK ↦ ?_
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt (s := 0) hX
    (fun t ↦ by rw [hHper t]) one_ne_zero hK he.continuous.continuousOn he_inj
    (mem_contractiblePeriodicSolutions.1 hx).1 hxK (by simpa only [zero_add] using hnd x hx hxK)
  exact ⟨ε, hε, fun y hy hyK hyx ↦ h y (mem_contractiblePeriodicSolutions.1 hy).1 hyK (hyx 0)⟩

/-- **Convergence of a contractible Floer half-cylinder on a closed manifold to a nondegenerate
contractible orbit.** The specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` to
`[CompactSpace M]`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {C : ℝ} (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, hconv, hpt⟩ :=
    hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH
      hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _)
      hnull J hc hJc hfloer hE hC fun x hx _ ↦ hnd x hx
  exact ⟨x, hx, hconv, hpt⟩

end NondegenerateOrbits

end IsNondegenerate

end SmoothTwoForm

end TauCeti
