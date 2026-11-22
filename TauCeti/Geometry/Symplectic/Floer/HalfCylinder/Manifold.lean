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
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Instances.AddCircle.PeriodicExtension
import TauCeti.Topology.Separation.InvFunOn

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

Under two further assumptions the loops converge for all `s → ∞`, not only along a sequence: if the
derivative of `e ∘ u` is bounded on the half-cylinder and the `1`-periodic orbits in `K` are
isolated, then the loops `t ↦ u(s, t)` converge to a single orbit
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`). On a
compact boundaryless manifold, for a `C²` Hamiltonian all of whose `1`-periodic orbits are
nondegenerate, the orbits are isolated
(`SmoothTwoForm.IsNondegenerate.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq`),
so the loops of a finite-energy half-cylinder whose derivative through `e` is bounded converge,
`u(s, ·) → x`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`).

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
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), so `x` is a `1`-periodic orbit. In general,
  every periodic solution of `y' = Y(t, y)` in `e(K)` is read through `e` from a periodic orbit
  in `K` (`TauCeti.exists_mem_periodicSolutions_comp_eq`).

**Windows of vanishing energy.** The same argument applies to a sequence of solutions `u k` rather
than to one half-cylinder. If the energies of the `u k` over windows `[σ k, σ k + ℓ] × [0, 1]` tend
to `0`, then so do the squared defect integrals of `e ∘ u k` over them, the windows contain loops
of `e ∘ u k` whose `L²` defects tend to `0`
(`TauCeti.exists_mem_Icc_tendsto_integral_norm_sq_sliceDefect`), and a subsequence of these loops
converges to a `1`-periodic orbit in `K`
(`IsNondegenerate.exists_subseq_mem_periodicSolutions_of_tendsto_setLIntegral_of_isCompact`,
and `IsNondegenerate.exists_subseq_mem_periodicSolutions_of_tendsto_setLIntegral` on a closed
manifold). This is the form that applies to windows in the long necks of a sequence of Floer
cylinders, over which the energy tends to `0`. As at a single end, no bound on the derivatives of
the solutions is needed.

For convergence along the whole end, the loops of `e ∘ u` converge to a single periodic solution
of `y' = Y(t, y)` when the derivative of `e ∘ u` is bounded and these solutions are isolated in
`e(K)`
(`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`). Since `e` restricts to a closed
embedding of `K`, isolation of the orbits in `K` is isolation of their images in `e(K)`.

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

/-- The pushforward `d e (X_{H_t})` of the Hamiltonian vector field on a compact set `K` on which
`e` is injective extends to a continuous field `Y` on `F`, `1`-periodic in time. -/
theorem IsNondegenerate.exists_continuous_periodic_extension (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hHper : Periodic H 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K) :
    ∃ Y : ℝ → F → F, Continuous (uncurry Y) ∧ (∀ v, Periodic (fun t ↦ Y t v) 1) ∧
      ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p) := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb := hK.isClosedEmbedding_domRestrict he.continuous.continuousOn he_inj
  -- The pushforward `(t, p) ↦ d e_p (X_{H_t}(p))` of the Hamiltonian vector field is continuous.
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  -- Extend it from `e(K)` to a continuous periodic field on `F`.
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hXe.comp (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  exact ⟨Y, hYc, hYper, fun t p hp ↦ hYe t ⟨p, hp⟩⟩

/-- The pushforward `d e (X_{H_t})` of the Hamiltonian vector field on a compact set `K` on which
`e` is injective extends to a continuous field `Y` on `F`, `1`-periodic in time, and the defect
`∂_t (e ∘ u) - Y(e ∘ u)` of a finite-energy Floer half-cylinder in `K` is square-integrable. -/
private theorem IsNondegenerate.exists_lintegral_norm_sq_sliceDefect_comp_ne_top
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤) :
    ∃ Y : ℝ → F → F, Continuous (uncurry Y) ∧ (∀ v, Periodic (fun t ↦ Y t v) 1) ∧
      (∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p)) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ := by
  obtain ⟨Y, hYc, hYper, hYe'⟩ := hω.exists_continuous_periodic_extension hH hHper he hK he_inj
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨Y, hYc, hYper, hYe', hω.lintegral_norm_sq_sliceDefect_comp_ne_top
    (measurableSet_Ioi.prod measurableSet_Icc) (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
    (fun z hz ↦ (hu.contMDiffAt (hU.mem_nhds ⟨hz.1, mem_univ _⟩)).mdifferentiableAt one_ne_zero)
    (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc hfloer hE⟩

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
  have hKe : IsCompact (e '' K) := hK.image he.continuous
  obtain ⟨Y, hYc, hYper, hYe, hfin⟩ :=
    hω.exists_lintegral_norm_sq_sliceDefect_comp_ne_top hH hHper he hK he_inj hu huK J hc hJc
      hfloer hE
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)`.
  obtain ⟨y, hyper, hy, φ, hφa, hφ, hconv, hL2⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) hKe
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
  -- The limit lies in the closed set `e(K)`, so it is read through `e` from an orbit in `K`.
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq hK he_inj hde hYe
    hyper hy fun t ↦ hKe.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  -- Inside `K`, convergence is measured by `e`.
  refine ⟨x, hx, hxK, φ, hφa, hφ, hconv, fun t ↦ hK.tendsto_nhds_of_tendsto_comp
    he.continuous.continuousOn he_inj (Eventually.of_forall fun n ↦ huK _ (hφa n) t) (hxK t)
      (hconv.tendsto_at t), hL2.congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  rw [sliceDefect_comp_eq_mvfderiv_sub (he.mdifferentiableAt one_ne_zero)
    ((hu.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds (x := (φ n, t)) ⟨hφa n, mem_univ t⟩))
      |>.mdifferentiableAt one_ne_zero) (hYe t _ (huK _ (hφa n) t))]

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

/-- **Periodic orbits along windows of vanishing energy, in a manifold.** Let `ω` be a
nondegenerate two-form on a manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in time, and let
`u k` be a sequence of maps, `C¹` on the half-cylinders `s > a k`. Let `e : M → F` be a `C¹` map
into a finite-dimensional normed space, injective on a compact set `K` and with injective
differential at the points of `K`. Fix windows `[σ k, σ k + ℓ]` with `ℓ > 0` and `a k < σ k`, and
suppose that for `s` in the window the loops `t ↦ u k (s, t)` are `1`-periodic and lie in `K`,
and that on `[σ k, σ k + ℓ] × [0, 1]` each `u k` solves the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for almost complex structures that are uniformly tame with
respect to `e`, `c ‖d e v‖² ≤ ω(v, J z v)` with one `c > 0` for all `k`. If the energies of the
`u k` over these windows tend to `0`, then there are times `s n` in the windows of a subsequence
`u (ψ n)` such that the loops `t ↦ u (ψ n) (s n, t)` converge to a `1`-periodic orbit `x` of the
Hamiltonian vector field in `K`, pointwise in `M` and uniformly after applying `e`, and the `L²`
norms of their defects `d e (∂_t u - X_{H_t}(u))` tend to `0`.

No bound on the derivatives of the `u k` is assumed. The windows may be taken in the long necks of
a sequence of Floer cylinders, over which the energy tends to `0`. -/
theorem IsNondegenerate.exists_subseq_mem_periodicSolutions_of_tendsto_setLIntegral_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℕ → ℝ × ℝ → M}
    {a σ : ℕ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (haσ : ∀ k, a k < σ k)
    (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u k) (Ioi (a k) ×ˢ univ))
    (hper : ∀ k, ∀ s ∈ Icc (σ k) (σ k + ℓ), Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k, ∀ s ∈ Icc (σ k) (σ k + ℓ), ∀ t, u k (s, t) ∈ K)
    (J : ∀ k z, AlmostComplexStructure (TangentSpace I (u k z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u k z) v‖ ^ 2 ≤ hω.symplecticFormAt (u k z) v (J k z v))
    (hfloer : ∀ k, ∀ z ∈ Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal +
        J k z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag -
          ω.hamiltonianVectorField (H z.2) (u k z)) = 0)
    (hE : Tendsto (fun k ↦ ∫⁻ z in Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) atTop (𝓝 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ s : ℕ → ℝ, (∀ n, s n ∈ Icc (σ (ψ n)) (σ (ψ n) + ℓ)) ∧
        TendstoUniformly (fun n t ↦ e (u (ψ n) (s n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (ψ n) (s n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (ψ n) (s n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u (ψ n)) (s n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (ψ n) (s n, t)))‖ ^ 2) atTop (𝓝 0) := by
  have hKe : IsCompact (e '' K) := hK.image he.continuous
  obtain ⟨Y, hYc, hYper, hYe⟩ := hω.exists_continuous_periodic_extension hH hHper he hK he_inj
  have hU (k : ℕ) : IsOpen (Ioi (a k) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hW (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Icc (σ k) (σ k + ℓ) ×ˢ Icc (0 : ℝ) 1) :
      z ∈ Ioi (a k) ×ˢ (univ : Set ℝ) :=
    ⟨(haσ k).trans_le hz.1.1, mem_univ _⟩
  have hdiff (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ioi (a k) ×ˢ (univ : Set ℝ)) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    ((hu k).contMDiffAt ((hU k).mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hv (k : ℕ) : ContDiffOn ℝ 1 (e ∘ u k) (Ioi (a k) ×ˢ univ) :=
    contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn (hu k))
  -- Over the windows, the squared defects of the loops of `e ∘ u k` are controlled by the
  -- energies, so their integrals tend to `0`, and the windows contain loops of vanishing defect.
  have hD : Tendsto (fun k ↦ ∫⁻ z in Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      ENNReal.ofReal (‖sliceDefect Y (e ∘ u k) z‖ ^ 2)) atTop (𝓝 0) := by
    have hcE := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c⁻¹) hE
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hcE
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcE (fun _ ↦ bot_le)
      fun k ↦ ?_
    exact hω.lintegral_norm_sq_sliceDefect_comp_le (measurableSet_Icc.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero) (fun z hz ↦ hdiff k (hW k hz))
      (fun z hz ↦ hYe _ _ (huK k z.1 hz.1 z.2)) (J k) hc (hJc k) (hfloer k)
  obtain ⟨s, hs, hdef⟩ := exists_mem_Icc_tendsto_integral_norm_sq_sliceDefect hℓ haσ hv hYc hD
  have has (k : ℕ) : a k < s k := (haσ k).trans_le (hs k).1
  -- A subsequence of these loops of `e ∘ u` converges to a periodic solution of `y' = Y(t, y)`.
  obtain ⟨ψ, hψ, y, hyper, hy, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral (u := fun k ↦ e ∘ u k) hv hYc
      hYper has (fun k t ↦ by simp only [comp_apply, hper k _ (hs k) t]) hKe
      (fun k t ↦ mem_image_of_mem e (huK k _ (hs k) t)) hdef
  -- The limit lies in the closed set `e(K)`, so it is read through `e` from an orbit in `K`.
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq hK he_inj hde hYe
    hyper hy fun t ↦ hKe.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ _ (hs (ψ n)) t))
  -- Inside `K`, convergence is measured by `e`.
  refine ⟨x, hx, hxK, ψ, hψ, s ∘ ψ, fun n ↦ hs (ψ n), hconv,
    fun t ↦ hK.tendsto_nhds_of_tendsto_comp he.continuous.continuousOn he_inj
      (Eventually.of_forall fun n ↦ huK _ _ (hs (ψ n)) t) (hxK t) (hconv.tendsto_at t),
    (hdef.comp hψ.tendsto_atTop).congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  simp only [comp_apply]
  rw [sliceDefect_comp_eq_mvfderiv_sub (he.mdifferentiableAt one_ne_zero)
    (hdiff (ψ n) (z := (s (ψ n), t)) ⟨has (ψ n), mem_univ t⟩)
    (hYe t _ (huK _ _ (hs (ψ n)) t))]

/-- **Periodic orbits along windows of vanishing energy, in a closed manifold.** Let `ω` be a
nondegenerate two-form on a compact manifold `M`, `H` a `C¹` Hamiltonian, `1`-periodic in time, and
`e : M → F` a `C¹` injective map with injective differential into a finite-dimensional normed space,
such as a Whitney embedding. Let `u k` be `C¹` on the half-cylinders `s > a k`. Fix windows
`[σ k, σ k + ℓ]` with `ℓ > 0` and `a k < σ k`, on which the loops `t ↦ u k (s, t)` are `1`-periodic
and each `u k` solves the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for almost complex
structures uniformly tame with respect to `e`. If the energies over the windows tend to `0`, then
along a subsequence some loops `t ↦ u (ψ n) (s n, t)` with `s n` in the windows converge to a
`1`-periodic orbit of the Hamiltonian vector field, pointwise in `M` and uniformly after applying
`e`, and the `L²` norms of their defects tend to `0`. -/
theorem IsNondegenerate.exists_subseq_mem_periodicSolutions_of_tendsto_setLIntegral
    [CompactSpace M] (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℕ → ℝ × ℝ → M} {a σ : ℕ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (haσ : ∀ k, a k < σ k)
    (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u k) (Ioi (a k) ×ˢ univ))
    (hper : ∀ k, ∀ s ∈ Icc (σ k) (σ k + ℓ), Periodic (fun t ↦ u k (s, t)) 1)
    (J : ∀ k z, AlmostComplexStructure (TangentSpace I (u k z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u k z) v‖ ^ 2 ≤ hω.symplecticFormAt (u k z) v (J k z v))
    (hfloer : ∀ k, ∀ z ∈ Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal +
        J k z (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag -
          ω.hamiltonianVectorField (H z.2) (u k z)) = 0)
    (hE : Tendsto (fun k ↦ ∫⁻ z in Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) atTop (𝓝 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ s : ℕ → ℝ, (∀ n, s n ∈ Icc (σ (ψ n)) (σ (ψ n) + ℓ)) ∧
        TendstoUniformly (fun n t ↦ e (u (ψ n) (s n, t))) (e ∘ x) atTop ∧
        (∀ t, Tendsto (fun n ↦ u (ψ n) (s n, t)) atTop (𝓝 (x t))) ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖mvfderiv I e (u (ψ n) (s n, t))
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u (ψ n)) (s n, t) stdComplexLineImag -
            ω.hamiltonianVectorField (H t) (u (ψ n) (s n, t)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_subseq_mem_periodicSolutions_of_tendsto_setLIntegral_of_isCompact hH hHper he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hℓ haσ hu hper (fun _ _ _ _ ↦ mem_univ _) J
      hc hJc hfloer hE
  exact ⟨x, hx, h⟩

/-- **Convergence of a finite-energy Floer half-cylinder in a manifold to an isolated orbit.**
Under the hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose
moreover that the derivative of `e ∘ u` is bounded on the half-cylinder, and that the
`1`-periodic orbits of the Hamiltonian vector field in `K` are isolated: for each such orbit `x`,
no other orbit in `K` starts close to `x 0`. Then the loops `t ↦ u(s, t)` converge, as `s → ∞`, to
a single `1`-periodic orbit `x` in `K`, pointwise in `M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
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
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ p in 𝓝 (x 0), ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → y 0 = p → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hKe : IsCompact (e '' K) := hK.image he.continuous
  obtain ⟨Y, hYc, hYper, hYe, hfin⟩ :=
    hω.exists_lintegral_norm_sq_sliceDefect_comp_ne_top hH hHper he hK he_inj hu huK J hc hJc
      hfloer hE
  -- The loops of `e ∘ u` converge to a single periodic solution of `y' = Y(t, y)`.
  obtain ⟨y, hyper, hy, hconv⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
    (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) hKe
    (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin hC
    fun _ ↦ exists_pos_forall_eq_of_forall_dist_lt_of_mem_image hK he_inj hde hYe hiso
  -- The limit lies in the closed set `e(K)`, so it is read through `e` from an orbit in `K`.
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq hK he_inj hde hYe
    hyper hy fun t ↦ hKe.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop a).mono fun s hs ↦ mem_image_of_mem e (huK s hs t))
  -- Inside `K`, convergence is measured by `e`.
  exact ⟨x, hx, hxK, hconv, fun t ↦ hK.tendsto_nhds_of_tendsto_comp he.continuous.continuousOn
    he_inj ((eventually_gt_atTop a).mono fun s hs ↦ huK s hs t) (hxK t) (hconv.tendsto_at t)⟩

/-- **Convergence of a finite-energy Floer half-cylinder to an isolated orbit, from a bound on the
strip.** The conclusion of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` holds
when the derivative of `e ∘ u` is only bounded on the strip `(a, ∞) × [0, 1]`: by `1`-periodicity
of the loops the bound extends to the whole half-cylinder (`TauCeti.norm_fderiv_le_of_periodic`). -/
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
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) :=
  hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH hHper he hK
    he_inj hde hu hper huK J hc hJc hfloer hE
    (fun z hz ↦ norm_fderiv_le_of_periodic
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) hC hz) hiso

/-- **Convergence of a finite-energy Floer half-cylinder in a closed manifold to a nondegenerate
orbit.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, `H` a `C²`
Hamiltonian, `1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with
`1`-periodic loops `t ↦ u(s, t)`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`
on `(a, ∞) × [0, 1]`. Let `e : M → F` be a `C¹` injective map with injective differential into a
finite-dimensional normed space, and suppose that the almost complex structures are uniformly tame
with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. Suppose that the energy of `u` over
`(a, ∞) × [0, 1]` is finite, that the derivative of `e ∘ u` is bounded on the half-cylinder, and
that every `1`-periodic orbit `x` of the Hamiltonian vector field is nondegenerate: `x 0` is a
nondegenerate fixed point of the time-one map. Then the loops `t ↦ u(s, t)` converge, as `s → ∞`,
to a single `1`-periodic orbit `x`, pointwise in `M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
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
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
      (hH.of_le one_le_two) hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper
      (fun _ _ _ ↦ mem_univ _) J hc hJc hfloer hE hC fun x hx _ ↦
        (hω.eventually_forall_mem_periodicSolutions_hamiltonianVectorField_eq hH hx
          (hnd x hx)).mono fun _ hp y hy _ ↦ hp y hy
  exact ⟨x, hx, h⟩

end SmoothTwoForm

end TauCeti
