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

When the derivative of `e ∘ u` is bounded on the half-cylinder and the `1`-periodic orbits of
`X_H` in `K` are isolated at `t = 0`, the connected `ω`-limit set of the loops in `e(K)` reduces to
a single point, so the whole family of loops `t ↦ u(s, t)` converges as `s → ∞` to a single
`1`-periodic orbit `x` in `K`, uniformly after `e` and pointwise in `M`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_eventually_eq`).
When `M` is boundaryless and Hausdorff and `H` is `C²`, nondegeneracy of the `1`-periodic orbits in
`K` as fixed points of the return map `timeDependentFlowOf X_H 0 1` implies their isolation
(`TauCeti.IsNondegenerateFixedPt.eventually_eq_of_mem_periodicSolutions`), giving whole-end
convergence in `K`
(`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`) and on
a closed manifold (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`).

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
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`), and converge as
  `s → ∞` when `e ∘ u` has bounded derivative and the periodic solutions in `e(K)` are isolated
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`).
  The limit lies in the closed set `e(K)`, so `y = e ∘ x` for a continuous periodic loop `x` in
  `K`, and there `y' = d e (X_{H_t}(x))`.
* Since `d e` is injective, `x` is differentiable with velocity `X_{H_t}(x)`
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), so `x` is a `1`-periodic orbit.

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

omit [FiniteDimensional ℝ E] in
/-- A `1`-periodic solution of the extended field `Y` in `e(K)` lifts to a `1`-periodic orbit of
`X_H` in `K`. -/
private theorem exists_mem_periodicSolutions_of_hasDerivAt_comp {K : Set M} (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hemb : IsClosedEmbedding fun p : K ↦ e p)
    {Y : ℝ → F → F}
    (hYe : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    {x' : ℝ → F} (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
    (hx'K : ∀ t, x' t ∈ e '' K) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ e ∘ x = x' := by
  choose x hxK hx using hx'K
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := by
    have h : Continuous fun t ↦ (⟨x t, hxK t⟩ : K) :=
      hemb.isEmbedding.continuous_iff.2 <| hex ▸
        continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt
    exact continuous_subtype_val.comp h
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (hxK _) (hxK _)
    (by rw [hx, hx, hx'per t])⟩, hxK, hex⟩
  refine hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t)) ?_
  rw [hex, ← hYe t _ (hxK t), hx]
  exact hx' t

namespace IsNondegenerate

/-- Extend the pushed-forward Hamiltonian vector field from `e(K)` to a continuous `1`-periodic
field `Y` on `F` with square-integrable slice defect along `e ∘ u`. -/
private theorem exists_periodic_extension_lintegral_sliceDefect_ne_top
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
    IsClosedEmbedding (fun p : K ↦ e p) ∧
      ∃ Y : ℝ → F → F, Continuous (uncurry Y) ∧ (∀ v, Periodic (fun t ↦ Y t v) 1) ∧
        (∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p)) ∧
        ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ := by
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
  exact ⟨hemb, Y, hYc, hYper, hYe', hω.lintegral_norm_sq_sliceDefect_comp_ne_top
    (measurableSet_Ioi.prod measurableSet_Icc) (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
    (fun z hz ↦ hmd z ⟨hz.1, mem_univ _⟩) (fun z hz ↦ hYe' _ _ (huK z.1 hz.1 z.2)) J hc hJc
    hfloer hE⟩

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
theorem exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
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
  obtain ⟨hemb, Y, hYc, hYper, hYe', hfin⟩ :=
    hω.exists_periodic_extension_lintegral_sliceDefect_ne_top hH hHper he hK he_inj hu huK J hc
      hJc hfloer hE
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmd : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)` in `e(K)`.
  obtain ⟨x', hx'per, hx', φ, hφa, hφ, hconv, hL2⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
  have hx'K : ∀ t, x' t ∈ e '' K := fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto
    (hconv.tendsto_at t) (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  obtain ⟨x, hx, hxK, hex⟩ :=
    exists_mem_periodicSolutions_of_hasDerivAt_comp he_inj hde hemb hYe' hx'per hx' hx'K
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
theorem exists_mem_periodicSolutions_tendstoUniformly_of_floer [CompactSpace M]
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

/-- **Whole-end convergence of a finite-energy Floer half-cylinder to an isolated orbit.** Under the
hypotheses of
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, suppose in
addition that the derivative of `e ∘ u` is bounded on `(a, ∞) × ℝ` and that each `1`-periodic orbit
`x` of `X_H` in `K` is isolated at `t = 0` among `1`-periodic orbits in `K`. Then as `s → ∞` the
loops `t ↦ u(s, t)` converge to a single `1`-periodic orbit `x` in `K`, uniformly after applying `e`
and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_eventually_eq
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∀ᶠ p in 𝓝 (x 0), ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → y 0 = p → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨hemb, Y, hYc, hYper, hYe', hfin⟩ :=
    hω.exists_periodic_extension_lintegral_sliceDefect_ne_top hH hHper he hK he_inj hu huK J hc
      hJc hfloer hE
  -- Periodic solutions of `Y` in `e(K)` lift to `K`, so isolation at `0` in `K` gives uniform
  -- isolation in `e(K)`.
  have hiso' (x' : ℝ → F) (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
      (hx'K : ∀ t, x' t ∈ e '' K) :
      ∃ ε > 0, ∀ y' : ℝ → F, Periodic y' 1 → (∀ t, HasDerivAt y' (Y t (y' t)) t) →
        (∀ t, y' t ∈ e '' K) → (∀ t, dist (y' t) (x' t) < ε) → y' = x' := by
    obtain ⟨x, hx, hxK, hex⟩ :=
      exists_mem_periodicSolutions_of_hasDerivAt_comp he_inj hde hemb hYe' hx'per hx' hx'K
    have hU := (continuous_subtype_val.tendsto (⟨x 0, hxK 0⟩ : K)).eventually (hiso x hx hxK)
    rw [hemb.isEmbedding.nhds_eq_comap, eventually_comap] at hU
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hU
    refine ⟨ε, hε, fun y' hy'per hy' hy'K hdist ↦ ?_⟩
    obtain ⟨y, hy, hyK, hey⟩ :=
      exists_mem_periodicSolutions_of_hasDerivAt_comp he_inj hde hemb hYe' hy'per hy' hy'K
    have hyx : y = x := hball
      (by simpa only [comp_apply, ← congrFun hex 0, ← congrFun hey 0] using hdist 0)
      ⟨y 0, hyK 0⟩ rfl y hy hyK rfl
    rw [← hey, ← hex, hyx]
  obtain ⟨x', hx'per, hx', hconv⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
    (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
    (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin hC hiso'
  have hx'K : ∀ t, x' t ∈ e '' K := fun t ↦ (hK.image he.continuous).isClosed.mem_of_tendsto
    (hconv.tendsto_at t) ((eventually_gt_atTop a).mono fun s hs ↦ mem_image_of_mem e (huK s hs t))
  obtain ⟨x, hx, hxK, hex⟩ :=
    exists_mem_periodicSolutions_of_hasDerivAt_comp he_inj hde hemb hYe' hx'per hx' hx'K
  refine ⟨x, hx, hxK, hex ▸ hconv, fun t ↦ ?_⟩
  -- Beyond `a` the curve `s ↦ u(s, t)` stays in `K`, where `e` is an embedding.
  let g : ℝ → K := fun s ↦ if hs : a < s then ⟨u (s, t), huK s hs t⟩ else ⟨x t, hxK t⟩
  have heg : (fun s ↦ e (g s)) =ᶠ[atTop] fun s ↦ e (u (s, t)) :=
    (eventually_gt_atTop a).mono fun s hs ↦ by simp [g, hs]
  have hpt : Tendsto (fun s ↦ e (u (s, t))) atTop (𝓝 (e (x t))) := by
    simpa only [comp_apply, ← congrFun hex t] using hconv.tendsto_at t
  have hg : Tendsto g atTop (𝓝 ⟨x t, hxK t⟩) :=
    hemb.isEmbedding.tendsto_nhds_iff.2 (hpt.congr' heg.symm)
  exact ((continuous_subtype_val.tendsto _).comp hg).congr'
    ((eventually_gt_atTop a).mono fun s hs ↦ by simp [g, hs])

/-- **Whole-end convergence of a finite-energy Floer half-cylinder to a nondegenerate orbit.** Let
`ω` be a nondegenerate two-form on a boundaryless Hausdorff manifold `M`, `H` a `C²` Hamiltonian,
`1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops in
a compact set `K`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on
`(a, ∞) × [0, 1]`. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space, injective
on `K` and with injective differential on `K`, such that `e ∘ u` has bounded derivative on
`(a, ∞) × ℝ` and `J` is uniformly tame with respect to `e`. If `u` has finite energy over
`(a, ∞) × [0, 1]` and every `1`-periodic orbit of `X_H` in `K` is a nondegenerate fixed point of
the time-one map `timeDependentFlowOf X_H 0 1` at `t = 0`, then as `s → ∞` the loops `t ↦ u(s, t)`
converge to a `1`-periodic orbit `x` in `K`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (H p.1) p.2⟩ : TangentBundle I M)) :=
    hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num))
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_eventually_eq
    (hH.of_le one_le_two) hHper he hK he_inj hde hu hper huK hC J hc hJc hfloer hE
    fun x hx hxK ↦ ?_
  have hnd₀ : IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 (0 + 1)) (x 0) := by
    simpa only [zero_add] using hnd x hx hxK
  exact (hnd₀.eventually_eq_of_mem_periodicSolutions hX (mem_periodicSolutions.1 hx).1).mono
    fun p hp y hy _ hpy ↦ hp y hy hpy

/-- **Whole-end convergence of a finite-energy Floer half-cylinder in a closed manifold.** Under the
hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer`,
suppose that `M` is boundaryless and Hausdorff, `H` is `C²`, `e ∘ u` has bounded derivative on
`(a, ∞) × ℝ`, and every `1`-periodic orbit of `X_H` is a nondegenerate fixed point of the time-one
map `timeDependentFlowOf X_H 0 1` at `t = 0`. Then as `s → ∞` the loops `t ↦ u(s, t)` converge to a
`1`-periodic orbit `x`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M} {a C : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1)
        (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  obtain ⟨x, hx, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH hHper he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) hC J hc hJc
      hfloer hE fun x hx _ ↦ hnd x hx
  exact ⟨x, hx, h⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
