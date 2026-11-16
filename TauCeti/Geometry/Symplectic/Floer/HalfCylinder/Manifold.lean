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
the cylindrical perturbation `K = H_t dt` and almost complex structures `J z` on the tangent spaces
`T_{u z} M`. This file establishes the manifold counterparts of the vector-space half-cylinder
results in `TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Basic`:

* **Accumulation along a sequence.** If `u` has finite energy on `(a, ∞) × [0, 1]`, there are
  `s_n → ∞` such that the loops `t ↦ u(s_n, t)` converge uniformly (as measured through an
  immersion `e : M → F` injective on `K`) to a `1`-periodic orbit `x` of `X_{H_t}` in `K`, along
  which the `L²` norms of the defects `d e (∂_t u - X_{H_t}(u))` tend to `0`
  (`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, and
  `IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer` on a compact manifold).
  When a slice `u(s₀, ·)` (`s₀ > a`) is null-homotopic on `AddCircle 1`, the limit is contractible
  (`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer`, `_of_isCompact`).
* **Convergence along the whole end.** When `e ∘ u` has bounded derivative on `(a, ∞) × ℝ` and the
  `1`-periodic (or contractible `1`-periodic) orbits in `K` are isolated in `e`, `u(s, ·)` converges
  as `s → ∞` (`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact`). For a
  jointly `C²` Hamiltonian on a Hausdorff boundaryless manifold, nondegeneracy isolates its orbits
  (`TauCeti.exists_pos_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt`), giving whole-end
  convergence (`exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer`,
  `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer`, and `_of_isCompact`).

Measuring the convergence needs a metric near `K`. It is measured through a `C¹` map `e : M → F`
into a finite-dimensional normed space, injective on `K` and with injective differential at the
points of `K`; on a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`. Since `K` is compact, `e` restricts to a closed embedding
of `K`, so uniform convergence of the loops `e ∘ u(s, ·)` is uniform convergence in `K`, and it
gives pointwise convergence `u(s, t) → x(t)` in `M`. Uniform tameness and the defects are also
measured through `e`: `c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0`.

The proof transports the problem to `F`, where the vector-space ODE limit theory in
`TauCeti.Analysis.ODE.PeriodicOrbitLimit` applies.

* The pushforward `d e (X_{H_t})` of the Hamiltonian vector field is a continuous periodic field
  on the image `e(K)`, and extends to a continuous periodic field `Y` on all of `F` by the Tietze
  extension theorem (`Topology.IsClosedEmbedding.exists_continuous_periodic_extension`).
* The defect `∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` is `d e (∂_t u - X_{H_t}(u))`
  (`TauCeti.sliceDefect_comp_eq_mvfderiv_sub`). By the Floer equation, the energy density is
  `ω(η, J η)` for `η = ∂_t u - X_{H_t}(u)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_eq_symplecticFormAt`), so
  the squared norm of the defect is at most the energy density divided by `c`, and has finite
  integral (`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_norm_sq_sliceDefect_comp_le`).
* Loops with square-integrable defect in `e(K)` accumulate at a periodic solution `y` of
  `y' = Y(t, y)` (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`), and
  under a derivative bound converge as `s → ∞` whenever the limit-closed orbit class in `e(K)` is
  isolated (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_forall_tendstoUniformly`,
  generalizing `TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`).
* Since `d e` is injective, each limit `y = e ∘ x` lifts to a `1`-periodic orbit `x` in `K`
  (`ContinuousAt.hasMFDerivAt_of_hasDerivAt_comp`), preserving contractibility by
  `TauCeti.mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, American Mathematical
  Society, 2012, on asymptotic convergence of Floer cylinders.
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

omit [NormedSpace ℝ F] in
/-- On a compact set `K`, a continuous map `e` injective on `K` restricts to a closed embedding. -/
private theorem isClosedEmbedding_subtype (he : Continuous e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) : IsClosedEmbedding fun p : K ↦ e p := by
  have := isCompact_iff_compactSpace.1 hK
  exact (he.comp continuous_subtype_val).isClosedEmbedding fun p q h ↦
    Subtype.ext (he_inj p.2 q.2 h)

variable [FiniteDimensional ℝ F]

/-- Lift a `1`-periodic solution of `y' = Y(t, y)` in `e '' K` to a `1`-periodic orbit in `K`. -/
private theorem exists_mem_periodicSolutions_of_hasDerivAt (he : ContMDiff I 𝓘(ℝ, F) 1 e)
    {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p))
    {Y : ℝ → F → F}
    (hYe' : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    {x' : ℝ → F} (hx'per : Periodic x' 1) (hx' : ∀ t, HasDerivAt x' (Y t (x' t)) t)
    (hx'K : ∀ t, x' t ∈ e '' K) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ e ∘ x = x' := by
  choose x hxK hx using hx'K
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := continuous_subtype_val.comp
    (show Continuous fun t ↦ (⟨x t, hxK t⟩ : K) from
      (isClosedEmbedding_subtype he.continuous hK he_inj).isEmbedding.continuous_iff.2
        (hex ▸ continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt))
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (hxK _) (hxK _)
    (by rw [hx, hx, hx'per t])⟩, hxK, hex⟩
  exact hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t))
    (by rw [hex, ← hYe' t _ (hxK t), hx]; exact hx' t)

variable [FiniteDimensional ℝ E]

/-- Extend `d e (X_{H_t})` on `e '' K` to a continuous `1`-periodic field `Y` on `F`. -/
private theorem IsNondegenerate.exists_periodic_extension_and_lintegral_sliceDefect_ne_top
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) {u : ℝ × ℝ → M} {a : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ)) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
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
  have := isCompact_iff_compactSpace.1 hK
  have hXe : Continuous fun q : ℝ × M ↦ mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) :=
    (he.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
        (by simpa using hH)).continuous
  obtain ⟨Y, hYc, hYper, hYe⟩ := (isClosedEmbedding_subtype he.continuous hK
    he_inj).exists_continuous_periodic_extension
    (f := fun t (p : K) ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p)) (T := 1)
    (hXe.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    fun p t ↦ congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  exact ⟨Y, hYc, hYper, fun t p hp ↦ hYe t ⟨p, hp⟩,
    hω.lintegral_norm_sq_sliceDefect_comp_ne_top (measurableSet_Ioi.prod measurableSet_Icc)
      (fun _ _ ↦ he.mdifferentiableAt one_ne_zero)
      (fun _ hz ↦ (hu.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        ⟨hz.1, mem_univ _⟩)).mdifferentiableAt one_ne_zero)
      (fun z hz ↦ hYe z.2 ⟨_, huK z.1 hz.1 z.2⟩) J hc hJc hfloer hE⟩

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
  have hemb := isClosedEmbedding_subtype he.continuous hK he_inj
  obtain ⟨Y, hYc, hYper, hYe', hfin⟩ :=
    hω.exists_periodic_extension_and_lintegral_sliceDefect_ne_top hH hHper he hK he_inj hu huK J hc
      hJc hfloer hE
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)` in the closed `e(K)`.
  obtain ⟨x', hx'per, hx', φ, hφa, hφ, hconv, hL2⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin
  have hx'K (t : ℝ) : x' t ∈ e '' K := (hK.image he.continuous).isClosed.mem_of_tendsto
    (hconv.tendsto_at t) (Eventually.of_forall fun n ↦ mem_image_of_mem e (huK _ (hφa n) t))
  obtain ⟨x, hx, hxK, hex⟩ :=
    exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe' hx'per hx' hx'K
  refine ⟨x, hx, hxK, φ, hφa, hφ, hex ▸ hconv, fun t ↦ ?_,
    hL2.congr fun n ↦ intervalIntegral.integral_congr fun t _ ↦ ?_⟩
  · exact (continuous_subtype_val.tendsto _).comp
      (show Tendsto (fun n ↦ (⟨u (φ n, t), huK _ (hφa n) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) from
        hemb.isEmbedding.tendsto_nhds_iff.2 <| by
          simpa only [comp_def, ← congrFun hex t] using hconv.tendsto_at t)
  · rw [sliceDefect_comp_eq_mvfderiv_sub (he.mdifferentiableAt one_ne_zero)
      ((hu.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show (φ n, t) ∈ Ioi a ×ˢ univ from ⟨hφa n, mem_univ t⟩))).mdifferentiableAt one_ne_zero)
      (hYe' t _ (huK _ (hφa n) t))]

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

variable {K : Set M} {u : ℝ × ℝ → M} {a c C : ℝ}

/-- **Contractible periodic orbits at the end of a finite-energy Floer half-cylinder.** Under
`exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, if some slice `u(s₀, ·)`
(`s₀ > a`) is null-homotopic on `AddCircle 1`, the sequential limit orbit `x` is contractible. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  obtain ⟨x, hx, hxK, φ, hφa, hφ, hconv, hpt, hL2⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact hH hHper he hK he_inj hde
      hu hper huK J hc hJc hfloer hE
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  refine ⟨x, (mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp hK
    he.continuous.continuousOn he_inj one_pos hx hxK
    (.of_forall fun n ↦ hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      fun t ↦ ⟨hφa n, mem_univ t⟩) (.of_forall fun n ↦ hper (φ n) (hφa n))
    (.of_forall fun n ↦ huK (φ n) (hφa n)) hconv).2 (.of_forall fun n ↦
      (exists_nullhomotopic_slice_iff_of_isPreconnected isPreconnected_Ioi hu.continuousOn one_pos
        hper hs₀ (hφa n)).1 hnull₀), hxK, φ, hφa, hφ, hconv, hpt, hL2⟩

/-- **Contractible periodic orbits at the end of a Floer half-cylinder on a closed manifold.**
Specialization of `exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact`
to `[CompactSpace M]`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
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
            ω.hamiltonianVectorField (H t) (u (φ n, t)))‖ ^ 2) atTop (𝓝 0) :=
  (hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_of_floer_of_isCompact hH hHper he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) hnull J hc hJc
    hfloer hE).imp fun _ ⟨hx, _, h⟩ ↦ ⟨hx, h⟩

/-! ### Convergence along the whole half-cylinder -/

/-- Shared whole-end convergence helper on `(a, ∞)` for an ω-limit-closed isolated predicate `P` on
`1`-periodic orbits in `K`. -/
private theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C) {P : (ℝ → M) → Prop}
    (hPlim : ∀ {l : Filter ℝ} [NeBot l] {x : ℝ → M},
      x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1 → (∀ t, x t ∈ K) →
      (∀ᶠ s in l, a + 1 ≤ s) → TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) l → P x)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) → P x → ∃ ε > 0,
      ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → P y → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧ P x ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hemb := isClosedEmbedding_subtype he.continuous hK he_inj
  obtain ⟨Y, hYc, hYper, hYe', hfin⟩ :=
    hω.exists_periodic_extension_and_lintegral_sliceDefect_ne_top hH hHper he hK he_inj hu huK J hc
      hJc hfloer hE
  obtain ⟨y, -, -, -, ⟨x, hx, hxK, hPx, hex⟩, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_forall_tendstoUniformly
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (hK.image he.continuous)
      (fun s hs t ↦ mem_image_of_mem e (huK s hs t)) hYc hYper hfin hC
      (P := fun y ↦ ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, x t ∈ K) ∧ P x ∧ e ∘ x = y)
      (fun {l} _ {y} hyper hy hyK hsl hconv_l ↦
        let ⟨x, hx, hxK, hex⟩ :=
          exists_mem_periodicSolutions_of_hasDerivAt he hK he_inj hde hYe' hyper hy hyK
        ⟨x, hx, hxK, hPlim hx hxK hsl (hex ▸ hconv_l), hex⟩)
      fun y₁ _ _ _ ⟨x₁, hx₁, hx₁K, hPx₁, hex₁⟩ ↦ by
        obtain ⟨ε, hε, hx₁ε⟩ := hiso x₁ hx₁ hx₁K hPx₁
        refine ⟨ε, hε, fun y₂ _ _ _ ⟨x₂, hx₂, hx₂K, hPx₂, hex₂⟩ hy₂₁ ↦ ?_⟩
        exact hex₂.symm.trans ((hx₁ε x₂ hx₂ hx₂K hPx₂ fun t ↦ by
          simpa only [← congrFun hex₂ t, ← congrFun hex₁ t, comp_apply] using hy₂₁ t) ▸ hex₁)
  have hconv' : TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop := hex ▸ hconv
  refine ⟨x, hx, hxK, hPx, hconv', fun t ↦ ?_⟩
  have hKconv : Tendsto (fun s ↦ (⟨u (max s (a + 1), t),
      huK _ ((lt_add_one a).trans_le (le_max_right _ _)) t⟩ : K)) atTop (𝓝 ⟨x t, hxK t⟩) :=
    hemb.isEmbedding.tendsto_nhds_iff.2 <| by
      simpa only [comp_def] using
        (hconv'.tendsto_at t).comp (tendsto_atTop_mono (fun s ↦ le_max_left s (a + 1)) tendsto_id)
  exact ((continuous_subtype_val.tendsto _).comp hKconv).congr'
    ((eventually_ge_atTop (a + 1)).mono fun s hs ↦ by simp only [comp_apply, max_eq_left hs])

/-- **Convergence of a finite-energy Floer half-cylinder to an isolated periodic orbit.** Under
`exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, if `e ∘ u` has bounded
derivative on `(a, ∞) × ℝ` and the `1`-periodic orbits of `X_{H_t}` in `K` are isolated in `e`,
`u(s, ·)` converges as `s → ∞` to a single orbit, uniformly in `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hiso : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly hH hHper he hK
    he_inj hde hu hper huK J hc hJc hfloer hE hC (P := fun _ ↦ True) (fun _ _ _ _ ↦ trivial)
    fun x hx hxK _ ↦ let ⟨ε, hε, h⟩ := hiso x hx hxK; ⟨ε, hε, fun y hy hyK _ ↦ h y hy hyK⟩).imp
    fun _ ⟨hx, hxK, _, h⟩ ↦ ⟨hx, hxK, h⟩

/-- **Convergence of a contractible Floer half-cylinder to an isolated contractible orbit.** Under
`exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact`, if `e ∘ u` has bounded
derivative on `(a, ∞) × ℝ`, some slice `u(s₀, ·)` (`s₀ > a`) is null-homotopic on `AddCircle 1`,
and contractible `1`-periodic orbits in `K` are isolated in `e`, `u(s, ·)` converges as `s → ∞` to
a single contractible orbit in `K`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hiso : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) → ∃ ε > 0,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
        (∀ t, y t ∈ K) → (∀ t, dist (e (y t)) (e (x t)) < ε) → y = x) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have := I.locallyPathConnectedSpace_of_chartedSpace M
  have := I.semilocallySimplyConnectedSpace M
  obtain ⟨s₀, hs₀, hnull₀⟩ := hnull
  have huP (s : ℝ) (hs : a + 1 ≤ s) := (exists_nullhomotopic_slice_iff_of_isPreconnected
    isPreconnected_Ioi hu.continuousOn one_pos hper hs₀ ((lt_add_one a).trans_le hs)).1 hnull₀
  refine (hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_forall_tendstoUniformly hH hHper
    he hK he_inj hde hu hper huK J hc hJc hfloer hE hC (fun {l} _ {x} hx hxK hsl hconv ↦
      (mem_contractiblePeriodicSolutions.1
        ((mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp hK
          he.continuous.continuousOn he_inj one_pos hx hxK
          (hsl.mono fun s hs ↦ hu.continuousOn.comp_continuous
            (continuous_const.prodMk continuous_id) fun _ ↦ ⟨(lt_add_one a).trans_le hs, trivial⟩)
          (hsl.mono fun s hs ↦ hper s ((lt_add_one a).trans_le hs))
          (hsl.mono fun s hs ↦ huK s ((lt_add_one a).trans_le hs)) hconv).2 (hsl.mono huP))).2)
    fun x hx hxK hPx ↦
      let ⟨ε, hε, h⟩ := hiso x (mem_contractiblePeriodicSolutions.2 ⟨hx, hPx⟩) hxK
      ⟨ε, hε, fun y hy hyK hPy ↦ h y (mem_contractiblePeriodicSolutions.2 ⟨hy, hPy⟩) hyK⟩).imp
    fun _ ⟨hx, hxK, hPx, h⟩ ↦ ⟨mem_contractiblePeriodicSolutions.2 ⟨hx, hPx⟩, hxK, h⟩

section NondegenerateOrbits

variable [T2Space M] [BoundarylessManifold I M]

/-- **Convergence of a finite-energy Floer half-cylinder to a nondegenerate periodic orbit.** On a
Hausdorff boundaryless finite-dimensional manifold `M` with jointly `C²` `1`-periodic `H`, if `u` is
a finite-energy `C¹` Floer half-cylinder in `K` with uniformly tame `J`, bounded `fderiv (e ∘ u)`,
and nondegenerate `1`-periodic orbits in `K`, then `u(s, ·)` converges as `s → ∞` to an orbit in
`K`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num))
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hH.of_le one_le_two) hHper he hK he_inj hde hu hper huK J hc hJc hfloer hE hC fun x hx hxK ↦
    let ⟨ε, hε, h⟩ := exists_pos_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt (s := 0)
      hX hK he.continuous.continuousOn he_inj hx (hxK 0)
      (by simpa only [zero_add] using hnd x hx hxK)
    ⟨ε, hε, fun y hy hyK hyx ↦ h y hy (hyK 0) (hyx 0)⟩

/-- **Convergence of a Floer half-cylinder on a closed manifold to a nondegenerate orbit.**
Specialization of `exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` to
`[CompactSpace M]`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) :=
  (hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH hHper he
    isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) J hc hJc hfloer
    hE hC fun x hx _ ↦ hnd x hx).imp fun _ ⟨hx, _, h⟩ ↦ ⟨hx, h⟩

/-- **Convergence of a contractible Floer half-cylinder to a nondegenerate contractible orbit.**
Under `exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact`, if some slice
`u(s₀, ·)` (`s₀ > a`) is null-homotopic on `AddCircle 1` and contractible `1`-periodic orbits in `K`
are nondegenerate, `u(s, ·)` converges as `s → ∞` to a contractible orbit in `K`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      (∀ t, x t ∈ K) ∧ TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) := by
  have hX := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) (hH.of_le (by norm_num))
  refine hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_isolated_of_isCompact
    (hH.of_le one_le_two) hHper he hK he_inj hde hu hper huK hnull J hc hJc hfloer hE hC
    fun x hx hxK ↦
      let ⟨ε, hε, h⟩ := exists_pos_forall_mem_periodicSolutions_eq_of_isNondegenerateFixedPt
        (s := 0) hX hK he.continuous.continuousOn he_inj (mem_contractiblePeriodicSolutions.1 hx).1
        (hxK 0) (by simpa only [zero_add] using hnd x hx hxK)
      ⟨ε, hε, fun y hy hyK hyx ↦ h y (mem_contractiblePeriodicSolutions.1 hy).1 (hyK 0) (hyx 0)⟩

/-- **Convergence of a contractible Floer half-cylinder on a closed manifold to a nondegenerate
contractible orbit.** Specialization of
`exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact` to
`[CompactSpace M]`. -/
theorem exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer [CompactSpace M]
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry H))
    (hHper : Periodic H 1) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hnull : ∃ s₀ > a, ∃ g : C(AddCircle (1 : ℝ), M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (s₀, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ (e ∘ u) z‖ ≤ C)
    (hnd : ∀ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H t)) 0 1) (x 0)) :
    ∃ x ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1,
      TendstoUniformly (fun s t ↦ e (u (s, t))) (e ∘ x) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (s, t)) atTop (𝓝 (x t)) :=
  (hω.exists_mem_contractiblePeriodicSolutions_tendstoUniformly_atTop_of_floer_of_isCompact hH
    hHper he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu hper (fun _ _ _ ↦ mem_univ _) hnull J
    hc hJc hfloer hE hC fun x hx _ ↦ hnd x hx).imp fun _ ⟨hx, _, h⟩ ↦ ⟨hx, h⟩

end NondegenerateOrbits

end IsNondegenerate

end SmoothTwoForm

end TauCeti
