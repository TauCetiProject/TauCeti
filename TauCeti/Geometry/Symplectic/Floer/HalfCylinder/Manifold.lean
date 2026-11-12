/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Algebra.Monoid
import TauCeti.Analysis.ODE.PeriodicOrbitLimit
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Topology.Instances.AddCircle.PeriodicExtension

/-!
# Periodic orbits at the ends of finite-energy Floer half-cylinders in a closed manifold

Let `ω` be a nondegenerate two-form on a compact manifold `M` without boundary, such as a closed
symplectic manifold, `H : ℝ → M → ℝ` a `C¹` Hamiltonian, `1`-periodic in time, and `u` a `C¹`
solution of the Floer equation

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

on the half-cylinder `s > a`, with `1`-periodic loops `t ↦ u(s, t)`, for the cylindrical
perturbation `K = H_t dt` and almost complex structures `J z` on the tangent spaces `T_{u z} M`.
This file shows that if `u` has finite energy, there are `s_n → ∞` such that the loops
`t ↦ u(s_n, t)` converge uniformly to a `1`-periodic orbit `x` of the Hamiltonian vector field
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer`).
This is the first step of Floer breaking at an end of a Floer cylinder or a pair of pants in a
closed manifold; `TauCeti.Geometry.Symplectic.Floer.HalfCylinder` proves it for a symplectic vector
space.

Measuring the convergence needs a metric on `M`. It is measured through a `C¹` injective map
`e : M → F` with injective differential into a finite-dimensional normed space; such a map exists
on a compact Hausdorff manifold by Mathlib's `exists_embedding_euclidean_of_compact`. Since `M` is
compact, `e` is a closed embedding, so uniform convergence of the loops `e ∘ u(s_n, ·)` is uniform
convergence in `M`, and it gives pointwise convergence `u(s_n, t) → x(t)` in `M`. Uniform tameness
is also measured through `e`: `c ‖d e v‖² ≤ ω(v, J z v)` for a constant `c > 0`.

The proof transports the problem to `F`, where the vector-space theory applies.

* The pushforward `d e (X_{H_t})` of the Hamiltonian vector field is a continuous periodic field
  on the image `e(M)`, and extends to a continuous periodic field `Y` on all of `F` by the Tietze
  extension theorem (`Topology.IsClosedEmbedding.exists_continuous_periodic_extension`).
* The defect `∂_t (e ∘ u) - Y(e ∘ u)` of the loops of `e ∘ u` is `d e (∂_t u - X_{H_t}(u))`. By the
  Floer equation, the energy density is `ω(η, J η)` for `η = ∂_t u - X_{H_t}(u)`, so the squared
  norm of the defect is at most the energy density divided by `c`, and has finite integral.
* Loops with square-integrable defect in the compact set `e(M)` accumulate at a periodic solution
  `y` of `y' = Y(t, y)`
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`).
  The limit lies in the closed set `e(M)`, so `y = e ∘ x` for a continuous periodic loop `x` in
  `M`, and there `y' = d e (X_{H_t}(x))`.
* Since `d e` is injective, `x` is differentiable with velocity `X_{H_t}(x)`
  (`ContMDiffAt.hasMFDerivAt_of_hasDerivAt_comp`), so `x` is a `1`-periodic orbit.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped Manifold ENNReal

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {e : M → F}

omit [FiniteDimensional ℝ F] in
/-- The pushforward `(t, p) ↦ d e_p (X_{H_t}(p))` of the Hamiltonian vector field of a `C¹`
family of Hamiltonians along a `C¹` map is continuous. -/
private theorem IsNondegenerate.continuous_mvfderiv_hamiltonianVectorField
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    Continuous fun q : ℝ × M ↦
      mvfderiv I e q.2 (ω.hamiltonianVectorField (H q.1) q.2) := by
  have hX := (hω.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
    (by simpa using hH)).continuous
  exact continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).continuous.comp
    ((he.continuous_tangentMap le_rfl).comp hX))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For a solution of the Floer equation `∂_s u + J η = 0` with `η = ∂_t u - X_{H_t}(u)`, the
energy density at `z` is `ω(η, J η)`. -/
private theorem IsNondegenerate.floerEnergyDensity_eq_symplecticFormAt (hω : ω.IsNondegenerate)
    {u : ℝ × ℝ → M} {z : ℝ × ℝ} {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      hω.symplecticFormAt (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z))
        (J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
          ω.hamiltonianVectorField (H z.2) (u z))) := by
  set η := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)
  have hs : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = -J η :=
    eq_neg_of_add_eq_zero_left hfloer
  have hρ : ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      hω.symplecticFormAt (u z) (-J η) η := by
    rw [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineImag,
      perturbedMFDeriv_apply_stdComplexLineReal, hs, hamiltonianVectorField_const, Pi.zero_apply,
      sub_zero, IsNondegenerate.symplecticFormAt_apply]
  rw [hρ, ← (hω.symplecticFormAt (u z)).neg_eq (J η)]
  simp

variable [I.Boundaryless] [CompactSpace M]

/-- **Periodic orbits at the end of a finite-energy Floer half-cylinder in a closed manifold.** Let
`ω` be a nondegenerate two-form on a compact manifold `M` without boundary, `H` a `C¹` Hamiltonian,
`1`-periodic in time, and let `u` be `C¹` on the half-cylinder `s > a`, with `1`-periodic loops
`t ↦ u(s, t)`, solving the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on
`(a, ∞) × [0, 1]`. Let `e : M → F` be a `C¹` injective map with injective differential into a
finite-dimensional normed space, and suppose that the almost complex structures are uniformly
tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over
`(a, ∞) × [0, 1]` is finite, then there are `s_n → ∞`, with `s_n > a`, such that the loops
`t ↦ u(s_n, t)` converge to a `1`-periodic orbit `x` of the Hamiltonian vector field, pointwise in
`M` and uniformly after applying `e`. -/
theorem IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_of_floer
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
        ∀ t, Tendsto (fun n ↦ u (φ n, t)) atTop (𝓝 (x t)) := by
  have hemb : IsClosedEmbedding e := he.continuous.isClosedEmbedding he_inj
  -- Extend the pushforward of the Hamiltonian vector field to a continuous periodic field on `F`.
  obtain ⟨Y, hYc, hYper, hYe⟩ := hemb.exists_continuous_periodic_extension
    (f := fun t p ↦ mvfderiv I e p (ω.hamiltonianVectorField (H t) p))
    (T := 1) (hω.continuous_mvfderiv_hamiltonianVectorField hH he) fun p t ↦
      congrArg (fun h ↦ mvfderiv I e p (ω.hamiltonianVectorField h p)) (hHper t)
  have hU : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmd : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := fun z hz ↦
    (hu.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero
  -- The defect of the loops of `e ∘ u` from `Y` is the image of the defect of `u` under `d e`.
  have hdef : ∀ z ∈ Ioi a ×ˢ (univ : Set ℝ), TauCeti.sliceDefect Y (e ∘ u) z =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) := fun z hz ↦ by
    -- The chain rule for `e ∘ u`, read as a map between vector spaces.
    have hd : fderiv ℝ (e ∘ u) z stdComplexLineImag =
        mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
      refine Eq.trans ?_ (mvfderiv_comp_apply z (he.mdifferentiableAt one_ne_zero) (hmd z hz) _)
      rw [mvfderiv_eq_fderiv]
      rfl
    rw [TauCeti.sliceDefect_def, ← stdComplexLineImag_eq, hd, comp_apply, hYe, map_sub]
  have hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (‖TauCeti.sliceDefect Y (e ∘ u) z‖ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := c⁻¹)) hE) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Icc) fun z hz ↦ ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hdef z ⟨hz.1, mem_univ _⟩, hω.floerEnergyDensity_eq_symplecticFormAt (hfloer z hz),
      le_inv_mul_iff₀ hc]
    exact hJc z hz _
  -- The loops of `e ∘ u` accumulate at a periodic solution of `y' = Y(t, y)`.
  obtain ⟨x', hx'per, hx', φ, hφa, hφ, hconv, -⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
      (contMDiffOn_iff_contDiffOn.1 (he.comp_contMDiffOn hu))
      (fun s hs t ↦ by simp only [comp_apply, hper s hs t]) (isCompact_range he.continuous)
      (fun _ _ _ ↦ mem_range_self _) hYc hYper hfin
  -- The limit lies in the closed image of `e`.
  have hmem : ∀ t, ∃ p, e p = x' t := fun t ↦ hemb.isClosed_range.mem_of_tendsto
    (hconv.tendsto_at t) (Eventually.of_forall fun _ ↦ mem_range_self _)
  choose x hx using hmem
  have hex : e ∘ x = x' := funext hx
  have hxc : Continuous x := hemb.isEmbedding.continuous_iff.2 <| hex ▸
    continuous_iff_continuousAt.2 fun t ↦ (hx' t).continuousAt
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (by rw [hx, hx, hx'per t])⟩, φ,
    hφa, hφ, hex ▸ hconv,
    fun t ↦ hemb.isEmbedding.tendsto_nhds_iff.2 ?_⟩
  · refine ContMDiffAt.hasMFDerivAt_of_hasDerivAt_comp he.contMDiffAt (hde _) hxc.continuousAt ?_
    rw [hex, ← hYe, hx]
    exact hx' t
  · simpa only [comp_def, hx] using hconv.tendsto_at t

end TauCeti.SmoothTwoForm
