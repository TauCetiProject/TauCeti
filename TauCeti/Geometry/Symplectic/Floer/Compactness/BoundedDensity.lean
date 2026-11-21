/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Separation.InvFunOn
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Floer solutions in a manifold with bounded energy density

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a closed symplectic manifold, and
let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` for a perturbation `K = K_s ds + K_t dt`
and almost complex structures `J` on the tangent spaces of `M`. Without a metric on `M`, the size
of the derivative of `u` is measured through a differentiable map `e : M → F` into a normed space,
such as the Whitney embedding of a closed manifold
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`), with `J` uniformly tame with
respect to `e`: `c ‖d e v‖² ≤ ω(v, J v)` for a constant `c > 0`.

* **The energy density bounds the derivative.** If the pushforwards `d e (X_{K_s})` and
  `d e (X_{K_t})` of the Hamiltonian vector fields are at most `B`, then at a solution
  `‖d (e ∘ u)‖ ≤ 2 (√(ρ / c) + B)`, where `ρ = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` is the Floer energy
  density (`TauCeti.SmoothTwoForm.IsNondegenerate.norm_fderiv_comp_le`). Writing
  `a = ∂ₛu - X_{K_s}`, the Floer equation says `∂ₜu - X_{K_t} = J a`, and `ρ = ω(a, J a)` bounds
  both `c ‖d e a‖²` and `c ‖d e (J a)‖² ≤ ω(J a, J J a) = ρ`.
* **Compactness where the energy density is bounded.** A sequence of solutions on an open set
  `Ω` of the domain with values in a compact set `K ⊆ M`, on which `e` is injective, and with
  energy densities bounded on every compact subset of `Ω`, has a subsequence converging locally
  uniformly on `Ω` through `e`, and pointwise in `M`, to a continuous limit with values in `K`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_strictMono_tendstoLocallyUniformlyOn_comp`).
  The derivative bounds make the maps `e ∘ uₙ` equicontinuous, the Arzelà–Ascoli theorem applies
  to them, and since `e` restricts to a closed embedding of `K` their limit is read back in `K`
  (`IsCompact.exists_tendsto_of_tendsto_comp`).
* **Compactness on exhausting discs.** The same holds for solutions defined on closed discs of
  radii `Rₙ → ∞`, with energy densities bounded on these discs by a common constant: a subsequence
  converges locally uniformly on all of `ℝ × ℝ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_strictMono_tendstoLocallyUniformly_comp`). This
  applies to the rescaled solutions at a bubbling point.

These are steps of Gromov–Floer compactness for a manifold target. Away from the bubbling points
the energy densities are locally bounded along a subsequence, so by the second result the solutions
converge there; and the rescaled solutions at a bubbling point converge by the third
(`TauCeti.Geometry.Symplectic.Floer.Rescaling.Limit`). The limits are only shown to be continuous.
Locating the bubbling points, which needs a lower bound on the energy concentrating at each of
them, is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ} {e : M → F}

/-- **The energy density bounds the derivative, measured through `e`.** Let `u` solve the Floer
equation `(du - X_K)^{0,1} = 0` at `z` for a structure `J` on `T_(u z) M` which is uniformly tame
with respect to `e : M → F`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and let the pushforwards
`d e (X_{K_s})` and `d e (X_{K_t})` of the Hamiltonian vector fields at `u z` be at most `B`. Then
`‖d (e ∘ u)(z)‖ ≤ 2 (√(ρ / c) + B)` for the Floer energy density `ρ` of `u` at `z`. -/
theorem IsNondegenerate.norm_fderiv_comp_le (hω : ω.IsNondegenerate)
    {J : AlmostComplexStructure (TangentSpace I (u z))} {c B : ℝ} (hc : 0 < c)
    (he : MDifferentiableAt I 𝓘(ℝ, F) e (u z)) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hJc : ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J v))
    (hBs : ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Ks z) (u z))‖ ≤ B)
    (hBt : ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Kt z) (u z))‖ ≤ B)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    ‖fderiv ℝ (e ∘ u) z‖ ≤ 2 * (√(ω.floerEnergyDensity Ks Kt u z / c) + B) := by
  set σ := hω.symplecticFormAt (u z)
  set a := ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal with ha
  have him : ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag = J a := by
    simpa only [ContinuousLinearMap.coe_coe] using h.apply_stdComplexLineImag
  -- The energy density is `ω(a, J a)`, and it also equals `ω(J a, J (J a))`.
  have hρ : ω.floerEnergyDensity Ks Kt u z = σ a (J a) := by
    rw [floerEnergyDensity_def, him, IsNondegenerate.symplecticFormAt_apply]
  have hρ' : ω.floerEnergyDensity Ks Kt u z = σ (J a) (J (J a)) := by
    rw [hρ, AlmostComplexStructure.apply_apply, ← σ.neg_eq (J a) a]
    simp
  have hroot {b : TangentSpace I (u z)}
      (hb : c * ‖mvfderiv I e (u z) b‖ ^ 2 ≤ ω.floerEnergyDensity Ks Kt u z) :
      ‖mvfderiv I e (u z) b‖ ≤ √(ω.floerEnergyDensity Ks Kt u z / c) := by
    refine (abs_norm (mvfderiv I e (u z) b)).symm.le.trans (Real.abs_le_sqrt ?_)
    rwa [le_div_iff₀ hc, mul_comm]
  have hra := hroot (hρ ▸ hJc a)
  have hrJa := hroot (hρ' ▸ hJc (J a))
  -- The chain rule for `e ∘ u`, with `∂ₛu = a + X_{K_s}` and `∂ₜu = J a + X_{K_t}`.
  have hd (w : ℝ × ℝ) : fderiv ℝ (e ∘ u) z w =
      mvfderiv I e (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z w) :=
    (mvfderiv_eq_fderiv_apply (e ∘ u) z w).symm.trans (mvfderiv_comp_apply z he hu _)
  have hs : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal =
      a + ω.hamiltonianVectorField (Ks z) (u z) := by
    rw [ha, perturbedMFDeriv_apply_stdComplexLineReal, sub_add_cancel]
  have ht : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J a + ω.hamiltonianVectorField (Kt z) (u z) := by
    rw [← him, perturbedMFDeriv_apply_stdComplexLineImag, sub_add_cancel]
  have hs' : ‖fderiv ℝ (e ∘ u) z (1, 0)‖ ≤ √(ω.floerEnergyDensity Ks Kt u z / c) + B := by
    rw [← stdComplexLineReal_eq, hd, hs, map_add]
    exact (norm_add_le _ _).trans (add_le_add hra hBs)
  have ht' : ‖fderiv ℝ (e ∘ u) z (0, 1)‖ ≤ √(ω.floerEnergyDensity Ks Kt u z / c) + B := by
    rw [← stdComplexLineImag_eq, hd, ht, map_add]
    exact (norm_add_le _ _).trans (add_le_add hrJa hBt)
  calc ‖fderiv ℝ (e ∘ u) z‖ ≤ ‖fderiv ℝ (e ∘ u) z (1, 0)‖ + ‖fderiv ℝ (e ∘ u) z (0, 1)‖ :=
        (fderiv ℝ (e ∘ u) z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one
    _ ≤ _ := by linarith

/-- **A bound on the energy density bounds the derivative, measured through `e`.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.norm_fderiv_comp_le`, if the Floer energy
density of `u` at `z` is at most `A`, then `‖d (e ∘ u)(z)‖ ≤ 2 (√(A / c) + B)`. -/
theorem IsNondegenerate.norm_fderiv_comp_le_of_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    {J : AlmostComplexStructure (TangentSpace I (u z))} {c A B : ℝ} (hc : 0 < c)
    (he : MDifferentiableAt I 𝓘(ℝ, F) e (u z)) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hJc : ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J v))
    (hBs : ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Ks z) (u z))‖ ≤ B)
    (hBt : ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Kt z) (u z))‖ ≤ B)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap)
    (hA : ω.floerEnergyDensity Ks Kt u z ≤ A) :
    ‖fderiv ℝ (e ∘ u) z‖ ≤ 2 * (√(A / c) + B) :=
  (hω.norm_fderiv_comp_le hc he hu hJc hBs hBt h).trans (by gcongr)

/-- **Floer solutions in a manifold converge where their energy density is bounded.** Let `uₙ`
solve the Floer equation `(du - X_{Kₙ})^{0,1} = 0` on an open set `Ω ⊆ ℝ × ℝ`, for perturbations
`Kₙ = K_{s,n} ds + K_{t,n} dt` and structures `Jₙ`, with values in a compact set `K ⊆ M`. Let
`e : M → F` be a map into a normed space, differentiable at the points of `K` and injective on
`K`, with the structures uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, Jₙ v)` with
`c > 0`, and the pushforwards `d e (X_{K_{s,n}})`, `d e (X_{K_{t,n}})` along the solutions at most
`B`. If the Floer
energy densities of the `uₙ` are uniformly bounded on every compact subset of `Ω`, then a
subsequence converges, locally uniformly on `Ω` after applying `e` and pointwise in `M`, to a map
`v` continuous on `Ω` with values in `K`. -/
theorem IsNondegenerate.exists_strictMono_tendstoLocallyUniformlyOn_comp (hω : ω.IsNondegenerate)
    {K : Set M} (hK : IsCompact K) (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : InjOn e K)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : ℕ → ℝ × ℝ → M} {Ks Kt : ℕ → ℝ × ℝ → M → ℝ}
    (J : ∀ n z, AlmostComplexStructure (TangentSpace I (u n z))) {c B : ℝ} (hc : 0 < c)
    (hu : ∀ n, ∀ z ∈ Ω, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u n) z) (huK : ∀ n, MapsTo (u n) Ω K)
    (hJc : ∀ n, ∀ z ∈ Ω, ∀ v,
      c * ‖mvfderiv I e (u n z) v‖ ^ 2 ≤ hω.symplecticFormAt (u n z) v (J n z v))
    (hBs : ∀ n, ∀ z ∈ Ω,
      ‖mvfderiv I e (u n z) (ω.hamiltonianVectorField (Ks n z) (u n z))‖ ≤ B)
    (hBt : ∀ n, ∀ z ∈ Ω,
      ‖mvfderiv I e (u n z) (ω.hamiltonianVectorField (Kt n z) (u n z))‖ ≤ B)
    (hfloer : ∀ n, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J n z)
      (ω.perturbedMFDeriv (Ks n) (Kt n) (u n) z).toLinearMap)
    (hρ : ∀ C, IsCompact C → C ⊆ Ω →
      ∃ A, ∀ n, ∀ z ∈ C, ω.floerEnergyDensity (Ks n) (Kt n) (u n) z ≤ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ × ℝ → M, ContinuousOn v Ω ∧ MapsTo v Ω K ∧
      TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop Ω ∧
      ∀ z ∈ Ω, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hdiff (n : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : DifferentiableAt ℝ (e ∘ u n) z :=
    mdifferentiableAt_iff_differentiableAt.1
      ((he _ (huK n hz)).comp z (hu n z hz))
  -- The energy density bounds the derivatives of the `e ∘ uₙ` on compact subsets of `Ω`.
  have hbd (C : Set (ℝ × ℝ)) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
      ∃ L, ∀ n, ∀ z ∈ C, ‖fderiv ℝ (e ∘ u n) z‖ ≤ L := by
    obtain ⟨A, hA⟩ := hρ C hC hCΩ
    exact ⟨2 * (√(A / c) + B), fun n z hz ↦ hω.norm_fderiv_comp_le_of_floerEnergyDensity_le hc
      (he _ (huK n (hCΩ hz))) (hu n z (hCΩ hz)) (hJc n z (hCΩ hz)) (hBs n z (hCΩ hz))
      (hBt n z (hCΩ hz)) (hfloer n z (hCΩ hz)) (hA n z hz)⟩
  have hequi : EquicontinuousOn (fun n ↦ e ∘ u n) Ω :=
    equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ
      (fun n z hz ↦ (hdiff n hz).differentiableWithinAt) hbd
  -- Arzelà–Ascoli for the maps `e ∘ uₙ`, with values in the compact set `e(K)`.
  have hec : ContinuousOn e K := fun x hx ↦ (he x hx).continuousAt.continuousWithinAt
  obtain ⟨φ, hφ, G, hGc, hconvG⟩ :=
    TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn hΩ hequi
      fun z hz ↦ ⟨e '' K, hK.image_of_continuousOn hec, fun n ↦ mem_image_of_mem e (huK n hz)⟩
  -- The limit is read back in `K` through `e`.
  obtain ⟨v, hv, hvK, hev, hpt⟩ := hK.exists_tendsto_of_tendsto_comp hec he_inj
    (fun n ↦ huK (φ n)) hGc fun z hz ↦ hconvG.tendsto_at hz
  exact ⟨φ, hφ, v, hv, hvK, hconvG.congr_right hev.symm, hpt⟩

/-- **Floer solutions in a manifold with bounded energy density on exhausting discs converge.**
Let `uₙ` solve the Floer equation `(du - X_{Kₙ})^{0,1} = 0` on the closed discs
`closedBall 0 (Rₙ)` of `ℝ × ℝ`, where `Rₙ → ∞`, with values there in a compact set `K ⊆ M`
and Floer energy density at most `A`. Let `e : M → F` be a map into a normed space,
differentiable at the points of `K` and injective on `K`, with the structures uniformly tame with
respect to `e`,
`c ‖d e v‖² ≤ ω(v, Jₙ v)` with `c > 0`, and the pushforwards `d e (X_{K_{s,n}})`,
`d e (X_{K_{t,n}})` along the solutions at most `B` on these discs. Then a subsequence converges,
locally uniformly on `ℝ × ℝ` after applying `e` and pointwise in `M`, to a continuous map
`v : ℝ × ℝ → M` with values in `K`. -/
theorem IsNondegenerate.exists_strictMono_tendstoLocallyUniformly_comp (hω : ω.IsNondegenerate)
    {K : Set M} (hK : IsCompact K) (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : InjOn e K)
    {u : ℕ → ℝ × ℝ → M} {Ks Kt : ℕ → ℝ × ℝ → M → ℝ}
    (J : ∀ n z, AlmostComplexStructure (TangentSpace I (u n z))) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) {c A B : ℝ} (hc : 0 < c)
    (hu : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u n) z)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall 0 (R n)) K)
    (hJc : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n), ∀ v,
      c * ‖mvfderiv I e (u n z) v‖ ^ 2 ≤ hω.symplecticFormAt (u n z) v (J n z v))
    (hBs : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n),
      ‖mvfderiv I e (u n z) (ω.hamiltonianVectorField (Ks n z) (u n z))‖ ≤ B)
    (hBt : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n),
      ‖mvfderiv I e (u n z) (ω.hamiltonianVectorField (Kt n z) (u n z))‖ ≤ B)
    (hfloer : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J n z)
        (ω.perturbedMFDeriv (Ks n) (Kt n) (u n) z).toLinearMap)
    (hρ : ∀ n, ∀ z ∈ Metric.closedBall 0 (R n),
      ω.floerEnergyDensity (Ks n) (Kt n) (u n) z ≤ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ × ℝ → M, Continuous v ∧ (∀ z, v z ∈ K) ∧
      TendstoLocallyUniformly (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop ∧
      ∀ z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- The energy density bounds the derivatives of the `e ∘ uₙ` on the discs, which are convex, so
  -- these maps are uniformly Lipschitz there.
  have hL (n : ℕ) : LipschitzOnWith (2 * (√(A / c) + B)).toNNReal (e ∘ u n)
      (Metric.closedBall 0 (R n)) := by
    refine (convex_closedBall 0 (R n)).lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ)
      (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · exact mdifferentiableAt_iff_differentiableAt.1
        ((he _ (huK n hz)).comp z (hu n z hz))
    · rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact (hω.norm_fderiv_comp_le_of_floerEnergyDensity_le hc (he _ (huK n hz)) (hu n z hz)
        (hJc n z hz) (hBs n z hz) (hBt n z hz) (hfloer n z hz) (hρ n z hz)).trans
        (Real.le_coe_toNNReal _)
  -- Arzelà–Ascoli along the exhausting discs, for maps with values in the compact set `e(K)`.
  have hec : ContinuousOn e K := fun x hx ↦ (he x hx).continuousAt.continuousWithinAt
  have hKe : IsCompact (e '' K) := hK.image_of_continuousOn hec
  obtain ⟨φ, hφ, g, hg⟩ :=
    TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall hKe hR hL
      fun n z hz ↦ mem_image_of_mem e (huK n hz)
  -- Every point eventually lies in the discs. Off the discs, replace the maps by a point `p₀` of
  -- `K`, so as to read the limit back in `K` through `e`.
  have hin (z : ℝ × ℝ) : ∀ᶠ n in atTop, z ∈ Metric.closedBall 0 (R (φ n)) :=
    ((hR.comp hφ.tendsto_atTop).eventually_ge_atTop ‖z‖).mono fun n hn ↦
      mem_closedBall_zero_iff.2 hn
  obtain ⟨n₀, hn₀⟩ := (hR.eventually_ge_atTop 0).exists
  set p₀ := u n₀ 0
  have hp₀ : p₀ ∈ K := huK n₀ (Metric.mem_closedBall_self hn₀)
  classical
  set x : ℕ → ℝ × ℝ → M := fun n z ↦ if z ∈ Metric.closedBall 0 (R (φ n)) then u (φ n) z else p₀
  have hxK (n : ℕ) : MapsTo (x n) univ K := fun z _ ↦ by
    by_cases hz : z ∈ Metric.closedBall 0 (R (φ n))
    · simpa only [x, ite_eq_left hz] using huK _ hz
    · simpa only [x, ite_eq_right hz] using hp₀
  have hxu (z : ℝ × ℝ) : (fun n ↦ u (φ n) z) =ᶠ[atTop] fun n ↦ x n z :=
    (hin z).mono fun n hn ↦ (ite_eq_left hn).symm
  obtain ⟨v, hv, hvK, hev, hpt⟩ := hK.exists_tendsto_of_tendsto_comp (Ω := univ) hec he_inj hxK
    g.continuous.continuousOn fun z _ ↦
      ((tendstoLocallyUniformlyOn_univ.2 hg).tendsto_at (mem_univ z)).congr'
        ((hxu z).mono fun n hn ↦ by simp only [comp_apply, hn])
  refine ⟨φ, hφ, v, continuousOn_univ.1 hv, fun z ↦ hvK (mem_univ z), ?_,
    fun z ↦ (hpt z (mem_univ z)).congr' (hxu z).symm⟩
  convert hg using 1
  exact funext fun z ↦ hev (mem_univ z)

end TauCeti.SmoothTwoForm
