/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Manifold.ExtChartAt
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
* **Quadratic derivative bound through a local Euclidean embedding.** Over a compact parameter
  window `C × D × K`, there exist an open neighbourhood `W_emb ⊇ K` and a smooth Euclidean
  embedding `emb : W_emb → ℝ^N` with extension `eM : M → ℝ^N` satisfying
  `‖d (eM ∘ u)‖² ≤ A_e ρ + B_e`
  (`TauCeti.SmoothTwoForm.`
  `IsNondegenerate.exists_opens_smoothEmbedding_norm_fderiv_sq_le`).
* **Lipschitz bounds where the energy density is bounded.** On a convex set where the density is at
  most `A`, the map `e ∘ u` is Lipschitz with constant `2 (√(A / c) + B)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.lipschitzOnWith_comp_of_floerEnergyDensity_le`).
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

open Bundle Filter Function Set Topology
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

/-- **Where the energy density is bounded, solutions are Lipschitz through `e`.** Let `u` solve
the Floer equation `(du - X_K)^{0,1} = 0` on a convex set `s ⊆ ℝ × ℝ`, for structures `J` uniformly
tame with respect to `e : M → F`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and with the pushforwards
`d e (X_{K_s})`, `d e (X_{K_t})` along `u` at most `B`. If the Floer energy density of `u` is at
most `A` on `s`, then `e ∘ u` is Lipschitz on `s` with constant `2 (√(A / c) + B)`. -/
theorem IsNondegenerate.lipschitzOnWith_comp_of_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    {s : Set (ℝ × ℝ)} (hs : Convex ℝ s) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    {c A B : ℝ} (hc : 0 < c) (he : ∀ z ∈ s, MDifferentiableAt I 𝓘(ℝ, F) e (u z))
    (hu : ∀ z ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hJc : ∀ z ∈ s, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hBs : ∀ z ∈ s, ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Ks z) (u z))‖ ≤ B)
    (hBt : ∀ z ∈ s, ‖mvfderiv I e (u z) (ω.hamiltonianVectorField (Kt z) (u z))‖ ≤ B)
    (hfloer : ∀ z ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap)
    (hρ : ∀ z ∈ s, ω.floerEnergyDensity Ks Kt u z ≤ A) :
    LipschitzOnWith (2 * (√(A / c) + B)).toNNReal (e ∘ u) s := by
  refine hs.lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · exact mdifferentiableAt_iff_differentiableAt.1 ((he z hz).comp z (hu z hz))
  · rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact (hω.norm_fderiv_comp_le_of_floerEnergyDensity_le hc (he z hz) (hu z hz) (hJc z hz)
      (hBs z hz) (hBt z hz) (hfloer z hz) (hρ z hz)).trans (Real.le_coe_toNNReal _)

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
  have : Nonempty M := ⟨u 0 0⟩
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
      (Metric.closedBall 0 (R n)) :=
    hω.lipschitzOnWith_comp_of_floerEnergyDensity_le (convex_closedBall 0 (R n)) (J n) hc
      (fun z hz ↦ he _ (huK n hz)) (hu n) (hJc n) (hBs n) (hBt n) (hfloer n) (hρ n)
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
  have : Nonempty M := ⟨p₀⟩
  obtain ⟨v, hv, hvK, hev, hpt⟩ := hK.exists_tendsto_of_tendsto_comp (Ω := univ) hec he_inj hxK
    g.continuous.continuousOn fun z _ ↦
      ((tendstoLocallyUniformlyOn_univ.2 hg).tendsto_at (mem_univ z)).congr'
        ((hxu z).mono fun n hn ↦ by simp only [comp_apply, hn])
  refine ⟨φ, hφ, v, continuousOn_univ.1 hv, fun z ↦ hvK (mem_univ z), ?_,
    fun z ↦ (hpt z (mem_univ z)).congr' (hxu z).symm⟩
  convert hg using 1
  exact funext fun z ↦ hev (mem_univ z)

section SmoothEmbedding

variable {P : Type*} [TopologicalSpace P] [FiniteDimensional ℝ E]

/-- Local embedded derivative bound on a chart neighbourhood with compact coordinate bound `B_α`,
under continuity of the Floer data and pointwise differentiability of `u`. -/
private theorem IsNondegenerate.exists_chart_embedding_bound [I.Boundaryless] [T2Space M]
    (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M}
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hXs : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hXt : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Kt q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x))
    {N : ℕ} {W_emb : TopologicalSpace.Opens M} {eM : M → EuclideanSpace ℝ (Fin N)}
    (heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb)
    (α : M) {B_α : Set E} (hB_comp : IsCompact B_α) (hB_tgt : B_α ⊆ (extChartAt I α).target)
    (hB_emb : (extChartAt I α).symm '' B_α ⊆ (W_emb : Set M))
    (hB_W : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' B_α)) ⊆ W) :
    ∃ A_α > 0, ∃ B_α_c ≥ 0,
      ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
        p ∈ C → z ∈ D → u z ∈ K →
        u z ∈ (extChartAt I α).source → extChartAt I α (u z) ∈ B_α →
        MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
        ‖fderiv ℝ (eM ∘ u) z‖ ^ 2 ≤ A_α * ω.floerEnergyDensity (Ks p) (Kt p) u z + B_α_c := by
  let Kα : Set E := B_α ∩ (extChartAt I α).symm ⁻¹' K
  have hKα_comp : IsCompact Kα := by
    have hcl : IsClosed Kα :=
      ((continuousOn_extChartAt_symm α).mono hB_tgt).preimage_isClosed_of_isClosed
        hB_comp.isClosed hK.isClosed
    exact hB_comp.of_isClosed_subset hcl inter_subset_left
  have hKα_tgt : Kα ⊆ (extChartAt I α).target := inter_subset_left.trans hB_tgt
  have hKα_W : C ×ˢ (D ×ˢ ((extChartAt I α).symm '' Kα)) ⊆ W :=
    (prod_mono_right (prod_mono_right (image_mono inter_subset_left))).trans hB_W
  have hKα_tame : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
      (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames (J p z ((extChartAt I α).symm y)) :=
    fun p hp z hz _ hy ↦ hJt p hp z hz _ hy.2
  set Oα := (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (W_emb : Set M)
  have hOα : IsOpen Oα := (continuousOn_extChartAt_symm α).isOpen_inter_preimage
    (isOpen_extChartAt_target α) W_emb.isOpen
  have hKαO : Kα ⊆ Oα := fun y hy ↦ ⟨hKα_tgt hy, hB_emb ⟨y, hy.1, rfl⟩⟩
  have heM_cd : ContDiffOn ℝ (⊤ : ℕ∞) (eM ∘ (extChartAt I α).symm) Oα :=
    contMDiffOn_iff_contDiffOn.1 <|
      heM_cmd.comp ((contMDiffOn_extChartAt_symm α).mono inter_subset_left) fun _ hy ↦ hy.2
  obtain ⟨Me, hMe⟩ := hKα_comp.exists_bound_of_continuousOn
    ((heM_cd.continuousOn_fderiv_of_isOpen hOα (by simp)).mono hKαO)
  set M_e := max Me 0
  have hWα_sub : C ×ˢ (D ×ˢ Kα) ⊆
      {q : P × ((ℝ × ℝ) × E) | q.2.2 ∈ (extChartAt I α).target ∧
        (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} :=
    fun q hq ↦ ⟨hKα_tgt hq.2.2, hKα_W ⟨hq.1, hq.2.1, ⟨q.2.2, hq.2.2, rfl⟩⟩⟩
  obtain ⟨A_c, hAc, B_c, hBc, _, _, _, _, hcbd⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le α hC hD hKα_comp
      hKα_tgt
      ((Floer.continuousOn_almostComplexInChartAt α hJ).mono hWα_sub)
      ((ω.continuousOn_hamiltonianVectorFieldInChartAt α hXs).mono hWα_sub)
      ((ω.continuousOn_hamiltonianVectorFieldInChartAt α hXt).mono hWα_sub)
      hKα_tame
  refine ⟨M_e ^ 2 * A_c + 1, by positivity, M_e ^ 2 * B_c, by positivity,
    fun p u z hp hz huzK hus huB hdiff_u hfl ↦ ?_⟩
  have huzKα : extChartAt I α (u z) ∈ Kα :=
    ⟨huB, by rw [mem_preimage, (extChartAt I α).left_inv hus]; exact huzK⟩
  have hcbd1 := (hcbd hp hz hus huzKα hdiff_u hfl).1
  have hev : eM ∘ u =ᶠ[𝓝 z] (eM ∘ (extChartAt I α).symm) ∘ (extChartAt I α ∘ u) := by
    filter_upwards [hdiff_u.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source α).mem_nhds hus)] with y hy
    simp only [Function.comp_apply, (extChartAt I α).left_inv hy]
  have hd1 : DifferentiableAt ℝ (eM ∘ (extChartAt I α).symm) (extChartAt I α (u z)) :=
    (heM_cd.differentiableOn (by simp) _ (hKαO huzKα)).differentiableAt
      (hOα.mem_nhds (hKαO huzKα))
  have hd2 : DifferentiableAt ℝ (extChartAt I α ∘ u) z :=
    ((((contMDiffOn_extChartAt (n := 1)).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (by rw [← extChartAt_source I]; exact (isOpen_extChartAt_source α).mem_nhds hus)).comp
        z hdiff_u).differentiableAt
  have hnorm : ‖fderiv ℝ (eM ∘ u) z‖ ≤ M_e * ‖fderiv ℝ (extChartAt I α ∘ u) z‖ := by
    rw [hev.fderiv_eq, fderiv_comp z hd1 hd2]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((hMe _ huzKα).trans (le_max_left _ _)) (norm_nonneg _))
  have he_nn : 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    floerEnergyDensity_nonneg hω (hJt p hp z hz (u z) huzK) hfl
  nlinarith [sq_nonneg M_e, norm_nonneg (fderiv ℝ (eM ∘ u) z),
    norm_nonneg (fderiv ℝ (extChartAt I α ∘ u) z)]

/-- **Smooth Euclidean embedding and global energy-to-derivative estimate.** For a compact subset
`K ⊆ M` and a compact parameter window `C × D × K ⊆ W` with jointly continuous `J`, `X_{K_s}`,
`X_{K_t}` on the open set `W`, there exist an open neighbourhood `W_emb ⊇ K`, a smooth embedding
`emb : W_emb → ℝ^N` with total extension `eM : M → ℝ^N`, and constants `A_e > 0`, `B_e ≥ 0` such
that every map `u` differentiable at `z ∈ D` with `u z ∈ K` solving the Floer equation for `p ∈ C`
at `z` satisfies `‖d(eM ∘ u)_z‖² ≤ A_e e(u)(z) + B_e`. -/
theorem IsNondegenerate.exists_opens_smoothEmbedding_norm_fderiv_sq_le [I.Boundaryless] [T2Space M]
    (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hXs : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hXt : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (Kt q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ (W_emb : TopologicalSpace.Opens M) (N : ℕ)
      (emb : SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) W_emb
        (EuclideanSpace ℝ (Fin N)))
      (eM : M → EuclideanSpace ℝ (Fin N)),
      K ⊆ (W_emb : Set M) ∧
      (∀ x (hx : x ∈ (W_emb : Set M)), eM x = emb ⟨x, hx⟩) ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb ∧
      ∃ A_e > 0, ∃ B_e ≥ 0,
        ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
          p ∈ C → z ∈ D → u z ∈ K → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
          IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
            (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap →
          ‖fderiv ℝ (eM ∘ u) z‖ ^ 2 ≤ A_e * ω.floerEnergyDensity (Ks p) (Kt p) u z + B_e := by
  classical
  obtain ⟨W_emb, hKW, -, N, ⟨emb⟩⟩ := hK.exists_opens_nonempty_smoothEmbedding_euclidean (I := I)
  let eM : M → EuclideanSpace ℝ (Fin N) :=
    fun x ↦ if hx : x ∈ (W_emb : Set M) then emb ⟨x, hx⟩ else 0
  have heM_eq (x : M) (hx : x ∈ (W_emb : Set M)) : eM x = emb ⟨x, hx⟩ := by
    simp only [eM, hx, ↓reduceDIte]
  have heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb := by
    intro x hx
    have hsub : (fun y : W_emb ↦ eM y) = emb := funext fun y ↦ heM_eq y.val y.property
    exact (contMDiffAt_subtype_iff (U := W_emb) (x := ⟨x, hx⟩) |>.1
      (hsub ▸ emb.contMDiff.contMDiffAt)).contMDiffWithinAt
  have hW_swap : IsOpen ((fun q : (P × (ℝ × ℝ)) × M ↦ (q.1.1, (q.1.2, q.2))) ⁻¹' W) :=
    hW.preimage ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨U₁, U₂, -, hU₂, hCDU₁, hKU₂, hprod⟩ :=
    generalized_tube_lemma (hC.prod hD) hK hW_swap fun ⟨⟨p, z⟩, x⟩ ⟨⟨hp, hz⟩, hx⟩ ↦
      hCDKW ⟨hp, hz, hx⟩
  let : LocallyCompactSpace H := I.isClosedEmbedding.locallyCompactSpace
  obtain ⟨n, -, α, u, b, hcov, hsK_cov⟩ :=
    exists_finite_precompact_chart_cover_of_isOpen_cover (I := I) hK
      (V := fun _ : Unit ↦ U₂ ∩ W_emb) (fun _ ↦ hU₂.inter W_emb.isOpen)
      fun x hx ↦ mem_iUnion.2 ⟨(), hKU₂ hx, hKW hx⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, 1, one_pos, 0, le_rfl,
      fun _ _ _ _ _ huzK _ _ ↦ ?_⟩
    obtain ⟨i, -⟩ := mem_iUnion.1 (hsK_cov huzK)
    exact (hn.false i).elim
  have hchart : ∀ i : Fin n,
      ∃ A_i > 0, ∃ B_i ≥ 0,
        ∀ ⦃p : P⦄ ⦃u_sol : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄,
          p ∈ C → z ∈ D → u_sol z ∈ K →
          u_sol z ∈ (extChartAt I (α i)).source → extChartAt I (α i) (u_sol z) ∈ b i →
          MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u_sol z →
          IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u_sol z))
            (ω.perturbedMFDeriv (Ks p) (Kt p) u_sol z).toLinearMap →
          ‖fderiv ℝ (eM ∘ u_sol) z‖ ^ 2 ≤
            A_i * ω.floerEnergyDensity (Ks p) (Kt p) u_sol z + B_i := by
    intro i
    have hi := hcov i
    refine hω.exists_chart_embedding_bound hJ hXs hXt hC hD hK hJt heM_cmd (α i)
      hi.2.2.2.2.1 hi.2.2.2.2.2.1 ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (hi.2.2.2.2.2.2.1 hy).2
    · rintro ⟨p, z, _⟩ ⟨hp, hz, y, hy, rfl⟩
      exact @hprod ((p, z), (extChartAt I (α i)).symm y)
        ⟨hCDU₁ ⟨hp, hz⟩, (hi.2.2.2.2.2.2.1 hy).1⟩
  choose A_i hAi B_i hBi hbd_i using hchart
  set A_e := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty A_i
  set B_e := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty B_i
  have hAe_pos : 0 < A_e := by
    obtain ⟨i⟩ := hn
    exact (hAi i).trans_le (Finset.le_sup' A_i (Finset.mem_univ i))
  have hBe_nn : 0 ≤ B_e := by
    obtain ⟨i⟩ := hn
    exact (hBi i).trans (Finset.le_sup' B_i (Finset.mem_univ i))
  refine ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, A_e, hAe_pos, B_e, hBe_nn,
    fun p u_sol z hp hz huzK hdiff_u hfl ↦ ?_⟩
  obtain ⟨i, huzi⟩ := mem_iUnion.1 (hsK_cov huzK)
  have h1 := hbd_i i hp hz huzK ((hcov i).2.2.2.1 huzi)
    ((hcov i).2.2.2.2.2.2.2 (mem_image_of_mem _ huzi)) hdiff_u hfl
  have he_nn : 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u_sol z :=
    floerEnergyDensity_nonneg hω (hJt p hp z hz (u_sol z) huzK) hfl
  have hA_le : A_i i ≤ A_e := Finset.le_sup' A_i (Finset.mem_univ i)
  have hB_le : B_i i ≤ B_e := Finset.le_sup' B_i (Finset.mem_univ i)
  nlinarith

end SmoothEmbedding

end TauCeti.SmoothTwoForm
