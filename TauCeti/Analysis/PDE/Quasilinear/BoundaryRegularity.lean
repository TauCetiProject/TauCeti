/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.GlobalHolder
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Global
import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.LipschitzDomain.SegmentChain
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder

/-!
# Gradient regularity up to the boundary for quasilinear Dirichlet problems

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set with `C^{1,α}` boundary: near each frontier point, in rigid
coordinates, `Ω` is the region above the graph of a `C¹` function whose derivative is `α`-Hölder.
Consider the quasilinear Dirichlet problem with zero boundary values

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`,

in weak form: `u ∈ H¹₀(Ω)` and `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every
`φ ∈ H¹₀(Ω)`. Suppose that `A(·, s)` is uniformly elliptic with constants `λ, Λ` on `closure Ω`
for every `s`, that `A` is `α`-Hölder in `x` on `closure Ω` uniformly in `s` and Lipschitz in `s`
uniformly in `x`, that `G` is `α`-Hölder on `closure Ω`, and that `f ∈ L^q(Ω)` with `q ≥ 2`. This
file proves that the gradient of every weak solution agrees almost everywhere with a function
that is `β`-Hölder on `closure Ω`, for every `0 < β < 1` with `β ≤ α` and
`β ≤ 1 - (n + 1) / q` (`TauCeti.PDE.exists_holderOnWith_gradient_closure_quasilinear`). These
are the exponents of the global estimate for the linear equation with `α`-Hölder coefficients
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`), so, as in the interior
(`exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq`, in
the `TauCeti.PDE` namespace), the dependence of the coefficients on `u` costs nothing up to the
boundary either. The statement is qualitative: the Hölder constant of `∇u` depends on `u`,
through the Hölder constant of `u` itself. Weak solutions exist, since a `C^{1,α}` boundary is
Lipschitz (`TauCeti.isLipschitzDomain_of_contDiffAt`), so the problem has a weak solution whose
gradient is `β`-Hölder up to the boundary
(`TauCeti.PDE.exists_forall_energyFormH1_quasilinear_eq_and_holderOnWith_gradient_closure`).

## The bootstrap

A weak solution `u` solves the linear equation with the frozen coefficient `a(x) = A(x, u(x))`.

* **De Giorgi.** The frozen coefficient is measurable and uniformly elliptic, so the global
  Hölder estimate (`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_quasilinear`) makes `u`
  agree with a function `v` that is `γ₀`-Hölder on `closure Ω` for some `γ₀ > 0`.
* **Schauder.** Then `x ↦ A(x, v(x))` is `β₁`-Hölder on `closure Ω`, `β₁ = min γ₀ β`
  (`HolderOnWith.comp_of_lipschitzWith_right`), and the global Schauder estimate makes
  `∇u` agree with a bounded function that is `β₁`-Hölder on `closure Ω`. The estimate takes the
  same exponent for the coefficient and the boundary charts, so the charts are first replaced by
  charts with `β₁`-Hölder derivative that agree with them on the cylinders
  (`TauCeti.PDE.forall_graph_holderWith_fderiv_of_le`).
* **Lipschitz.** A continuous function with a bounded continuous weak gradient is `C¹`
  (`TauCeti.HasWeakFDerivOn.hasFDerivAt_of_continuousOn`), and on a bounded Lipschitz domain a
  bounded derivative gives a Lipschitz bound between nearby points
  (`Set.IsLipschitzDomain.exists_dist_le_of_norm_fderiv_le`). So `v` is `β`-Hölder on
  `closure Ω`, and so is the frozen coefficient.
* **Schauder again.** A second application of the global Schauder estimate gives the exponent
  `β`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_gradient_closure_quasilinear`: the gradient of a weak solution
  of the quasilinear Dirichlet problem with zero boundary values on a bounded `C^{1,α}` domain is
  `β`-Hölder up to the boundary.
* `TauCeti.PDE.exists_forall_energyFormH1_quasilinear_eq_and_holderOnWith_gradient_closure`: such
  a weak solution exists.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.29 and 8.33, and the regularity of quasilinear equations in Chapter 13.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

variable {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u : W1p0 volume Ω 2} {lam Lam : ℝ}
  {α : ℝ≥0} {Kx L KG : ℝ≥0} {q : ℝ≥0∞}

/-- The weak formulation against `H¹₀(Ω)` gives the one against test functions, for any
coefficient agreeing almost everywhere with the frozen one. -/
private theorem forall_testFunction_of_forall_w1p0
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : a =ᵐ[volume.restrict Ω] fun x => A x (W1p.value (u : W1p volume Ω 2) x))
    (hu : ∀ φ : W1p0 volume Ω 2,
      energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0 u
          (φ : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x) (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 a 0 0 (u : W1p volume Ω 2) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x := by
  rw [energyFormH1_congr_ae ha .rfl .rfl, hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω) 2 φ] with y hy
    rw [W1p.gradient_ofTestFunctionₗ, hy]
  · refine integral_congr_ae ?_
    filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with y hy
    rw [hy]

/-- **The data in the form of the global Hölder estimates.** For `q > n + 1` there is an exponent
`r` with `n + 1 < r < q`, so that `f ∈ Lʳ(Ω)`; the bounded datum `-G` lies in `L^{n + 3}(Ω)`; the
frozen coefficients are measurable in `x` and continuous in `s` on `Ω`; and the zero boundary
datum has value zero. These are the hypotheses of the global Hölder estimate and of the existence
theorem for quasilinear problems, with the exponents `r` and `n + 3`. -/
private theorem exists_memLp_and_aestronglyMeasurable (hα : 0 < α) (hqn : (n : ℝ≥0∞) + 1 < q)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict Ω)) :
    ∃ r : ℝ≥0, 1 < r ∧ (n + 1 : ℝ) < 2 * r ∧ (2 : ℝ) < ((n + 3 : ℝ≥0) : ℝ) ∧
      MemLp f r (volume.restrict Ω) ∧
      MemLp (-G) (n + 3 : ℝ≥0) (volume.restrict Ω) ∧
      (∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Ω)) ∧
      (∀ᵐ x ∂volume.restrict Ω, Continuous (A x)) ∧
      W1p.value (0 : W1p volume Ω 2) =ᵐ[volume.restrict Ω] 0 := by
  obtain ⟨r, hnr, hrq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqn
  have hnr' : (n : ℝ) + 1 < r := by exact_mod_cast hnr
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) := Ω.isOpen.measurableSet
  refine ⟨r, by exact_mod_cast (show (1 : ℝ) < r by linarith), by linarith, by push_cast; linarith,
    hf.mono_exponent (by exact_mod_cast hrq.le),
    ((MeasureTheory.memLp_top_of_holderOnWith hΩm hΩ hα (hG.mono subset_closure)).neg
      ).mono_exponent le_top,
    fun s => (continuousOn_of_continuousOn_matrixBilinearForm
      (((hAx s).continuousOn hα).mono subset_closure)).aestronglyMeasurable hΩm,
    ae_restrict_of_forall_mem hΩm fun x hx =>
      continuous_of_continuous_matrixBilinearForm (hAs x (subset_closure hx)).continuous, ?_⟩
  rw [W1p.value_zero]
  exact Lp.coeFn_zero _ _ _

/-- The right-hand side of the weak formulation with the divergence datum `-G`, in the form of
the global Hölder estimate. -/
private theorem setIntegral_sub_setIntegral_neg_eq (φ : W1p volume Ω 2) :
    (∫ x in Ω, f x * W1p.value φ x) - ∫ x in Ω, ⟪(-G) x, W1p.gradient φ x⟫_ℝ =
      (∫ x in Ω, ⟪G x, W1p.gradient φ x⟫_ℝ) + ∫ x in Ω, f x * W1p.value φ x := by
  simp only [Pi.neg_apply, inner_neg_left, integral_neg, sub_neg_eq_add]
  ring

/-- **The De Giorgi step.** A weak solution agrees almost everywhere on `Ω` with a function that
is `γ₀`-Hölder on `closure Ω`, for some `γ₀ > 0`. -/
private theorem exists_holderOnWith_closure_value (hα : 0 < α) (hqn : (n : ℝ≥0∞) + 1 < q)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hLip : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : W1p0 volume Ω 2,
      energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0 u
          (φ : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x) :
    ∃ γ₀ : ℝ≥0, 0 < γ₀ ∧ ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v ∧
        ∃ C : ℝ≥0, HolderOnWith C γ₀ v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  -- The global De Giorgi estimate with `f ∈ Lʳ`, `n + 1 < r < q`, and `-G ∈ L^{n + 3}`.
  obtain ⟨r, hr, hrn, hq3, hfr, hG3, hAm, hAc, h0⟩ :=
    exists_memLp_and_aestronglyMeasurable hα hqn hΩ hAx hAs hG hf
  obtain ⟨γ₀, C, hγ₀, -, -, hreg⟩ :=
    hLip.exists_ae_eq_and_holderOnWith_quasilinear (mu := volume) hΩ (lam := lam) (Lam := Lam) hr
      (by simpa using hrn) hq3 (by simp)
  obtain ⟨v, hv, hvH⟩ := hreg (u := u) (g := 0) (G := 0) (K₀ := 0) (K₁ := 0)
    (fun s => (hA s).mono_set subset_closure) hAm hAc hfr hG3 (by simp)
    (fun φ => (hu φ).trans (setIntegral_sub_setIntegral_neg_eq _).symm) h0
    (LipschitzWith.const (0 : ℝ)).lipschitzOnWith (fun x _ => by simp)
  obtain ⟨w, hwv, hwH⟩ := hvH.exists_eqOn_holderOnWith_closure hγ₀
  exact ⟨γ₀, hγ₀, w, hv.trans (ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx =>
    (hwv hx).symm), _, hwH⟩

/-- **The Schauder step.** If the weak solution agrees with a `γ`-Hölder function `v` on
`closure Ω`, the frozen coefficient `A(x, v(x))` is `β'`-Hölder there for `β' ≤ min γ α`, so the
global Schauder estimate makes `∇u` agree with a bounded `β'`-Hölder function on `closure Ω`. -/
private theorem exists_holderOnWith_gradient_of_holderOnWith_value {β' γ : ℝ≥0}
    (hβ' : 0 < β') (hβ'1 : β' < 1) (hβ'α : β' ≤ α) (hβ'γ : β' ≤ γ) (hq2 : 2 ≤ q)
    (hβ'q : (β' : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : W1p0 volume Ω 2,
      energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0 u
          (φ : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hv : W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v) {Cv : ℝ≥0}
    (hvH : HolderOnWith Cv γ v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
      ∃ C M : ℝ≥0, HolderOnWith C β' g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
        ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖g y‖ ≤ M := by
  -- A bound for the distances in the bounded set `closure Ω`.
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), edist x y ≤ D :=
    ⟨_, fun _ hx _ hy => Metric.edist_le_diam_of_mem hΩ.closure hx hy⟩
  have haK := HolderOnWith.comp_of_lipschitzWith_right (F := fun x s => matrixBilinearForm (A x s))
    hD hAx hAs hβ'α (hvH.of_le hD hβ'γ)
  obtain ⟨C, -, h⟩ := exists_holderOnWith_gradient_closure_of_forall_graph hβ' hβ'1 le_rfl hq2
    hβ'q hΩ (forall_graph_holderWith_fderiv_of_le hβ'α hβ'1.le hbdry) lam Lam
    ((Kx * D ^ ((α : ℝ) - β') + L * (Cv * D ^ ((γ : ℝ) - β')) : ℝ≥0) : ℝ)
  have htest := forall_testFunction_of_forall_w1p0 (a := fun x => A x (v x))
    (by filter_upwards [hv] with x hx; rw [hx]) hu
  obtain ⟨g, hg, hgH, hgb⟩ := h (UniformlyEllipticOn.apply_of_forall hA v) haK le_rfl
    (hG.of_le hD hβ'α) hf htest
  exact ⟨g, hg, _, _, hgH, fun y hy => (hgb y hy).trans (Real.le_coe_toNNReal _)⟩

/-- **The Lipschitz step.** If the weak solution agrees with a function `v` that is Hölder on
`closure Ω`, and its gradient with a function that is bounded and Hölder on `closure Ω`, then
`v` is `β`-Hölder on `closure Ω` for every `β ≤ 1`. -/
private theorem exists_holderOnWith_closure_of_gradient {β γ β₁ : ℝ≥0} (hβ1 : β ≤ 1)
    (hγ : 0 < γ) (hβ₁ : 0 < β₁)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hLip : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hv : W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v) {Cv : ℝ≥0}
    (hvH : HolderOnWith Cv γ v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hg : (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g) {Cg M : ℝ≥0}
    (hgH : HolderOnWith Cg β₁ g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hgb : ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖g y‖ ≤ M) :
    ∃ C : ℝ≥0, HolderOnWith C β v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  have hvc := hvH.continuousOn hγ
  -- `v` is differentiable on `Ω`, with derivative `⟪g, ·⟫`.
  have hd (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x ∈ Ω) :
      HasFDerivAt v (innerSL ℝ (g x)) x :=
    (((W1p.hasWeakFDerivOn (u : W1p volume Ω 2)).congr_ae hv).congr_ae_deriv
      (hg.fun_comp (innerSL ℝ))).hasFDerivAt_of_continuousOn (hvc.mono subset_closure)
      ((innerSL ℝ).continuous.comp_continuousOn ((hgH.continuousOn hβ₁).mono subset_closure)) hx
  obtain ⟨Cc, δ, hδ, hchain⟩ := hLip.exists_dist_le_of_norm_fderiv_le hΩ
  have hlip := hchain (g := v) (L := M) (fun x hx => (hd x hx).differentiableAt) fun x hx => by
    rw [(hd x hx).fderiv, innerSL_apply_norm]
    exact hgb x (subset_closure hx)
  -- `v` has bounded oscillation on `Ω`.
  obtain ⟨Dv, hDv⟩ := Metric.isBounded_iff.1 ((hvH.mono subset_closure).isBounded_image hΩ)
  have hH := HolderOnWith.of_le_of_dist_le (K := Cc * M) (D := Dv.toNNReal) (β := 1)
    (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) (fun x hx y hy hxy => by
      simpa only [NNReal.coe_one, Real.rpow_one, NNReal.coe_mul] using hlip x hx y hy hxy)
    (fun x hx y hy => (hDv (mem_image_of_mem v hx) (mem_image_of_mem v hy)).trans
      (Real.le_coe_toNNReal Dv)) hβ1 hδ
  exact ⟨_, hH.of_subset_closure subset_rfl fun x hx => (hvc x hx).mono subset_closure⟩

/-- A `C^{1,α}` boundary is Lipschitz. -/
private theorem isLipschitzDomain_of_forall_graph
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst)) :
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E :=
  isLipschitzDomain_of_contDiffAt fun x hx => by
    obtain ⟨e, γ, h₀, r₀, -, hex, hh₀, hr₀, hγ0, hγ, -, hgraph⟩ := hbdry x hx
    exact ⟨e, γ, h₀, r₀, hex, hh₀, hr₀, hγ0, hγ.contDiffAt, hgraph⟩

/-- **Gradient regularity up to the boundary for quasilinear Dirichlet problems.** Let
`Ω ⊆ ℝⁿ⁺¹` be a bounded open set with `C^{1,α}` boundary, and let `A(x, s)` be a field of
matrices, uniformly elliptic with constants `λ, Λ` on `closure Ω` for every `s`, `α`-Hölder in `x`
on `closure Ω` with a constant independent of `s`, and Lipschitz in `s` with a constant
independent of `x`. Let `G` be `α`-Hölder on `closure Ω` and `f ∈ L^q(Ω)` with `q ≥ 2`. If
`u ∈ H¹₀(Ω)` is a weak solution of the quasilinear equation

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every `φ ∈ H¹₀(Ω)`, then `∇u`
agrees almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, for every
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`; such `β` exist
exactly when `0 < α` and `q > n + 1`. These are the exponents of the linear estimate
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`. -/
theorem exists_holderOnWith_gradient_closure_quasilinear {β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) (hq2 : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : W1p0 volume Ω 2,
      energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0 u
          (φ : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
      ∃ C : ℝ≥0, HolderOnWith C β g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  have hα : 0 < α := hβ.trans_le hβα
  have hLip := isLipschitzDomain_of_forall_graph hbdry
  -- De Giorgi: `u` agrees with a `γ₀`-Hölder function `v` on `closure Ω`.
  obtain ⟨γ₀, hγ₀, v, hv, Cv, hvH⟩ :=
    exists_holderOnWith_closure_value hα
      (natCast_add_one_lt_of_le_one_sub_div (zero_lt_two.trans_le hq2).ne' hβ hβq) hΩ hLip hA hAx
      hAs hG hf hu
  -- First Schauder pass, with the small positive exponent `β₁ = min γ₀ β`.
  have hβ₁ : 0 < min γ₀ β := lt_min hγ₀ hβ
  obtain ⟨g₁, hg₁, C₁, M₁, hg₁H, hg₁b⟩ := exists_holderOnWith_gradient_of_holderOnWith_value
    hβ₁ ((min_le_right γ₀ β).trans_lt hβ1) ((min_le_right γ₀ β).trans hβα) (min_le_left γ₀ β)
    hq2 ((NNReal.coe_le_coe.2 (min_le_right γ₀ β)).trans hβq) hΩ hbdry hA hAx hAs hG hf hu hv
    hvH
  -- Lipschitz: `v` is `β`-Hölder on `closure Ω`.
  obtain ⟨Cv', hvH'⟩ :=
    exists_holderOnWith_closure_of_gradient hβ1.le hγ₀ hβ₁ hΩ hLip hv hvH hg₁ hg₁H hg₁b
  -- Second Schauder pass, with the exponent `β`.
  obtain ⟨g, hg, C, -, hgH, -⟩ := exists_holderOnWith_gradient_of_holderOnWith_value hβ hβ1 hβα
    le_rfl hq2 hβq hΩ hbdry hA hAx hAs hG hf hu hv hvH'
  exact ⟨g, hg, C, hgH⟩

/-- **Weak solutions with Hölder gradient up to the boundary.** Under the hypotheses of
`TauCeti.PDE.exists_holderOnWith_gradient_closure_quasilinear`, the quasilinear Dirichlet problem

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`

has a weak solution `u ∈ H¹₀(Ω)` whose gradient agrees almost everywhere on `Ω` with a function
that is `β`-Hölder on `closure Ω`. No uniqueness is claimed. -/
theorem exists_forall_energyFormH1_quasilinear_eq_and_holderOnWith_gradient_closure {β : ℝ≥0}
    (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) (hq2 : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict Ω)) :
    ∃ u : W1p0 volume Ω 2,
      (∀ φ : W1p0 volume Ω 2,
        energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0 u
            (φ : W1p volume Ω 2) =
          (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
            ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x) ∧
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
        ∃ C : ℝ≥0, HolderOnWith C β g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  -- The existence theorem with the exponents `n + 1 < r < q` for `f` and `n + 3` for `-G`.
  obtain ⟨r, hr, hrn, hq3, hfr, hG3, hAm, hAc, h0⟩ :=
    exists_memLp_and_aestronglyMeasurable (hβ.trans_le hβα)
      (natCast_add_one_lt_of_le_one_sub_div (zero_lt_two.trans_le hq2).ne' hβ hβq) hΩ hAx hAs hG hf
  obtain ⟨_, _, -, -, -, hex⟩ :=
    (isLipschitzDomain_of_forall_graph hbdry
      ).exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_holderOnWith hΩ
      (lam := lam) (Lam := Lam) hr hrn hq3 (by simp)
  obtain ⟨u, hu0, hu, -⟩ := hex (A := A) (g := 0) (G := 0) (K₀ := 0) (K₁ := 0)
    (fun s => (hA s).mono_set subset_closure) hAm hAc hfr hG3 h0
    (LipschitzWith.const (0 : ℝ)).lipschitzOnWith (fun x _ => by simp)
  have hu' := fun φ : W1p0 volume Ω 2 => (hu φ).trans (setIntegral_sub_setIntegral_neg_eq _)
  exact ⟨⟨u, by simpa using hu0⟩, hu', exists_holderOnWith_gradient_closure_quasilinear hβ hβ1
    hβα hq2 hβq hΩ hbdry hA hAx hAs hG hf hu'⟩

end PDE

end TauCeti
