/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.GlobalHolder
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Global
import TauCeti.Analysis.Holder.LipschitzDomain
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Quasilinear.Regularity
import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.Topology.MetricSpace.Bounded

/-!
# Global `C^{1,β}` regularity for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set with `C^{1,α}` boundary: near each of its frontier points, in
rigid coordinates, `Ω` is the region above the graph of a `C¹` function whose derivative is
`α`-Hölder. Consider the quasilinear Dirichlet problem with zero boundary values

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`,

whose coefficient matrix depends on the solution. Suppose that on `closure Ω` every `A(·, s)` is
uniformly elliptic with constants `λ, Λ`, that `A` is `α`-Hölder in `x` uniformly in `s` and
Lipschitz in `s` uniformly in `x`, that `G` is `α`-Hölder on `closure Ω`, and that `f ∈ L^q(Ω)`
with `q ≥ 2`. This file proves that the gradient of every weak solution `u ∈ H¹₀(Ω)` agrees
almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, for every
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_energyFormH1_quasilinear_eq`). These
are the exponents of the linear global estimate with Hölder coefficients
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`), so the dependence of the
coefficient on `u` costs nothing up to the boundary either. Weak solutions exist in every
dimension (`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`), so the
problem has a weak solution whose gradient is `β`-Hölder on `closure Ω`
(`TauCeti.PDE.exists_forall_energyFormH1_quasilinear_eq_and_holderOnWith_gradient_closure`). The
interior form of the theorem is
`exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq`, in the
`TauCeti.PDE` namespace.

## The bootstrap

A weak solution `u` solves the linear equation with the frozen coefficient `a(x) = A(x, u(x))`.

* **De Giorgi up to the boundary.** A `C^{1,α}` boundary is Lipschitz
  (`TauCeti.isLipschitzDomain_of_contDiffAt`), and the frozen coefficient is measurable and
  uniformly elliptic, so the global Hölder estimate for quasilinear equations
  (`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_quasilinear`) makes `u` agree almost
  everywhere with a function `v₁` which is `γ₀`-Hölder on `closure Ω`, for some `γ₀ > 0`.
* **Schauder.** Then `x ↦ A(x, v₁(x))` is Hölder on `closure Ω` with exponent `min γ₀ β`, and the
  global Schauder estimate for divergence-form equations makes `∇u` agree almost everywhere with a
  function `g₁` which is Hölder and bounded on `closure Ω`.
* **Lipschitz.** The continuous function `v₁` has the continuous weak derivative `g₁`, so it is
  differentiable on `Ω` with bounded derivative
  (`TauCeti.HasWeakFDerivOn.hasFDerivAt_of_continuousOn`).
  Nearby points of a Lipschitz domain are joined in `Ω` by short paths, so `v₁` is `β`-Hölder on
  `Ω` (`Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`), hence on `closure Ω`.
* **Schauder again.** A second application of the global Schauder estimate, with the coefficient
  `x ↦ A(x, v₁(x))` now `β`-Hölder, gives the exponent `β`.

The global Schauder estimate takes a single Hölder exponent for the coefficient and for the
derivatives of the boundary graphs. Each pass lowers the exponent of the graphs, after cutting
them off outside the chart: a graph `γ` with `α`-Hölder derivative agrees near the chart centre
with a graph whose derivative is `β`-Hölder on the whole space for every `β ≤ min α 1`
(`ContDiff.exists_eqOn_ball_holderWith_fderiv`), so the charts of a `C^{1,α}` boundary are also
charts of a `C^{1,β}` boundary (`TauCeti.PDE.forall_frontier_chart_of_le`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.29 and 8.33, and the regularity of quasilinear equations in Chapter 13.
* O. A. Ladyzhenskaya, N. N. Ural'tseva, *Linear and Quasilinear Elliptic Equations*, Academic
  Press, 1968, Chapter 4, Section 6 (`C^{1,β}` estimates up to the boundary).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The bootstrap -/

variable {α : ℝ≥0} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ} {Kx L KG : ℝ≥0}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {q : ℝ≥0∞} {u : W1p0 volume Ω 2}

/-- The coefficient field `A`, Hölder in `x` on `closure Ω` and Lipschitz in `s`, satisfies on `Ω`
the hypotheses of the existence and the global Hölder theorems: ellipticity, measurability in `x`
and continuity in `s`. -/
private theorem caratheodory_of_holderOnWith (hα : 0 < α)
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s)) :
    (∀ s, UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (fun x => A x s)
      lam Lam) ∧ (∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Ω)) ∧
      ∀ᵐ x ∂volume.restrict Ω, Continuous (A x) :=
  ⟨fun s => (hA s).mono_set subset_closure, fun s =>
    ((continuousOn_of_continuousOn_matrixBilinearForm ((hAx s).continuousOn hα)).mono
      subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet,
    ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx =>
      continuous_of_continuous_matrixBilinearForm (hAs x (subset_closure hx)).continuous⟩

/-- **De Giorgi up to the boundary.** On a bounded Lipschitz domain, a weak solution
`u ∈ H¹₀(Ω)` of the quasilinear equation agrees almost everywhere on `Ω` with a function that is
Hölder on `closure Ω`, with some positive exponent: the frozen coefficient `A(x, u(x))` is
measurable and uniformly elliptic, so the global Hölder estimate applies. -/
private theorem exists_holderOnWith_value_closure
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hLip : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E) (hα : 0 < α)
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hq2 : 2 ≤ q) (hqn : (n : ℝ≥0∞) + 1 < q) (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0
        (u : W1p volume Ω 2) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x) :
    ∃ (γ₀ C₀ : ℝ≥0) (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), 0 < γ₀ ∧
      W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v ∧
      HolderOnWith C₀ γ₀ v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  obtain ⟨r, hnr, hrq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqn
  have hnr' : (n : ℝ) + 1 < r := by exact_mod_cast hnr
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  obtain ⟨γ₀, C₀, hγ₀, -, -, hDG⟩ := hLip.exists_ae_eq_and_holderOnWith_quasilinear
    (mu := volume) hΩ (lam := lam) (Lam := Lam) (r := r) (q := n + 3)
    (by exact_mod_cast (show (1 : ℝ) < r by linarith)) (by rw [hcard]; linarith)
    (by push_cast; linarith) (by rw [hcard]; push_cast; linarith)
  obtain ⟨hAΩ, hAm, hAc⟩ := caratheodory_of_holderOnWith hα hA hAx hAs
  have hGtop : MemLp G ⊤ (volume.restrict Ω) :=
    hG.memLp_top hα hΩ.closure Ω.isOpen.measurableSet subset_closure
  -- The equation holds against all of `H¹₀(Ω)`.
  have hell := UniformlyEllipticOn.apply_of_forall hAΩ (W1p.value (u : W1p volume Ω 2))
  have hint : MemLp (fun x => energyIntegrand (A x (W1p.value (u : W1p volume Ω 2) x)) 0 0) ⊤
      (volume.restrict Ω) :=
    memLp_energyIntegrand_of_bounds hell.upper_nonneg
      ((Lp.aestronglyMeasurable _).apply_of_forall_of_continuousAt hAm
        (hAc.mono fun _ hx => hx.continuousAt)) aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ hx η ξ => hell.upper_bound hx η ξ) (beta := 0)
      (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
  have hw := forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner le_rfl hint hu
    (hGtop.mono_exponent le_top) (hf.mono_exponent hq2)
  obtain ⟨v₀, huv₀, hv₀⟩ := hDG (u := (u : W1p volume Ω 2)) (g := 0) (G := 0) (K₀ := 0) (K₁ := 0)
    (F := fun x => -G x) hAΩ hAm hAc (hf.mono_exponent hrq.le) (hGtop.neg.mono_exponent le_top)
    (by simp) (fun φ => by simpa only [W1p.restrictL_self] using hw φ)
    (by simpa using (Lp.coeFn_zero ℝ 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))))
    (LipschitzWith.const 0).lipschitzOnWith (fun _ _ => by simp)
  obtain ⟨v₁, hv₁₀, hv₁⟩ := hv₀.exists_eqOn_holderOnWith_closure hγ₀
  exact ⟨γ₀, _, v₁, hγ₀, huv₀.trans (ae_restrict_of_forall_mem Ω.isOpen.measurableSet
    fun x hx => (hv₁₀ hx).symm), hv₁⟩

/-- **The Schauder step.** If a weak solution `u ∈ H¹₀(Ω)` agrees almost everywhere on `Ω` with a
function `v` that is `γ`-Hölder on `closure Ω`, then `A(x, v(x))` is `β`-Hölder on `closure Ω`,
and the global Schauder estimate makes `∇u` agree almost everywhere on `Ω` with a function that is
`β`-Hölder and bounded on `closure Ω`, for every `0 < β < 1` with `β ≤ γ`, `β ≤ α` and
`β ≤ 1 - (n + 1) / q`. -/
private theorem exists_holderOnWith_gradient_closure_of_holderOnWith_value
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
    (hq2 : 2 ≤ q) (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0
        (u : W1p volume Ω 2) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x)
    {γ β Cv : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβγ : β ≤ γ) (hβα : β ≤ α)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (huv : W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v)
    (hv : HolderOnWith Cv γ v (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
      ∃ C : ℝ≥0, HolderOnWith C β g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
        ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖g y‖ ≤ C := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), edist x y ≤ D :=
    ⟨_, fun _ hx _ hy => Metric.edist_le_diam_of_mem hΩ.closure hx hy⟩
  -- `u` solves the linear equation with the coefficient frozen at `v`, which is `β`-Hölder.
  have haK := holderOnWith_matrixBilinearForm_comp hD subset_rfl hAx hAs hβα (hv.of_le hD hβγ)
  have hu' : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (v x)) 0 0 (u : W1p volume Ω 2)
      (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x := fun φ => by
    rw [← hu φ]
    exact energyFormH1_congr_ae (huv.mono fun x hx => by rw [hx]) .rfl .rfl _ _
  obtain ⟨C, -, h⟩ := exists_holderOnWith_gradient_closure_of_forall_graph hβ hβ1 le_rfl hq2 hβq
    hΩ (forall_frontier_chart_of_le hβα hβ1.le hbdry) lam Lam
    ((Kx * D ^ ((α : ℝ) - β) + L * (Cv * D ^ ((γ : ℝ) - β)) : ℝ≥0) : ℝ)
  obtain ⟨g, hg, hgH, hgb⟩ := h (UniformlyEllipticOn.apply_of_forall hA v) haK le_rfl
    (hG.of_le hD hβα) hf hu'
  exact ⟨g, hg, _, hgH, fun y hy => (hgb y hy).trans (Real.le_coe_toNNReal _)⟩

/-- **Global `C^{1,β}` regularity for quasilinear divergence-form equations.** Let `Ω ⊆ ℝⁿ⁺¹` be a
bounded open set with `C^{1,α}` boundary: for every frontier point `x` there are rigid
coordinates `e` with `e x = 0` in which, inside the normal cylinder of half-height `h₀` and radius
`r₀`, `Ω` is the region above the graph of a `C¹` function `γ` with `γ 0 = 0` and `α`-Hölder
derivative. Let `A(x, s)` be a field of matrices which, on `closure Ω`, is uniformly elliptic with
constants `λ, Λ` in `x` for every `s`, `α`-Hölder in `x` with a constant independent of `s`, and
Lipschitz in `s` with a constant independent of `x`. Let `G` be `α`-Hölder on `closure Ω` and
`f ∈ L^q(Ω)` with `q ≥ 2`. If `u ∈ H¹₀(Ω)` is a weak solution of the quasilinear Dirichlet problem

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, then `∇u`
agrees almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, for every
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`. These are the
exponents of the linear global estimate with Hölder coefficients
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`). -/
theorem exists_holderOnWith_gradient_closure_of_forall_energyFormH1_quasilinear_eq
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
    (hq2 : 2 ≤ q) (hf : MemLp f q (volume.restrict Ω))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0
        (u : W1p volume Ω 2) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x)
    {β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
      ∃ C : ℝ≥0, HolderOnWith C β g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  have hα : 0 < α := hβ.trans_le hβα
  have hΩΩ : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ closure Ω := subset_closure
  have hΩm := Ω.isOpen.measurableSet
  have hqn := natCast_add_one_lt_of_le_one_sub_div (NNReal.coe_pos.2 hβ)
    (zero_lt_two.trans_le hq2).ne' hβq
  -- **De Giorgi up to the boundary**: `u` agrees with a function `v₁`, Hölder on `closure Ω`.
  have hLip : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E :=
    isLipschitzDomain_of_contDiffAt fun x hx => by
      obtain ⟨e, γ, h₀, r₀, -, hex, hh₀, hr₀, hγ0, hγ, -, hgraph⟩ := hbdry x hx
      exact ⟨e, γ, h₀, r₀, hex, hh₀, hr₀, hγ0, hγ.contDiffAt, hgraph⟩
  obtain ⟨γ₀, C₀, v₁, hγ₀, huv₁, hv₁⟩ :=
    exists_holderOnWith_value_closure hΩ hLip hα hA hAx hAs hG hq2 hqn hf hu
  -- **Schauder**: `∇u` agrees with a function `g₁`, Hölder and bounded on `closure Ω`.
  have hβ₁ : 0 < min γ₀ β := lt_min hγ₀ hβ
  obtain ⟨g₁, hg₁, C₁, hg₁H, hg₁b⟩ := exists_holderOnWith_gradient_closure_of_holderOnWith_value
    hΩ hbdry hA hAx hAs hG hq2 hf hu hβ₁ ((min_le_right _ _).trans_lt hβ1) (min_le_left _ _)
    ((min_le_right _ _).trans hβα) ((NNReal.coe_le_coe.2 (min_le_right _ _)).trans hβq) huv₁ hv₁
  -- **Lipschitz**: `v₁` is differentiable on `Ω` with derivative `⟪g₁, ·⟫`, so `β`-Hölder.
  have hW := ((W1p.hasWeakFDerivOn (u : W1p volume Ω 2)).congr_ae huv₁).congr_ae_deriv
    (hg₁.fun_comp (innerSL ℝ))
  have hder : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      HasFDerivAt v₁ (innerSL ℝ (g₁ x)) x := fun x hx =>
    hW.hasFDerivAt_of_continuousOn ((hv₁.continuousOn hγ₀).mono hΩΩ)
      ((innerSL ℝ).continuous.comp_continuousOn ((hg₁H.continuousOn hβ₁).mono hΩΩ)) hx
  obtain ⟨M₀, hM₀⟩ := (hv₁.isBounded_image hΩ.closure).exists_norm_le
  obtain ⟨CL, hCL⟩ := hLip.exists_holderOnWith_of_norm_fderiv_le hΩ hβ1.le
  have hv₁Ω := hCL (g := v₁) (M := M₀.toNNReal) (L := C₁) (fun x hx => (hder x hx).differentiableAt)
    (fun x hx => (hM₀ _ (mem_image_of_mem _ (hΩΩ hx))).trans (Real.le_coe_toNNReal _))
    (fun x hx => by rw [(hder x hx).fderiv, innerSL_apply_norm]; exact hg₁b x (hΩΩ hx))
  obtain ⟨v₂, hv₂₁, hv₂⟩ := hv₁Ω.exists_eqOn_holderOnWith_closure hβ
  have huv₂ : W1p.value (u : W1p volume Ω 2) =ᵐ[volume.restrict Ω] v₂ :=
    huv₁.trans (ae_restrict_of_forall_mem hΩm fun x hx => (hv₂₁ hx).symm)
  -- **Schauder again**, with the coefficient frozen at the `β`-Hölder function `v₂`.
  obtain ⟨g, hg, C, hgH, -⟩ := exists_holderOnWith_gradient_closure_of_holderOnWith_value hΩ hbdry
    hA hAx hAs hG hq2 hf hu hβ hβ1 le_rfl hβα hβq huv₂ hv₂
  exact ⟨g, hg, C, hgH⟩

/-- **Existence of weak solutions that are `C^{1,β}` up to the boundary.** Under the hypotheses of
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_energyFormH1_quasilinear_eq`, the
quasilinear Dirichlet problem

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`

has a weak solution `u ∈ H¹₀(Ω)`, tested against every `φ ∈ H¹₀(Ω)` and so in particular against
every test function, whose gradient agrees almost everywhere on `Ω` with a function that is
`β`-Hölder on `closure Ω`. No uniqueness is claimed; the regularity of every weak solution
is `TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_energyFormH1_quasilinear_eq`. -/
theorem exists_forall_energyFormH1_quasilinear_eq_and_holderOnWith_gradient_closure
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
    (hq2 : 2 ≤ q) (hf : MemLp f q (volume.restrict Ω)) {β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) :
    ∃ u : W1p0 volume Ω 2,
      (∀ φ : W1p0 volume Ω 2, energyFormH1 (fun x => A x (W1p.value (u : W1p volume Ω 2) x)) 0 0
          (u : W1p volume Ω 2) (φ : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x) ∧
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
        ∃ C : ℝ≥0, HolderOnWith C β g (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  have hα : 0 < α := hβ.trans_le hβα
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  obtain ⟨hAΩ, hAm, hAc⟩ := caratheodory_of_holderOnWith hα hA hAx hAs
  have hG2 : MemLp G 2 (volume.restrict Ω) :=
    (hG.memLp_top hα hΩ.closure Ω.isOpen.measurableSet subset_closure).mono_exponent le_top
  have hf2 : MemLp f 2 (volume.restrict Ω) := hf.mono_exponent hq2
  -- The forcing `v ↦ ∫_Ω f v + ∫_Ω ⟪G, ∇v⟫` on `H¹₀(Ω)`.
  obtain ⟨u, hu0, hu⟩ := exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq hAΩ hAm
    hAc hΩ 0 (dirichletForcing (hf2.toLp f) - divergenceForcing (hG2.toLp G))
  have huH : ∀ φ : W1p0 volume Ω 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
      (φ : W1p volume Ω 2) =
      (∫ x in Ω, ⟪G x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ) +
        ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x := fun φ => by
    rw [hu φ, sub_apply, dirichletForcing_apply_eq_setIntegral, divergenceForcing_toLp_apply,
      sub_neg_eq_add, add_comm]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  -- In particular `u` is a weak solution tested against test functions.
  have hu' : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
      (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x := fun φ => by
    rw [huH ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    congr 1 <;> refine integral_congr_ae ?_
    · filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
      simp [hx]
    · filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hφx
      rw [hφx]
  exact ⟨⟨u, by simpa using hu0⟩, huH,
    exists_holderOnWith_gradient_closure_of_forall_energyFormH1_quasilinear_eq hΩ hbdry hA hAx hAs
      hG hq2 hf hu' hβ hβ1 hβα hβq⟩

end PDE

end TauCeti
