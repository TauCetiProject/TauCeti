/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.DivergenceForm
import TauCeti.Analysis.Holder.Superposition
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Holder

/-!
# Interior regularity for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be open and consider the quasilinear divergence-form equation

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`,

whose coefficient matrix depends on the solution itself. Suppose that `A(·, s)` is uniformly
elliptic with constants `λ, Λ` for every `s`, that `A` is `α`-Hölder in `x` uniformly in `s` and
Lipschitz in `s` uniformly in `x`, with `0 < α`, that `G` is `α`-Hölder, and that
`f ∈ L^q(Ω)` with `q ≥ 2`. This file proves that the gradient of every weak
solution `u ∈ H¹(Ω)` is Hölder continuous in the interior of `Ω`, with every exponent
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`; such exponents exist when `q > n + 1`
(`exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq`, in
the `TauCeti.PDE` namespace).
These are the exponents of the linear theory with `α`-Hölder coefficients, so the dependence of the
coefficients on `u` costs nothing. Weak solutions exist on every bounded open set
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`).

One more derivative of the coefficient buys one more derivative of the solution. If `G = 0`, if
`0 < α < 1`, if `f ∈ L²(Ω)` is `α`-Hölder near every point of `Ω`, and if every entry of `A` is
`C¹` as a function of `(x, s)` with derivative `α`-Hölder near every point of `Ω × ℝ`, then every
weak solution agrees almost everywhere with a function that is `C²` on `Ω` and whose second
derivative is `α`-Hölder on every compact subset of `Ω`
(`exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_energyFormH1_quasilinear_eq`).
This is interior `C^{2,α}` regularity.

## The bootstrap

A weak solution `u` solves the linear equation with the frozen coefficient `a(x) = A(x, u(x))`.

* **De Giorgi.** The frozen coefficient is measurable and uniformly elliptic, so De Giorgi's
  theorem with a right-hand side makes the precise representative `ū` of `u` Hölder continuous
  inside `Ω`, with some exponent `γ₀ > 0` depending on the ellipticity.
* **Schauder.** Then `x ↦ A(x, ū(x))` is Hölder continuous with exponent `min γ₀ α`, and the
  Schauder estimate for divergence-form equations with Hölder coefficients makes `∇u` Hölder
  continuous with a small positive exponent.
* **Lipschitz.** A Hölder gradient is locally bounded, so `ū` is locally Lipschitz, hence
  `β`-Hölder (`TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_forall_norm_le`), and the
  frozen coefficient is `β`-Hölder.
* **Schauder again.** A second application of the Schauder estimate gives the exponents above.
* **Differentiating the equation.** For the `C^{2,α}` statement, the data are bounded near each
  point, so `∇u` is `α`-Hölder near each point, and `u` has a `C¹` representative `g₁`
  (`TauCeti.W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative`). The frozen
  coefficient `x ↦ A(x, g₁(x))` is then `C^{1,α}` near each point
  (`TauCeti.exists_mem_nhds_holderOnWith_fderiv_superposition`), and the linear theorem for
  `C^{1,α}` coefficients
  (`TauCeti.PDE.exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn`)
  applies to `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.24 and 8.32, and the regularity of quasilinear equations in Chapter 13.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ} {α : ℝ≥0} {Kx L : ℝ≥0}

/-- A coefficient Hölder in `x` and Lipschitz in `s`, frozen at a measurable function, is
measurable. -/
private theorem aestronglyMeasurable_comp_of_holderOnWith (hα : 0 < α)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    AEStronglyMeasurable (fun x => A x (v x)) (volume.restrict Omega) :=
  hv.apply_of_forall_of_continuousAt
    (fun s => (continuousOn_of_continuousOn_matrixBilinearForm
      ((hAx s).continuousOn hα)).aestronglyMeasurable Omega.isOpen.measurableSet)
    (ae_restrict_of_forall_mem Omega.isOpen.measurableSet fun x hx =>
      (continuous_of_continuous_matrixBilinearForm (hAs x hx).continuous).continuousAt)

variable {u : W1p volume Omega 2}
  {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {KG : ℝ≥0} {q : ℝ≥0∞}

/-- **The De Giorgi step.** A weak solution of the quasilinear equation solves the linear equation
with the measurable, uniformly elliptic coefficient `A(·, u)`, so De Giorgi's theorem makes its
precise representative Hölder continuous inside `Ω`. -/
private theorem exists_holderOnWith_preciseRepresentative_value (hα : 0 < α) (hq2 : 2 ≤ q)
    (hqn : (n : ℝ≥0∞) + 1 < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G Omega) (hf : MemLp f q (volume.restrict Omega))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : Bornology.IsBounded S) {R : ℝ}
    (hR : 0 < R) (hRS : thickening R S ⊆ Omega) :
    ∃ γ C : ℝ≥0, 0 < γ ∧
      HolderOnWith C γ (preciseRepresentative volume (W1p.value u)) (thickening (R / 2) S) := by
  -- The exponents for De Giorgi's theorem: `f ∈ Lʳ` with `n + 1 < r < q`, and the bounded
  -- divergence datum in `L^{n + 3}`.
  obtain ⟨r, hnr, hrq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqn
  have hnr' : (n : ℝ) + 1 < r := by exact_mod_cast hnr
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  obtain ⟨γ, C, hγ, -, -, hDG⟩ :=
    exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence (ι := Fin (n + 1))
      (mu := volume) (lam := lam) (Lam := Lam) (r := r) (q := n + 3)
      (by exact_mod_cast (show (1 : ℝ) < r by linarith))
      (by rw [hcard]; linarith) (by push_cast; linarith) (by rw [hcard]; push_cast; linarith)
  -- Restrict the equation to the bounded open set `B = S_R`.
  obtain ⟨B, hBdef⟩ : ∃ B : Opens (EuclideanSpace ℝ (Fin (n + 1))),
      (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = thickening R S :=
    ⟨⟨thickening R S, isOpen_thickening⟩, rfl⟩
  have hBb : Bornology.IsBounded (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    hBdef ▸ hS.thickening
  have hB : B ≤ Omega := fun x hx => hRS (hBdef ▸ hx)
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hBb.measure_lt_top.ne
  have hrestr : volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict Omega := Measure.restrict_mono hB le_rfl
  have hell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x (W1p.value u x)) lam Lam :=
    (UniformlyEllipticOn.apply_of_forall hA _).mono_set hB
  have hmeas : AEStronglyMeasurable (fun x => A x (W1p.value u x)) (volume.restrict B) :=
    (aestronglyMeasurable_comp_of_holderOnWith hα hAx hAs
      (Lp.aestronglyMeasurable (W1p.value u))).mono_measure hrestr
  have hint : MemLp (fun x => energyIntegrand (A x (W1p.value u x)) 0 0) ⊤ (volume.restrict B) :=
    memLp_energyIntegrand_of_bounds hell.upper_nonneg hmeas aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ hx η ξ => hell.upper_bound hx η ξ) (beta := 0)
      (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
  -- The datum `G` is bounded on the bounded set `B`.
  have hGB : HolderOnWith KG α G B := hG.mono hB
  obtain ⟨MG, hMG⟩ := (hGB.isBounded_image hBb).exists_norm_le
  have hGtop : MemLp G ⊤ (volume.restrict B) :=
    memLp_top_of_bound ((hGB.continuousOn hα).aestronglyMeasurable B.isOpen.measurableSet) MG
      (ae_restrict_of_forall_mem B.isOpen.measurableSet (forall_mem_image.1 hMG))
  have hfB : MemLp f q (volume.restrict B) := hf.mono_measure hrestr
  have hw := forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner hB hint hu
    (hGtop.mono_exponent le_top) (hfB.mono_exponent hq2)
  have hK : cthickening (R / 4) (thickening (R / 2) S) ⊆
      (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    hBdef ▸ (cthickening_thickening_subset (by positivity) _ _).trans
      (cthickening_subset_thickening' hR (by linarith) S)
  have hH := hDG hell hmeas (hfB.mono_exponent hrq.le) (hGtop.neg.mono_exponent le_top) hw
    (by positivity) hK
  refine ⟨γ, _, hγ, hH.congr fun x hx => ?_⟩
  exact preciseRepresentative_congr_ae_nhds
    (B.isOpen.mem_nhds (hK (self_subset_cthickening _ hx))) (W1p.value_restrictL_ae hB u)

/-- The coefficient `A(x, v(x))` frozen at a `γ`-Hölder function `v` is `γ`-Hölder on a bounded
set, when `A` is `α`-Hölder in `x`, with `γ ≤ α`, and Lipschitz in `s`. -/
private theorem holderOnWith_matrixBilinearForm_comp {T : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {D : ℝ≥0} (hD : ∀ x ∈ T, ∀ y ∈ T, edist x y ≤ D) (hTΩ : T ⊆ Omega)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    {γ Cv : ℝ≥0} (hγα : γ ≤ α) {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hv : HolderOnWith Cv γ v T) :
    HolderOnWith (Kx * D ^ ((α : ℝ) - γ) + L * Cv) γ
      (fun x => matrixBilinearForm (A x (v x))) T := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have h1 := (((hAx (v x)).mono hTΩ).of_le hD hγα).dist_le hx hy
  have h2 := (hAs y (hTΩ hy)).dist_le_mul (v x) (v y)
  have h3 := hv.dist_le hx hy
  calc dist (matrixBilinearForm (A x (v x))) (matrixBilinearForm (A y (v y)))
      ≤ dist (matrixBilinearForm (A x (v x))) (matrixBilinearForm (A y (v x))) +
        dist (matrixBilinearForm (A y (v x))) (matrixBilinearForm (A y (v y))) :=
        dist_triangle _ _ _
    _ ≤ ↑(Kx * D ^ ((α : ℝ) - γ)) * dist x y ^ (γ : ℝ) + L * (Cv * dist x y ^ (γ : ℝ)) :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 L.coe_nonneg))
    _ = ↑(Kx * D ^ ((α : ℝ) - γ) + L * Cv) * dist x y ^ (γ : ℝ) := by push_cast; ring

/-- **The Schauder step.** If the precise representative `ū` of a weak solution is `γ`-Hölder on
the `ρ`-thickening of a bounded set `S`, the coefficient `A(x, ū(x))` is `γ`-Hölder there, so the
Schauder estimate for divergence-form equations makes the precise representative of `∇u`
`β`-Hölder on `S` for every `0 < β < 1` with `β ≤ γ` and `β ≤ 1 - (n + 1) / q`. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_value
    (hq2 : 2 ≤ q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G Omega) (hf : MemLp f q (volume.restrict Omega))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    {γ₀ γ β : ℝ≥0} (hγγ₀ : γ ≤ γ₀) (hγα : γ ≤ α) (hβ : 0 < β) (hβ1 : β < 1)
    (hβγ : β ≤ γ)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : Bornology.IsBounded S) {ρ : ℝ}
    (hρ : 0 < ρ) (hρS : thickening ρ S ⊆ Omega) {Cv : ℝ≥0}
    (hv : HolderOnWith Cv γ₀ (preciseRepresentative volume (W1p.value u)) (thickening ρ S)) :
    ∃ C : ℝ≥0, HolderOnWith C β (preciseRepresentative volume (W1p.gradient u)) S := by
  -- A bound for the distances in the bounded set `S_ρ`.
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ thickening ρ S, ∀ y ∈ thickening ρ S, edist x y ≤ D :=
    ⟨(Metric.ediam (thickening ρ S)).toNNReal, fun x hx y hy => by
      rw [ENNReal.coe_toNNReal (Metric.isBounded_iff_ediam_ne_top.1 hS.thickening)]
      exact Metric.edist_le_ediam_of_mem hx hy⟩
  have haK := holderOnWith_matrixBilinearForm_comp hD hρS hAx hAs hγα (hv.of_le hD hγγ₀)
  have hGK : HolderOnWith (KG * D ^ ((α : ℝ) - γ)) γ G (thickening ρ S) :=
    (hG.mono hρS).of_le hD hγα
  have hell : UniformlyEllipticOn S
      (fun x => A x (preciseRepresentative volume (W1p.value u) x)) lam Lam :=
    (UniformlyEllipticOn.apply_of_forall hA _).mono_set
      ((self_subset_thickening hρ S).trans hρS)
  -- `u` solves the linear equation with the coefficient frozen at its precise representative.
  have hu' : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun x => A x (preciseRepresentative volume (W1p.value u) x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x := fun φ => by
    rw [← hu φ]
    exact energyFormH1_congr_ae ((W1p.ae_eq_preciseRepresentative u).mono fun x hx => by
      rw [hx]) .rfl .rfl _ _
  obtain ⟨C, -, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
      (n := n) hβ hβ1 hβγ hq2 hβq (lam := lam) (Lam := Lam)
      (M := ↑(Kx * D ^ ((α : ℝ) - γ) + L * (Cv * D ^ ((γ₀ : ℝ) - γ))) * ρ ^ (γ : ℝ))
  exact ⟨_, h hell haK hGK le_rfl (hf.mono_measure (Measure.restrict_mono hρS le_rfl)) hu' hρ hρS⟩

/-- **Interior `C^{1,β}` regularity for quasilinear divergence-form equations.** Let `Ω ⊆ ℝⁿ⁺¹`
be open and let `A(x, s)` be a field of matrices, uniformly elliptic with constants `λ, Λ` in `x`
for every `s`, `α`-Hölder in `x` with a constant independent of `s`, and Lipschitz in `s` with a
constant independent of `x`, where `0 < α`. Let `G` be `α`-Hölder on `Ω` and `f ∈ L^q(Ω)`
with `q ≥ 2`. If `u ∈ H¹(Ω)` is a weak solution of the quasilinear equation

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, then the
precise representative of `∇u` is `β`-Hölder on every bounded set `S` with `S_R ⊆ Ω` for some
`R > 0`, for every `0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, where
`(n + 1) / ∞ = 0`; such `β` exist exactly when `q > n + 1`. These are the exponents of the
linear estimate with Hölder coefficients
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`
in `TauCeti.PDE`).
The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq
    (hq2 : 2 ≤ q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hG : HolderOnWith KG α G Omega) (hf : MemLp f q (volume.restrict Omega))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      (∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Omega, f x * φ x)
    {β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : Bornology.IsBounded S) {R : ℝ}
    (hR : 0 < R) (hRS : thickening R S ⊆ Omega) :
    ∃ C : ℝ≥0, HolderOnWith C β (preciseRepresentative volume (W1p.gradient u)) S := by
  have hα : 0 < α := hβ.trans_le hβα
  -- The datum costs `(n + 1) / q < 1` of a derivative, so `q > n + 1`.
  have hβ' : (0 : ℝ) < β := hβ
  have hqn : (n : ℝ≥0∞) + 1 < q := by
    rcases eq_or_ne q ⊤ with rfl | hqt
    · simp
    · have hq0 : 0 < q.toReal := ENNReal.toReal_pos (by rintro rfl; simp at hq2) hqt
      refine (ENNReal.toReal_lt_toReal (by simp) hqt).1 ?_
      rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one]
      exact (div_lt_one hq0).1 (by linarith)
  -- De Giorgi: `ū` is `γ₀`-Hölder on `S_{R/2}`.
  obtain ⟨γ₀, C₀, hγ₀, h₀⟩ :=
    exists_holderOnWith_preciseRepresentative_value hα hq2 hqn hA hAx hAs hG hf hu hS hR hRS
  have hU : Bornology.IsBounded (thickening (R / 4) S) := hS.thickening
  have hUΩ : thickening (R / 4) S ⊆ Omega :=
    (thickening_mono (by linarith) S).trans hRS
  have hUU : thickening (R / 4) (thickening (R / 4) S) ⊆ thickening (R / 2) S :=
    (thickening_thickening_subset _ _ _).trans (by rw [show R / 4 + R / 4 = R / 2 by ring])
  -- First Schauder pass, on `S_{R/4}`, with the small positive exponent `β₁ = min γ₀ β`.
  have hβ₁0 : 0 < min γ₀ β := lt_min hγ₀ hβ
  obtain ⟨C₁, h₁⟩ := exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_value
    hq2 hA hAx hAs hG hf hu (min_le_left γ₀ β) ((min_le_right γ₀ β).trans hβα) hβ₁0
    ((min_le_right γ₀ β).trans_lt hβ1) le_rfl
    ((NNReal.coe_le_coe.2 (min_le_right γ₀ β)).trans hβq) hU (by positivity)
    (hUU.trans ((thickening_mono (by linarith) S).trans hRS)) (h₀.mono hUU)
  -- The Lipschitz step: `ū` is `β`-Hölder on `S_{R/8}`.
  obtain ⟨M₁, hM₁⟩ :=
    ((h₀.mono (thickening_mono (by linarith) S)).isBounded_image hU).exists_norm_le
  obtain ⟨M₂, hM₂⟩ := (h₁.isBounded_image hU).exists_norm_le
  obtain ⟨C₂, h₂⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_forall_norm_le u
    (by positivity) hUΩ (forall_mem_image.1 hM₁) (forall_mem_image.1 hM₂) hβ1.le
  -- Second Schauder pass, on `S`, with the exponent `β`.
  have hR8 : R / 4 / 2 = R / 8 := by ring
  rw [hR8] at h₂
  exact exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_value hq2 hA hAx
    hAs hG hf hu le_rfl hβα hβ hβ1 le_rfl hβq hS (by positivity)
    ((thickening_mono (by linarith) S).trans hRS) h₂

/-- **The `C^{1,α}` step, near a point.** If the data `f` of the quasilinear equation is
`α`-Hölder near every point of `Ω`, the precise representative of `∇u` is `α`-Hölder near every
point of `Ω`. The equation is restricted to a ball on which `f` is bounded, where the interior
`C^{1,β}` theorem applies with `q = ∞`. -/
private theorem exists_mem_nhds_holderOnWith_preciseRepresentative_gradient (hα : 0 < α)
    (hα1 : α < 1)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ C : ℝ≥0, HolderOnWith C α f (ball x r))
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Omega) :
    ∃ T ∈ 𝓝 x, ∃ C : ℝ≥0, HolderOnWith C α
      (preciseRepresentative volume (W1p.gradient u)) T := by
  obtain ⟨rf, hrf, Cf, hCf⟩ := hfH x hx
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
  set R := min rf ρ
  have hR : 0 < R := lt_min hrf hρ
  let B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x R, isOpen_ball⟩
  have hBΩ : B ≤ Omega := (ball_subset_ball (min_le_right _ _)).trans hρΩ
  -- The datum is Hölder, hence bounded, on `B`.
  have hfB : HolderOnWith Cf α f B := hCf.mono (ball_subset_ball (min_le_left _ _))
  obtain ⟨M, hM⟩ := (hfB.isBounded_image isBounded_ball).exists_norm_le
  have hftop : MemLp f ⊤ (volume.restrict B) :=
    memLp_top_of_bound ((hfB.continuousOn hα).aestronglyMeasurable
      B.isOpen.measurableSet) M (ae_restrict_of_forall_mem B.isOpen.measurableSet
        (forall_mem_image.1 hM))
  -- The restriction of `u` to `B` solves the restricted equation against test functions.
  have huB : ∀ φ : 𝓓(B, ℝ), energyFormH1 (fun y => A y (W1p.value (W1p.restrictL hBΩ u) y)) 0 0
      (W1p.restrictL hBΩ u) (W1p.ofTestFunctionₗ volume B 2 φ) =
      (∫ y in B, ⟪(0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y,
        ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ) + ∫ y in B, f y * φ y := by
    intro φ
    rw [energyFormH1_congr_ae (a' := fun y => A y (W1p.value u y))
      ((W1p.value_restrictL_ae hBΩ u).mono fun y hy => by rw [hy]) .rfl .rfl,
      energyFormH1_restrictL_eq_setIntegral hBΩ hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add]
    exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun y hy =>
      congrArg (f y * ·) hy)
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq
      (Omega := B) (q := ⊤) (G := 0) (KG := 0) le_top (fun s => (hA s).mono_set hBΩ)
      (fun s => (hAx s).mono hBΩ) (fun y hy => hAs y (hBΩ hy)) (HolderWith.zero.holderOnWith _)
      hftop huB (β := α) hα hα1 le_rfl (by simpa using hα1.le) isBounded_ball (half_pos hR)
      (S := ball x (R / 2)) ((thickening_ball x _ _).trans_eq (by rw [add_halves, Opens.coe_mk]))
  refine ⟨ball x (R / 2), ball_mem_nhds x (half_pos hR), C, hC.congr fun y hy => ?_⟩
  exact preciseRepresentative_congr_ae_nhds
    (B.isOpen.mem_nhds (ball_subset_ball (half_le_self hR.le) hy)) (W1p.gradient_restrictL_ae hBΩ u)

/-- **Interior `C^{2,α}` regularity for quasilinear divergence-form equations.** Let `Ω ⊆ ℝⁿ⁺¹` be
open, let `0 < α < 1`, and let `A(x, s)` be a field of matrices satisfying the hypotheses of the
interior `C^{1,β}` theorem
(`exists_holderOnWith_preciseRepresentative_gradient_of_forall_energyFormH1_quasilinear_eq`):
uniformly elliptic with constants `λ, Λ` in `x` for every `s`, `α`-Hölder in `x` with a constant
independent of `s`, and Lipschitz in `s` with a constant independent of `x`. Suppose moreover that
every entry of `A`, as a function of `(x, s)`, is `C¹` on `Ω × ℝ` with derivative `α`-Hölder near
every point of `Ω × ℝ`, and that `f ∈ L²(Ω)` is `α`-Hölder near every point of `Ω`. If
`u ∈ H¹(Ω)` is a weak solution of

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, then `u` agrees almost everywhere
on `Ω` with a function `g` that is `C²` on `Ω` and whose second derivative is `α`-Hölder on every
compact subset of `Ω`. No boundary condition is imposed on `u` and nothing is assumed about `∂Ω`.
-/
theorem
    exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_energyFormH1_quasilinear_eq
    (hα : 0 < α) (hα1 : α < 1)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s)) Omega)
    (hAs : ∀ x ∈ Omega, LipschitzWith L fun s => matrixBilinearForm (A x s))
    (hA1 : ∀ i j, ContDiffOn ℝ 1 (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => A p.1 p.2 i j)
      ((Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ×ˢ univ))
    (hdA : ∀ p ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ×ˢ univ, ∃ r > 0, ∃ C : ℝ≥0,
      ∀ i j, HolderOnWith C α
        (fderiv ℝ fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => A q.1 q.2 i j) (ball p r))
    (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ C : ℝ≥0, HolderOnWith C α f (ball x r))
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 2 g Omega ∧
      W1p.value u =ᵐ[volume.restrict Omega] g ∧
      ∀ K ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsCompact K →
        ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ 2 g) K := by
  -- The `C^{1,α}` step: `u` has a `C¹` representative `g₁` with locally `α`-Hölder derivative.
  have hloc := fun x (hx : x ∈ Omega) =>
    exists_mem_nhds_holderOnWith_preciseRepresentative_gradient hα hα1 hA hAx hAs hfH hu hx
  have hP : ContinuousOn (preciseRepresentative volume (W1p.gradient u)) Omega := fun x hx => by
    obtain ⟨T, hT, C, hC⟩ := hloc x hx
    exact ((hC.continuousOn hα).continuousAt hT).continuousWithinAt
  obtain ⟨g₁, hg₁, hug₁, hdg₁⟩ :=
    W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative u le_rfl hP
  have hdg₁H : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ C : ℝ≥0, HolderOnWith C α (fderiv ℝ g₁) T :=
    fun x hx => by
      obtain ⟨T, hT, C, hC⟩ := hloc x hx
      exact ⟨T ∩ Omega, Filter.inter_mem hT (Omega.isOpen.mem_nhds hx), _,
        ((innerSL ℝ).lipschitzWith.comp_holderOnWith (hC.mono inter_subset_left)).congr
          fun y hy => (hdg₁ y hy.2).fderiv.symm⟩
  -- The frozen coefficient `A(·, g₁)` is `C^{1,α}`, by the superposition rule.
  have ha : ∀ i j, ContDiffOn ℝ 1 (fun x => A x (g₁ x) i j) Omega := fun i j =>
    (hA1 i j).comp (contDiffOn_id.prodMk hg₁) fun x hx => ⟨hx, mem_univ _⟩
  have hda : ∀ x ∈ Omega, ∃ r > 0, ∃ C : ℝ≥0, ∀ i j,
      HolderOnWith C α (fderiv ℝ (fun y => A y (g₁ y) i j)) (ball x r) := by
    intro x hx
    choose T hT C hC using fun i j =>
      exists_mem_nhds_holderOnWith_fderiv_superposition (A := fun y s => A y s i j)
        Omega.isOpen (hA1 i j) (fun p hp => by
          obtain ⟨r, hr, C, hC⟩ := hdA p hp
          exact ⟨ball p r, ball_mem_nhds p hr, C, hC i j⟩) hg₁ hdg₁H le_rfl le_rfl hx
    obtain ⟨r, hr, hrT⟩ := nhds_basis_ball.mem_iff.1
      (Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hT i j)
    refine ⟨r, hr, ∑ i, ∑ j, C i j, fun i j => ((hC i j).mono
      (hrT.trans ((iInter_subset _ i).trans (iInter_subset _ j)))).mono_const ?_⟩
    exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, C i j) (fun _ _ => zero_le)
        (Finset.mem_univ i))
  -- `u` solves the linear equation with this coefficient, and the linear theorem applies.
  refine exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn hα hα1
    (UniformlyEllipticOn.apply_of_forall hA g₁) ha hda hf hfH fun v => ?_
  rw [← hu v]
  exact energyFormH1_congr_ae (hug₁.mono fun x hx => by simp only [hx]) .rfl .rfl _ _

end PDE

end TauCeti
