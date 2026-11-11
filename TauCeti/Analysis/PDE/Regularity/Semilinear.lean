/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Classical
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Holder
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# Smoothness of continuous weak solutions of semilinear Poisson equations

Let `F : E → ℝ → ℝ` be smooth on `Ω × ℝ` for an open set `Ω` of a finite-dimensional real inner
product space `E`. This file proves that a weak solution `u ∈ H¹(Ω)` of the semilinear equation

`Δu = F(x, u)` in `Ω`,

that is `∫_Ω ⟪∇u, ∇φ⟫ = -∫_Ω F(x, u) φ` for every test function `φ`, is smooth as soon as it has
a representative `g` that is continuous on `Ω`: then `g` itself is smooth on `Ω` and solves the
equation at every point
(`TauCeti.PDE.contDiffOn_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg`).
The continuity hypothesis is where the nonlinearity enters: it makes `F(x, u)` locally bounded,
and for nonlinearities of exponential growth in dimension two it follows from Trudinger's
inequality. No boundary condition and no regularity of `∂Ω` is assumed.

## The bootstrap

The argument climbs the classical regularity ladder.

* **Hölder continuity.** The right-hand side `F(x, g)` is continuous, hence in `Lʳ` on compact
  sets for every `r`, and De Giorgi's theorem with a right-hand side
  (`TauCeti.PDE.exists_forall_exists_holderOnWith_preciseRepresentative_of_forall_memLp`) makes
  `g` locally `α`-Hölder for some `α ∈ (0, 1]`.
* **`C²`.** Then `F(x, g)` is locally Hölder (`ContDiffAt.exists_holderOnWith_comp_prodMk`), and
  the interior `C²` regularity of Poisson's equation with Hölder data
  (`TauCeti.PDE.contDiffOn_two_and_neg_laplacian_eq_of_forall_testFunction`) makes `g` a `C²`
  classical solution.
* **`C^∞`.** A `C²` function whose Laplacian is `C^{k+1}` is `C^{k+2}`
  (`TauCeti.PDE.contDiffOn_add_two_of_contDiffOn_laplacian`). For the step, a directional derivative
  `ψ = ∂ₑg` is `C¹` and solves the differentiated equation `Δψ = ∂ₑ(Δg)` weakly
  (`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_neg_fderiv_laplacian`), whose
  right-hand side is `C¹` and so locally Hölder; hence `ψ` is `C²`, the induction hypothesis
  applies to `ψ`, and `g` gains a derivative. Since `Δg = F(x, g)` is as smooth as `g`, this
  gives `g ∈ C^k` for every `k`.

The coordinate statements are for `ℝ^{n+1}`, where the Sobolev and Schauder theory lives; the
semilinear theorem is transported to `E` through the coordinates of an orthonormal basis.

## Main declarations

* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_neg_fderiv_laplacian`: a directional
  derivative of a `C²` function with `C¹` Laplacian solves the differentiated equation weakly.
* `TauCeti.PDE.contDiffOn_add_two_of_contDiffOn_laplacian`: a `C²` function with `C^{k+1}`
  Laplacian is `C^{k+2}`.
* `TauCeti.PDE.contDiffOn_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg`: a continuous
  representative of a weak solution of `Δu = F(x, u)` with smooth `F` is a smooth classical
  solution.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 4.6 (interior `C²` regularity with Hölder data), Theorem 6.17 (higher interior
  regularity) and Theorem 8.24 (De Giorgi's interior Hölder estimate).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1 (differentiating the equation).
-/

public section

noncomputable section

open InnerProductSpace Laplacian LineDeriv MeasureTheory Metric Module Set TopologicalSpace
open TauCeti.MeasureTheory
open scoped ContDiff Distributions Gradient InnerProductSpace NNReal Topology

namespace TauCeti.PDE

variable {n : ℕ}

/-! ### Higher regularity for Poisson's equation -/

/-- **The differentiated equation.** Let `g` be `C²` on an open set `U` with `Δg` of class `C¹`
on `U`, and let `B ⊆ U` be open. If `G, D ∈ H¹(B)` are represented by `g` and by its directional
derivative `∂ₑg`, then `D` solves `-Δ(∂ₑg) = -∂ₑ(Δg)` weakly in `B`:
`∫_B ⟪∇D, ∇φ⟫ = -∫_B ∂ₑ(Δg) φ` for every test function `φ` on `B`. Only one derivative of `∂ₑg`
is used, so `∂ₑg` need not be `C²`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_setIntegral_neg_fderiv_laplacian
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hg : ContDiffOn ℝ 2 g U)
    (hΔ : ContDiffOn ℝ 1 (Δ g) U) {B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hBU : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ U) {G D : W1p volume B 2}
    (e : EuclideanSpace ℝ (Fin (n + 1))) (hG : W1p.value G =ᵐ[volume.restrict B] g)
    (hD : W1p.value D =ᵐ[volume.restrict B] fun x => fderiv ℝ g x e) (φ : 𝓓(B, ℝ)) :
    energyFormH1 (fun _ => 1) 0 0 D (W1p.ofTestFunctionₗ volume B 2 φ) =
      ∫ x in B, -fderiv ℝ (Δ g) x e * φ x := by
  have hBm := B.isOpen.measurableSet
  have hdiff : ∀ {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, ContDiffOn ℝ 1 f U →
      ∀ x ∈ (B : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        HasLineDerivAt ℝ f (fderiv ℝ f x e) x e := fun hf x hx =>
    ((hf.differentiableOn one_ne_zero).differentiableAt
      (hU.mem_nhds (hBU hx))).hasFDerivAt.hasLineDerivAt e
  have hcont : ∀ {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, ContDiffOn ℝ 1 f U →
      ContinuousOn (fun x => fderiv ℝ f x e) B := fun hf =>
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hBU
  have hg1 : ContDiffOn ℝ 1 g U := hg.of_le one_le_two
  -- `∂ₑg` is the weak derivative of `g` on `B`, and `∂ₑ(Δg)` that of `Δg`.
  have hd : HasWeakLineDerivOn volume B (W1p.value G) (W1p.value D) e :=
    ((hasWeakLineDerivOn_of_hasLineDerivAt ((hg1.continuousOn.mono hBU).locallyIntegrableOn hBm)
      ((hcont hg1).locallyIntegrableOn hBm) (hdiff hg1)).congr_ae hG.symm).congr_ae_deriv hD.symm
  have hΔd : HasWeakLineDerivOn volume B (Δ g) (fun x => fderiv ℝ (Δ g) x e) e :=
    hasWeakLineDerivOn_of_hasLineDerivAt ((hΔ.continuousOn.mono hBU).locallyIntegrableOn hBm)
      ((hcont hΔ).locallyIntegrableOn hBm) (hdiff hΔ)
  -- `a(D, φ) = -a(G, ∂ₑφ) = ∫_B ∂ₑφ Δg = -∫_B ∂ₑ(Δg) φ`.
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn (A := 1) hd φ,
    energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_divMatrixGradient (hg.mono hBU) hG, neg_neg]
  have hΔφ := hΔd.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    ← setIntegral_smul_eq_integral_smul, ← integral_neg] at hΔφ
  simp only [smul_eq_mul] at hΔφ
  rw [← setIntegral_congr_fun hBm fun x hx => by
    rw [TestFunction.lineDerivOp_apply, divMatrixGradient_one_eq_laplacian (hg.mono hBU) hx], hΔφ]
  exact setIntegral_congr_fun hBm fun x _ => by ring

/-- **Higher interior regularity for Poisson's equation.** A function that is `C²` on an open set
`Ω ⊆ ℝ^{n+1}` and whose Laplacian is `C^{k+1}` on `Ω` is `C^{k+2}` on `Ω`. No boundary condition
and no regularity of `∂Ω` is assumed. -/
theorem contDiffOn_add_two_of_contDiffOn_laplacian {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hg : ContDiffOn ℝ 2 g Omega) {k : ℕ}
    (hΔ : ContDiffOn ℝ (k + 1) (Δ g) Omega) :
    ContDiffOn ℝ (k + 2) g Omega := by
  induction k generalizing g Omega with
  | zero => simpa using hg
  | succ k ih =>
    have hgk : ContDiffOn ℝ (k + 2) g Omega := ih hg (hΔ.of_le (by norm_cast; omega))
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) + 2 = ((k + 2 : ℕ) : WithTop ℕ∞) + 1 by norm_cast]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Omega.isOpen).2
      ⟨hg.differentiableOn two_ne_zero, by simp, contDiffOn_clm_apply.2 fun e => ?_⟩
    -- The directional derivative `ψ = ∂ₑg` is `C¹` and solves `Δψ = ∂ₑ(Δg)` weakly, with a `C¹`
    -- right-hand side; so `ψ` is a `C²` classical solution, and the induction hypothesis applies.
    set ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => fderiv ℝ g x e
    have hψ1 : ContDiffOn ℝ 1 ψ Omega :=
      (hgk.fderiv_of_isOpen Omega.isOpen (by norm_cast; omega)).clm_apply contDiffOn_const
    have hΔψ : ContDiffOn ℝ (k + 1) (fun x => fderiv ℝ (Δ g) x e) Omega :=
      (hΔ.fderiv_of_isOpen Omega.isOpen (by norm_cast)).clm_apply contDiffOn_const
    have hloc : ∀ x ∈ Omega, ∃ B : Opens (EuclideanSpace ℝ (Fin (n + 1))), x ∈ B ∧
        B ≤ Omega ∧ ContDiffOn ℝ 2 ψ B ∧ ∀ y ∈ B, Δ ψ y = fderiv ℝ (Δ g) y e := by
      intro x hx
      obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
      let B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x ε, isOpen_ball⟩
      have hBΩ : B ≤ Omega := ball_subset_closedBall.trans hεΩ
      obtain ⟨G, hG, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
        (mu := volume) (Omega := B) (p := 2) Omega.isOpen (hg.of_le one_le_two)
        (isCompact_closedBall x ε) ball_subset_closedBall hεΩ
      obtain ⟨D, hD, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
        (mu := volume) (Omega := B) (p := 2) Omega.isOpen hψ1
        (isCompact_closedBall x ε) ball_subset_closedBall hεΩ
      have hHolder : ∀ y ∈ B, ∃ T ∈ 𝓝 y, ∃ K : ℝ≥0,
          HolderOnWith K (1 / 2) (fun z => -fderiv ℝ (Δ g) z e) T := fun y hy =>
        ((hΔψ.of_le (by norm_cast; omega)).neg.contDiffAt
          (Omega.isOpen.mem_nhds (hBΩ hy))).exists_holderOnWith (by norm_num)
      obtain ⟨hψ2, hψΔ⟩ := contDiffOn_two_and_neg_laplacian_eq_of_forall_testFunction
        (α := 1 / 2) (by norm_num) (by norm_num) (hψ1.continuousOn.mono hBΩ) hD hHolder
        fun φ => energyFormH1_ofTestFunctionₗ_eq_setIntegral_neg_fderiv_laplacian Omega.isOpen
          hg (hΔ.of_le (by norm_cast; omega)) hBΩ e hG hD φ
      exact ⟨B, mem_ball_self hε, hBΩ, hψ2, fun y hy => neg_injective (hψΔ y hy)⟩
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨B, hxB, hBΩ, hψ2, hψΔ⟩ := hloc x hx
    refine ⟨B, B.isOpen, hxB, ?_⟩
    rw [inter_eq_right.2 hBΩ]
    exact_mod_cast ih (Omega := B) hψ2 ((hΔψ.mono hBΩ).congr hψΔ)

/-! ### Semilinear equations -/

/-- The first two rungs of the bootstrap, in the coordinates `ℝ^{n+1}`: for a continuous
representative `g` of a weak solution of `Δu = F(x, u)` with `F` of class `C¹`, the data
`-F(x, g)` is locally Hölder with an exponent `β < 1`. De Giorgi's theorem makes `g` locally
`α`-Hölder, which is lowered to `α / 2 < 1` by composing with the identity, `(1 / 2)`-Hölder near
each point, and `F` is locally Lipschitz. -/
private theorem exists_forall_exists_holderOnWith_neg_of_energyFormH1_eq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (Omega ×ˢ univ)) {u : W1p volume Omega 2}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hg : ContinuousOn g Omega)
    (hug : W1p.value u =ᵐ[volume.restrict Omega] g)
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, -F x (g x) * φ x) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 1 ∧ ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0,
      HolderOnWith K β (fun y => -F y (g y)) T := by
  have hmaps : MapsTo (fun x => (x, g x)) Omega (Omega ×ˢ univ) := fun x hx => ⟨hx, mem_univ _⟩
  obtain ⟨α, hα, hα1, hhol⟩ :=
    exists_forall_exists_holderOnWith_preciseRepresentative_of_forall_memLp
      (ι := Fin (n + 1)) (mu := volume) (lam := 1) (Lam := 1) (r := n + 2)
      (by exact_mod_cast (show 2 ≤ n + 2 by omega))
      (by simp only [Fintype.card_fin]; push_cast; linarith)
  have hFc : ContinuousOn (fun x => -F x (g x)) Omega :=
    (hF.continuousOn.comp (continuousOn_id.prodMk hg) hmaps).neg
  have heq : EqOn (preciseRepresentative volume (W1p.value u)) g Omega :=
    eqOn_preciseRepresentative_of_continuousOn Omega.isOpen
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn hug hg
  refine ⟨α * (1 / 2), mul_pos hα (by norm_num),
    (mul_le_of_le_one_left (by positivity) hα1).trans_lt (by norm_num), fun x hx => ?_⟩
  -- `g` is the precise representative of `u` on `Ω`, which is `α`-Hölder near `x`.
  obtain ⟨T, hT, C, hC⟩ := hhol (f := fun x => -F x (g x))
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const
    (fun K hK hKΩ => (hFc.mono hKΩ).memLp_restrict_of_subset_isCompact hK hK.measurableSet
      subset_rfl _) hu x hx
  have hgT : HolderOnWith C α g (T ∩ Omega) := fun y hy z hz => by
    rw [← heq hy.2, ← heq hz.2]
    exact hC y hy.1 z hz.1
  obtain ⟨S, hS, D, hD⟩ := (contDiffAt_id (𝕜 := ℝ) (x := x)).exists_holderOnWith
    (show (1 / 2 : ℝ≥0) ≤ 1 by norm_num)
  have hgS : HolderOnWith (C * D ^ (α : ℝ)) (α * (1 / 2)) g (S ∩ (T ∩ Omega)) :=
    hgT.comp (hD.mono inter_subset_left) fun y hy => hy.2
  exact ((hF.contDiffAt ((Omega.isOpen.prod isOpen_univ).mem_nhds (hmaps hx))).neg
    ).exists_holderOnWith_comp_prodMk (mul_le_one' hα1 (by norm_num)) hgS
    (Filter.inter_mem hS (Filter.inter_mem hT (Omega.isOpen.mem_nhds hx)))
    (hg.continuousAt (Omega.isOpen.mem_nhds hx))

/-- The semilinear theorem in the coordinates `ℝ^{n+1}`, for the energy form of the identity
matrix. -/
private theorem contDiffOn_and_laplacian_eq_of_energyFormH1_eq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Omega ×ˢ univ)) {u : W1p volume Omega 2}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hg : ContinuousOn g Omega)
    (hug : W1p.value u =ᵐ[volume.restrict Omega] g)
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, -F x (g x) * φ x) :
    ContDiffOn ℝ ∞ g Omega ∧ ∀ x ∈ Omega, Δ g x = F x (g x) := by
  -- Hölder data make `g` a `C²` classical solution.
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_forall_exists_holderOnWith_neg_of_energyFormH1_eq
    (hF.of_le (by exact_mod_cast le_top)) hg hug hu
  obtain ⟨hg2, hΔ⟩ :=
    contDiffOn_two_and_neg_laplacian_eq_of_forall_testFunction hβ hβ1 hg hug hdata hu
  have hΔeq : ∀ x ∈ Omega, Δ g x = F x (g x) := fun x hx => neg_injective (hΔ x hx)
  -- If `g` is `C^{k+2}`, then so is `Δg = F(x, g)`, and higher regularity for Poisson's equation
  -- makes `g` a `C^{k+3}` function.
  have hk : ∀ k : ℕ, ContDiffOn ℝ (k + 2) g Omega := by
    intro k
    induction k with
    | zero => simpa using hg2
    | succ k ih =>
      have hFg : ContDiffOn ℝ (k + 2) (fun x => F x (g x)) Omega :=
        (hF.of_le (by simp)).comp (contDiffOn_id.prodMk ih) fun x hx => ⟨hx, mem_univ _⟩
      exact contDiffOn_add_two_of_contDiffOn_laplacian hg2
        ((hFg.congr hΔeq).of_le (by push_cast; rfl))
  exact ⟨contDiffOn_infty.2 fun k => (hk k).of_le (by exact_mod_cast (by omega : k ≤ k + 2)),
    hΔeq⟩

/-- **Smoothness of continuous weak solutions of semilinear Poisson equations.** Let `E` be a
nonzero finite-dimensional real inner product space, `Ω ⊆ E` open, and `F : E → ℝ → ℝ` smooth on
`Ω × ℝ`. Let `u ∈ H¹(Ω)` solve `Δu = F(x, u)` weakly in `Ω`, that is

`∫_Ω ⟪∇u, ∇φ⟫ = -∫_Ω F(x, u) φ`

for every test function `φ` on `Ω`. If `g` is a representative of `u` that is continuous on `Ω`,
then `g` is smooth on `Ω` and `Δg = F(x, g)` at every point of `Ω`. No growth condition on `F` and
no boundary condition on `u` is assumed. -/
theorem contDiffOn_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] {Omega : Opens E} {F : E → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Omega ×ˢ univ)) {u : W1p volume Omega 2}
    {g : E → ℝ} (hg : ContinuousOn g Omega) (hug : W1p.value u =ᵐ[volume.restrict Omega] g)
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, ⟪W1p.gradient u x, ∇ (φ : E → ℝ) x⟫_ℝ =
        -∫ x in Omega, F x (W1p.value u x) * φ x) :
    ContDiffOn ℝ ∞ g Omega ∧ ∀ x ∈ Omega, Δ g x = F x (g x) := by
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Module.finrank_pos.ne'
  -- Orthonormal coordinates `e : E ≃ ℝ^{m+1}`, with inverse `G`, and `Ω' = e(Ω)`.
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hm)).repr
  let G : EuclideanSpace ℝ (Fin (m + 1)) ≃ᵃⁱ[ℝ] E := e.symm.toAffineIsometryEquiv
  have hG : ∀ y, G y = e.symm y := fun y => rfl
  have heG : ∀ x, G (e x) = x := fun x => by simp [hG]
  let Ω' : Opens (EuclideanSpace ℝ (Fin (m + 1))) :=
    ⟨G ⁻¹' Omega, Omega.isOpen.preimage G.continuous⟩
  have hΩ : (Omega : Set E) = e ⁻¹' Ω' := by ext x; simp [Ω', heG]
  have hGm : MeasurePreserving G volume volume := by
    simpa [G] using e.symm.measurePreserving
  have hres : MeasurePreserving G (volume.restrict Ω') (volume.restrict Omega) :=
    hGm.restrict_preimage Omega.isOpen.measurableSet
  set u' := W1p.compAffineIsometryEquivL G (U := Ω') rfl u
  have hug' : (fun y => W1p.value u (G y)) =ᵐ[volume.restrict Ω'] g ∘ G :=
    hres.quasiMeasurePreserving.ae_eq_comp hug
  -- The weak equation on `Ω'` is the one on `Ω` read in the coordinates `G`.
  have hu' : ∀ φ' : 𝓓(Ω', ℝ), energyFormH1 (fun _ => 1) 0 0 u'
      (W1p.ofTestFunctionₗ volume Ω' 2 φ') = ∫ y in Ω', -F (G y) ((g ∘ G) y) * φ' y := by
    intro φ'
    have hu'' : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, ⟪W1p.gradient u x, ∇ (φ : E → ℝ) x⟫_ℝ =
        ∫ x in Omega, -F x (W1p.value u x) * φ x := fun φ => by
      simp only [neg_mul, integral_neg, hu]
    rw [energyFormH1_one_zero_zero_eq_inner, L2.inner_def]
    refine ((integral_congr_ae ?_).trans
      (W1p.setIntegral_inner_gradient_compAffineIsometryEquivL_eq_setIntegral_mul e.symm rfl u
        hu'' φ')).trans (integral_congr_ae ?_)
    · filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω') 2 φ'] with y hφy
      rw [W1p.gradient_ofTestFunctionₗ, hφy]
    · filter_upwards [hug'] with y hy
      simp only [← hG, hy, Function.comp_apply]
  have hF' : ContDiffOn ℝ ∞ (Function.uncurry fun y => F (G y)) (Ω' ×ˢ univ) := by
    have hmap : ContDiff ℝ ∞ (Prod.map G (id : ℝ → ℝ)) := by
      rw [show (G : EuclideanSpace ℝ (Fin (m + 1)) → E) = e.symm from funext hG]
      exact e.symm.contDiff.prodMap contDiff_id
    exact hF.comp hmap.contDiffOn fun p hp => ⟨hp.1, mem_univ _⟩
  obtain ⟨hsmooth, hΔ⟩ := contDiffOn_and_laplacian_eq_of_energyFormH1_eq hF'
    (hg.comp G.continuous.continuousOn fun y hy => hy)
    ((W1p.value_compAffineIsometryEquivL_ae G (U := Ω') rfl u).trans hug') hu'
  -- Pull back along `e`: `g = (g ∘ G) ∘ e`.
  have hge : g = (g ∘ G) ∘ e := funext fun x => by simp [heG]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hge]
    exact hsmooth.comp e.contDiff.contDiffOn fun x hx => by rwa [hΩ] at hx
  · have hx' : e x ∈ Ω' := by
      have hx : x ∈ (Omega : Set E) := hx
      rwa [hΩ] at hx
    rw [hge, laplacian_comp_linearIsometryEquiv_right, Function.comp_apply, hΔ _ hx']
    simp [heG]

end TauCeti.PDE
