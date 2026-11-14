/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex

/-!
# Weierstrass preparation and division for Nash germs

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, where `σ` indexes
finitely many parameter coordinates and `Unit` the distinguished vertical coordinate, and suppose
that the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d` at `t₀`.
This file proves that `f` factors near `p₀` as `P_x (t - t₀) * u (x, t)`, where `P_x` is the monic
polynomial `TauCeti.Polynomial.monicOfCoeff (c · x)` of degree `d` whose lower coefficients `c i`
are Nash germs at `x₀` vanishing at `x₀`, and `u` is a Nash germ nonvanishing at `p₀`
(`TauCeti.IsNashAt.exists_weierstrassPreparation`). Moreover, any Nash germ `g` at `p₀` can be
divided by `P_x (t - t₀)` — or directly by `f` — with Nash quotient germ `q` and Nash remainder
coefficients `r : Fin d → (σ → ℝ) → ℝ` (`TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`,
`TauCeti.IsNashAt.exists_weierstrassDivision`).

Nash Weierstrass preparation and division reduce the local geometry of Nash zero sets and Nash
ideals in `σ ⊕ Unit → ℝ` to polynomials in one variable with Nash coefficients over the parameter
space `σ → ℝ`. In particular, discriminants and subresultants of Nash Weierstrass polynomials
project Nash hypersurface singularities to lower-dimensional parameter loci, and Weierstrass
division underlies Noetherianity and local normal decomposition for Nash germs.

To show that any real analytic Weierstrass preparation `(c, u)` of a Nash germ `f` consists of Nash
germs (`TauCeti.IsNashAt.of_weierstrassPreparation`), we complexify `f`, `c`, and `u` near `p₀`. On
a polydisc where the complexified unit has no zeros and all `d` complex roots of `P_x` remain
confined by continuity on the symmetric power (`Sym.eventually_exists_ofFn_eq_coeffEquiv_symm`), an
ordered tuple `z : Fin d → ℂ` enumerates the roots of `P_x` with multiplicity exactly when the
iterated complex vertical derivatives of the complexification of `f` vanish up to each cluster size
(`Polynomial.Monic.prod_X_sub_C_eq_iff_iteratedDeriv_eq_zero`). Realification of vertical Nash
derivatives (`TauCeti.IsNashAt.iteratedDeriv_sumElim`, `TauCeti.IsNashAt.complexification_re_im`),
complex Vieta equations (`TauCeti.isSemialgebraic_setOf_eval_ofReal_eq_zero`), and
Tarski–Seidenberg projection (`TauCeti.IsSemialgebraic.setOf_exists_sumElim`) make the coefficient
graph locally semialgebraic, hence Nash; exact analytic division (`TauCeti.IsNashAt.of_mul`) then
makes `u` Nash. Nash Weierstrass division follows by preparing the one-parameter deformation
`P_x (t - t₀) + ε * g (x, t)` at `ε = 0` and differentiating with respect to `ε`.

## Main results

* `TauCeti.IsNashAt.of_weierstrassPreparation`: any real analytic Weierstrass preparation of a
  Nash germ has Nash coefficients and Nash unit.
* `TauCeti.IsNashAt.exists_weierstrassPreparation`: **Nash Weierstrass preparation theorem.**
* `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`: **Nash Weierstrass division** by a
  Nash Weierstrass polynomial.
* `TauCeti.IsNashAt.of_weierstrassDivision_monicOfCoeff`: any real analytic Weierstrass division
  of a Nash germ by a Nash Weierstrass polynomial has Nash quotient and remainder coefficients.
* `TauCeti.IsNashAt.exists_weierstrassDivision`: **Nash Weierstrass division theorem** for a Nash
  divisor of finite vertical vanishing order.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Sections 8.1–8.2.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2.
-/

public section

open Filter Metric MvPolynomial Polynomial Set Topology

namespace TauCeti

variable {σ : Type*} [Fintype σ]

/-! ### Semialgebraicity of the Weierstrass coefficient graph -/

section PreparationAux

/-- Holomorphic complexification of `f` together with semialgebraic zero loci for its first `d`
complex vertical derivatives on a common open neighbourhood in doubled real coordinates. -/
private theorem exists_complexification_verticalIteratedDeriv_zeroSets
    {f : (σ ⊕ Unit → ℝ) → ℝ} {p₀ : σ ⊕ Unit → ℝ} (hf : IsNashAt f p₀) (d : ℕ) :
    ∃ ρ > (0 : ℝ), ∃ F : (σ ⊕ Unit → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (ball (fun a ↦ (p₀ a : ℂ)) ρ) ∧
      (∀ y ∈ ball p₀ ρ, F (fun a ↦ (y a : ℂ)) = f y) ∧
      ∃ W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ),
        IsOpen W ∧ complexToRealPi (σ ⊕ Unit) (fun a ↦ (p₀ a : ℂ)) ∈ W ∧
        IsSemialgebraic W ∧
        ∀ k : Fin d, IsSemialgebraic (W ∩ {a |
          iteratedDeriv (k : ℕ) (fun w ↦ F (Sum.elim
            ((complexToRealPi (σ ⊕ Unit)).symm a ∘ Sum.inl) (fun _ ↦ w)))
            ((complexToRealPi (σ ⊕ Unit)).symm a (Sum.inr ())) = 0}) := by
  let p₀ℂ : σ ⊕ Unit → ℂ := fun a ↦ (p₀ a : ℂ)
  let e := complexToRealPi (σ ⊕ Unit)
  let splitℂ : ((σ ⊕ Unit) → ℂ) ≃L[ℂ] ((σ → ℂ) × ℂ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi (R := ℂ) σ Unit (fun _ ↦ ℂ)).trans
      ((ContinuousLinearEquiv.refl ℂ (σ → ℂ)).prodCongr
        (ContinuousLinearEquiv.funUnique Unit ℂ ℂ))
  obtain ⟨ρ, hρ, F, hF, hFr, _⟩ := hf.analyticAt.exists_complexification
  let F_jet (k : ℕ) (q : σ ⊕ Unit → ℂ) : ℂ :=
    iteratedDeriv k (fun w ↦ F (Sum.elim (q ∘ Sum.inl) (fun _ ↦ w))) (q (Sum.inr ()))
  have hF_jet_an (k : ℕ) : AnalyticOnNhd ℂ (F_jet k) (ball p₀ℂ ρ) := fun q hq ↦ by
    have hcomp : AnalyticAt ℂ (F ∘ splitℂ.symm) (splitℂ q) :=
      (hF q hq).comp_of_eq (splitℂ.symm.analyticAt _) (splitℂ.symm_apply_apply q)
    have hsymm (z : (σ → ℂ) × ℂ) : splitℂ.symm z = Sum.elim z.1 (fun _ ↦ z.2) := by
      ext (s | ⟨⟩) <;> rfl
    have happ (x : σ ⊕ Unit → ℂ) : splitℂ x = (x ∘ Sum.inl, x (Sum.inr ())) := rfl
    simpa [F_jet, Function.comp_def, hsymm, happ] using
      (hcomp.iteratedDeriv_snd k).comp (splitℂ.analyticAt q)
  have hF_jet_real (k : ℕ) : ∀ y ∈ ball p₀ ρ, F_jet k (fun a ↦ (y a : ℂ)) =
      iteratedDeriv k (fun t ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ t))) (y (Sum.inr ())) := by
    intro y hy
    have hy_sum : Sum.elim (y ∘ Sum.inl) (fun _ ↦ y (Sum.inr ())) = y := by ext (s | ⟨⟩) <;> rfl
    have hslice_an : AnalyticAt ℂ
        (fun w : ℂ ↦ F (Sum.elim (fun s ↦ (y (.inl s) : ℂ)) (fun _ ↦ w))) (y (Sum.inr ())) := by
      have hline : AnalyticAt ℂ
          (fun w : ℂ ↦ Sum.elim (fun s ↦ (y (.inl s) : ℂ)) (fun _ : Unit ↦ w)) (y (Sum.inr ())) :=
        analyticAt_pi_iff.2 fun j ↦ by cases j with
          | inl _ => exact analyticAt_const
          | inr _ => exact analyticAt_id
      have hpt : (Sum.elim (fun s ↦ (y (.inl s) : ℂ))
          (fun _ : Unit ↦ (y (Sum.inr ()) : ℂ))) = fun a ↦ (y a : ℂ) := by ext (s | ⟨⟩) <;> rfl
      have hyℂ : (fun a ↦ (y a : ℂ)) ∈ ball p₀ℂ ρ := by
        rw [mem_ball, dist_pi_lt_iff hρ] at hy ⊢
        intro a
        simpa only [p₀ℂ, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using hy a
      exact (hF _ hyℂ).comp_of_eq hline hpt
    have hslice_eq : (fun s : ℝ ↦ F (Sum.elim (fun i ↦ (y (.inl i) : ℂ)) (fun _ ↦ (s : ℂ))))
        =ᶠ[𝓝 (y (Sum.inr ()))] fun s : ℝ ↦ (f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ s)) : ℂ) := by
      have hcont : Continuous (fun s : ℝ ↦ Sum.elim (y ∘ Sum.inl) (fun _ : Unit ↦ s)) :=
        continuous_pi fun j ↦ by cases j with
          | inl _ => exact continuous_const
          | inr _ => exact continuous_id
      filter_upwards [(hcont.tendsto (y (Sum.inr ()))).eventually
        (isOpen_ball.mem_nhds (hy_sum.symm ▸ hy))] with s hs
      have hcast : (Sum.elim (fun i ↦ (y (.inl i) : ℂ)) (fun _ : Unit ↦ (s : ℂ))) =
          fun a ↦ ((Sum.elim (y ∘ Sum.inl) (fun _ : Unit ↦ s) : σ ⊕ Unit → ℝ) a : ℂ) := by
        ext (i | ⟨⟩) <;> rfl
      rw [hcast, hFr _ hs]
    have hg_cd : ContDiffAt ℝ k (fun s : ℝ ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ s)))
        (y (Sum.inr ())) :=
      (hslice_an.contDiffAt (n := k)).real_of_complex.congr_of_eventuallyEq
        (hslice_eq.mono fun s hs ↦ by simpa using congrArg Complex.re hs.symm)
    dsimp only [F_jet]
    have hcomp_inl : ((fun a ↦ (y a : ℂ)) ∘ Sum.inl) = fun i ↦ (y (.inl i) : ℂ) := rfl
    rw [hcomp_inl, ← hslice_an.iteratedDeriv_comp_ofReal, hslice_eq.iteratedDeriv_eq k]
    simpa only [Complex.real_smul, mul_one] using iteratedDeriv_smul_const hg_cd (1 : ℂ)
  have hNash_re_im (k : Fin d) :
      IsNashAt (fun a ↦ (F_jet k (e.symm a)).re) (e p₀ℂ) ∧
        IsNashAt (fun a ↦ (F_jet k (e.symm a)).im) (e p₀ℂ) :=
    (hf.iteratedDeriv_sumElim k).complexification_re_im (hF_jet_an k p₀ℂ (mem_ball_self hρ))
      (eventually_of_mem (ball_mem_nhds p₀ hρ) (hF_jet_real k))
  let fam : Fin d ⊕ Fin d → ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ) → ℝ :=
    Sum.elim (fun k a ↦ (F_jet k (e.symm a)).re) (fun k a ↦ (F_jet k (e.symm a)).im)
  obtain ⟨W, hWo, hpW, hWs, hWfam⟩ := exists_isSemialgebraicOn_of_forall_isNashAt
    (f := fam) fun s ↦ by cases s with
      | inl k => exact (hNash_re_im k).1
      | inr k => exact (hNash_re_im k).2
  refine ⟨ρ, hρ, F, hF, hFr, W, hWo, hpW, hWs, fun k ↦ ?_⟩
  have hre : IsSemialgebraic (W ∩ {a | (F_jet k (e.symm a)).re = 0}) := by
    simpa only [fam, Sum.elim_inl, funext_iff, forall_const] using
      (hWfam (.inl k)).isSemialgebraic_inter_setOf_eq
        (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hWs)
  have him : IsSemialgebraic (W ∩ {a | (F_jet k (e.symm a)).im = 0}) := by
    simpa only [fam, Sum.elim_inr, funext_iff, forall_const] using
      (hWfam (.inr k)).isSemialgebraic_inter_setOf_eq
        (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hWs)
  convert hre.inter him using 1
  ext a
  simp [F_jet, e, Complex.ext_iff, and_left_comm, and_assoc]

/-- Real coordinates of the complex root point `(x, t₀ + z_j)` in `(σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ`. -/
private noncomputable def rootClusterPoint {d : ℕ} (t₀ : ℝ) (x : σ → ℝ)
    (u : Fin d ⊕ Fin d → ℝ) (j : Fin d) : (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ :=
  complexToRealPi (σ ⊕ Unit) <| Sum.elim (fun s ↦ (x s : ℂ))
    (fun _ ↦ (t₀ : ℂ) + ((u (.inl j) : ℂ) + (u (.inr j) : ℂ) * Complex.I))

/-- The unprojected root-cluster relation in `((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ`, combining
complex Vieta equations, disc bounds, and finite cluster-multiplicity conditions, is
semialgebraic. -/
private theorem isSemialgebraic_rootClusterLocus {d : ℕ} (x₀ : σ → ℝ) (t₀ δ R : ℝ)
    {Z : Fin d → Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)} (hZ : ∀ k, IsSemialgebraic (Z k)) :
    IsSemialgebraic {w : ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ |
      w ∘ Sum.inl ∘ Sum.inl ∈ ball x₀ δ ∧
      (∀ j : Fin d, w (.inr (.inl j)) ^ 2 + w (.inr (.inr j)) ^ 2 < R ^ 2) ∧
      (∀ i : Fin d,
        (∏ j : Fin d, (Polynomial.X -
          Polynomial.C ((w (.inr (.inl j)) : ℂ) +
            (w (.inr (.inr j)) : ℂ) * Complex.I))).coeff (i : ℕ) =
          (w (.inl (.inr i)) : ℂ)) ∧
      ∀ (j : Fin d) (S : Finset (Fin d)) (k : Fin d),
        (k : ℕ) < S.card →
        (∀ l ∈ S, w (.inr (.inl l)) = w (.inr (.inl j)) ∧
          w (.inr (.inr l)) = w (.inr (.inr j))) →
        rootClusterPoint t₀ (w ∘ Sum.inl ∘ Sum.inl) (w ∘ Sum.inr) j ∈ Z k} := by
  let Zvar (j : Fin d) : MvPolynomial ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) ℂ :=
    MvPolynomial.X (.inr (.inl j)) + MvPolynomial.X (.inr (.inr j)) * MvPolynomial.C Complex.I
  let Puniv : (MvPolynomial ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) ℂ)[X] :=
    ∏ j : Fin d, (Polynomial.X - Polynomial.C (Zvar j))
  let vietaPoly (i : Fin d) : MvPolynomial ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) ℂ :=
    Puniv.coeff (i : ℕ) - MvPolynomial.X (.inl (.inr i))
  have hvieta_eval (w : ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) (i : Fin d) :
      MvPolynomial.eval (fun a ↦ (w a : ℂ)) (vietaPoly i) = 0 ↔
        (∏ j : Fin d, (Polynomial.X -
          Polynomial.C ((w (.inr (.inl j)) : ℂ) +
            (w (.inr (.inr j)) : ℂ) * Complex.I))).coeff (i : ℕ) = (w (.inl (.inr i)) : ℂ) := by
    let φ : MvPolynomial ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) ℂ →+* ℂ :=
      MvPolynomial.eval fun a ↦ (w a : ℂ)
    have hmap : Puniv.map φ = ∏ j : Fin d, (Polynomial.X -
        Polynomial.C ((w (.inr (.inl j)) : ℂ) + (w (.inr (.inr j)) : ℂ) * Complex.I)) := by
      simp [Puniv, Zvar, φ, Polynomial.map_prod]
    have hval : MvPolynomial.eval (fun a ↦ (w a : ℂ)) (vietaPoly i) =
        (Puniv.map φ).coeff (i : ℕ) - (w (.inl (.inr i)) : ℂ) := by
      simp [vietaPoly, φ, Polynomial.coeff_map]
    rw [hval, hmap, sub_eq_zero]
  let ptPoly (j : Fin d) : (σ ⊕ Unit) ⊕ (σ ⊕ Unit) →
      MvPolynomial ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) ℝ := fun idx ↦
    match idx with
    | .inl (.inl s) => MvPolynomial.X (.inl (.inl s))
    | .inl (.inr ()) => MvPolynomial.C t₀ + MvPolynomial.X (.inr (.inl j))
    | .inr (.inl _) => 0
    | .inr (.inr ()) => MvPolynomial.X (.inr (.inr j))
  have hpt_eval (w : ((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) (j : Fin d) :
      (fun idx ↦ MvPolynomial.eval w (ptPoly j idx)) =
        rootClusterPoint t₀ (w ∘ Sum.inl ∘ Sum.inl) (w ∘ Sum.inr) j := by
    ext ((s | ⟨⟩) | (s | ⟨⟩)) <;> simp [ptPoly, rootClusterPoint, complexToRealPi_apply]
  let S_norm : Set (((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) :=
    ⋂ j : Fin d, {w | MvPolynomial.eval w
      (MvPolynomial.X (.inr (.inl j)) ^ 2 + MvPolynomial.X (.inr (.inr j)) ^ 2) <
        MvPolynomial.eval w (MvPolynomial.C (R ^ 2))}
  let S_vieta : Set (((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) :=
    ⋂ i : Fin d, {w | MvPolynomial.eval (fun a ↦ (w a : ℂ)) (vietaPoly i) = 0}
  let S_mult (j : Fin d) (S : Finset (Fin d)) (k : Fin d) :
      Set (((σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) :=
    if (k : ℕ) < S.card then
      (⋂ l ∈ S, {w | MvPolynomial.eval w (MvPolynomial.X (.inr (.inl l))) =
            MvPolynomial.eval w (MvPolynomial.X (.inr (.inl j)))} ∩
          {w | MvPolynomial.eval w (MvPolynomial.X (.inr (.inr l))) =
            MvPolynomial.eval w (MvPolynomial.X (.inr (.inr j)))})ᶜ ∪
        (fun w idx ↦ MvPolynomial.eval w (ptPoly j idx)) ⁻¹' Z k
    else univ
  have hS_mult (j : Fin d) (S : Finset (Fin d)) (k : Fin d) : IsSemialgebraic (S_mult j S k) := by
    dsimp only [S_mult]
    split_ifs
    · refine (IsSemialgebraic.biInter S.finite_toSet fun l _ ↦
        (isSemialgebraic_eval_eq _ _).inter (isSemialgebraic_eval_eq _ _)).compl.union ?_
      exact (hZ k).preimage_eval (ptPoly j)
    · exact isSemialgebraic_univ
  have hL : IsSemialgebraic
      (((fun w ↦ w ∘ (Sum.inl ∘ Sum.inl)) ⁻¹' ball x₀ δ) ∩ S_norm ∩ S_vieta ∩
        ⋂ (j : Fin d) (S : Finset (Fin d)) (k : Fin d), S_mult j S k) :=
    ((((isSemialgebraic_ball x₀ δ).preimage_comp (Sum.inl ∘ Sum.inl)).inter
      (.iInter fun _ ↦ isSemialgebraic_eval_lt _ _)).inter
      (.iInter fun i ↦ isSemialgebraic_setOf_eval_ofReal_eq_zero (vietaPoly i))).inter <|
      .iInter fun j ↦ .iInter fun S ↦ .iInter fun k ↦ hS_mult j S k
  convert hL using 1
  ext w
  simp only [S_norm, S_vieta, S_mult, mem_inter_iff, mem_preimage, mem_iInter, mem_ofPred_eq,
    MvPolynomial.eval_add, MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
    hvieta_eval, and_assoc]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    forall_congr' fun j ↦ forall_congr' fun S ↦ forall_congr' fun k ↦ ?_
  by_cases hk : (k : ℕ) < S.card <;> simp [hk, hpt_eval, imp_iff_not_or, Classical.not_forall]

/-- Semialgebraicity of the Weierstrass coefficient map from a first-order root-cluster description
over `ball x₀ δ`, via Tarski–Seidenberg projection. -/
private theorem isSemialgebraicOn_of_rootCluster_iff {d : ℕ} {x₀ : σ → ℝ} {t₀ δ R : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ}
    {Z : Fin d → Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)} (hZ : ∀ k, IsSemialgebraic (Z k))
    (hiff : ∀ x ∈ ball x₀ δ, ∀ y : Fin d → ℝ,
      (fun i ↦ c i x) = y ↔
        ∃ u : Fin d ⊕ Fin d → ℝ,
          (∀ j : Fin d, u (.inl j) ^ 2 + u (.inr j) ^ 2 < R ^ 2) ∧
          (∀ i : Fin d,
            (∏ j : Fin d, (Polynomial.X -
              Polynomial.C ((u (.inl j) : ℂ) + (u (.inr j) : ℂ) * Complex.I))).coeff (i : ℕ) =
              (y i : ℂ)) ∧
          ∀ (j : Fin d) (S : Finset (Fin d)) (k : Fin d),
            (k : ℕ) < S.card →
            (∀ l ∈ S, u (.inl l) = u (.inl j) ∧ u (.inr l) = u (.inr j)) →
            rootClusterPoint t₀ x u j ∈ Z k) :
    IsSemialgebraicOn (fun x i ↦ c i x) (ball x₀ δ) := by
  refine isSemialgebraicOn_def.2 ⟨isSemialgebraic_ball x₀ δ, ?_⟩
  convert (isSemialgebraic_rootClusterLocus x₀ t₀ δ R hZ).setOf_exists_sumElim using 1
  ext xy
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · rintro ⟨hx, hcxy⟩
    obtain ⟨u, hunorm, huvieta, humult⟩ := (hiff (xy ∘ Sum.inl) hx (xy ∘ Sum.inr)).1 hcxy
    exact ⟨u, by simpa [← Function.comp_assoc] using hx, hunorm, huvieta,
      by simpa [← Function.comp_assoc] using humult⟩
  · rintro ⟨u, hx, hunorm, huvieta, humult⟩
    have hx' : xy ∘ Sum.inl ∈ ball x₀ δ := by simpa [← Function.comp_assoc] using hx
    refine ⟨hx', (hiff (xy ∘ Sum.inl) hx' (xy ∘ Sum.inr)).2 ⟨u, hunorm, huvieta, ?_⟩⟩
    simpa [← Function.comp_assoc] using humult

/-- Simultaneous polydisc radius `R` and parameter radius `δ` on which the complexified Weierstrass
factorization holds, the complexified unit has no zeros, the vertical-derivative zero sets `Z k`
apply, and all complex roots of `monicOfCoeff (c · x)` lie in `ball 0 R`. -/
private theorem exists_holomorphic_weierstrassPreparation_ball {d : ℕ}
    {f u : (σ ⊕ Unit → ℝ) → ℝ} {c : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F
      (ball (fun a ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) a : ℂ)) ρ))
    (hFr : ∀ y ∈ ball (Sum.elim x₀ (fun _ : Unit ↦ t₀)) ρ, F (fun a ↦ (y a : ℂ)) = f y)
    {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)} (hWo : IsOpen W)
    (hpW : complexToRealPi (σ ⊕ Unit)
      (fun a ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) a : ℂ)) ∈ W)
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀))) (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p) :
    ∃ (R δ : ℝ) (U : (σ ⊕ Unit → ℂ) → ℂ), 0 < R ∧ 0 < δ ∧
      AnalyticOnNhd ℂ F
        (ball (fun a ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) a : ℂ)) R) ∧
      AnalyticOnNhd ℂ U
        (ball (fun a ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) a : ℂ)) R) ∧
      (∀ q ∈ ball (fun a ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) a : ℂ)) R,
        complexToRealPi (σ ⊕ Unit) q ∈ W ∧ U q ≠ 0) ∧
      (∀ x ∈ ball x₀ δ, x ∈ ball x₀ R ∧
        (∀ w ∈ ball (t₀ : ℂ) R,
          F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)) =
            (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (w - t₀) *
              U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w))) ∧
        ∃ z : Fin d → ℂ, (∀ j, ‖z j‖ < R) ∧
          ∏ j : Fin d, (Polynomial.X - Polynomial.C (z j)) =
            Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let p₀ℂ : σ ⊕ Unit → ℂ := fun a ↦ (p₀ a : ℂ)
  choose ρc hρc C hC hCc _ using fun i ↦ (hc i).exists_complexification
  obtain ⟨ρu, hρu, U, hU, hUu, _⟩ := hu.exists_complexification
  have hPan : AnalyticAt ℂ (fun q : σ ⊕ Unit → ℂ ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (q ∘ Sum.inl))).eval (q (Sum.inr ()) - t₀)) p₀ℂ := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    have hline : AnalyticAt ℂ (fun q : σ ⊕ Unit → ℂ ↦ q (Sum.inr ()) - (t₀ : ℂ)) p₀ℂ :=
      ((ContinuousLinearMap.proj (R := ℂ) (Sum.inr ())).analyticAt p₀ℂ).sub analyticAt_const
    have hproj : AnalyticAt ℂ (fun q : σ ⊕ Unit → ℂ ↦ q ∘ Sum.inl) p₀ℂ :=
      AnalyticAt.pi fun s ↦ (ContinuousLinearMap.proj (R := ℂ) (Sum.inl s)).analyticAt p₀ℂ
    exact (hline.pow d).add <| Finset.univ.analyticAt_fun_sum fun i _ ↦
      ((hC i _ (mem_ball_self (hρc i))).comp_of_eq hproj rfl).mul (hline.pow _)
  have hF_fac : F =ᶠ[𝓝 p₀ℂ] fun q ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (q ∘ Sum.inl))).eval (q (Sum.inr ()) - t₀) * U q := by
    refine (hF p₀ℂ (mem_ball_self hρ)).eventuallyEq_of_eventually_real
      (hPan.mul (hU p₀ℂ (mem_ball_self hρu))) ?_
    have hproj_cont : ContinuousAt (fun y : σ ⊕ Unit → ℝ ↦ y ∘ Sum.inl) p₀ :=
      continuousAt_pi.2 fun s ↦ (continuous_apply (Sum.inl s)).continuousAt
    have hCc' : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun s ↦ (x s : ℂ)) = c i x :=
      eventually_all.2 fun i ↦ Filter.mem_of_superset (ball_mem_nhds x₀ (hρc i)) (hCc i)
    filter_upwards [ball_mem_nhds p₀ hρ, ball_mem_nhds p₀ hρu, hfac,
      hproj_cont.tendsto.eventually hCc'] with y hyF hyU hyfac hyC
    rw [hFr y hyF, hUu y hyU]
    simp only [Polynomial.eval_monicOfCoeff] at hyfac ⊢
    have hyC' (i : Fin d) : C i (fun s ↦ (y (.inl s) : ℂ)) = c i (y ∘ Sum.inl) := hyC i
    simp only [Function.comp_def] at hyC' ⊢
    simp only [hyC']
    exact_mod_cast hyfac
  have hU_ne : ∀ᶠ q in 𝓝 p₀ℂ, U q ≠ 0 :=
    (hU p₀ℂ (mem_ball_self hρu)).continuousAt.eventually_ne <| by
      rw [hUu p₀ (mem_ball_self hρu)]; exact_mod_cast hu0
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.1 <|
    inter_mem (inter_mem (ball_mem_nhds p₀ℂ hρ) (ball_mem_nhds p₀ℂ hρu))
      (inter_mem ((hWo.preimage (complexToRealPi (σ ⊕ Unit)).continuous).mem_nhds hpW)
        (hF_fac.and hU_ne))
  have hzero_sym : Sym.coeffEquiv ℂ d (Sym.ofFn fun _ : Fin d ↦ (0 : ℂ)) = 0 := by
    ext i
    have hX : ((Polynomial.X : ℂ[X]) ^ d).coeff (i : ℕ) = 0 := by
      simp [Polynomial.coeff_X_pow, i.2.ne]
    rw [Sym.coeffEquiv_ofFn_apply, Pi.zero_apply]
    simpa using hX
  have hroots_ev : ∀ᶠ x in 𝓝 x₀, ∃ z : Fin d → ℂ, (∀ j, ‖z j‖ < R) ∧
      ∏ j : Fin d, (Polynomial.X - Polynomial.C (z j)) =
        Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ)) := by
    have hev := Sym.eventually_exists_ofFn_eq_coeffEquiv_symm (fun _ : Fin d ↦ (0 : ℂ)) hR
    rw [hzero_sym] at hev
    have hc_cont : ContinuousAt (fun x : σ → ℝ ↦ fun i : Fin d ↦ (c i x : ℂ)) x₀ :=
      continuousAt_pi.2 fun i ↦ Complex.continuous_ofReal.continuousAt.comp (hc i).continuousAt
    have hc_at0 : (fun i : Fin d ↦ (c i x₀ : ℂ)) = 0 := by ext i; simp [hc0 i]
    filter_upwards [(hc_at0 ▸ hc_cont.tendsto).eventually hev] with x ⟨z, hz_eq, hz_norm⟩
    exact ⟨z, fun j ↦ by simpa using hz_norm j,
      by rw [← Sym.toMonic_ofFn, hz_eq, Sym.toMonic_coeffEquiv_symm]⟩
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.1 <|
    inter_mem (inter_mem (ball_mem_nhds x₀ hR)
      (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρc i))) hroots_ev
  refine ⟨R, δ, U, hR, hδ, hF.mono fun q hq ↦ (hRball hq).1.1,
    hU.mono fun q hq ↦ (hRball hq).1.2, fun q hq ↦ ⟨(hRball hq).2.1, (hRball hq).2.2.2⟩,
    fun x hx ↦ ?_⟩
  obtain ⟨⟨hxR, hxρc⟩, hroots⟩ := hδball hx
  refine ⟨hxR, fun w hw ↦ ?_, hroots⟩
  have hq_mem : Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ w) ∈ ball p₀ℂ R := by
    rw [mem_ball, dist_pi_lt_iff hR]
    rintro (s | ⟨⟩)
    · simpa [p₀ℂ, p₀, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (dist_pi_lt_iff hR).1 (mem_ball.1 hxR) s
    · simpa [p₀ℂ, p₀] using mem_ball.1 hw
  have hCx (i : Fin d) : C i (fun s ↦ (x s : ℂ)) = (c i x : ℂ) := hCc i x (hxρc i)
  simpa [Function.comp_def, hCx] using (hRball hq_mem).2.2.1

/-- The lower coefficients `c i` of any real analytic Weierstrass preparation of a Nash germ `f`
are Nash germs. -/
private theorem isNashAt_coeff_of_weierstrassPreparation {d : ℕ}
    {f u : (σ ⊕ Unit → ℝ) → ℝ} {c : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀))) (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p) :
    ∀ i, IsNashAt (c i) x₀ := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let p₀ℂ : σ ⊕ Unit → ℂ := fun a ↦ (p₀ a : ℂ)
  obtain ⟨ρ, hρ, F, hF, hFr, W, hWo, hpW, _, hZ⟩ :=
    exists_complexification_verticalIteratedDeriv_zeroSets hf d
  obtain ⟨R, δ, U, hR, hδ, hF_R, hU_R, hWU_R, hδ_prop⟩ :=
    exists_holomorphic_weierstrassPreparation_ball hρ hF hFr hWo hpW hc hc0 hu hu0 hfac
  refine forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨AnalyticAt.pi hc, ball x₀ δ, isOpen_ball, mem_ball_self hδ, ?_⟩
  refine isSemialgebraicOn_of_rootCluster_iff (t₀ := t₀) (R := R) hZ fun x hx y ↦ ?_
  obtain ⟨hxR, hΦ_fac, ⟨z₀, hz₀R, hz₀P⟩⟩ := hδ_prop x hx
  have hq_mem {w : ℂ} (hw : w ∈ ball (t₀ : ℂ) R) :
      Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ w) ∈ ball p₀ℂ R := by
    rw [mem_ball, dist_pi_lt_iff hR]
    rintro (s | ⟨⟩)
    · simpa [p₀ℂ, p₀, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (dist_pi_lt_iff hR).1 (mem_ball.1 hxR) s
    · simpa [p₀ℂ, p₀] using mem_ball.1 hw
  let Φ (w : ℂ) : ℂ := F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w))
  let Ψ (w : ℂ) : ℂ := U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w))
  let Px : ℂ[X] := Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))
  have hline_an (w : ℂ) : AnalyticAt ℂ
      (fun ζ : ℂ ↦ Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ)) w :=
    analyticAt_pi_iff.2 fun j ↦ by cases j with
      | inl _ => exact analyticAt_const
      | inr _ => exact analyticAt_id
  have hΦ_an : AnalyticOnNhd ℂ Φ (ball (t₀ : ℂ) R) :=
    fun w hw ↦ (hF_R _ (hq_mem hw)).comp_of_eq (hline_an w) rfl
  have hΨ_an : AnalyticOnNhd ℂ Ψ (ball (t₀ : ℂ) R) :=
    fun w hw ↦ (hU_R _ (hq_mem hw)).comp_of_eq (hline_an w) rfl
  have hΨ_ne : ∀ w ∈ ball (t₀ : ℂ) R, Ψ w ≠ 0 := fun w hw ↦ (hWU_R _ (hq_mem hw)).2
  constructor
  · rintro rfl
    refine ⟨Sum.elim (fun j ↦ (z₀ j).re) (fun j ↦ (z₀ j).im), fun j ↦ ?_, fun i ↦ ?_,
      fun j S k hk hcl ↦ ?_⟩
    · have hsq : (z₀ j).re ^ 2 + (z₀ j).im ^ 2 = ‖z₀ j‖ ^ 2 := by
        rw [← Complex.normSq_add_mul_I, Complex.re_add_im, Complex.normSq_eq_norm_sq]
      dsimp only [Sum.elim_inl, Sum.elim_inr]
      exact hsq ▸ (sq_lt_sq₀ (norm_nonneg _) hR.le).2 (hz₀R j)
    · simp only [Sum.elim_inl, Sum.elim_inr, Complex.re_add_im, hz₀P, Polynomial.coeff_monicOfCoeff]
    · have hnorm (m : Fin d) : ‖((z₀ m).re : ℂ) + (z₀ m).im * Complex.I‖ < R := by
        simpa [Complex.re_add_im] using hz₀R m
      have hjet := ((Polynomial.monic_monicOfCoeff _).prod_X_sub_C_eq_iff_iteratedDeriv_eq_zero
        (IsAlgClosed.splits Px) (Polynomial.natDegree_monicOfCoeff _) hΦ_an hΨ_an hΨ_ne hΦ_fac
        hnorm).1 (by simpa [Complex.re_add_im] using hz₀P) j S (k : ℕ) hk fun l hl ↦
          Complex.ext (by simpa using (hcl l hl).1) (by simpa using (hcl l hl).2)
      have hpt_in_R := hq_mem (w := (t₀ : ℂ) + z₀ j) (by simpa [dist_eq_norm] using hz₀R j)
      refine ⟨by simpa [rootClusterPoint, Complex.re_add_im] using (hWU_R _ hpt_in_R).1, ?_⟩
      simpa [rootClusterPoint, Φ, add_assoc, Complex.re_add_im] using hjet
  · rintro ⟨u_vec, hunorm, huvieta, humult⟩
    let z (j : Fin d) : ℂ := (u_vec (.inl j) : ℂ) + (u_vec (.inr j) : ℂ) * Complex.I
    have hzR (j : Fin d) : ‖z j‖ < R := by
      have hsq : ‖z j‖ ^ 2 = u_vec (.inl j) ^ 2 + u_vec (.inr j) ^ 2 := by
        dsimp only [z]
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
      exact (sq_lt_sq₀ (norm_nonneg _) hR.le).1 (hsq ▸ hunorm j)
    have hzP : ∏ j : Fin d, (Polynomial.X - Polynomial.C (z j)) = Px := by
      refine ((Polynomial.monic_monicOfCoeff _).prod_X_sub_C_eq_iff_iteratedDeriv_eq_zero
        (IsAlgClosed.splits Px) (Polynomial.natDegree_monicOfCoeff _) hΦ_an hΨ_an hΨ_ne hΦ_fac
        hzR).2 fun j S k hk hS ↦ ?_
      have hScard : S.card ≤ d := S.card_le_univ.trans_eq (Fintype.card_fin d)
      have hcl : ∀ l ∈ S, u_vec (.inl l) = u_vec (.inl j) ∧ u_vec (.inr l) = u_vec (.inr j) :=
        fun l hl ↦ ⟨by simpa [z] using congrArg Complex.re (hS l hl),
          by simpa [z] using congrArg Complex.im (hS l hl)⟩
      simpa [rootClusterPoint, Φ, z, add_assoc] using
        (humult j S ⟨k, hk.trans_le hScard⟩ hk hcl).2
    ext i
    exact Complex.ofReal_injective (by rw [← huvieta i, hzP, Polynomial.coeff_monicOfCoeff])

end PreparationAux

/-! ### Nash Weierstrass preparation -/

/-- **Nashness of any real analytic Weierstrass preparation.** If `f` is a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)` and `(c, u)` is any real analytic Weierstrass preparation of `f`
at `p₀`, then every coefficient `c i` is a Nash germ at `x₀` and `u` is a Nash germ at `p₀`. -/
theorem IsNashAt.of_weierstrassPreparation
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {u : (σ ⊕ Unit → ℝ) → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀))) (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p) :
    (∀ i, IsNashAt (c i) x₀) ∧ IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  have hc_nash : ∀ i, IsNashAt (c i) x₀ :=
    isNashAt_coeff_of_weierstrassPreparation hf hc hc0 hu hu0 hfac
  let P_eval : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦
    (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀)
  have hP_nash : IsNashAt P_eval p₀ := by
    simp only [P_eval, Polynomial.eval_monicOfCoeff]
    have hline : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦ p (Sum.inr ()) - t₀) p₀ :=
      (isNashAt_apply (Sum.inr ())).sub (isNashAt_const t₀)
    refine (hline.pow d).add <| Finset.fun_isNashAt_sum Finset.univ fun i _ ↦ ?_
    exact ((hc_nash i).comp (g := fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl)
      fun s ↦ isNashAt_apply (Sum.inl s)).mul (hline.pow _)
  have hP_ne0 : ¬ P_eval =ᶠ[𝓝 p₀] 0 := by
    intro hzero
    have hcont : Continuous (fun t : ℝ ↦ Sum.elim x₀ (fun _ : Unit ↦ t)) :=
      continuous_pi fun j ↦ by cases j with
        | inl _ => exact continuous_const
        | inr _ => exact continuous_id
    obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 ((hcont.tendsto t₀).eventually hzero)
    have hval : P_eval (Sum.elim x₀ (fun _ ↦ t₀ + ε / 2)) = 0 :=
      hεball (by simp [dist_eq_norm, abs_of_pos hε, half_lt_self hε])
    have hpow : (ε / 2) ^ d = 0 := by simpa [P_eval, Polynomial.eval_monicOfCoeff, hc0] using hval
    exact pow_ne_zero d (half_pos hε).ne' hpow
  exact ⟨hc_nash, hP_nash.of_mul (hf.congr hfac) hP_ne0 hu⟩

/-- **Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)` whose vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes
to finite order `d` at `t₀`. Then there exist Nash germs `c : Fin d → (σ → ℝ) → ℝ` at `x₀`
vanishing at `x₀` and a Nash germ `u : (σ ⊕ Unit → ℝ) → ℝ` nonvanishing at `p₀` such that near
`p₀`, `f p = (monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p`. -/
theorem IsNashAt.exists_weierstrassPreparation
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p := by
  let splitℝ : ((σ ⊕ Unit) → ℝ) ≃L[ℝ] ((σ → ℝ) × ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi (R := ℝ) σ Unit (fun _ ↦ ℝ)).trans
      ((ContinuousLinearEquiv.refl ℝ (σ → ℝ)).prodCongr
        (ContinuousLinearEquiv.funUnique Unit ℝ ℝ))
  have hsymm (q : (σ → ℝ) × ℝ) : splitℝ.symm q = Sum.elim q.1 (fun _ ↦ q.2) := by
    ext (s | ⟨⟩) <;> rfl
  have hf_prod : AnalyticAt ℝ (f ∘ splitℝ.symm) (x₀, t₀) :=
    hf.analyticAt.comp_of_eq (splitℝ.symm.analyticAt _) (hsymm (x₀, t₀))
  obtain ⟨c, u₀, hc_an, hc0, hu₀_an, hu₀0, hprep₀⟩ :=
    hf_prod.exists_weierstrassPreparation_real (by simpa [hsymm] using hd)
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let u : (σ ⊕ Unit → ℝ) → ℝ := u₀ ∘ splitℝ
  have hsplit_p₀ : splitℝ p₀ = (x₀, t₀) := rfl
  have hu_an : AnalyticAt ℝ u p₀ := hu₀_an.comp_of_eq (splitℝ.analyticAt _) hsplit_p₀
  have hu0 : u p₀ ≠ 0 := by simpa [u, hsplit_p₀] using hu₀0
  have hprep : f =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p := by
    have happ (p : σ ⊕ Unit → ℝ) : splitℝ p = (p ∘ Sum.inl, p (Sum.inr ())) := rfl
    have hT : Tendsto splitℝ (𝓝 p₀) (𝓝 (x₀, t₀)) := hsplit_p₀ ▸ splitℝ.continuous.tendsto p₀
    filter_upwards [hT.eventually hprep₀] with p hp
    rw [Function.comp_apply, splitℝ.symm_apply_apply] at hp
    simpa [u, Function.comp_apply, happ] using hp
  obtain ⟨hc_nash, hu_nash⟩ := hf.of_weierstrassPreparation hc_an hc0 hu_an hu0 hprep
  exact ⟨c, u, hc_nash, hc0, hu_nash, hu0, hprep⟩

/-! ### Nash Weierstrass division -/

section DivisionAux

/-- Nash Weierstrass preparation of the deformed germ
`H (x, ε, t) = P_{c x} (t - t₀) + ε * g (x, t)` at `(x₀, 0, t₀)`, together with its specialization
at `ε = 0`. -/
private theorem exists_deformed_weierstrassPreparation {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (C : Fin d → (σ ⊕ Unit → ℝ) → ℝ) (U : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (C i) (Sum.elim x₀ (fun _ ↦ 0))) ∧
      IsNashAt U (Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀)) ∧
      ((fun m : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (m ∘ Sum.inl ∘ Sum.inl))).eval (m (Sum.inr ()) - t₀) +
          m (.inl (.inr ())) * g (Sum.elim (m ∘ Sum.inl ∘ Sum.inl) (m ∘ Sum.inr)))
        =ᶠ[𝓝 (Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀))] fun m ↦
          (Polynomial.monicOfCoeff (fun i ↦ C i (m ∘ Sum.inl))).eval (m (Sum.inr ()) - t₀) * U m) ∧
      (∀ i, (fun x ↦ C i (Sum.elim x (fun _ ↦ 0))) =ᶠ[𝓝 x₀] c i) ∧
      (fun p : σ ⊕ Unit → ℝ ↦
        U (Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (p ∘ Sum.inr)))
          =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] 1 := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let x₀' : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ 0)
  let p₀' : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim x₀' (fun _ ↦ t₀)
  let H : ((σ ⊕ Unit) ⊕ Unit → ℝ) → ℝ := fun m ↦
    (Polynomial.monicOfCoeff (fun i ↦ c i (m ∘ Sum.inl ∘ Sum.inl))).eval (m (Sum.inr ()) - t₀) +
      m (.inl (.inr ())) * g (Sum.elim (m ∘ Sum.inl ∘ Sum.inl) (m ∘ Sum.inr))
  have hH_nash : IsNashAt H p₀' := by
    simp only [H, Polynomial.eval_monicOfCoeff]
    have ht : IsNashAt (fun m : (σ ⊕ Unit) ⊕ Unit → ℝ ↦ m (Sum.inr ()) - t₀) p₀' :=
      (isNashAt_apply (Sum.inr ())).sub (isNashAt_const t₀)
    have hP : IsNashAt (fun m : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        (m (Sum.inr ()) - t₀) ^ d + ∑ i : Fin d,
          c i (m ∘ Sum.inl ∘ Sum.inl) * (m (Sum.inr ()) - t₀) ^ (i : ℕ)) p₀' :=
      (ht.pow d).add <| Finset.fun_isNashAt_sum Finset.univ fun i _ ↦
        ((hc i).comp (g := fun m : (σ ⊕ Unit) ⊕ Unit → ℝ ↦ m ∘ Sum.inl ∘ Sum.inl)
          fun s ↦ isNashAt_apply (Sum.inl (Sum.inl s))).mul (ht.pow _)
    have hpt : Sum.elim (p₀' ∘ Sum.inl ∘ Sum.inl) (p₀' ∘ Sum.inr) = p₀ := by ext (s | ⟨⟩) <;> rfl
    have hg' : IsNashAt (fun m : (σ ⊕ Unit) ⊕ Unit → ℝ ↦
        g (Sum.elim (m ∘ Sum.inl ∘ Sum.inl) (m ∘ Sum.inr))) p₀' :=
      (hpt ▸ hg).comp (g := fun m ↦ Sum.elim (m ∘ Sum.inl ∘ Sum.inl) (m ∘ Sum.inr)) fun j ↦
        by cases j with
          | inl s => exact isNashAt_apply (Sum.inl (Sum.inl s))
          | inr u => exact isNashAt_apply (Sum.inr u)
    exact hP.add ((isNashAt_apply (Sum.inl (Sum.inr ()))).mul hg')
  have hH_ord : analyticOrderAt (fun t ↦ H (Sum.elim x₀' (fun _ ↦ t))) t₀ = d := by
    have hslice : (fun t ↦ H (Sum.elim x₀' (fun _ ↦ t))) = fun t : ℝ ↦ (t - t₀) ^ d := by
      ext t; simp [H, x₀', Polynomial.eval_monicOfCoeff, ← Function.comp_assoc, hc0]
    rw [hslice]
    exact ((analyticAt_id.sub analyticAt_const).pow d).analyticOrderAt_eq_natCast.2
      ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun t ↦ by simp⟩
  obtain ⟨C, U, hC_nash, hC0, hU_nash, hU0, hH_fac⟩ := hH_nash.exists_weierstrassPreparation hH_ord
  let embX (x : σ → ℝ) : σ ⊕ Unit → ℝ := Sum.elim x (fun _ ↦ 0)
  let embQ (q : (σ → ℝ) × ℝ) : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim (embX q.1) (fun _ ↦ q.2)
  have hembX_an : AnalyticAt ℝ embX x₀ :=
    analyticAt_pi_iff.2 fun j ↦ by cases j with
      | inl s => exact (ContinuousLinearMap.proj (R := ℝ) s).analyticAt x₀
      | inr _ => exact analyticAt_const
  have hembQ_an : AnalyticAt ℝ embQ (x₀, t₀) :=
    analyticAt_pi_iff.2 fun j ↦ by cases j with
      | inl k => cases k with
        | inl s =>
          exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) s).analyticAt x₀).comp
            (analyticAt_fst (p := (x₀, t₀)))
        | inr _ => exact analyticAt_const
      | inr _ => exact analyticAt_snd
  obtain ⟨hC_eq, hU_eq⟩ := eventuallyEq_of_weierstrassPreparation_real
    (c := fun i x ↦ C i (embX x)) (c' := c) (u := U ∘ embQ) (u' := fun _ ↦ 1)
    (fun i ↦ (hC_nash i).analyticAt.comp hembX_an) (fun i ↦ hC0 i)
    (hU_nash.analyticAt.comp_of_eq hembQ_an rfl) hU0
    (fun i ↦ (hc i).analyticAt) hc0 analyticAt_const one_ne_zero <| by
      filter_upwards [(hembQ_an.continuousAt.tendsto : Tendsto embQ (𝓝 (x₀, t₀)) (𝓝 p₀')).eventually
        hH_fac] with q hq
      have hHq : H (embQ q) = (Polynomial.monicOfCoeff (fun i ↦ c i q.1)).eval (q.2 - t₀) * 1 := by
        simp [H, embQ, embX, ← Function.comp_assoc]
      simpa [Function.comp_apply, embQ, embX] using hq.symm.trans hHq
  refine ⟨C, U, hC_nash, hU_nash, hH_fac, hC_eq, ?_⟩
  have hsplit_cont : ContinuousAt (fun p : σ ⊕ Unit → ℝ ↦ (p ∘ Sum.inl, p (Sum.inr ()))) p₀ := by
    fun_prop
  have hsplit_p₀ : (p₀ ∘ Sum.inl, p₀ (Sum.inr ())) = (x₀, t₀) := rfl
  filter_upwards [(hsplit_p₀ ▸ hsplit_cont.tendsto).eventually hU_eq] with p hp
  have hcast : embQ (p ∘ Sum.inl, p (Sum.inr ())) =
      Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ 0)) (p ∘ Sum.inr) := by
    ext ((s | ⟨⟩) | ⟨⟩) <;> rfl
  simpa [Function.comp_apply, hcast] using hp

end DivisionAux

/-- **Nash Weierstrass division by a Nash Weierstrass polynomial.** Let `c : Fin d → (σ → ℝ) → ℝ`
be Nash germs at `x₀` vanishing at `x₀`, and let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`. Then there exist a Nash germ `q` at `p₀` and Nash germs
`r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = (monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
  ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let p₀' : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀)
  obtain ⟨C, U, hC_nash, hU_nash, hH_fac, hC_eq, hU_eq⟩ :=
    exists_deformed_weierstrassPreparation hg hc hc0
  let embX (x : σ → ℝ) : σ ⊕ Unit → ℝ := Sum.elim x (fun _ ↦ 0)
  let embP (p : σ ⊕ Unit → ℝ) : (σ ⊕ Unit) ⊕ Unit → ℝ :=
    Sum.elim (embX (p ∘ Sum.inl)) (p ∘ Sum.inr)
  let wε : σ ⊕ Unit → ℝ := Sum.elim 0 (fun _ ↦ 1)
  let vε : (σ ⊕ Unit) ⊕ Unit → ℝ := Sum.elim wε (fun _ ↦ 0)
  let q (p : σ ⊕ Unit → ℝ) : ℝ := fderiv ℝ U (embP p) vε
  let r (i : Fin d) (x : σ → ℝ) : ℝ := fderiv ℝ (C i) (embX x) wε
  have hembP0 : Sum.elim (Sum.elim x₀ (fun _ ↦ 0)) (fun _ ↦ t₀) = embP p₀ := by
    ext ((s | ⟨⟩) | ⟨⟩) <;> rfl
  have hq_nash : IsNashAt q p₀ :=
    (hembP0 ▸ hU_nash.fderiv_apply vε).comp (g := embP) fun j ↦ by cases j with
      | inl k => cases k with
        | inl s => exact isNashAt_apply (Sum.inl s)
        | inr _ => exact isNashAt_const 0
      | inr u => exact isNashAt_apply (Sum.inr u)
  have hr_nash (i : Fin d) : IsNashAt (r i) x₀ :=
    ((hC_nash i).fderiv_apply wε).comp (g := embX) fun j ↦ by cases j with
      | inl s => exact isNashAt_apply s
      | inr _ => exact isNashAt_const 0
  refine ⟨q, r, hq_nash, hr_nash, ?_⟩
  have hembP_T : Tendsto embP (𝓝 p₀) (𝓝 p₀') := by
    dsimp only [p₀']
    rw [hembP0]
    exact (continuous_pi fun j ↦ by cases j with
      | inl k => cases k with
        | inl s => exact continuous_apply (Sum.inl s)
        | inr _ => exact continuous_const
      | inr u => exact continuous_apply (Sum.inr u)).tendsto p₀
  have hproj_T : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_pi fun s ↦ continuous_apply (Sum.inl s)).tendsto p₀
  obtain ⟨ρ', hρ', hball'⟩ := Metric.mem_nhds_iff.1 <|
    inter_mem hH_fac (inter_mem hU_nash.analyticAt.eventually_analyticAt
      (eventually_all.2 fun i ↦
        ((continuous_pi fun j ↦ continuous_apply (Sum.inl j)).tendsto p₀').eventually
          (hC_nash i).analyticAt.eventually_analyticAt))
  filter_upwards [hembP_T.eventually (ball_mem_nhds p₀' hρ'),
    hproj_T.eventually (eventually_all.2 hC_eq), hU_eq] with p hp_in hCp hUp
  let curve (ε : ℝ) : (σ ⊕ Unit) ⊕ Unit → ℝ :=
    Sum.elim (Sum.elim (p ∘ Sum.inl) (fun _ ↦ ε)) (p ∘ Sum.inr)
  let curveX (ε : ℝ) : σ ⊕ Unit → ℝ := Sum.elim (p ∘ Sum.inl) (fun _ ↦ ε)
  have hcurve_der : HasDerivAt curve vε 0 :=
    hasDerivAt_pi.2 fun j ↦ by cases j with
      | inl k => cases k with
        | inl s => simpa [curve, vε, wε] using hasDerivAt_const (0 : ℝ) (p (.inl s))
        | inr u => cases u; simpa [curve, vε, wε] using hasDerivAt_id' (0 : ℝ)
      | inr u => simpa [curve, vε] using hasDerivAt_const (0 : ℝ) (p (.inr u))
  have hcurveX_der : HasDerivAt curveX wε 0 :=
    hasDerivAt_pi.2 fun j ↦ by cases j with
      | inl s => simpa [curveX, wε] using hasDerivAt_const (0 : ℝ) (p (.inl s))
      | inr u => cases u; simpa [curveX, wε] using hasDerivAt_id' (0 : ℝ)
  have hU_der : HasDerivAt (fun ε ↦ U (curve ε)) (q p) 0 :=
    ((hball' hp_in).2.1.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
      hcurve_der).congr_deriv rfl
  have hC_der (i : Fin d) : HasDerivAt (fun ε ↦ C i (curveX ε)) (r i (p ∘ Sum.inl)) 0 :=
    (((hball' hp_in).2.2 i).differentiableAt.hasFDerivAt.comp_hasDerivAt 0
      hcurveX_der).congr_deriv rfl
  have hP_der : HasDerivAt
      (fun ε ↦ (Polynomial.monicOfCoeff (fun i ↦ C i (curveX ε))).eval (p (Sum.inr ()) - t₀))
      (∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)) 0 := by
    simp only [Polynomial.eval_monicOfCoeff]
    convert ((hasDerivAt_const (0 : ℝ) ((p (Sum.inr ()) - t₀) ^ d)).add <|
      HasDerivAt.sum (u := Finset.univ) fun i _ ↦
        (hC_der i).mul_const ((p (Sum.inr ()) - t₀) ^ (i : ℕ))) using 1
    · ext ε; simp
    · simp
  have hRHS_der := hP_der.mul hU_der
  have hUp' : U (curve 0) = 1 := hUp
  have hP_at0 : (Polynomial.monicOfCoeff (fun i ↦ C i (curveX 0))).eval (p (Sum.inr ()) - t₀) =
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) := by
    simp only [Polynomial.eval_monicOfCoeff, curveX, hCp]
  rw [hUp', mul_one, hP_at0] at hRHS_der
  have hLHS_der : HasDerivAt (fun ε ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (curve ε ∘ Sum.inl ∘ Sum.inl))).eval
        (curve ε (Sum.inr ()) - t₀) +
        curve ε (.inl (.inr ())) * g (Sum.elim (curve ε ∘ Sum.inl ∘ Sum.inl) (curve ε ∘ Sum.inr)))
      (g p) 0 := by
    have hps : Sum.elim (p ∘ Sum.inl) (p ∘ Sum.inr) = p := Sum.elim_comp_inl_inr p
    have hval (ε : ℝ) :
        (Polynomial.monicOfCoeff (fun i ↦ c i (curve ε ∘ Sum.inl ∘ Sum.inl))).eval
          (curve ε (Sum.inr ()) - t₀) +
          curve ε (.inl (.inr ())) *
            g (Sum.elim (curve ε ∘ Sum.inl ∘ Sum.inl) (curve ε ∘ Sum.inr)) =
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) +
          ε * g p := by
      simp [curve, ← Function.comp_assoc, hps]
    simp_rw [hval]
    simpa only [Pi.add_def, zero_add, one_mul] using
      (hasDerivAt_const (0 : ℝ) _).add ((hasDerivAt_id' (0 : ℝ)).mul_const (g p))
  have heq_ε := ((hcurve_der.continuousAt.tendsto).eventually
    (isOpen_ball.mem_nhds hp_in)).mono fun ε hε_in ↦ (hball' hε_in).1
  rw [hLHS_der.unique (hRHS_der.congr_of_eventuallyEq
    (heq_ε.mono fun ε hε ↦ by simpa [curve, curveX, Function.comp_def] using hε)), add_comm]

/-- **Nashness of any real analytic Weierstrass division.** If `g` is a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, `c i` are Nash germs at `x₀` vanishing at `x₀`, and `(q, r)` is
any real analytic Weierstrass division of `g` by `monicOfCoeff c` at `p₀`, then `q` is a Nash germ
at `p₀` and every `r i` is a Nash germ at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision_monicOfCoeff {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g q : (σ ⊕ Unit → ℝ) → ℝ} {r : Fin d → (σ → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀))) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  obtain ⟨q', r', hq'_nash, hr'_nash, hdiv'⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  let splitℝ : ((σ ⊕ Unit) → ℝ) ≃L[ℝ] ((σ → ℝ) × ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi (R := ℝ) σ Unit (fun _ ↦ ℝ)).trans
      ((ContinuousLinearEquiv.refl ℝ (σ → ℝ)).prodCongr
        (ContinuousLinearEquiv.funUnique Unit ℝ ℝ))
  have hsymm (m : (σ → ℝ) × ℝ) : splitℝ.symm m = Sum.elim m.1 (fun _ ↦ m.2) := by
    ext (s | ⟨⟩) <;> rfl
  have hT_symm : Tendsto splitℝ.symm (𝓝 (x₀, t₀)) (𝓝 p₀) := by
    simpa [hsymm, p₀] using splitℝ.symm.continuous.tendsto (x₀, t₀)
  obtain ⟨hqq', hrr'⟩ := eventuallyEq_of_weierstrassDivision_real
    (fun i ↦ (hc i).analyticAt) hc0
    (hq.comp_of_eq (splitℝ.symm.analyticAt _) (hsymm (x₀, t₀))) hr
    (hq'_nash.analyticAt.comp_of_eq (splitℝ.symm.analyticAt _) (hsymm (x₀, t₀)))
    (fun i ↦ (hr'_nash i).analyticAt) <| by
      filter_upwards [hT_symm.eventually (hdiv.symm.trans hdiv')] with m hm
      simpa [Function.comp_apply, hsymm] using hm
  have hsplit_p₀ : splitℝ p₀ = (x₀, t₀) := rfl
  have hT : Tendsto splitℝ (𝓝 p₀) (𝓝 (x₀, t₀)) := hsplit_p₀ ▸ splitℝ.continuous.tendsto p₀
  refine ⟨hq'_nash.congr ?_, fun i ↦ (hr'_nash i).congr (hrr' i).symm⟩
  filter_upwards [hT.eventually hqq'.symm] with p hp
  simpa [Function.comp_apply, splitℝ.symm_apply_apply] using hp

/-- **Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, and suppose the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))`
vanishes to finite order `d` at `t₀`. Then there exist a Nash germ `q` at `p₀` and Nash germs
`r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision
    {f g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.fun_div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end TauCeti
