/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Weierstrass.Preparation
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex

/-!
# The Nash Weierstrass division theorem

Given Nash coefficient germs `c : Fin d → (σ → ℝ) → ℝ` at `x₀` vanishing at `x₀`, with `σ` finite,
and a Nash germ `g : (σ ⊕ Unit → ℝ) → ℝ` at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, the real analytic
Weierstrass division theorem (`AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`) writes `g`
near `p₀` as
`P_x (t - t₀) * q (x, t) + ∑ i : Fin d, r i x * (t - t₀) ^ (i : ℕ)`,
where `P_x = TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)`, `q` is real analytic at `p₀`, and
each remainder coefficient `r i` is real analytic at `x₀`. This file proves that `q` and every `r i`
are Nash germs (`TauCeti.IsNashAt.of_weierstrassDivision`,
`TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`), and combines this with Nash
Weierstrass preparation (`TauCeti.IsNashAt.exists_weierstrassPreparation`) to obtain general Nash
Weierstrass division by any Nash germ of finite vertical order
(`TauCeti.IsNashAt.exists_weierstrassDivision`).

## Proof outline

Passing to holomorphic extensions `G` and `Q` of `g` and `q` on a small polydisc
`ball x₀ δ ×ˢ ball t₀ R` where all complex roots of `P_x` lie in `ball 0 R`, a candidate tuple
`r' : Fin d → ℝ` equals `fun i ↦ r i x` if and only if at every `w ∈ ball t₀ R` and `k < d` where
the first `k + 1` derivatives `P_x^{(j)} (w - t₀)` (`j ≤ k`) vanish, the vertical derivative
`∂_w^k G (x, w)` agrees with the `k`-th derivative of `(Polynomial.ofFn d r').eval (· - t₀)` at `w`:
any difference polynomial of degree `< d` matching those jets at all roots of `P_x` up to their
multiplicities is divisible by the split degree-`d` polynomial `P_x`
(`Polynomial.Splits.dvd_of_roots_le_roots`), hence zero. Universal quantifier elimination over the
two real coordinates of `w ∈ ℂ` (`TauCeti.IsSemialgebraic.setOf_forall_sumElim`) makes the remainder
tuple `r` semialgebraic on `ball x₀ δ`, hence Nash. Subtracting the Nash remainder and applying
`TauCeti.IsNashAt.of_eventuallyEq_eval_monicOfCoeff_mul` then makes `q` Nash.

## Main results

* `TauCeti.IsNashAt.of_weierstrassDivision`: Nashness of the quotient and remainder coefficients of
  any real analytic Weierstrass division of a Nash germ by a Nash Weierstrass polynomial.
* `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`: **Nash Weierstrass division by a
  Weierstrass polynomial.**
* `TauCeti.IsNashAt.exists_weierstrassDivision`: **the Nash Weierstrass division theorem.**

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
-/

public section

open Complex Filter Metric Polynomial Set Topology

namespace TauCeti

section Aux

/-! ### Jet characterization of the Weierstrass remainder -/

open Classical in
private theorem iteratedDeriv_eq_of_weierstrassDivision {G Q : ℂ → ℂ} {w₀ : ℂ} {R : ℝ} {d : ℕ}
    {c r : Fin d → ℂ} (hQ : ∀ w ∈ ball w₀ R, AnalyticAt ℂ Q w)
    (hdiv : ∀ w ∈ ball w₀ R,
      G w = (Polynomial.monicOfCoeff c).eval (w - w₀) * Q w + ∑ i : Fin d, r i * (w - w₀) ^ (i : ℕ))
    {w : ℂ} (hw : w ∈ ball w₀ R) (k : Fin d)
    (hPk : ∀ j : Fin d, (j : ℕ) ≤ (k : ℕ) →
      (Polynomial.derivative^[j] (Polynomial.monicOfCoeff c)).eval (w - w₀) = 0) :
    iteratedDeriv (k : ℕ) G w =
      (Polynomial.derivative^[k] (Polynomial.ofFn d r)).eval (w - w₀) := by
  let P := Polynomial.monicOfCoeff c
  have hsub_an : AnalyticAt ℂ (fun ζ : ℂ ↦ ζ - w₀) w :=
    (analyticAt_id (𝕜 := ℂ)).fun_sub analyticAt_const
  have hPa : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - w₀)) w :=
    ((AnalyticOnNhd.eval_polynomial P) (w - w₀) (mem_univ _)).comp_of_eq hsub_an rfl
  have hRa : AnalyticAt ℂ (fun ζ ↦ (Polynomial.ofFn d r).eval (ζ - w₀)) w :=
    ((AnalyticOnNhd.eval_polynomial (Polynomial.ofFn d r)) (w - w₀) (mem_univ _)).comp_of_eq
      hsub_an rfl
  have hordP : (((k : ℕ) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun ζ ↦ P.eval (ζ - w₀)) w := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hPa]
    intro j hj
    have hj' : j < d := (Nat.lt_succ_iff.1 hj).trans_lt k.is_lt
    rw [iteratedDeriv_comp_sub_const (f := fun t ↦ P.eval t), Polynomial.iteratedDeriv]
    exact hPk ⟨j, hj'⟩ (Nat.lt_succ_iff.1 hj)
  have hordPQ : (((k : ℕ) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun ζ ↦ P.eval (ζ - w₀) * Q ζ) w := by
    rw [analyticOrderAt_fun_mul hPa (hQ w hw)]
    exact hordP.trans le_self_add
  have hPQ0 : iteratedDeriv (k : ℕ) (fun ζ ↦ P.eval (ζ - w₀) * Q ζ) w = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hPa.fun_mul (hQ w hw))).1 hordPQ
      (k : ℕ) (Nat.lt_succ_self _)
  have hGw : G =ᶠ[𝓝 w]
      (fun ζ ↦ P.eval (ζ - w₀) * Q ζ) + (fun ζ ↦ (Polynomial.ofFn d r).eval (ζ - w₀)) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with ζ hζ
    simp [P, hdiv ζ hζ, Polynomial.ofFn_eq_sum_monomial, eval_finsetSum]
  rw [hGw.iteratedDeriv_eq, iteratedDeriv_add (hPa.fun_mul (hQ w hw)).contDiffAt hRa.contDiffAt,
    hPQ0, zero_add, iteratedDeriv_comp_sub_const (f := fun t ↦ (Polynomial.ofFn d r).eval t),
    Polynomial.iteratedDeriv]

open Classical in
/-- When `G w = P.eval (w - w₀) * Q w + ∑ i, r i * (w - w₀) ^ i` on `ball w₀ R` and all roots of
`P = monicOfCoeff c` lie in `ball 0 R`, a tuple `r' : Fin d → ℂ` equals `r` if and only if at
every `w ∈ ball w₀ R` and `k : Fin d` where `P^{(j)} (w - w₀) = 0` for all `j ≤ k`, `∂_w^k G w`
equals `(Polynomial.ofFn d r')^{(k)} (w - w₀)`. -/
private theorem eq_rem_of_weierstrassDivision_iff {G Q : ℂ → ℂ} {w₀ : ℂ} {R : ℝ} {d : ℕ}
    {c r : Fin d → ℂ} (hQ : ∀ w ∈ ball w₀ R, AnalyticAt ℂ Q w)
    (hdiv : ∀ w ∈ ball w₀ R,
      G w = (Polynomial.monicOfCoeff c).eval (w - w₀) * Q w + ∑ i : Fin d, r i * (w - w₀) ^ (i : ℕ))
    (hroots : ∀ ζ : ℂ, (Polynomial.monicOfCoeff c).IsRoot ζ → ‖ζ‖ < R) (r' : Fin d → ℂ) :
    r' = r ↔
      ∀ w ∈ ball w₀ R, ∀ k : Fin d,
        (∀ j : Fin d, (j : ℕ) ≤ (k : ℕ) →
          (Polynomial.derivative^[j] (Polynomial.monicOfCoeff c)).eval (w - w₀) = 0) →
        iteratedDeriv (k : ℕ) G w =
          (Polynomial.derivative^[k] (Polynomial.ofFn d r')).eval (w - w₀) := by
  let P := Polynomial.monicOfCoeff c
  have hP0 : P ≠ 0 := (Polynomial.monic_monicOfCoeff c).ne_zero
  have hjet := fun {w} hw ↦ iteratedDeriv_eq_of_weierstrassDivision hQ hdiv (w := w) hw
  refine ⟨fun h _ hw k hPk ↦ h ▸ hjet hw k hPk, fun hr' ↦ ?_⟩
  set Δ := Polynomial.ofFn d (r' - r)
  have hΔ_eq : Δ = Polynomial.ofFn d r' - Polynomial.ofFn d r := map_sub (Polynomial.ofFn d) r' r
  by_cases hΔ0 : Δ = 0
  · exact sub_eq_zero.1 ((map_eq_zero_iff (Polynomial.ofFn d) (Polynomial.injective_ofFn d)).1 hΔ0)
  · exfalso
    have hroots_le : P.roots ≤ Δ.roots := by
      rw [Multiset.le_iff_count]
      intro ζ
      rw [Polynomial.count_roots, Polynomial.count_roots]
      rcases Nat.eq_zero_or_pos (P.rootMultiplicity ζ) with hμ0 | hμpos
      · simp [hμ0]
      · have hζR : ζ + w₀ ∈ ball w₀ R := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
          exact hroots ζ ((rootMultiplicity_pos hP0).1 hμpos)
        have hμd : P.rootMultiplicity ζ ≤ d := by
          rw [← Polynomial.count_roots]
          exact (Multiset.count_le_card _ _).trans
            (P.card_roots'.trans_eq (Polynomial.natDegree_monicOfCoeff c))
        rw [← Nat.cast_le (α := ℕ∞), ← Polynomial.analyticOrderAt_eval hΔ0 ζ,
          natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
            ((AnalyticOnNhd.eval_polynomial Δ) ζ (mem_univ _))]
        intro m hm
        have hPm : ∀ j : Fin d, (j : ℕ) ≤ m → (Polynomial.derivative^[j] P).eval ζ = 0 := by
          intro j hjm
          have hleP : ((P.rootMultiplicity ζ : ℕ) : ℕ∞) ≤
              analyticOrderAt (fun z ↦ P.eval z) ζ := by rw [Polynomial.analyticOrderAt_eval hP0 ζ]
          simpa only [Polynomial.iteratedDeriv] using
            (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
              ((AnalyticOnNhd.eval_polynomial P) ζ (mem_univ _))).1 hleP j (hjm.trans_lt hm)
        have h1 := hr' (ζ + w₀) hζR ⟨m, hm.trans_le hμd⟩ (by simpa [add_sub_cancel_right] using hPm)
        have h2 := hjet hζR ⟨m, hm.trans_le hμd⟩ (by simpa [add_sub_cancel_right] using hPm)
        rw [Polynomial.iteratedDeriv]
        simp only [hΔ_eq, Polynomial.iterate_derivative_sub, eval_sub, sub_eq_zero]
        simpa only [add_sub_cancel_right] using h1.symm.trans h2
    have hdvd : P ∣ Δ := (IsAlgClosed.splits P).dvd_of_roots_le_roots hP0 hroots_le
    have hdeg : Δ.natDegree < d :=
      Polynomial.ofFn_natDegree_lt
        (Nat.one_le_iff_ne_zero.2 (Polynomial.ne_zero_of_ofFn_ne_zero hΔ0)) (r' - r)
    exact hdeg.not_ge <| by
      simpa [P, Polynomial.natDegree_monicOfCoeff] using Polynomial.natDegree_le_of_dvd hdvd hΔ0

/-! ### Semialgebraic graph of the division remainder via universal quantifier elimination -/

private noncomputable def monicJetMvPoly {d : ℕ} (t₀ : ℝ) (j : ℕ) :
    MvPolynomial (Fin d ⊕ (Unit ⊕ Unit)) ℂ :=
  (Polynomial.derivative^[j]
    (Polynomial.monicOfCoeff (fun m : Fin d ↦ MvPolynomial.X (.inl m)))).eval
    (MvPolynomial.X (.inr (.inl ())) + MvPolynomial.X (.inr (.inr ())) * MvPolynomial.C I -
      MvPolynomial.C (t₀ : ℂ))

private noncomputable def remJetMvPoly {d : ℕ} (t₀ : ℝ) (k : ℕ) :
    MvPolynomial (Fin d ⊕ (Unit ⊕ Unit)) ℂ :=
  (Polynomial.derivative^[k]
    (∑ m : Fin d, Polynomial.monomial (m : ℕ) (MvPolynomial.X (.inl m)))).eval
    (MvPolynomial.X (.inr (.inl ())) + MvPolynomial.X (.inr (.inr ())) * MvPolynomial.C I -
      MvPolynomial.C (t₀ : ℂ))

private theorem eval_monicJetMvPoly {d : ℕ} (t₀ : ℝ) (j : ℕ) (s : Fin d → ℝ)
    (y : Unit ⊕ Unit → ℝ) :
    MvPolynomial.eval (fun t ↦ ((Sum.elim s y) t : ℂ)) (monicJetMvPoly t₀ j) =
      (Polynomial.derivative^[j] (Polynomial.monicOfCoeff (fun m ↦ (s m : ℂ)))).eval
        (((y (.inl ()) : ℂ) + y (.inr ()) * I) - (t₀ : ℂ)) := by
  have hZ : MvPolynomial.eval (fun t ↦ ((Sum.elim s y) t : ℂ))
      (MvPolynomial.X (.inr (.inl ())) + MvPolynomial.X (.inr (.inr ())) * MvPolynomial.C I -
        MvPolynomial.C (t₀ : ℂ)) = ((y (.inl ()) : ℂ) + y (.inr ()) * I) - (t₀ : ℂ) := by simp
  rw [monicJetMvPoly, ← hZ, ← Polynomial.eval_map_apply, ← Polynomial.iterate_derivative_map,
    Polynomial.map_monicOfCoeff]
  simp

open Classical in
private theorem eval_remJetMvPoly {d : ℕ} (t₀ : ℝ) (k : ℕ) (s : Fin d → ℝ)
    (y : Unit ⊕ Unit → ℝ) :
    MvPolynomial.eval (fun t ↦ ((Sum.elim s y) t : ℂ)) (remJetMvPoly t₀ k) =
      (Polynomial.derivative^[k] (Polynomial.ofFn d (fun m ↦ (s m : ℂ)))).eval
        (((y (.inl ()) : ℂ) + y (.inr ()) * I) - (t₀ : ℂ)) := by
  have hZ : MvPolynomial.eval (fun t ↦ ((Sum.elim s y) t : ℂ))
      (MvPolynomial.X (.inr (.inl ())) + MvPolynomial.X (.inr (.inr ())) * MvPolynomial.C I -
        MvPolynomial.C (t₀ : ℂ)) = ((y (.inl ()) : ℂ) + y (.inr ()) * I) - (t₀ : ℂ) := by simp
  rw [remJetMvPoly, ← hZ, ← Polynomial.eval_map_apply, ← Polynomial.iterate_derivative_map,
    Polynomial.ofFn_eq_sum_monomial]
  simp [Polynomial.map_sum]

private def divPhiX {σ : Type*} {d : ℕ} : σ → (σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) :=
  Sum.inl ∘ Sum.inl

private def divPhiQ {σ : Type*} {d : ℕ} : σ ⊕ (Unit ⊕ Unit) → (σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) :=
  Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr

private def divPhiRY {σ : Type*} {d : ℕ} : Fin d ⊕ (Unit ⊕ Unit) → (σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) :=
  Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr

private noncomputable def divBodySet {σ : Type*} {d : ℕ} (t₀ : ℝ)
    (Ω : Set ((σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) → ℝ))
    (c : Fin d → (σ → ℝ) → ℝ)
    (D_re D_im : Fin d → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ) :
    Set ((σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) → ℝ) :=
  Ωᶜ ∪ ⋂ k : Fin d,
    (⋂ j : {j : Fin d // (j : ℕ) ≤ (k : ℕ)},
      Ω ∩ {z | (Polynomial.derivative^[j.1] (Polynomial.monicOfCoeff
        (fun m ↦ (c m (z ∘ divPhiX) : ℂ)))).eval
        (((z (.inr (.inl ())) : ℂ) + z (.inr (.inr ())) * I) - (t₀ : ℂ)) = 0})ᶜ ∪
      (Ω ∩ {z | ((D_re k (z ∘ divPhiQ) : ℂ) + D_im k (z ∘ divPhiQ) * I) =
        MvPolynomial.eval (fun t ↦ (z (divPhiRY t) : ℂ)) (remJetMvPoly t₀ k)})

private theorem isSemialgebraic_divBodySet {σ : Type*} [Finite σ] {d : ℕ} {t₀ : ℝ}
    {Ω : Set ((σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) → ℝ)}
    {U_c : Set (σ → ℝ)} {U_G : Set (σ ⊕ (Unit ⊕ Unit) → ℝ)}
    {c : Fin d → (σ → ℝ) → ℝ}
    {D_re D_im : Fin d → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ}
    (hΩ : IsSemialgebraic Ω) (hcU : IsSemialgebraicOn (fun x i ↦ c i x) U_c)
    (hmapsc : MapsTo (fun z ↦ z ∘ divPhiX) Ω U_c)
    (hUG : ∀ k, IsSemialgebraicOn (fun q (_ : Unit) ↦ D_re k q) U_G ∧
      IsSemialgebraicOn (fun q (_ : Unit) ↦ D_im k q) U_G)
    (hmapsG : MapsTo (fun z ↦ z ∘ divPhiQ) Ω U_G) :
    IsSemialgebraic (divBodySet t₀ Ω c D_re D_im) := by
  have hcompX : IsSemialgebraicOn (fun z ↦ z ∘ divPhiX) Ω := by
    simpa only [Function.comp_def, MvPolynomial.eval_X] using
      isSemialgebraicOn_eval (fun b ↦ MvPolynomial.X (divPhiX b)) hΩ
  have hcompInr : IsSemialgebraicOn (fun z : (σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) → ℝ ↦ z ∘ Sum.inr) Ω := by
    simpa only [Function.comp_def, MvPolynomial.eval_X] using
      isSemialgebraicOn_eval (fun b : Unit ⊕ Unit ↦ MvPolynomial.X (Sum.inr b)) hΩ
  have hcompQ : IsSemialgebraicOn (fun z ↦ z ∘ divPhiQ) Ω := by
    simpa only [Function.comp_def, MvPolynomial.eval_X] using
      isSemialgebraicOn_eval (fun b ↦ MvPolynomial.X (divPhiQ b)) hΩ
  have hcompRY : IsSemialgebraicOn (fun z ↦ z ∘ divPhiRY) Ω := by
    simpa only [Function.comp_def, MvPolynomial.eval_X] using
      isSemialgebraicOn_eval (fun b ↦ MvPolynomial.X (divPhiRY b)) hΩ
  have hc_Ω : IsSemialgebraicOn (fun z ↦ Sum.elim (fun m ↦ c m (z ∘ divPhiX)) (z ∘ Sum.inr)) Ω :=
    (hcU.comp hcompX hmapsc).sumElim hcompInr
  have hPzero (j : Fin d) : IsSemialgebraic
      (Ω ∩ {z | (Polynomial.derivative^[j] (Polynomial.monicOfCoeff
        (fun m ↦ (c m (z ∘ divPhiX) : ℂ)))).eval
        (((z (.inr (.inl ())) : ℂ) + z (.inr (.inr ())) * I) - (t₀ : ℂ)) = 0}) := by
    convert hc_Ω.isSemialgebraic_inter_preimage
      (isSemialgebraic_setOf_eval_ofReal_eq_zero (monicJetMvPoly t₀ j)) using 2
    ext z; simp [eval_monicJetMvPoly]
  have hjetEq (k : Fin d) : IsSemialgebraic
      (Ω ∩ {z | ((D_re k (z ∘ divPhiQ) : ℂ) + D_im k (z ∘ divPhiQ) * I) =
        MvPolynomial.eval (fun t ↦ (z (divPhiRY t) : ℂ)) (remJetMvPoly t₀ k)}) := by
    have hD_re := (hUG k).1.comp hcompQ hmapsG
    have hD_im := (hUG k).2.comp hcompQ hmapsG
    have hmap := (hD_re.sumElim hD_im).sumElim hcompRY
    convert hmap.isSemialgebraic_inter_preimage
      (isSemialgebraic_setOf_eval_ofReal_eq_zero
        (MvPolynomial.X (.inl (.inl ())) + MvPolynomial.X (.inl (.inr ())) * MvPolynomial.C I -
          MvPolynomial.rename Sum.inr (remJetMvPoly t₀ k))) using 2
    ext z
    simp [MvPolynomial.eval_rename, Function.comp_def, sub_eq_zero]
  exact hΩ.compl.union (IsSemialgebraic.iInter fun k ↦
    (IsSemialgebraic.iInter fun (j : {j : Fin d // (j : ℕ) ≤ (k : ℕ)}) ↦
      hPzero j.1).compl.union (hjetEq k))

private theorem isSemialgebraicOn_rem_of_weierstrassDivision {σ : Type*} [Fintype σ]
    {x₀ : σ → ℝ} {t₀ δ R : ℝ} {d : ℕ} {c r : Fin d → (σ → ℝ) → ℝ}
    {G Q : (σ ⊕ Unit → ℂ) → ℂ}
    {D_re D_im : Fin d → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ} {U_G : Set (σ ⊕ (Unit ⊕ Unit) → ℝ)}
    {U_c : Set (σ → ℝ)}
    (hcU : IsSemialgebraicOn (fun x i ↦ c i x) U_c) (hsubc : ball x₀ δ ⊆ U_c)
    (hUG : ∀ k, IsSemialgebraicOn (fun q (_ : Unit) ↦ D_re k q) U_G ∧
      IsSemialgebraicOn (fun q (_ : Unit) ↦ D_im k q) U_G)
    (hsubG : ∀ x ∈ ball x₀ δ, ∀ y : Unit ⊕ Unit → ℝ,
      ((y (.inl ()) : ℂ) + y (.inr ()) * I) ∈ ball (t₀ : ℂ) R → Sum.elim x y ∈ U_G)
    (hDeq : ∀ k : Fin d, ∀ x ∈ ball x₀ δ, ∀ y : Unit ⊕ Unit → ℝ,
      let w : ℂ := (y (.inl ()) : ℂ) + y (.inr ()) * I
      D_re k (Sum.elim x y) =
          (iteratedDeriv (k : ℕ) (fun ζ ↦ G (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).re ∧
        D_im k (Sum.elim x y) =
          (iteratedDeriv (k : ℕ) (fun ζ ↦ G (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).im)
    (hQan : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      AnalyticAt ℂ (fun ζ ↦ Q (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w)
    (hdiv : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      G (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)) =
        (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (w - (t₀ : ℂ)) *
          Q (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)) +
          ∑ i : Fin d, (r i x : ℂ) * (w - (t₀ : ℂ)) ^ (i : ℕ))
    (hroots : ∀ x ∈ ball x₀ δ, ∀ ζ : ℂ,
      (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).IsRoot ζ → ‖ζ‖ < R) :
    IsSemialgebraicOn (fun x i ↦ r i x) (ball x₀ δ) := by
  have hB : IsSemialgebraic (ball x₀ δ) := isSemialgebraic_ball x₀ δ
  let Ω : Set ((σ ⊕ Fin d) ⊕ (Unit ⊕ Unit) → ℝ) :=
    (fun z ↦ z ∘ divPhiX) ⁻¹' ball x₀ δ ∩
      (fun z ↦ z ∘ Sum.inr) ⁻¹'
        {y : Unit ⊕ Unit → ℝ | ((y (.inl ()) : ℂ) + y (.inr ()) * I) ∈ ball (t₀ : ℂ) R}
  have hΩ : IsSemialgebraic Ω :=
    (hB.preimage_comp _).inter
      ((isSemialgebraic_setOf_mem_ball_complex (t₀ : ℂ) R).preimage_comp Sum.inr)
  have hmapsG : MapsTo (fun z ↦ z ∘ divPhiQ) Ω U_G := fun z ⟨hzB, hzR⟩ ↦ by
    have heq : z ∘ divPhiQ = Sum.elim (z ∘ divPhiX) (z ∘ Sum.inr) := by ext (s | u) <;> rfl
    dsimp only; rw [heq]; exact hsubG _ hzB _ hzR
  have hbody := isSemialgebraic_divBodySet (t₀ := t₀) hΩ hcU (fun z hz ↦ hsubc hz.1) hUG hmapsG
  refine isSemialgebraicOn_def.2 ⟨hB, ?_⟩
  convert (hB.preimage_comp Sum.inl).inter hbody.setOf_forall_sumElim using 1
  ext p
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  refine and_congr_right fun hpB ↦ ?_
  have hr_iff : (fun m ↦ r m (p ∘ Sum.inl)) = p ∘ Sum.inr ↔
      (fun m ↦ (p (.inr m) : ℂ)) = fun m ↦ (r m (p ∘ Sum.inl) : ℂ) := by
    simp [funext_iff, eq_comm]
  rw [hr_iff, eq_rem_of_weierstrassDivision_iff (hQan _ hpB) (hdiv _ hpB) (hroots _ hpB)]
  have hφq (y : Unit ⊕ Unit → ℝ) : Sum.elim p y ∘ divPhiQ = Sum.elim (p ∘ Sum.inl) y := by
    ext (s | u) <;> rfl
  have hφry (y : Unit ⊕ Unit → ℝ) : Sum.elim p y ∘ divPhiRY = Sum.elim (p ∘ Sum.inr) y := by
    ext (m | u) <;> rfl
  constructor
  · intro h y
    by_cases hzΩ : Sum.elim p y ∈ Ω
    · refine Or.inr <| mem_iInter.2 fun k ↦ ?_
      by_cases hPk : ∀ j : {j : Fin d // (j : ℕ) ≤ (k : ℕ)},
          Sum.elim p y ∈ Ω ∩ {z | (Polynomial.derivative^[j.1] (Polynomial.monicOfCoeff
            (fun m ↦ (c m (z ∘ divPhiX) : ℂ)))).eval
            (((z (.inr (.inl ())) : ℂ) + z (.inr (.inr ())) * I) - (t₀ : ℂ)) = 0}
      · right
        have hk_eq := h _ hzΩ.2 k fun j hjk ↦ (hPk ⟨j, hjk⟩).2
        have hD := hDeq k (p ∘ Sum.inl) hpB y
        have hre_im : ((D_re k (Sum.elim p y ∘ divPhiQ) : ℂ) +
            D_im k (Sum.elim p y ∘ divPhiQ) * I) =
            iteratedDeriv (k : ℕ)
              (fun ζ ↦ G (Sum.elim (fun s ↦ (p (.inl s) : ℂ)) (fun _ ↦ ζ)))
              ((y (.inl ()) : ℂ) + y (.inr ()) * I) := by
          rw [hφq y, hD.1, hD.2]
          exact Complex.re_add_im _
        have hry_eval := eval_remJetMvPoly t₀ k (p ∘ Sum.inr) y
        rw [← hφry y] at hry_eval
        exact ⟨hzΩ, hre_im.trans (hk_eq.trans hry_eval.symm)⟩
      · exact Or.inl (by rw [mem_compl_iff, mem_iInter]; exact hPk)
    · exact Or.inl hzΩ
  · intro h w hwR k hPk
    let y : Unit ⊕ Unit → ℝ := Sum.elim (fun _ ↦ w.re) (fun _ ↦ w.im)
    have hyw : (y (.inl ()) : ℂ) + y (.inr ()) * I = w := Complex.re_add_im w
    have hzΩ : Sum.elim p y ∈ Ω := ⟨hpB, by
      simpa only [mem_preimage, mem_ofPred_eq, Sum.elim_comp_inr, hyw] using hwR⟩
    have hz_k := mem_iInter.1 ((h y).resolve_left (not_not.2 hzΩ)) k
    have hz_P : Sum.elim p y ∈ ⋂ j : {j : Fin d // (j : ℕ) ≤ (k : ℕ)},
        Ω ∩ {z | (Polynomial.derivative^[j.1] (Polynomial.monicOfCoeff
          (fun m ↦ (c m (z ∘ divPhiX) : ℂ)))).eval
          (((z (.inr (.inl ())) : ℂ) + z (.inr (.inr ())) * I) - (t₀ : ℂ)) = 0} :=
      mem_iInter.2 fun ⟨j, hjk⟩ ↦ ⟨hzΩ, by simpa [divPhiX, Function.comp_def, hyw] using hPk j hjk⟩
    have hz_jet := (hz_k.resolve_left (not_not.2 hz_P)).2
    simp only [mem_ofPred_eq] at hz_jet
    have hD := hDeq k (p ∘ Sum.inl) hpB y
    have hre_im : ((D_re k (Sum.elim p y ∘ divPhiQ) : ℂ) +
        D_im k (Sum.elim p y ∘ divPhiQ) * I) =
        iteratedDeriv (k : ℕ)
          (fun ζ ↦ G (Sum.elim (fun s ↦ (p (.inl s) : ℂ)) (fun _ ↦ ζ))) w := by
      rw [hφq y, hD.1, hD.2]
      simpa only [hyw, Function.comp_apply] using Complex.re_add_im _
    have hry_eval := eval_remJetMvPoly t₀ k (p ∘ Sum.inr) y
    rw [← hφry y] at hry_eval
    exact hre_im.symm.trans (hz_jet.trans (by simpa only [hyw, Function.comp_apply] using hry_eval))

end Aux

/-! ### Public Nash Weierstrass division theorems -/

variable {σ : Type*} [Fintype σ]

/-- **Nashness of a Weierstrass division.** Let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, let `c : Fin d → (σ → ℝ) → ℝ` be Nash germs at `x₀` vanishing at
`x₀`, and let
`g p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p
  + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ i`
be a real analytic Weierstrass division of `g` near `p₀`, with `q` real analytic at `p₀` and each
`r i` real analytic at `x₀`. Then `q` is a Nash germ at `p₀` and every `r i` is a Nash germ at
`x₀`. -/
theorem IsNashAt.of_weierstrassDivision {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {q : (σ ⊕ Unit → ℝ) → ℝ} {r : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀))) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  -- Complexify `g`, `q`, `c i`, and `r i`, and propagate the division identity to `ℂ`.
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let p₀ℂ : σ ⊕ Unit → ℂ := fun j ↦ (p₀ j : ℂ)
  obtain ⟨ρg, hρg, G, hG, hGg, _⟩ := hg.analyticAt.exists_complexification
  obtain ⟨ρq, hρq, Q, hQ, hQq, _⟩ := hq.exists_complexification
  choose ρc hρc C hC hCc _ using fun i ↦ (hc i).analyticAt.exists_complexification
  choose ρr hρr R_rem hR_rem hRr _ using fun i ↦ (hr i).exists_complexification
  have hGan0 : AnalyticAt ℂ G p₀ℂ := hG _ (mem_ball_self hρg)
  have hQan0 : AnalyticAt ℂ Q p₀ℂ := hQ _ (mem_ball_self hρq)
  have hCan0 (i : Fin d) : AnalyticAt ℂ (C i) (fun s ↦ (x₀ s : ℂ)) := hC i _ (mem_ball_self (hρc i))
  have hRan0 (i : Fin d) : AnalyticAt ℂ (R_rem i) (fun s ↦ (x₀ s : ℂ)) :=
    hR_rem i _ (mem_ball_self (hρr i))
  have hC0ℂ (i : Fin d) : C i (fun s ↦ (x₀ s : ℂ)) = 0 := by
    rw [hCc i x₀ (mem_ball_self (hρc i)), hc0 i, ofReal_zero]
  have hinl : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p ∘ Sum.inl) p₀ℂ :=
    analyticAt_pi_iff.2 fun s ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inl s)).analyticAt p₀ℂ
  have hinr : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (Sum.inr ()) - (t₀ : ℂ)) p₀ℂ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ)
      (Sum.inr ())).analyticAt p₀ℂ).fun_sub analyticAt_const
  have hPan0 : AnalyticAt ℂ
      (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - (t₀ : ℂ)))
      p₀ℂ := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    exact (hinr.fun_pow d).fun_add <| Finset.analyticAt_fun_sum _ fun i _ ↦
      ((hCan0 i).comp_of_eq hinl rfl).fun_mul (hinr.fun_pow _)
  have hRem_an0 : AnalyticAt ℂ
      (fun p : σ ⊕ Unit → ℂ ↦
        ∑ i : Fin d, R_rem i (p ∘ Sum.inl) * (p (Sum.inr ()) - (t₀ : ℂ)) ^ (i : ℕ)) p₀ℂ :=
    Finset.analyticAt_fun_sum _ fun i _ ↦ ((hRan0 i).comp_of_eq hinl rfl).fun_mul (hinr.fun_pow _)
  have hdivℂ : G =ᶠ[𝓝 p₀ℂ] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - (t₀ : ℂ)) * Q p +
        ∑ i : Fin d, R_rem i (p ∘ Sum.inl) * (p (Sum.inr ()) - (t₀ : ℂ)) ^ (i : ℕ) := by
    refine hGan0.eventuallyEq_of_eventually_real ((hPan0.fun_mul hQan0).fun_add hRem_an0) ?_
    have hinl_cont : Continuous fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl :=
      continuous_pi fun s ↦ continuous_apply (Sum.inl s)
    filter_upwards [hdiv, ball_mem_nhds p₀ hρg, ball_mem_nhds p₀ hρq,
      (hinl_cont.tendsto p₀).eventually (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρc i)),
      (hinl_cont.tendsto p₀).eventually (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρr i))]
      with y hy hyg hyq hyc hyr
    rw [hGg y hyg, hQq y hyq]
    have hCy (i : Fin d) : C i ((fun j ↦ (y j : ℂ)) ∘ Sum.inl) = (c i (y ∘ Sum.inl) : ℂ) :=
      hCc i (y ∘ Sum.inl) (hyc i)
    have hRy (i : Fin d) : R_rem i ((fun j ↦ (y j : ℂ)) ∘ Sum.inl) = (r i (y ∘ Sum.inl) : ℂ) :=
      hRr i (y ∘ Sum.inl) (hyr i)
    simpa only [Polynomial.eval_monicOfCoeff, ofReal_mul, ofReal_add, ofReal_pow, ofReal_sum,
      ofReal_sub, hCy, hRy] using congrArg ((↑) : ℝ → ℂ) hy
  -- Choose a polydisc where `c` and vertical derivatives of `G` are semialgebraic and all complex
  -- roots of `P_x` stay inside `ball 0 R`.
  obtain ⟨_, U_c, hUc_open, hx₀_Uc, hcU⟩ :=
    (forall_isNashAt_apply_iff_exists_isSemialgebraicOn (g := fun x i ↦ c i x)).1 hc
  obtain ⟨U_G, R, hR, hW_polydisc, hUG_polydisc, hUG_semi⟩ :=
    hg.exists_isSemialgebraicOn_complexification_iteratedDeriv_sumElim hGan0
      (eventually_of_mem (ball_mem_nhds p₀ hρg) hGg) d
      (hQan0.eventually_analyticAt.and hdivℂ)
  have hofReal_cont : Continuous fun x : σ → ℝ ↦ fun s ↦ (x s : ℂ) :=
    continuous_pi fun s ↦ Complex.continuous_ofReal.comp (continuous_apply s)
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 <|
    inter_mem (ball_mem_nhds x₀ hR) <| inter_mem (hUc_open.mem_nhds hx₀_Uc) <|
      inter_mem (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρc i)) <|
        inter_mem (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρr i))
          (TauCeti.Polynomial.eventually_norm_lt_of_isRoot_monicOfCoeff
            (fun i ↦ (hCan0 i).continuousAt.comp hofReal_cont.continuousAt) hC0ℂ hR)
  have hslice_an (x : σ → ℝ) (w : ℂ) :
      AnalyticAt ℂ (fun ζ : ℂ ↦ Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ)) w :=
    analyticAt_pi_iff.2 fun j ↦ by cases j with | inl _ => exact analyticAt_const | inr _ =>
      exact analyticAt_id
  -- Characterize the remainder tuple by universal jet matching on `ball t₀ R`, then deduce `q`.
  have hr_nash : ∀ i, IsNashAt (r i) x₀ :=
    forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
      ⟨AnalyticAt.pi hr, ball x₀ δ, isOpen_ball, mem_ball_self hδ,
        isSemialgebraicOn_rem_of_weierstrassDivision hcU
          (fun _ hx ↦ (hδ_prop hx).2.1) hUG_semi
          (fun _ hx _ hy ↦ hUG_polydisc _ (hδ_prop hx).1 _ hy)
          (fun _ _ _ _ ↦ ⟨rfl, rfl⟩)
          (fun x hx w hw ↦ ((hW_polydisc _ (hδ_prop hx).1 _ hw).1).comp_of_eq (hslice_an x w) rfl)
          (fun x hx w hw ↦ by
            simpa only [Sum.elim_comp_inl, Sum.elim_inr,
              fun i ↦ hCc i x ((hδ_prop hx).2.2.1 i),
              fun i ↦ hRr i x ((hδ_prop hx).2.2.2.1 i)] using
              (hW_polydisc _ (hδ_prop hx).1 _ hw).2)
          (fun x hx ζ hζ ↦ (hδ_prop hx).2.2.2.2 ζ
            (by simpa only [Function.comp_apply, fun i ↦ hCc i x ((hδ_prop hx).2.2.1 i)] using hζ))⟩
  have hrem_nash : IsNashAt
      (fun p : σ ⊕ Unit → ℝ ↦ ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) p₀ :=
    Finset.fun_isNashAt_sum _ fun i _ ↦
      ((hr_nash i).comp fun s ↦ isNashAt_apply (Sum.inl s)).fun_mul
        (((isNashAt_apply (Sum.inr ())).fun_sub (isNashAt_const t₀)).fun_pow _)
  have hq_nash : IsNashAt q p₀ :=
    (hg.fun_sub hrem_nash).of_eventuallyEq_eval_monicOfCoeff_mul hc hq <| by
      filter_upwards [hdiv] with p hp; simp [hp]
  exact ⟨hq_nash, hr_nash⟩

/-- **Nash Weierstrass division by a Weierstrass polynomial.** Let `c : Fin d → (σ → ℝ) → ℝ` be
Nash germs at `x₀` vanishing at `x₀`, with `σ` finite, and let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash
germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`. Then there exist a Nash germ `q` at `p₀` and Nash germs
`r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p
  + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {d : ℕ}
    {c : Fin d → (σ → ℝ) → ℝ} {g : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  have hjoin : AnalyticAt ℝ (fun q : (σ → ℝ) × ℝ ↦ Sum.elim q.1 (fun _ : Unit ↦ q.2)) (x₀, t₀) :=
    analyticAt_pi_iff.2 fun i ↦ by
      cases i with
      | inl s =>
        exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) s).analyticAt x₀).comp_of_eq
          analyticAt_fst rfl
      | inr _ => exact analyticAt_snd
  obtain ⟨q₀, r, hq₀, hr, hdiv₀⟩ :=
    (hg.analyticAt.comp_of_eq hjoin rfl).exists_weierstrassDivision_monicOfCoeff_real
      (fun i ↦ (hc i).analyticAt) hc0
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let split : (σ ⊕ Unit → ℝ) → (σ → ℝ) × ℝ := fun p ↦ (p ∘ Sum.inl, p (Sum.inr ()))
  have hsplit : AnalyticAt ℝ split p₀ :=
    (analyticAt_pi_iff.2 fun s ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ)
        (Sum.inl s)).analyticAt p₀).prod
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (Sum.inr ())).analyticAt p₀)
  let q : (σ ⊕ Unit → ℝ) → ℝ := q₀ ∘ split
  have hq : AnalyticAt ℝ q p₀ := hq₀.comp_of_eq hsplit rfl
  have hdiv : g =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
    filter_upwards [(hsplit.continuousAt.tendsto).eventually hdiv₀] with p hp
    have hp_eq : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ())) = p := by ext (s | ⟨⟩) <;> rfl
    simpa [q, split, hp_eq] using hp
  obtain ⟨hq_nash, hr_nash⟩ := hg.of_weierstrassDivision hc hc0 hq hr hdiv
  exact ⟨q, r, hq_nash, hr_nash, hdiv⟩

/-- **The Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d` at `t₀`. Then there exist a Nash
germ `q` at `p₀` and Nash germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision {f g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.fun_div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end TauCeti
