/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Quotient
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
import TauCeti.RingTheory.Polynomial.RootEnumeration

/-!
# The Nash Weierstrass preparation theorem

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite,
and suppose that the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d`
at `t₀`. By the real analytic Weierstrass preparation theorem
(`AnalyticAt.exists_weierstrassPreparation_real`), `f` factors near `p₀` as
`P_x (t - t₀) * u (x, t)`, where `P_x = TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)` has real
analytic lower coefficients `c i` vanishing at `x₀` and `u` is real analytic and nonvanishing at
`p₀`. This file proves that the coefficient germs `c i` and the unit germ `u` are themselves Nash
germs (`TauCeti.IsNashAt.of_weierstrassPreparation`,
`TauCeti.IsNashAt.exists_weierstrassPreparation`).

## Proof outline

The roots of `P_x` need not be real, so the proof passes to a holomorphic extension `F` of `f` on
`σ ⊕ Unit → ℂ`. All iterated vertical complex derivatives `∂_w^k F` (`k ≤ d`) have Nash — hence
uniformly locally semialgebraic — real and imaginary parts
(`TauCeti.IsNashAt.exists_isSemialgebraicOn_complexification_iteratedDeriv_sumElim`).

On a small polydisc `(x, w) ∈ ball x₀ δ ×ˢ ball t₀ R` where the complexified unit `U` is
nonvanishing and all complex roots of `P_x` lie in `ball 0 R`
(`TauCeti.Polynomial.eventually_norm_lt_of_isRoot_monicOfCoeff`), a tuple `w : Fin d → ℂ` lists
the roots of `P_x(· - t₀)` with multiplicity (`Polynomial.IsRootEnumeration`) if and only if each
`w j` lies in `ball t₀ R` and, when `m` entries of `w` equal `w j`, the vertical derivatives
`∂_w^r F (x, w j)` vanish for `r < m` and `∂_w^m F (x, w j) ≠ 0`. Vieta's formula
(`Polynomial.IsRootEnumeration.aeval_esymm_eq_coeff`) expresses `c i x` as a polynomial in `w`.
Eliminating the `2 d` real coordinates of `w` (`TauCeti.IsSemialgebraic.setOf_exists_sumElim`)
makes the graph of `c i` semialgebraic near `x₀`, so `c i` is Nash by the local Nash graph
criterion (`TauCeti.isNashAt_iff_exists_isSemialgebraicOn`). Since `P_x (t - t₀)` is Nash and
monic in `t`, the exact analytic quotient `u` is Nash by
`TauCeti.IsNashAt.of_eventuallyEq_eval_monicOfCoeff_mul`.

Nash Weierstrass division is proved in `TauCeti.Geometry.RealAlgebraic.Nash.Weierstrass.Division`.

## Main results

* `TauCeti.IsNashAt.eval_monicOfCoeff`: evaluating `TauCeti.Polynomial.monicOfCoeff` at Nash
  coefficient and argument germs gives a Nash germ.
* `TauCeti.IsNashAt.of_eventuallyEq_eval_monicOfCoeff_mul`: an analytic germ whose product with a
  Nash Weierstrass polynomial is Nash is itself Nash.
* `TauCeti.IsNashAt.of_weierstrassPreparation`: Nashness of the coefficients and unit of any real
  analytic Weierstrass preparation of a Nash germ.
* `TauCeti.IsNashAt.exists_weierstrassPreparation`: **the Nash Weierstrass preparation theorem.**

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

/-! ### Algebraic characterization of the complex root cluster -/

open Classical in
private theorem iteratedDeriv_eq_zero_iff_count_roots_monicOfCoeff {F u : ℂ → ℂ} {w₀ : ℂ}
    {R : ℝ} {d : ℕ} {c : Fin d → ℂ} (hF : ∀ w ∈ ball w₀ R, AnalyticAt ℂ F w)
    (hu : ∀ w ∈ ball w₀ R, AnalyticAt ℂ u w) (hu0 : ∀ w ∈ ball w₀ R, u w ≠ 0)
    (hfac : ∀ w ∈ ball w₀ R, F w = (Polynomial.monicOfCoeff c).eval (w - w₀) * u w)
    {z : ℂ} (hz : z ∈ ball w₀ R) (m : ℕ) :
    ((∀ r < m, iteratedDeriv r F z = 0) ∧ iteratedDeriv m F z ≠ 0) ↔
      Multiset.count (z - w₀) (Polynomial.monicOfCoeff c).roots = m := by
  let P := Polynomial.monicOfCoeff c
  have hsub_an : AnalyticAt ℂ (fun ζ : ℂ ↦ ζ - w₀) z :=
    (analyticAt_id (𝕜 := ℂ)).fun_sub analyticAt_const
  have hPa : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - w₀)) z :=
    ((AnalyticOnNhd.eval_polynomial P) (z - w₀) (mem_univ _)).comp_of_eq hsub_an rfl
  have hPord : analyticOrderAt (fun ζ : ℂ ↦ P.eval (ζ - w₀)) z = P.rootMultiplicity (z - w₀) :=
    (analyticOrderAt_comp_of_deriv_ne_zero (f := fun t ↦ P.eval t) hsub_an
      (by rw [((hasDerivAt_id' z).sub_const w₀).deriv]; exact one_ne_zero)).trans
      (Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff c).ne_zero (z - w₀))
  rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hF z hz), Polynomial.count_roots]
  have hFz : F =ᶠ[𝓝 z] (fun ζ ↦ P.eval (ζ - w₀)) * u :=
    eventually_of_mem (isOpen_ball.mem_nhds hz) hfac
  rw [analyticOrderAt_congr hFz, analyticOrderAt_mul hPa (hu z hz), hPord,
    (hu z hz).analyticOrderAt_eq_zero.2 (hu0 z hz), add_zero, Nat.cast_inj]

/-- When `F w = (monicOfCoeff c).eval (w - w₀) * u w` on `ball w₀ R` with `u` nonvanishing and all
roots of `monicOfCoeff c` inside `ball 0 R`, a tuple `w : Fin d → ℂ` enumerates the shifted roots
of `monicOfCoeff c` with multiplicity if and only if each `w j` lies in `ball w₀ R` and the
cardinality of `{k | w k = w j}` equals the vanishing order of `F` at `w j` read off its iterated
derivatives. -/
private theorem isRootEnumeration_monicOfCoeff_iff {F u : ℂ → ℂ} {w₀ : ℂ} {R : ℝ} {d : ℕ}
    {c : Fin d → ℂ} (hF : ∀ w ∈ ball w₀ R, AnalyticAt ℂ F w)
    (hu : ∀ w ∈ ball w₀ R, AnalyticAt ℂ u w) (hu0 : ∀ w ∈ ball w₀ R, u w ≠ 0)
    (hfac : ∀ w ∈ ball w₀ R, F w = (Polynomial.monicOfCoeff c).eval (w - w₀) * u w)
    (hroots : ∀ ζ : ℂ, (Polynomial.monicOfCoeff c).IsRoot ζ → ‖ζ‖ < R) (w : Fin d → ℂ) :
    (Polynomial.monicOfCoeff c).IsRootEnumeration (fun j ↦ w j - w₀) ↔
      (∀ j, w j ∈ ball w₀ R) ∧
        ∀ j, ∃ S : Finset (Fin d), (∀ k, k ∈ S ↔ w k = w j) ∧
          (∀ r < S.card, iteratedDeriv r F (w j) = 0) ∧
          iteratedDeriv S.card F (w j) ≠ 0 := by
  classical
  let P := Polynomial.monicOfCoeff c
  have hP0 : P ≠ 0 := (Polynomial.monic_monicOfCoeff c).ne_zero
  have hcount (j : Fin d) :
      Multiset.count (w j - w₀) (Finset.univ.val.map fun k ↦ w k - w₀) =
        (Finset.univ.filter fun k ↦ w k = w j).card := by
    rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
    exact congrArg Multiset.card (Multiset.filter_congr fun _ _ ↦ sub_left_inj.trans eq_comm)
  constructor
  · intro henum
    have hroots_eq : P.roots = Finset.univ.val.map fun j ↦ w j - w₀ := by
      simpa [Polynomial.isRootEnumeration_iff] using henum
    have hw_ball (j : Fin d) : w j ∈ ball w₀ R := by
      have hmem : w j - w₀ ∈ P.roots := by
        rw [hroots_eq]; exact Multiset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩
      rw [mem_ball, dist_eq_norm]
      exact hroots _ ((Polynomial.mem_roots hP0).1 hmem)
    refine ⟨hw_ball, fun j ↦ ⟨Finset.univ.filter fun k ↦ w k = w j,
      fun k ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ k)), ?_⟩⟩
    rw [iteratedDeriv_eq_zero_iff_count_roots_monicOfCoeff hF hu hu0 hfac (hw_ball j),
      hroots_eq, hcount j]
  · rintro ⟨hw_ball, hmult⟩
    have hle : Finset.univ.val.map (fun k ↦ w k - w₀) ≤ P.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ Finset.univ.val.map fun k ↦ w k - w₀
      · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hα
        obtain ⟨S, hS, hSj⟩ := hmult j
        have hSeq : S = Finset.univ.filter fun k ↦ w k = w j := by ext k; simp [hS k]
        rw [(iteratedDeriv_eq_zero_iff_count_roots_monicOfCoeff hF hu hu0 hfac (hw_ball j)
          S.card).1 hSj, hSeq, ← hcount j]
      · rw [Multiset.count_eq_zero_of_notMem hα]
        exact Nat.zero_le _
    have hcard : P.roots.card ≤ (Finset.univ.val.map fun k ↦ w k - w₀).card :=
      P.card_roots'.trans_eq (by simp [P, Polynomial.natDegree_monicOfCoeff])
    simpa [Polynomial.isRootEnumeration_iff] using (Multiset.eq_of_le_of_card_le hle hcard).symm

/-! ### Semialgebraic graph of the preparation coefficients via Vieta's formula -/

private noncomputable def vietaMvPoly {σ : Type*} {d : ℕ} (t₀ : ℝ) (i : Fin d) :
    MvPolynomial ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d)) ℂ :=
  (-1) ^ (d - (i : ℕ)) * MvPolynomial.bind₁
    (fun j : Fin d ↦ MvPolynomial.X (.inr (.inl j)) +
      MvPolynomial.X (.inr (.inr j)) * MvPolynomial.C I - MvPolynomial.C (t₀ : ℂ))
    (MvPolynomial.esymm (Fin d) ℂ (d - (i : ℕ)))

private theorem eval_vietaMvPoly_of_isRootEnumeration {σ : Type*} {d : ℕ}
    {t₀ : ℝ} {i : Fin d} {γ : Fin d → ℂ} {p : σ ⊕ Unit → ℝ} {u : Fin d ⊕ Fin d → ℝ}
    (henum : (Polynomial.monicOfCoeff γ).IsRootEnumeration
      (fun j ↦ ((u (.inl j) : ℂ) + u (.inr j) * I) - (t₀ : ℂ))) :
    MvPolynomial.eval (fun t ↦ ((Sum.elim p u) t : ℂ)) (vietaMvPoly t₀ i) = γ i := by
  have hvieta := henum.aeval_esymm_eq_coeff (Polynomial.monic_monicOfCoeff γ)
    (by simp [Polynomial.natDegree_monicOfCoeff])
    (by simpa only [Fintype.card_fin] using Nat.sub_le d (i : ℕ))
  have hcoeff : (Polynomial.monicOfCoeff γ).coeff (Fintype.card (Fin d) - (d - (i : ℕ))) = γ i := by
    have hidx : Fintype.card (Fin d) - (d - (i : ℕ)) = (i : ℕ) := by
      rw [Fintype.card_fin, Nat.sub_sub_self i.is_lt.le]
    rw [hidx, Polynomial.coeff_monicOfCoeff]
  have hbind : MvPolynomial.eval (fun t ↦ ((Sum.elim p u) t : ℂ)) (vietaMvPoly t₀ i) =
      (-1) ^ (d - (i : ℕ)) * MvPolynomial.aeval
        (fun j ↦ ((u (.inl j) : ℂ) + u (.inr j) * I) - (t₀ : ℂ))
        (MvPolynomial.esymm (Fin d) ℂ (d - (i : ℕ))) := by
    rw [← MvPolynomial.aeval_eq_eval, vietaMvPoly, map_mul, map_pow, map_neg, map_one,
      MvPolynomial.aeval_bind₁]
    congr 2; ext j; simp
  rw [hbind, hvieta, Algebra.algebraMap_self_apply, hcoeff, ← mul_assoc, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_mul]

private def prepPhiQ {σ : Type*} {d : ℕ} (j : Fin d) :
    σ ⊕ (Unit ⊕ Unit) → (σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) :=
  Sum.elim (Sum.inl ∘ Sum.inl)
    (Sum.elim (fun _ ↦ Sum.inr (Sum.inl j)) (fun _ ↦ Sum.inr (Sum.inr j)))

private def prepEqPair {σ : Type*} {d : ℕ} (k j : Fin d) :
    Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ) :=
  {z | MvPolynomial.eval z (MvPolynomial.X (.inr (.inl k))) =
      MvPolynomial.eval z (MvPolynomial.X (.inr (.inl j)))} ∩
    {z | MvPolynomial.eval z (MvPolynomial.X (.inr (.inr k))) =
      MvPolynomial.eval z (MvPolynomial.X (.inr (.inr j)))}

private def prepMultSet {σ : Type*} {d : ℕ}
    (Ω : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ))
    (D_re D_im : Fin (d + 1) → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ)
    (j : Fin d) (S : Finset (Fin d)) : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ) :=
  let m : Fin (d + 1) :=
    ⟨S.card, Nat.lt_succ_of_le (S.card_le_univ.trans_eq (Fintype.card_fin d))⟩
  Ω ∩ (⋂ k : Fin d, if k ∈ S then prepEqPair k j else (prepEqPair k j)ᶜ) ∩
    (⋂ r : {r : Fin (d + 1) // (r : ℕ) < S.card},
      (Ω ∩ {z | D_re r.1 (z ∘ prepPhiQ j) = 0}) ∩ (Ω ∩ {z | D_im r.1 (z ∘ prepPhiQ j) = 0})) ∩
    ((Ω ∩ {z | D_re m (z ∘ prepPhiQ j) = 0}) ∩ (Ω ∩ {z | D_im m (z ∘ prepPhiQ j) = 0}))ᶜ

private theorem isSemialgebraic_prepMultSet {σ : Type*} [Finite σ] {d : ℕ}
    {Ω : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ)} {U_D : Set (σ ⊕ (Unit ⊕ Unit) → ℝ)}
    {D_re D_im : Fin (d + 1) → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ}
    (hΩ : IsSemialgebraic Ω)
    (hUD : ∀ r, IsSemialgebraicOn (fun q (_ : Unit) ↦ D_re r q) U_D ∧
      IsSemialgebraicOn (fun q (_ : Unit) ↦ D_im r q) U_D)
    (hmaps : ∀ j, MapsTo (fun z ↦ z ∘ prepPhiQ j) Ω U_D)
    (j : Fin d) (S : Finset (Fin d)) :
    IsSemialgebraic (prepMultSet Ω D_re D_im j S) := by
  have hcomp : IsSemialgebraicOn (fun z ↦ z ∘ prepPhiQ j) Ω := by
    simpa only [Function.comp_def, MvPolynomial.eval_X] using
      isSemialgebraicOn_eval (fun b ↦ MvPolynomial.X (prepPhiQ j b)) hΩ
  have hzero_re (r : Fin (d + 1)) : IsSemialgebraic (Ω ∩ {z | D_re r (z ∘ prepPhiQ j) = 0}) := by
    have hD_Ω : IsSemialgebraicOn (fun z (_ : Unit) ↦ D_re r (z ∘ prepPhiQ j)) Ω :=
      (hUD r).1.comp hcomp (hmaps j)
    simpa only [funext_iff, forall_const] using
      hD_Ω.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hΩ)
  have hzero_im (r : Fin (d + 1)) : IsSemialgebraic (Ω ∩ {z | D_im r (z ∘ prepPhiQ j) = 0}) := by
    have hD_Ω : IsSemialgebraicOn (fun z (_ : Unit) ↦ D_im r (z ∘ prepPhiQ j)) Ω :=
      (hUD r).2.comp hcomp (hmaps j)
    simpa only [funext_iff, forall_const] using
      hD_Ω.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hΩ)
  have heqPair (k : Fin d) : IsSemialgebraic (prepEqPair (σ := σ) k j) :=
    (isSemialgebraic_eval_eq _ _).inter (isSemialgebraic_eval_eq _ _)
  refine ((hΩ.inter (IsSemialgebraic.iInter fun k ↦ ?_)).inter
    (IsSemialgebraic.iInter fun (r : {r : Fin (d + 1) // (r : ℕ) < S.card}) ↦
      (hzero_re r.1).inter (hzero_im r.1))).inter
    ((hzero_re _).inter (hzero_im _)).compl
  by_cases hk : k ∈ S
  · simp [hk, heqPair k]
  · simp [hk, (heqPair k).compl]

private theorem mem_prepMultSet_iff {σ : Type*} [Fintype σ] {d : ℕ} {x₀ : σ → ℝ} {δ : ℝ}
    {Ω : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ)}
    {D_re D_im : Fin (d + 1) → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ}
    {F : (σ ⊕ Unit → ℂ) → ℂ} {p : σ ⊕ Unit → ℝ} {u : Fin d ⊕ Fin d → ℝ}
    (hpB : p ∘ Sum.inl ∈ ball x₀ δ) (hzΩ : Sum.elim p u ∈ Ω)
    (hDeq : ∀ r : Fin (d + 1), ∀ x ∈ ball x₀ δ, ∀ y : Unit ⊕ Unit → ℝ,
      let w : ℂ := (y (.inl ()) : ℂ) + y (.inr ()) * I
      D_re r (Sum.elim x y) =
          (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).re ∧
        D_im r (Sum.elim x y) =
          (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).im)
    (j : Fin d) (S : Finset (Fin d)) :
    let w : Fin d → ℂ := fun k ↦ (u (.inl k) : ℂ) + u (.inr k) * I
    let fx : ℂ → ℂ := fun ζ ↦ F (Sum.elim (fun s ↦ (p (.inl s) : ℂ)) (fun _ ↦ ζ))
    Sum.elim p u ∈ prepMultSet Ω D_re D_im j S ↔
      (∀ k, k ∈ S ↔ w k = w j) ∧
        (∀ r < S.card, iteratedDeriv r fx (w j) = 0) ∧
        iteratedDeriv S.card fx (w j) ≠ 0 := by
  intro w fx
  have hφq : Sum.elim p u ∘ prepPhiQ j =
      Sum.elim (p ∘ Sum.inl) (Sum.elim (fun _ ↦ u (.inl j)) (fun _ ↦ u (.inr j))) := by
    ext (s | (⟨⟩ | ⟨⟩)) <;> rfl
  have heqPair (k : Fin d) : Sum.elim p u ∈ prepEqPair k j ↔ w k = w j := by
    simp [prepEqPair, w, Complex.ext_iff]
  let m : Fin (d + 1) :=
    ⟨S.card, Nat.lt_succ_of_le (S.card_le_univ.trans_eq (Fintype.card_fin d))⟩
  constructor
  · rintro ⟨⟨⟨-, hS_eq⟩, hS_zero⟩, hS_ne⟩
    refine ⟨fun k ↦ ?_, fun r hr ↦ ?_, fun h0 ↦ hS_ne ?_⟩
    · have hk_mem := mem_iInter.1 hS_eq k
      by_cases hk : k ∈ S
      · simp only [hk, ↓reduceIte, heqPair] at hk_mem
        exact ⟨fun _ ↦ hk_mem, fun _ ↦ hk⟩
      · simp only [hk, ↓reduceIte, mem_compl_iff, heqPair] at hk_mem
        exact ⟨fun h ↦ (hk h).elim, fun hw ↦ (hk_mem hw).elim⟩
    · let r' : {r : Fin (d + 1) // (r : ℕ) < S.card} :=
        ⟨⟨r, Nat.lt_succ_of_le (hr.le.trans (S.card_le_univ.trans_eq (Fintype.card_fin d)))⟩, hr⟩
      have hr_mem := mem_iInter.1 hS_zero r'
      have hD := hDeq r'.1 (p ∘ Sum.inl) hpB (Sum.elim (fun _ ↦ u (.inl j)) (fun _ ↦ u (.inr j)))
      rw [← hφq] at hD
      exact Complex.ext (hD.1.symm.trans hr_mem.1.2) (hD.2.symm.trans hr_mem.2.2)
    · have hD := hDeq m (p ∘ Sum.inl) hpB (Sum.elim (fun _ ↦ u (.inl j)) (fun _ ↦ u (.inr j)))
      rw [← hφq] at hD
      exact ⟨⟨hzΩ, hD.1.trans (by simp [m, fx, w, h0])⟩, ⟨hzΩ, hD.2.trans (by simp [m, fx, w, h0])⟩⟩
  · rintro ⟨hS, hr0, hr_ne⟩
    refine ⟨⟨⟨hzΩ, mem_iInter.2 fun k ↦ ?_⟩, mem_iInter.2 fun r ↦ ?_⟩, fun hboth ↦ hr_ne ?_⟩
    · by_cases hk : k ∈ S
      · simp only [hk, ↓reduceIte, heqPair]; exact (hS k).1 hk
      · simp only [hk, ↓reduceIte, mem_compl_iff, heqPair]; exact mt (hS k).2 hk
    · have hD := hDeq r.1 (p ∘ Sum.inl) hpB (Sum.elim (fun _ ↦ u (.inl j)) (fun _ ↦ u (.inr j)))
      rw [← hφq] at hD
      have h0 := hr0 r.1 r.2
      exact ⟨⟨hzΩ, hD.1.trans (by simp [fx, w, h0])⟩, ⟨hzΩ, hD.2.trans (by simp [fx, w, h0])⟩⟩
    · have hD := hDeq m (p ∘ Sum.inl) hpB (Sum.elim (fun _ ↦ u (.inl j)) (fun _ ↦ u (.inr j)))
      rw [← hφq] at hD
      exact Complex.ext (hD.1.symm.trans hboth.1.2) (hD.2.symm.trans hboth.2.2)

private theorem isSemialgebraicOn_coeff_of_weierstrassPreparation {σ : Type*} [Fintype σ]
    {x₀ : σ → ℝ} {t₀ δ R : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    {F U : (σ ⊕ Unit → ℂ) → ℂ} {C : Fin d → (σ → ℂ) → ℂ}
    {D_re D_im : Fin (d + 1) → (σ ⊕ (Unit ⊕ Unit) → ℝ) → ℝ} {U_D : Set (σ ⊕ (Unit ⊕ Unit) → ℝ)}
    (hUD : ∀ r, IsSemialgebraicOn (fun q (_ : Unit) ↦ D_re r q) U_D ∧
      IsSemialgebraicOn (fun q (_ : Unit) ↦ D_im r q) U_D)
    (hsubD : ∀ x ∈ ball x₀ δ, ∀ y : Unit ⊕ Unit → ℝ,
      ((y (.inl ()) : ℂ) + y (.inr ()) * I) ∈ ball (t₀ : ℂ) R → Sum.elim x y ∈ U_D)
    (hDeq : ∀ r : Fin (d + 1), ∀ x ∈ ball x₀ δ, ∀ y : Unit ⊕ Unit → ℝ,
      let w : ℂ := (y (.inl ()) : ℂ) + y (.inr ()) * I
      D_re r (Sum.elim x y) =
          (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).re ∧
        D_im r (Sum.elim x y) =
          (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w).im)
    (hFan : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      AnalyticAt ℂ (fun ζ ↦ F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w)
    (hUan : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      AnalyticAt ℂ (fun ζ ↦ U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ))) w)
    (hU0 : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)) ≠ 0)
    (hfac : ∀ x ∈ ball x₀ δ, ∀ w ∈ ball (t₀ : ℂ) R,
      F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)) =
        (Polynomial.monicOfCoeff (fun i ↦ C i (fun s ↦ (x s : ℂ)))).eval (w - (t₀ : ℂ)) *
          U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ w)))
    (hCc : ∀ x ∈ ball x₀ δ, ∀ i, C i (fun s ↦ (x s : ℂ)) = c i x)
    (hroots : ∀ x ∈ ball x₀ δ, ∀ ζ : ℂ,
      (Polynomial.monicOfCoeff (fun i ↦ C i (fun s ↦ (x s : ℂ)))).IsRoot ζ → ‖ζ‖ < R)
    (i : Fin d) :
    IsSemialgebraicOn (fun x (_ : Unit) ↦ c i x) (ball x₀ δ) := by
  have hB : IsSemialgebraic (ball x₀ δ) := isSemialgebraic_ball x₀ δ
  let rootPhi (j : Fin d) : Unit ⊕ Unit → (σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) :=
    Sum.elim (fun _ ↦ Sum.inr (Sum.inl j)) (fun _ ↦ Sum.inr (Sum.inr j))
  let Ω : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ) :=
    (fun z ↦ z ∘ (Sum.inl ∘ Sum.inl)) ⁻¹' ball x₀ δ ∩
      ⋂ j : Fin d, (fun z ↦ z ∘ rootPhi j) ⁻¹'
        {y : Unit ⊕ Unit → ℝ | ((y (.inl ()) : ℂ) + y (.inr ()) * I) ∈ ball (t₀ : ℂ) R}
  have hΩ : IsSemialgebraic Ω :=
    (hB.preimage_comp _).inter <| IsSemialgebraic.iInter fun j ↦
      (isSemialgebraic_setOf_mem_ball_complex (t₀ : ℂ) R).preimage_comp (rootPhi j)
  have hmaps (j : Fin d) : MapsTo (fun z ↦ z ∘ prepPhiQ j) Ω U_D := fun z ⟨hzB, hzR⟩ ↦ by
    have heq : z ∘ prepPhiQ j = Sum.elim (z ∘ (Sum.inl ∘ Sum.inl)) (z ∘ rootPhi j) := by
      ext (s | (⟨⟩ | ⟨⟩)) <;> rfl
    dsimp only
    rw [heq]
    exact hsubD _ hzB _ (mem_iInter.1 hzR j)
  let vietaSet : Set ((σ ⊕ Unit) ⊕ (Fin d ⊕ Fin d) → ℝ) :=
    {z | MvPolynomial.eval (fun t ↦ (z t : ℂ))
      (vietaMvPoly t₀ i - MvPolynomial.X (.inl (.inr ()))) = 0}
  let totalSet :=
    Ω ∩ (⋂ j : Fin d, ⋃ S : Finset (Fin d), prepMultSet Ω D_re D_im j S) ∩ vietaSet
  have htotal : IsSemialgebraic totalSet :=
    (hΩ.inter (IsSemialgebraic.iInter fun j ↦
      IsSemialgebraic.iUnion fun S ↦ isSemialgebraic_prepMultSet hΩ hUD hmaps j S)).inter
      (isSemialgebraic_setOf_eval_ofReal_eq_zero _)
  refine isSemialgebraicOn_def.2 ⟨hB, ?_⟩
  convert htotal.setOf_exists_sumElim using 1
  ext p
  rw [mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hpB, hcp⟩
    let P := Polynomial.monicOfCoeff (fun m ↦ C m (fun s ↦ (p (.inl s) : ℂ)))
    obtain ⟨ζ, hζ⟩ := (Polynomial.exists_isRootEnumeration_iff_splits
      (R := ℂ) (f := P) (L := ℂ) (ι := Fin d)
      (by simp [P, Polynomial.natDegree_monicOfCoeff])).2
      (by simpa using IsAlgClosed.splits P)
    let w : Fin d → ℂ := fun j ↦ ζ j + (t₀ : ℂ)
    have hw_enum : P.IsRootEnumeration (fun j ↦ w j - (t₀ : ℂ)) := by
      simpa [w, add_sub_cancel_right] using hζ
    obtain ⟨hw_ball, hmult⟩ := (isRootEnumeration_monicOfCoeff_iff (hFan _ hpB) (hUan _ hpB)
      (hU0 _ hpB) (hfac _ hpB) (hroots _ hpB) w).1 hw_enum
    let u : Fin d ⊕ Fin d → ℝ := complexToRealPi (Fin d) w
    have hu_w (j : Fin d) : (u (.inl j) : ℂ) + u (.inr j) * I = w j := by simp [u]
    have hzΩ : Sum.elim p u ∈ Ω := ⟨hpB, mem_iInter.2 fun j ↦ by
      simpa only [mem_preimage, mem_ofPred_eq, rootPhi, Function.comp_apply, Sum.elim_inl,
        Sum.elim_inr, hu_w j] using hw_ball j⟩
    refine ⟨u, ⟨hzΩ, mem_iInter.2 fun j ↦ ?_⟩, ?_⟩
    · obtain ⟨S, hSj⟩ := hmult j
      exact mem_iUnion.2 ⟨S, (mem_prepMultSet_iff hpB hzΩ hDeq j S).2 (by simpa [hu_w] using hSj)⟩
    · have heval := eval_vietaMvPoly_of_isRootEnumeration (p := p) (u := u) (t₀ := t₀) (i := i)
        (by simpa only [P, hu_w] using hw_enum)
      have hCp : C i (fun s ↦ (p (.inl s) : ℂ)) = c i (p ∘ Sum.inl) := hCc (p ∘ Sum.inl) hpB i
      simp only [vietaSet, mem_ofPred_eq, map_sub, heval, hCp, MvPolynomial.eval_X, Sum.elim_inl,
        hcp, sub_self]
  · rintro ⟨u, ⟨hzΩ, hmult_u⟩, hvieta_u⟩
    have hpB : p ∘ Sum.inl ∈ ball x₀ δ := hzΩ.1
    refine ⟨hpB, ?_⟩
    let w : Fin d → ℂ := fun j ↦ (u (.inl j) : ℂ) + u (.inr j) * I
    have hw_ball (j : Fin d) : w j ∈ ball (t₀ : ℂ) R := mem_iInter.1 hzΩ.2 j
    have hw_enum :
        (Polynomial.monicOfCoeff (fun m ↦ C m (fun s ↦ (p (.inl s) : ℂ)))).IsRootEnumeration
          (fun j ↦ w j - (t₀ : ℂ)) :=
      (isRootEnumeration_monicOfCoeff_iff (hFan _ hpB) (hUan _ hpB) (hU0 _ hpB)
        (hfac _ hpB) (hroots _ hpB) w).2 ⟨hw_ball, fun j ↦ by
          obtain ⟨S, hS⟩ := mem_iUnion.1 (mem_iInter.1 hmult_u j)
          exact ⟨S, (mem_prepMultSet_iff hpB hzΩ hDeq j S).1 hS⟩⟩
    have heval := eval_vietaMvPoly_of_isRootEnumeration (p := p) (t₀ := t₀) (i := i) hw_enum
    have hCp : C i (fun s ↦ (p (.inl s) : ℂ)) = c i (p ∘ Sum.inl) := hCc (p ∘ Sum.inl) hpB i
    apply Complex.ofReal_injective
    exact sub_eq_zero.1 (by
      simpa only [vietaSet, mem_ofPred_eq, map_sub, heval, hCp, MvPolynomial.eval_X, Sum.elim_inl]
        using hvieta_u)

end Aux

/-! ### Public Nash Weierstrass preparation theorems -/

variable {σ : Type*} [Fintype σ]

/-- Evaluating `TauCeti.Polynomial.monicOfCoeff` at Nash coefficient and argument germs produces a
Nash germ. -/
theorem IsNashAt.eval_monicOfCoeff {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {r : (σ → ℝ) → ℝ}
    {x : σ → ℝ} (hc : ∀ i, IsNashAt (c i) x) (hr : IsNashAt r x) :
    IsNashAt (fun y ↦ (Polynomial.monicOfCoeff (fun i ↦ c i y)).eval (r y)) x := by
  simp_rw [Polynomial.eval_monicOfCoeff]
  exact (hr.fun_pow d).fun_add <| Finset.fun_isNashAt_sum _ fun i _ ↦ (hc i).fun_mul (hr.fun_pow _)

/-- If a Nash germ `f` factors near `Sum.elim x₀ (fun _ ↦ t₀)` as a Nash monic polynomial
`(TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀)` times a
real analytic germ `q`, then `q` is a Nash germ. -/
theorem IsNashAt.of_eventuallyEq_eval_monicOfCoeff_mul {f q : (σ ⊕ Unit → ℝ) → ℝ}
    {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀))) (hc : ∀ i, IsNashAt (c i) x₀)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀)))
    (h : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) := by
  have hP_nash : IsNashAt
      (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀))
      (Sum.elim x₀ (fun _ ↦ t₀)) :=
    IsNashAt.eval_monicOfCoeff
      (fun i ↦ (hc i).comp fun s ↦ isNashAt_apply (Sum.inl s))
      ((isNashAt_apply (Sum.inr ())).fun_sub (isNashAt_const t₀))
  refine hf.of_eventuallyEq_mul_left hP_nash (fun h0 ↦ ?_) hq h
  have hcont : Continuous fun s : ℝ ↦ Sum.elim x₀ (fun _ : Unit ↦ s + t₀) :=
    continuous_pi fun i ↦ by
      cases i with
      | inl _ => exact continuous_const
      | inr _ => exact continuous_id.add continuous_const
  have hline : (fun s : ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i x₀)).eval s) =ᶠ[𝓝 0] 0 := by
    have h0' : Sum.elim x₀ (fun _ : Unit ↦ (0 : ℝ) + t₀) = Sum.elim x₀ (fun _ ↦ t₀) := by
      ext (i | ⟨⟩) <;> simp
    filter_upwards [(hcont.tendsto 0).eventually (h0' ▸ h0)] with s hs
    simpa [add_sub_cancel_right] using hs
  have htop : analyticOrderAt
      (fun s : ℝ ↦ (Polynomial.monicOfCoeff (fun i ↦ c i x₀)).eval s) 0 = ⊤ :=
    analyticOrderAt_eq_top.2 hline
  rw [Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff _).ne_zero 0] at htop
  exact ENat.natCast_ne_top _ htop

/-- **Nashness of a Weierstrass preparation.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, and let
`f p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p`
be a real analytic Weierstrass preparation of `f` near `p₀`, with `c i` real analytic at `x₀` and
vanishing at `x₀`, and `u` real analytic and nonvanishing at `p₀`. Then every coefficient `c i` is
a Nash germ at `x₀` and `u` is a Nash germ at `p₀`. -/
theorem IsNashAt.of_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {u : (σ ⊕ Unit → ℝ) → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀)))
    (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p) :
    (∀ i, IsNashAt (c i) x₀) ∧ IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) := by
  -- Complexify `f`, `u`, and `c i`, and propagate the factorization by the real identity principle.
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let p₀ℂ : σ ⊕ Unit → ℂ := fun j ↦ (p₀ j : ℂ)
  obtain ⟨ρf, hρf, F, hF, hFf, _⟩ := hf.analyticAt.exists_complexification
  obtain ⟨ρu, hρu, U, hU, hUu, _⟩ := hu.exists_complexification
  choose ρc hρc C hC hCc _ using fun i ↦ (hc i).exists_complexification
  have hFan0 : AnalyticAt ℂ F p₀ℂ := hF _ (mem_ball_self hρf)
  have hUan0 : AnalyticAt ℂ U p₀ℂ := hU _ (mem_ball_self hρu)
  have hCan0 (i : Fin d) : AnalyticAt ℂ (C i) (fun s ↦ (x₀ s : ℂ)) := hC i _ (mem_ball_self (hρc i))
  have hU0ℂ : U p₀ℂ ≠ 0 := by rw [hUu p₀ (mem_ball_self hρu)]; exact_mod_cast hu0
  have hC0ℂ (i : Fin d) : C i (fun s ↦ (x₀ s : ℂ)) = 0 := by
    rw [hCc i x₀ (mem_ball_self (hρc i)), hc0 i, ofReal_zero]
  have hPan0 : AnalyticAt ℂ
      (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - (t₀ : ℂ)))
      p₀ℂ := by
    simp_rw [Polynomial.eval_monicOfCoeff]
    have hinl : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p ∘ Sum.inl) p₀ℂ :=
      analyticAt_pi_iff.2 fun s ↦
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inl s)).analyticAt p₀ℂ
    have hinr : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (Sum.inr ()) - (t₀ : ℂ)) p₀ℂ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ)
        (Sum.inr ())).analyticAt p₀ℂ).fun_sub analyticAt_const
    exact (hinr.fun_pow d).fun_add <| Finset.analyticAt_fun_sum _ fun i _ ↦
      ((hCan0 i).comp_of_eq hinl rfl).fun_mul (hinr.fun_pow _)
  have hfacℂ : F =ᶠ[𝓝 p₀ℂ] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - (t₀ : ℂ)) *
        U p := by
    refine hFan0.eventuallyEq_of_eventually_real (hPan0.fun_mul hUan0) ?_
    have hinl_cont : Continuous fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl :=
      continuous_pi fun s ↦ continuous_apply (Sum.inl s)
    filter_upwards [hfac, ball_mem_nhds p₀ hρf, ball_mem_nhds p₀ hρu,
      (hinl_cont.tendsto p₀).eventually
        (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρc i))] with y hy hyf hyu hyc
    rw [hFf y hyf, hUu y hyu]
    have hCy (i : Fin d) : C i ((fun j ↦ (y j : ℂ)) ∘ Sum.inl) = (c i (y ∘ Sum.inl) : ℂ) :=
      hCc i (y ∘ Sum.inl) (hyc i)
    simpa only [Polynomial.eval_monicOfCoeff, ofReal_mul, ofReal_add, ofReal_pow, ofReal_sum,
      ofReal_sub, hCy] using congrArg ((↑) : ℝ → ℂ) hy
  -- Choose a polydisc where vertical derivatives of `F` are semialgebraic, `U ≠ 0`, and all
  -- complex roots of `P_x` stay inside `ball 0 R`.
  obtain ⟨U_D, R, hR, hW_polydisc, hUD_polydisc, hUD_semi⟩ :=
    hf.exists_isSemialgebraicOn_complexification_iteratedDeriv_sumElim hFan0
      (eventually_of_mem (ball_mem_nhds p₀ hρf) hFf) (d + 1)
      (hFan0.eventually_analyticAt.and <| hUan0.eventually_analyticAt.and <|
        (hUan0.continuousAt.eventually_ne hU0ℂ).and hfacℂ)
  have hofReal_cont : Continuous fun x : σ → ℝ ↦ fun s ↦ (x s : ℂ) :=
    continuous_pi fun s ↦ Complex.continuous_ofReal.comp (continuous_apply s)
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 <|
    inter_mem (ball_mem_nhds x₀ hR) <|
      inter_mem (eventually_all.2 fun i ↦ ball_mem_nhds x₀ (hρc i))
        (TauCeti.Polynomial.eventually_norm_lt_of_isRoot_monicOfCoeff
          (fun i ↦ (hCan0 i).continuousAt.comp hofReal_cont.continuousAt) hC0ℂ hR)
  have hslice_an (x : σ → ℝ) (w : ℂ) :
      AnalyticAt ℂ (fun ζ : ℂ ↦ Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ)) w :=
    analyticAt_pi_iff.2 fun j ↦ by cases j with | inl _ => exact analyticAt_const | inr _ =>
      exact analyticAt_id
  -- Eliminate the complex root tuple via Vieta's formulas to make each `c i` Nash, then deduce `u`.
  have hc_nash (i : Fin d) : IsNashAt (c i) x₀ :=
    isNashAt_iff_exists_isSemialgebraicOn.2
      ⟨hc i, ball x₀ δ, isOpen_ball, mem_ball_self hδ, isSemialgebraic_ball x₀ δ,
        isSemialgebraicOn_coeff_of_weierstrassPreparation hUD_semi
          (fun _ hx _ hy ↦ hUD_polydisc _ (hδ_prop hx).1 _ hy)
          (fun _ _ _ _ ↦ ⟨rfl, rfl⟩)
          (fun x hx w hw ↦ ((hW_polydisc _ (hδ_prop hx).1 _ hw).1).comp_of_eq (hslice_an x w) rfl)
          (fun x hx w hw ↦ ((hW_polydisc _ (hδ_prop hx).1 _ hw).2.1).comp_of_eq (hslice_an x w) rfl)
          (fun _ hx _ hw ↦ (hW_polydisc _ (hδ_prop hx).1 _ hw).2.2.1)
          (fun _ hx _ hw ↦ (hW_polydisc _ (hδ_prop hx).1 _ hw).2.2.2)
          (fun x hx j ↦ hCc j x ((hδ_prop hx).2.1 j))
          (fun _ hx ζ hζ ↦ (hδ_prop hx).2.2 ζ hζ) i⟩
  exact ⟨hc_nash, hf.of_eventuallyEq_eval_monicOfCoeff_mul hc_nash hu hfac⟩

/-- **The Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d` at `t₀`. Then there exist Nash
coefficient germs `c : Fin d → (σ → ℝ) → ℝ` at `x₀` vanishing at `x₀` and a Nash germ `u` at `p₀`
nonvanishing at `p₀` such that near `p₀`,
`f p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p`.
-/
theorem IsNashAt.exists_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
  have hjoin : AnalyticAt ℝ (fun q : (σ → ℝ) × ℝ ↦ Sum.elim q.1 (fun _ : Unit ↦ q.2)) (x₀, t₀) :=
    analyticAt_pi_iff.2 fun i ↦ by
      cases i with
      | inl s =>
        exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) s).analyticAt x₀).comp_of_eq
          analyticAt_fst rfl
      | inr _ => exact analyticAt_snd
  obtain ⟨c, u₀, hc, hc0, hu₀, hu₀0, hfac₀⟩ :=
    (hf.analyticAt.comp_of_eq hjoin rfl).exists_weierstrassPreparation_real hd
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let split : (σ ⊕ Unit → ℝ) → (σ → ℝ) × ℝ := fun p ↦ (p ∘ Sum.inl, p (Sum.inr ()))
  have hsplit : AnalyticAt ℝ split p₀ :=
    (analyticAt_pi_iff.2 fun s ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ)
        (Sum.inl s)).analyticAt p₀).prod
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (Sum.inr ())).analyticAt p₀)
  let u : (σ ⊕ Unit → ℝ) → ℝ := u₀ ∘ split
  have hu : AnalyticAt ℝ u p₀ := hu₀.comp_of_eq hsplit rfl
  have hfac : f =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
    filter_upwards [(hsplit.continuousAt.tendsto).eventually hfac₀] with p hp
    have hp_eq : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ())) = p := by ext (s | ⟨⟩) <;> rfl
    simpa [u, split, hp_eq] using hp
  obtain ⟨hc_nash, hu_nash⟩ := hf.of_weierstrassPreparation hc hc0 hu hu₀0 hfac
  exact ⟨c, u, hc_nash, hc0, hu_nash, hu₀0, hfac⟩

end TauCeti
