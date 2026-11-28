/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FrobeniusRiesz.CharacterAverage
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.ScaleBounds
import TauCeti.NumberTheory.FrobeniusRiesz.TranslateAverage
import TauCeti.NumberTheory.FrobeniusRiesz.TopComparison
import TauCeti.NumberTheory.MulChar.Lemmas
import TauCeti.RepresentationTheory.LinearCharacter.QuadraticCoset

/-!
# Comparing Frobenius sums with cyclic-family remainders

Average the compensated prime sums over translates, project onto the characters trivial on the
translate subgroup, and use the `4 : 3` law of the top cosets to extract the cyclic family.
The cutoff in the scale is independent of the finite quotient carrying the Frobenius data.

The comparison follows Levent Alpöge's `Deduction.CharacterBalanceMoves.core` and
`Deduction.CharacterBalanceMoves.one_char` in [`ChCore.lean`][ch-core].

[ch-core]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
-/

public section

open Finset Function TauCeti
open scoped BigOperators ComplexConjugate

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- After averaging the compensated Frobenius sums over `H`, the thin caps cost at most the
thin-scale saving and the thick caps may be frozen at `b`. The remaining sum is over characters
trivial on `H`, with scale `a t / b` at each top `t`. The normalization uses the entire off-kernel
coset, not just the thick set `T`. -/
theorem norm_expect_sum_frobeniusRiesz_sub_projected_le {ι : Type*}
    (f : (ZMod N)ˣ →* G) (hf : Surjective f) (q : G →* ℂˣ) (hq : q * q = 1)
    (c d : G) (H : Subgroup G) [Fintype H]
    (tops : Finset G) (T : Finset H) (steps : Finset ι) (a : G → ℝ) (w : H → ι → G → ℝ)
    {x b b' D X S : ℝ} (hx : 3 ≤ x) (hD : 0 ≤ D) (hXb : b' * X ≤ x * b)
    (hscale : ∀ t ∈ tops, |a t / b - x| ≤ 1)
    (hJ : ∀ u : H, ∀ t ∈ tops, ∀ s ∈ T, q (d * u * s * t⁻¹) ≠ 1)
    (hw : ∀ (u : H) (k : ι), k ∈ steps → ∀ h ∈ q.ker, 0 < w u k h)
    (hthick : ∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ s ∈ T,
      w u k ((c * t) * (d * u * s * t⁻¹)) ∈ Set.Icc b (b + D))
    (hthin : ∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ g, q g ≠ 1 →
      (∀ s ∈ T, d * u * s * t⁻¹ ≠ g) → w u k ((c * t) * g) ≤ 2 * b')
    (hcoset : ∀ t ∈ tops, q (c * t) ≠ 1)
    (hthickCost : (Fintype.card (G →* ℂˣ) : ℝ) * (3 * (x + 1) * D) ≤ b / x)
    (hthinCost : (Fintype.card (G →* ℂˣ) : ℝ) * ((x + 1) * b * S) ≤ b / x) :
    let P (χ : G →* ℂˣ) := PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))
    let J := univ.filter (fun g ↦ q g ≠ 1)
    (∀ χ, ∀ y ≥ X / 3, ‖(P χ).rieszRemainder y‖ ≤ S * y) →
    ‖(𝔼 u : H, ∑ t ∈ tops, ∑ k ∈ steps,
        (2 * (↑(f.frobeniusRieszSum J (fun g ↦ w u k ((c * t) * g)) (a t)) : ℂ) -
          f.frobeniusRieszMainTerm q (w u k) (a t))) -
      ((steps.card : ℂ) * (b : ℂ) * T.card / J.card) *
        ∑ χ ∈ (univ : Finset (G →* ℂˣ)).filter (fun χ ↦ χ.comp H.subtype = 1),
          conj (χ d : ℂ) * ∑ t ∈ tops,
          (χ t : ℂ) * (P χ).rieszRemainder (a t / b)‖ ≤ tops.card * steps.card * (b / x) := by
  intro P J hsaving
  have hbalance (u : H) (t) (ht : t ∈ tops) (k) (hk : k ∈ steps) :=
    f.two_mul_frobeniusRieszSum_sub_frobeniusRieszMainTerm hf q hq (hcoset t ht) (hw u k hk) (a t)
  have havg : (𝔼 u : H, ∑ t ∈ tops, ∑ k ∈ steps,
      (2 * (↑(f.frobeniusRieszSum J (fun g ↦ w u k ((c * t) * g)) (a t)) : ℂ) -
        f.frobeniusRieszMainTerm q (w u k) (a t))) =
      𝔼 u : H, ∑ t ∈ tops, ∑ k ∈ steps, f.frobeniusRieszCharAverage q (c * t) (w u k) (a t) :=
    expect_congr rfl fun u _ ↦ sum_congr rfl fun t ht ↦
      sum_congr rfl fun k hk ↦ hbalance u t ht k hk
  rw [havg]
  simp_rw [frobeniusRieszCharAverage_def]
  have hdiv : 0 ≤ b / x := ((by positivity : 0 ≤
    (Fintype.card (G →* ℂˣ) : ℝ) * (3 * (x + 1) * D)).trans hthickCost)
  have hb₀ : 0 ≤ b := by simpa using (le_div_iff₀ (by linarith : 0 < x)).mp hdiv
  have hsurv (χ : G →* ℂˣ) : ((Units.coeHom ℂ).comp χ).comp H.subtype = 1 ↔
      χ.comp H.subtype = 1 := by
    simp [MonoidHom.ext_iff, ← Units.val_eq_one]
  have hscale' (t) (ht : t ∈ tops) : 0 < b ∧ 0 ≤ a t := by
    have hlo := (abs_le.mp (hscale t ht)).1
    have hb := hb₀.lt_of_ne' (fun h ↦ by simp [h] at hlo; linarith)
    exact ⟨hb, (mul_nonneg (by linarith : 0 ≤ x - 1) hb.le).trans
      ((le_div_iff₀ hb).mp (by linarith))⟩
  simpa only [card_univ, Units.coeHom_apply, comp_apply, hsurv] using
    H.norm_expect_sum_scaledRemainder_sub_card_mul_sum_filter_le J tops T steps univ
      (fun χ : G →* ℂˣ ↦ (Units.coeHom ℂ).comp χ) d (fun χ ↦ (P χ).rieszRemainder)
      a (fun u t k g ↦ w u k ((c * t) * g))
      (by simpa only [J, mem_filter, mem_univ, true_and] using hJ) hx hD hXb hscale hthick
      (fun u t ht k hk g hg hnot ↦ ⟨(hw u k hk _ (mem_ker.mpr
        ((q.apply_ne_one_iff_apply_mul_eq_one hq (hcoset t ht) g).mp (mem_filter.mp hg).2))).le,
        hthin u t ht k hk g (mem_filter.mp hg).2 hnot⟩)
      (fun χ _ ↦ hsaving χ) (fun t ht χ _ v hv ↦ by
        obtain ⟨hb, ha⟩ := hscale' t ht
        simpa only [min_eq_right hv.1, abs_of_nonneg (sub_nonneg.mpr hv.1)] using
          (P χ).norm_mul_rieszRemainder_div_sub_le ha (hb.trans_le hv.1) hb)
      (by simpa using hthickCost) (by simpa using hthinCost)

open scoped Classical in
private theorem exists_cyclicFamily_le_projected (ψ : PrimitiveDirichletCharacter) (C' : ℝ)
    {ε : ℝ} (hε : -(1 / 2) < ε) :
    ∃ x₀ ≥ (3 : ℝ), ∀ x ≥ x₀,
    ∀ {N : ℕ} [NeZero N] {G Q : Type*} [Group G] [Group Q] [Fintype Q]
      (f : (ZMod N)ˣ →* G), Surjective f →
    ∀ (tops : Finset G) (p : G → Q) (I K : Finset (G →* ℂˣ)) (ρ : (G →* ℂˣ) → Q →* ℂ)
      (d : G) (y : G → ℝ),
    let P (χ : G →* ℂˣ) := PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))
    Fintype.card Q = ψ.cyclicFamily.card → I.card ≤ 4 * ψ.cyclicFamily.card →
    K ⊆ I → K.image P = ψ.cyclicFamily →
    (∀ χ ∈ I, ∀ t ∈ tops, ρ χ (p t) = (χ t : ℂ)) →
    (∀ χ ∈ K, χ d = 1 ∧ (ρ χ = 1 ↔ χ = 1)) →
    (∀ j, |((tops.filter fun t ↦ p t = j).card : ℝ) -
      ((if j = 1 then 4 else 3) / (3 * (Fintype.card Q : ℝ) + 1)) * tops.card| ≤
        x ^ (-1 + ε) * tops.card) →
    (∀ t ∈ tops, |y t - x| ≤ 1) →
    (∀ χ ∈ I \ K, ‖logDeriv (P χ).character.LFunction 1‖ ≤ C' * Real.log x) →
    tops.card * ((∑ κ ∈ ψ.cyclicFamily, (if κ = 1 then 1 else
      (3 * (ψ.cyclicFamily.card : ℝ) + 1)⁻¹) * (κ.rieszRemainder x).re) -
      (∑ χ ∈ I \ K, ‖(P χ).rieszRemainder x‖) - 4 * x ^ (1 / 2 + ε)) ≤
      (∑ χ ∈ I, conj (χ d : ℂ) * ∑ t ∈ tops, (χ t : ℂ) * (P χ).rieszRemainder (y t)).re := by
  obtain ⟨C, hC, hR⟩ :=
    PrimitiveDirichletCharacter.exists_norm_rieszRemainder_sub_le_mul_log_and_norm_le
      ψ.cyclicFamily C'
  obtain ⟨x₀, hx₀, htop⟩ := exists_forall_ge_card_mul_le_sum_re_weighted_characters
    ψ.cyclicFamily.card C hε
  refine ⟨x₀, hx₀, fun x hx N _ G Q _ _ _ f hf tops p I K ρ d y ↦ ?_⟩
  intro P hQ hI hKI hK hρ hkeep hν hy hderiv
  have hP : Injective P := PrimitiveDirichletCharacter.of_injective.comp
    (MulChar.ofUnitHom_comp_injective hf)
  have hQ' (χ) (hχ : χ ∈ K) : ρ χ = 1 ↔ P χ = 1 :=
    (hkeep χ hχ).2.trans (PrimitiveDirichletCharacter.of_ofUnitHom_comp_eq_one_iff hf).symm
  have hR' (χ) (hχ : χ ∈ I) (v : ℝ) (hv : |v - x| ≤ 1) :=
    hR (P χ) (by linarith : 2 ≤ x) hv (fun hnot _ ↦ hderiv χ (mem_sdiff.mpr
      ⟨hχ, fun hm ↦ hnot (hK ▸ mem_image_of_mem P hm)⟩))
  have hnorm (χ : G →* ℂˣ) : ‖conj (χ d : ℂ)‖ ≤ 1 := by
    have : Finite G := Finite.of_surjective f hf
    rw [Complex.norm_conj, ← Units.coeHom_apply, ← comp_apply,
      (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite d)).norm_eq_one]
  have hb := htop x hx hQ.le tops p I K hKI hI ρ (fun χ ↦ conj (χ d : ℂ))
    (fun χ ↦ (P χ).rieszRemainder x) (fun χ t ↦ (P χ).rieszRemainder (y t)) hν
    (fun χ _ ↦ hnorm χ) (fun χ hχ ↦ by simp [(hkeep χ hχ).1])
    (fun χ hχ t ht ↦ by simpa [abs_of_pos hC] using (hR' χ hχ _ (hy t ht)).1)
    (fun χ hχ ↦ by simpa [abs_of_pos hC] using (hR' χ (hKI hχ) x (by simp : |x - x| ≤ 1)).2)
  have hsum : (∑ χ ∈ K, (if ρ χ = 1 then 1 else (3 * (Fintype.card Q : ℝ) + 1)⁻¹) *
      ((P χ).rieszRemainder x).re) = ∑ κ ∈ ψ.cyclicFamily,
        (if κ = 1 then 1 else (3 * (ψ.cyclicFamily.card : ℝ) + 1)⁻¹) * (κ.rieszRemainder x).re := by
    rw [← hK, sum_image hP.injOn, hK, hQ]
    exact sum_congr rfl fun χ hχ ↦ by rw [hQ' χ hχ]
  rw [hsum] at hb
  rw [Complex.re_sum]
  refine hb.trans_eq (sum_congr rfl fun χ hχ ↦ ?_)
  rw [sum_congr rfl fun t ht ↦ by rw [hρ χ hχ t ht]]

open scoped Classical in
/-- A lower bound for the mean compensated Frobenius sum in terms of the cyclic family's
weighted Riesz remainder, with weights `1` and `1 / (3 * #𝒦 + 1)`. The kept characters `K`
represent the cyclic family; the other characters trivial on `H` contribute their remainder
norms to the error. The cutoff depends only on `ψ`, the log-derivative bound constant `C'`, and
the precision exponent, not on the host data. -/
theorem exists_cyclicFamily_riesz_le_of_frobeniusRiesz (ψ : PrimitiveDirichletCharacter) (C' : ℝ)
    {ε : ℝ} (hε : -(1 / 2) < ε) :
    ∃ x₀ ≥ (3 : ℝ), ∀ x ≥ x₀,
    ∀ {N : ℕ} [NeZero N] {G Q ι : Type*} [Group G] [Fintype G] [Group Q] [Fintype Q]
      (f : (ZMod N)ˣ →* G), Surjective f →
    ∀ (q : G →* ℂˣ), q * q = 1 → ∀ c d : G,
    ∀ (H : Subgroup G) [Fintype H] (tops : Finset G) (T : Finset H) (steps : Finset ι)
      (a : G → ℝ) (w : H → ι → G → ℝ) (p : G → Q) (K : Finset (G →* ℂˣ))
      (ρ : (G →* ℂˣ) → Q →* ℂ) (b b' D X S : ℝ),
    let P (χ : G →* ℂˣ) := PrimitiveDirichletCharacter.of (MulChar.ofUnitHom (χ.comp f))
    let J := univ.filter (fun g ↦ q g ≠ 1)
    let I := (univ : Finset (G →* ℂˣ)).filter (fun χ ↦ χ.comp H.subtype = 1)
    0 ≤ D → b' * X ≤ x * b →
    (∀ t ∈ tops, |a t / b - x| ≤ 1) →
    (∀ u : H, ∀ t ∈ tops, ∀ s ∈ T, q (d * u * s * t⁻¹) ≠ 1) →
    (∀ (u : H) (k : ι), k ∈ steps → ∀ h ∈ q.ker, 0 < w u k h) →
    (∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ s ∈ T,
      w u k ((c * t) * (d * u * s * t⁻¹)) ∈ Set.Icc b (b + D)) →
    (∀ (u : H) t, t ∈ tops → ∀ k ∈ steps, ∀ g, q g ≠ 1 →
      (∀ s ∈ T, d * u * s * t⁻¹ ≠ g) → w u k ((c * t) * g) ≤ 2 * b') →
    (∀ t ∈ tops, q (c * t) ≠ 1) →
    (∀ χ, ∀ y ≥ X / 3, ‖(P χ).rieszRemainder y‖ ≤ S * y) →
    (Fintype.card (G →* ℂˣ) : ℝ) * (3 * (x + 1) * D) ≤ b / x →
    (Fintype.card (G →* ℂˣ) : ℝ) * ((x + 1) * b * S) ≤ b / x →
    Fintype.card Q = ψ.cyclicFamily.card → I.card ≤ 4 * ψ.cyclicFamily.card →
    K ⊆ I → K.image P = ψ.cyclicFamily →
    (∀ χ ∈ I, ∀ t ∈ tops, ρ χ (p t) = (χ t : ℂ)) →
    (∀ χ ∈ K, χ d = 1 ∧ (ρ χ = 1 ↔ χ = 1)) →
    (∀ j, |((tops.filter fun t ↦ p t = j).card : ℝ) -
      ((if j = 1 then 4 else 3) / (3 * (Fintype.card Q : ℝ) + 1)) * tops.card| ≤
        x ^ (-1 + ε) * tops.card) →
    (∀ χ ∈ I \ K, ‖logDeriv (P χ).character.LFunction 1‖ ≤ C' * Real.log x) →
    (tops.card : ℝ) * steps.card * b * (T.card / (J.card : ℝ)) *
      ((∑ κ ∈ ψ.cyclicFamily, (if κ = 1 then 1 else
        (3 * (ψ.cyclicFamily.card : ℝ) + 1)⁻¹) * (κ.rieszRemainder x).re) -
        (∑ χ ∈ I \ K, ‖(P χ).rieszRemainder x‖) - 4 * x ^ (1 / 2 + ε)) ≤
      (𝔼 u : H, ∑ t ∈ tops, ∑ k ∈ steps,
        (2 * f.frobeniusRieszSum J (fun g ↦ w u k ((c * t) * g)) (a t) -
          (f.frobeniusRieszMainTerm q (w u k) (a t)).re)) + tops.card * steps.card * (b / x) := by
  obtain ⟨x₀, hx₀, htop⟩ := exists_cyclicFamily_le_projected ψ C' hε
  refine ⟨x₀, hx₀, fun x hx N _ G Q ι _ _ _ _ f hf q hq c d H _ tops T steps a w p K ρ
    b b' D X S ↦ ?_⟩
  intro P J I hD hXb hscale hJ hw hthick hthin hcoset hsaving hthickCost hthinCost
    hQ hI hKI hK hρ hkeep hν hderiv
  have htop' := htop x hx f hf tops p I K ρ d (fun t ↦ a t / b)
    hQ hI hKI hK hρ hkeep hν hscale hderiv
  have hx3 := hx₀.trans hx
  have he := f.norm_expect_sum_frobeniusRiesz_sub_projected_le hf q hq c d H tops T steps a w
    hx3 hD hXb hscale hJ hw hthick hthin hcoset hthickCost hthinCost hsaving
  rw [norm_sub_rev] at he
  have hle := (Complex.re_le_norm _).trans he
  have hb : 0 ≤ b := by
    have hdiv := (show 0 ≤ (Fintype.card (G →* ℂˣ) : ℝ) * (3 * (x + 1) * D) by positivity).trans
      hthickCost
    simpa using (le_div_iff₀ (by linarith : 0 < x)).mp hdiv
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (T.card),
    ← Complex.ofReal_natCast J.card, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, Complex.sub_re, Complex.re_ofReal_mul] at hle
  simp only [Complex.re_expect, Complex.re_sum, Complex.sub_re, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hle
  have hmul := mul_le_mul_of_nonneg_left htop'
    (show 0 ≤ (steps.card : ℝ) * b * T.card / J.card by positivity)
  rw [Complex.re_sum] at hmul
  convert hmul.trans (sub_le_iff_le_add.mp hle) using 1 <;> ring

end MonoidHom
