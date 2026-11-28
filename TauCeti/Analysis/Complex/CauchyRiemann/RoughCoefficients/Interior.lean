/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

/-!
# Interior `W^{1,r}` regularity for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}_loc(Ω; End V)` with `J² = -1` and `S ∈ Lᵖ_loc(Ω; End V)`,
`p > 2`, consider a weak solution `ξ ∈ L^q_loc` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, with `1/p + 1/q < 1`. This file proves that if
`η ∈ Lʳ_loc` for some `1 < r < ∞` with `r ≤ p`, then `ξ ∈ W^{1,r}_loc(Ω)`
(`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`). This is the first-order case of interior
regularity with Sobolev coefficients: taking `r = q ≤ p` gives `ξ ∈ W^{1,q}_loc` whenever
`η ∈ L^q_loc`, and taking `r = p` gives `ξ ∈ W^{1,p}_loc` whenever `η ∈ Lᵖ_loc`. In McDuff and
Salamon's induction on the order of differentiability, this case is applied to the first
derivatives of a solution, which solve the differentiated system of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated`.

The order-zero lemma `TauCeti.IsWeakCRSolution.memWkpLoc_one` only gains a derivative at the cost
of integrability: from `ξ ∈ Lˢ_loc` it gives `ξ ∈ W^{1,r'}_loc` for `1/r' = 1/p + 1/s`. The
two-dimensional Sobolev embedding then gives back `ξ ∈ L^{s'}_loc` with `1/s' = 1/r' - 1/2`, which
is better than `Lˢ_loc` because `1/s' = 1/s - (1/2 - 1/p)` and `p > 2`. Iterating, the reciprocal
exponent of `ξ` decreases by a fixed amount at each step until either `1/p + 1/s ≤ 1/r`, when one
last application of the order-zero lemma gives `W^{1,r}_loc`, or `r' > 2`, when Morrey's embedding
makes `ξ` locally bounded and the last step applies with `s = ∞`. To avoid the critical exponent
`r' = 2` of the Sobolev embedding, each step lowers the reciprocal exponent by only
`d = (1/2 - 1/p) / 2`.

The exponent ladder `TauCeti.exists_finite_sobolev_exponent_ladder` records the same arithmetic
for one particular starting exponent; here the starting exponent `q` and the target `r` are
arbitrary, so the induction runs on the reciprocal exponents directly.

## Main results

* `TauCeti.exists_inv_le_inv_sub_and_eLpNorm_le_mul_eLpNormWkp_one`: one rung of the exponent
  ladder, the Sobolev or Morrey estimate of `W^{1,r'}` for `1/r' = 1/p + 1/s`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`: interior `W^{1,r}` regularity for `r ≤ p`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemmas B.4.4 and B.4.6 and Proposition B.4.9.
-/

public section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

section Rung

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **One rung of the exponent ladder.** Let `p > 2` and `1 ≤ r'` with `1/r' = 1/p + 1/s`. There
is an exponent `s'` with `1/s' ≤ 1/s - (1/2 - 1/p) / 2` and the local estimate
`‖u‖_{L^{s'}(U)} ≤ C ‖u‖_{W^{1,r'}(W)}` whenever `U` has compact closure in the open set `W`; so
`W^{1,r'}_loc ⊂ L^{s'}_loc` (`TauCeti.MemWkpLoc.memLpLoc_of_forall_exists_eLpNorm_le`). For
`r' > 2` this is Morrey's embedding with `s' = ∞`; otherwise it is the Sobolev embedding with
`1/s' = 1/s - (1/2 - 1/p) / 2`, which stays away from the critical exponent `r' = 2`. -/
theorem exists_inv_le_inv_sub_and_eLpNorm_le_mul_eLpNormWkp_one (hp : 2 < p)
    {s : ℝ≥0∞} (hr' : 1 ≤ (p⁻¹ + s⁻¹)⁻¹) :
    ∃ s' : ℝ≥0∞, s'⁻¹ ≤ s⁻¹ - (2⁻¹ - p⁻¹) / 2 ∧
      ∀ {U : Set ℂ} {W : Opens ℂ}, IsCompact (closure U) → closure U ⊆ W →
        ∃ C : ℝ≥0, ∀ u : ℂ → F,
          eLpNorm u s' (volume.restrict U) ≤ C * eLpNormWkp (p⁻¹ + s⁻¹)⁻¹ W 1 u := by
  have hp2 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
  set d : ℝ≥0∞ := (2⁻¹ - p⁻¹) / 2 with hd_def
  have hd : 0 < d := ENNReal.div_pos (tsub_pos_of_lt hp2).ne' ENNReal.ofNat_ne_top
  have hd_top : d ≠ ⊤ := ENNReal.div_ne_top (by finiteness) two_ne_zero
  have hpd : p⁻¹ + d + d = 2⁻¹ := by
    rw [add_assoc, hd_def, ENNReal.add_halves, add_tsub_cancel_of_le hp2.le]
  set r' : ℝ≥0∞ := (p⁻¹ + s⁻¹)⁻¹
  have hr'_inv : r'⁻¹ = p⁻¹ + s⁻¹ := inv_inv _
  by_cases h2r' : 2 < r'
  · -- Morrey: `u` is locally bounded.
    exact ⟨⊤, by simp, fun hUc hUW => exists_eLpNorm_top_le_mul_eLpNormWkp_one h2r' hUc hUW⟩
  -- Sobolev: `1/s' = 1/s - d`.
  rw [not_lt] at h2r'
  have hds : d < s⁻¹ := by
    refine (ENNReal.lt_add_right hd_top hd.ne').trans_le ?_
    rw [← ENNReal.add_le_add_iff_left (ENNReal.inv_ne_top.2 (zero_lt_two.trans hp).ne'),
      ← add_assoc, hpd, ← hr'_inv]
    exact ENNReal.inv_le_inv.2 h2r'
  have hs'_inv : (s⁻¹ - d)⁻¹⁻¹ = s⁻¹ - d := inv_inv _
  have hs'_top : (s⁻¹ - d)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hds).ne'
  have hr's : r' ≤ (s⁻¹ - d)⁻¹ := by
    refine ENNReal.inv_le_inv.1 ?_
    rw [hs'_inv, hr'_inv]
    exact tsub_le_self.trans le_add_self
  have hgap : r'⁻¹ - (s⁻¹ - d)⁻¹⁻¹ ≤ 2⁻¹ := by
    rw [tsub_le_iff_right, hs'_inv, hr'_inv]
    calc p⁻¹ + s⁻¹ = p⁻¹ + d + (s⁻¹ - d) := by
          rw [add_assoc, add_comm d, tsub_add_cancel_of_le hds.le]
      _ ≤ p⁻¹ + d + d + (s⁻¹ - d) := by gcongr; exact le_self_add
      _ = 2⁻¹ + (s⁻¹ - d) := by rw [hpd]
  exact ⟨(s⁻¹ - d)⁻¹, hs'_inv.le, fun hUc hUW =>
    exists_eLpNorm_le_mul_eLpNormWkp_one_of_ne_top hr' hs'_top hr's hgap hUc hUW⟩

end Rung

namespace IsWeakCRSolution

/-- One rung of the ladder. If a weak solution `ξ` is locally `Lˢ` with `1/s ≤ 1/q` and
`1/p + 1/s > 1/r`, the order-zero lemma followed by the Sobolev or Morrey embedding makes `ξ`
locally `L^{s'}` for some `s'` with `1/s' ≤ 1/s - (1/2 - 1/p) / 2`. -/
private theorem exists_memLpLoc_inv_le_inv_sub [FiniteDimensional ℝ V]
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hpq : p⁻¹ + q⁻¹ < 1)
    (hη : MemLpLoc r Ω η) {s : ℝ≥0∞} (hsq : s⁻¹ ≤ q⁻¹) (hs : MemLpLoc s Ω ξ)
    (hsr : r⁻¹ < p⁻¹ + s⁻¹) :
    ∃ s' : ℝ≥0∞, s'⁻¹ ≤ s⁻¹ - (2⁻¹ - p⁻¹) / 2 ∧ MemLpLoc s' Ω ξ := by
  -- The order-zero lemma, with `1/r' = 1/p + 1/s`.
  have hr'_inv : (p⁻¹ + s⁻¹)⁻¹⁻¹ = p⁻¹ + s⁻¹ := inv_inv _
  have hr'1 : 1 < (p⁻¹ + s⁻¹)⁻¹ := ENNReal.one_lt_inv.2 ((add_le_add le_rfl hsq).trans_lt hpq)
  have hw : MemWkpLoc (p⁻¹ + s⁻¹)⁻¹ Ω 1 ξ := (h.of_memLpLoc hs).memWkpLoc_one hc hp hJ2 hr'1
    (ENNReal.inv_ne_top.2 (pos_of_gt hsr).ne') hr'_inv.ge
      (hη.mono_exponent (ENNReal.inv_le_inv.1 (by rw [hr'_inv]; exact hsr.le)))
  obtain ⟨s', hs', hest⟩ :=
    exists_inv_le_inv_sub_and_eLpNorm_le_mul_eLpNormWkp_one (F := V) hp hr'1.le
  exact ⟨s', hs', hw.memLpLoc_of_forall_exists_eLpNorm_le hest⟩

/-- **Interior `W^{1,r}` regularity.** Let `J ∈ W^{1,p}_loc` with `J² = -1` and `S ∈ Lᵖ_loc`,
`p > 2`, and let `ξ ∈ L^q_loc` be a weak solution of `∂_s ξ + J ∂_t ξ + S ξ = η` with
`1/p + 1/q < 1`. If `η ∈ Lʳ_loc` with `1 < r < ∞` and `r ≤ p`, then `ξ ∈ W^{1,r}_loc`.

Unlike the order-zero lemma `TauCeti.IsWeakCRSolution.memWkpLoc_one`, no relation between `q` and
`r` beyond `1/p + 1/q < 1` is needed; in particular `r = q ≤ p` gives `ξ ∈ W^{1,q}_loc` from
`η ∈ L^q_loc`. -/
theorem memWkpLoc_one_of_le [FiniteDimensional ℝ V] (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hrp : r ≤ p) (hη : MemLpLoc r Ω η) : MemWkpLoc r Ω 1 ξ := by
  -- Each rung lowers the reciprocal exponent of `ξ` by `d`.
  set d : ℝ≥0∞ := (2⁻¹ - p⁻¹) / 2
  have hd : 0 < d :=
    ENNReal.div_pos (tsub_pos_of_lt (ENNReal.inv_lt_inv.2 hp)).ne' ENNReal.ofNat_ne_top
  have hd_top : d ≠ ⊤ := ENNReal.div_ne_top (by finiteness) two_ne_zero
  -- The last step: once `1/p + 1/s ≤ 1/r`, the order-zero lemma gives `W^{1,r}_loc`.
  have hlast : ∀ s : ℝ≥0∞, MemLpLoc s Ω ξ → p⁻¹ + s⁻¹ ≤ r⁻¹ → MemWkpLoc r Ω 1 ξ :=
    fun s hs hsr => (h.of_memLpLoc hs).memWkpLoc_one hc hp hJ2 hr hr_top hsr hη
  -- After `n` more rungs the last step applies.
  suffices H : ∀ n : ℕ, ∀ s : ℝ≥0∞, s⁻¹ ≤ q⁻¹ → MemLpLoc s Ω ξ →
      s⁻¹ ≤ r⁻¹ - p⁻¹ + n * d → MemWkpLoc r Ω 1 ξ by
    have hq_top : q⁻¹ ≠ ⊤ := ((le_add_self.trans_lt hpq).trans ENNReal.one_lt_top).ne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hq_top hd.ne')
    have hqn : q⁻¹ ≤ n * d := (ENNReal.div_le_iff hd.ne' hd_top).1 hn.le
    exact H n q le_rfl h.memLpLoc (hqn.trans le_add_self)
  intro n
  induction n with
  | zero =>
    intro s _ hs hsn
    rw [Nat.cast_zero, zero_mul, add_zero] at hsn
    exact hlast s hs (add_le_of_le_tsub_left_of_le (ENNReal.inv_le_inv.2 hrp) hsn)
  | succ n ih =>
    intro s hsq hs hsn
    by_cases hsr : p⁻¹ + s⁻¹ ≤ r⁻¹
    · exact hlast s hs hsr
    obtain ⟨s', hs's, hs'⟩ := h.exists_memLpLoc_inv_le_inv_sub hc hp hJ2 hpq hη hsq hs
      (not_le.1 hsr)
    refine ih s' (hs's.trans (tsub_le_self.trans hsq)) hs' (hs's.trans ?_)
    rw [tsub_le_iff_right]
    calc s⁻¹ ≤ r⁻¹ - p⁻¹ + ↑(n + 1) * d := hsn
      _ = r⁻¹ - p⁻¹ + ↑n * d + d := by push_cast; ring

end IsWeakCRSolution

end TauCeti
