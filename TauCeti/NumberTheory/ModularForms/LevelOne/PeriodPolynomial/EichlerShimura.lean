/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.ParityDimension
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Parity
import TauCeti.NumberTheory.ModularForms.LevelOne.Newform
import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.LValue
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The Eichler–Shimura theorem for odd period polynomials

Let `f` be a cusp form of weight `k = w + 2` on `SL(2, ℤ)`, with even and odd period polynomials
`r_f^±` (`TauCeti.evenPeriodPolynomial`, `TauCeti.oddPeriodPolynomial`). This file proves that
both maps `f ↦ r_f^±` are injective, and that the odd one is an isomorphism
`S_k(SL(2, ℤ)) ≃ W_w^-` onto the odd period polynomials which intertwines the Hecke operator `Tₙ`
with the action of every solution `ξ` of Popa and Zagier's period relation (A). In particular
`tr(Tₙ | S_k(SL(2, ℤ))) = tr(ξ | W_w^-)`, which is how the trace of `Tₙ` on cusp forms is read off
period polynomials.

The argument goes through Hecke eigenforms, not through a pairing on period polynomials. The maps
`f ↦ r_f^±` intertwine `Tₙ` with the action of a solution of (A)
(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_oddPeriodPolynomial` and its even
analogue). At level one every cusp form is new, so the newforms of level one span
`S_k(SL(2, ℤ))`, and each is an eigenvector of every `Tₙ` with eigenvalue its Fourier coefficient
`aₙ`. Their period polynomials `r^±` are therefore joint eigenvectors of the actions of the
solutions of (A), with pairwise distinct eigenvalue systems, and so linearly independent as soon
as they are nonzero. They are nonzero because a coefficient of `r^-`, respectively `r^+`, is a
nonzero multiple of the critical value `L(f, w)`, respectively `L(f, w + 1)`
(`TauCeti.oddPeriodPolynomial_ne_zero`, `TauCeti.evenPeriodPolynomial_ne_zero`), and for `k ≥ 12`
both points lie in the half-plane `Re s > k/2 + 1` where the Euler product of a newform does not
vanish. In odd weight and below weight `12` there are no nonzero cusp forms.

Since `dim W_w^- = dim S_k(SL(2, ℤ))` (`TauCeti.finrank_oddPeriodPolynomials_eq_finrank_cuspForm`),
the injective odd period map is an isomorphism. The even period map is injective but not onto:
`dim W_w^+ = dim M_k(SL(2, ℤ))` (`TauCeti.finrank_evenPeriodPolynomials_eq_finrank_modularForm`),
which exceeds `dim S_k(SL(2, ℤ))` by one for even `k ≥ 4`.

## Main definitions

* `TauCeti.oddPeriodPolynomialEquiv hk`: the linear isomorphism `f ↦ r_f^-` from
  `S_k(SL(2, ℤ))` onto `W_w^-`.

## Main results

* `TauCeti.oddPeriodPolynomial_injective`, `TauCeti.evenPeriodPolynomial_injective`: the maps
  `f ↦ r_f^-` and `f ↦ r_f^+` are injective.
* `TauCeti.oddPeriodPolynomial_surjective`: every odd period polynomial is `r_f^-` for a cusp
  form `f`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_mem_oddPeriodPolynomials`: every
  solution of the period relation (A) preserves `W_w^-`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.oddPeriodPolynomialEquiv_conj_heckeTCuspLevelOne`
  says that on `W_w^-` it acts as `Tₙ` transported along the odd period map.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.trace_heckeTCuspLevelOne`:
  `tr(Tₙ | S_k(SL(2, ℤ))) = tr(ξ | W_w^-)`.

## References

* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
* Y. I. Manin, *Periods of parabolic forms and p-adic Hecke series*, Mat. Sb. **92** (1973),
  378–401, §1.
-/

public section

open MonoidAlgebra MvPolynomial CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
  UpperHalfPlane TauCeti.TraceFormulaMatrixModule
open scoped MatrixGroups

namespace TauCeti

variable {k : ℤ} {w : ℕ}

/-- For `k = w + 2 ≥ 12`, the `L`-function of a newform of level one does not vanish at any `s`
with `Re s ≥ w`, in particular at the critical values `s = w` and `s = w + 1` seen by the period
polynomials. -/
private theorem L_ne_zero_of_le_re (hk : k = w + 2) (hw : 10 ≤ w) (g : Newform 1 k) {s : ℂ}
    (hs : (w : ℝ) ≤ s.re) :
    ModularForm.L (by omega) (cuspFormGamma1OneEquiv g.toCuspForm) s ≠ 0 :=
  g.L_cuspFormGamma1OneEquiv_ne_zero _ <| by
    have : (k : ℝ) = w + 2 := by exact_mod_cast hk
    have : (10 : ℝ) ≤ w := by exact_mod_cast hw
    linarith

/-- A linear map from `S_k(SL(2, ℤ))`, `k = w + 2`, to a space of binary forms of degree `w`
that intertwines every `Tₙ` with the action of every solution of the period relation (A), and
is nonzero on every newform of weight `k ≥ 12`, is injective. -/
private theorem injective_of_periodAction (hk : k = w + 2)
    {p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ w)} (Φ : CuspForm 𝒮ℒ k →ₗ[ℂ] p)
    (hΦ : ∀ (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]},
      PeriodRelation ℂ n ξ → ∀ f, periodAction hw ξ (Φ f) = Φ (heckeTCuspLevelOne k n f))
    (hne : ∀ g : Newform 1 k, 10 ≤ w → Φ (cuspFormGamma1OneEquiv g.toCuspForm) ≠ 0) :
    Function.Injective Φ := by
  by_cases h : Even w ∧ 12 ≤ k
  · obtain ⟨hw, h12⟩ := h
    choose ξ hξ using fun n : ℕ+ ↦ exists_periodRelation ℂ ((n : ℕ) : ℤ)
    refine fun f f' hff' ↦ injective_of_map_heckeTCuspLevelOne_eq (p.subtype ∘ₗ Φ)
      (fun n ↦ periodAction hw (ξ n)) (fun n f ↦ (hΦ hw n (hξ n) f).symm)
      (fun g h0 ↦ hne g (by omega) (Subtype.ext h0)) (by simp [hff'])
  · have : Subsingleton (CuspForm 𝒮ℒ k) := subsingleton_cuspForm_levelOne <| by
      by_cases hw : Even w
      · exact .inr (not_le.1 fun h12 ↦ h ⟨hw, h12⟩)
      · exact .inl (hk ▸ (Nat.not_even_iff_odd.1 hw).natCast.add_even even_two)
    exact Function.injective_of_subsingleton _

/-! ### Injectivity of the even and odd period maps -/

/-- **The odd period polynomial determines the cusp form**: `f ↦ r_f^-` is injective on
`S_k(SL(2, ℤ))`. -/
theorem oddPeriodPolynomial_injective (hk : k = w + 2) :
    Function.Injective (oddPeriodPolynomial hk) :=
  injective_of_periodAction hk _ (fun hw n _ _ h f ↦ h.periodAction_oddPeriodPolynomial hk hw n f)
    fun g hw ↦ oddPeriodPolynomial_ne_zero hk _ (by omega) <| L_ne_zero_of_le_re hk hw g (by simp)

/-- **The even period polynomial determines the cusp form**: `f ↦ r_f^+` is injective on
`S_k(SL(2, ℤ))`. -/
theorem evenPeriodPolynomial_injective (hk : k = w + 2) :
    Function.Injective (evenPeriodPolynomial hk) :=
  injective_of_periodAction hk _ (fun hw n _ _ h f ↦ h.periodAction_evenPeriodPolynomial hk hw n f)
    fun g hw ↦ evenPeriodPolynomial_ne_zero hk _ <| L_ne_zero_of_le_re hk hw g (by simp)

/-! ### The odd period map is an isomorphism -/

/-- **Every odd period polynomial is the odd period polynomial of a cusp form**: `f ↦ r_f^-` is
an injective linear map between spaces of the same dimension. -/
theorem oddPeriodPolynomial_surjective (hk : k = w + 2) :
    Function.Surjective (oddPeriodPolynomial hk) := by
  have hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = Module.finrank ℂ (oddPeriodPolynomials ℂ w) := by
    rw [finrank_oddPeriodPolynomials_eq_finrank_cuspForm w, hk]
    norm_cast
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (V := CuspForm 𝒮ℒ k)
    (V₂ := oddPeriodPolynomials ℂ w) hdim).1 (oddPeriodPolynomial_injective hk)

/-- **The Eichler–Shimura isomorphism for odd period polynomials**: the odd period map
`f ↦ r_f^-` is a linear isomorphism from the cusp forms of weight `k = w + 2` on `SL(2, ℤ)` onto
the odd period polynomials `W_w^-`. -/
noncomputable def oddPeriodPolynomialEquiv (hk : k = w + 2) :
    CuspForm 𝒮ℒ k ≃ₗ[ℂ] oddPeriodPolynomials ℂ w :=
  LinearEquiv.ofBijective (oddPeriodPolynomial hk)
    ⟨oddPeriodPolynomial_injective hk, oddPeriodPolynomial_surjective hk⟩

/-- The odd period isomorphism sends `f` to its odd period polynomial `r_f^-`. -/
@[simp]
theorem oddPeriodPolynomialEquiv_apply (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    oddPeriodPolynomialEquiv hk f = oddPeriodPolynomial hk f :=
  (rfl)

/-- The odd period polynomial of the cusp form corresponding to `P ∈ W_w^-` is `P`. -/
@[simp]
theorem oddPeriodPolynomial_oddPeriodPolynomialEquiv_symm_apply (hk : k = w + 2)
    (P : oddPeriodPolynomials ℂ w) :
    oddPeriodPolynomial hk ((oddPeriodPolynomialEquiv hk).symm P) = P :=
  (oddPeriodPolynomialEquiv hk).apply_symm_apply P

namespace TraceFormulaMatrixModule

/-- **A solution of the period relation preserves the odd period polynomials.** For `n ≥ 1` and
even `w`, every solution `ξ` of the period relation (A) maps `W_w^-` into itself: each odd period
polynomial is `r_f^-` for a cusp form `f`, and `r_f^- ∣ ξ = r_{Tₙ f}^-`. -/
theorem PeriodRelation.periodAction_mem_oddPeriodPolynomials (hw : Even w) (n : ℕ) [NeZero n]
    {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    {P : homogeneousSubmodule (Fin 2) ℂ w} (hP : P ∈ oddPeriodPolynomials ℂ w) :
    periodAction hw ξ P ∈ oddPeriodPolynomials ℂ w := by
  obtain ⟨f, hf⟩ := oddPeriodPolynomial_surjective (k := w + 2) rfl ⟨P, hP⟩
  have hf' : (oddPeriodPolynomial rfl f : homogeneousSubmodule (Fin 2) ℂ w) = P :=
    congrArg Subtype.val hf
  rw [← hf', h.periodAction_oddPeriodPolynomial rfl hw n f]
  exact Submodule.coe_mem _

/-- **On odd period polynomials, a solution of the period relation acts as `Tₙ`.** For `n ≥ 1`
and every solution `ξ` of the period relation (A), the restriction of the action of `ξ` to
`W_w^-` is the Hecke operator `Tₙ` on `S_k(SL(2, ℤ))`, `k = w + 2`, transported along the odd
period map `TauCeti.oddPeriodPolynomialEquiv`. -/
theorem PeriodRelation.oddPeriodPolynomialEquiv_conj_heckeTCuspLevelOne (hk : k = w + 2)
    (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℂ n ξ) :
    (oddPeriodPolynomialEquiv hk).conj (heckeTCuspLevelOne k n) =
      (periodAction hw ξ).restrict fun _ hP ↦ h.periodAction_mem_oddPeriodPolynomials hw n hP := by
  refine LinearMap.ext fun P ↦ ?_
  obtain ⟨f, rfl⟩ := (oddPeriodPolynomialEquiv hk).surjective P
  refine Subtype.ext ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [h.periodAction_oddPeriodPolynomial hk hw n f]

/-- **The trace of `Tₙ` on cusp forms is its trace on odd period polynomials**: for `n ≥ 1` and
every solution `ξ` of the period relation (A), `tr(Tₙ | S_k(SL(2, ℤ))) = tr(ξ | W_w^-)`,
`k = w + 2`. -/
theorem PeriodRelation.trace_heckeTCuspLevelOne (hk : k = w + 2) (hw : Even w) (n : ℕ) [NeZero n]
    {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ) :
    LinearMap.trace ℂ _ (heckeTCuspLevelOne k n) =
      LinearMap.trace ℂ _ ((periodAction hw ξ).restrict
        fun _ hP ↦ h.periodAction_mem_oddPeriodPolynomials hw n hP) := by
  rw [← h.oddPeriodPolynomialEquiv_conj_heckeTCuspLevelOne hk hw n]
  exact (LinearMap.trace_conj' (M := CuspForm 𝒮ℒ k) (N := oddPeriodPolynomials ℂ w) _ _).symm

end TraceFormulaMatrixModule

end TauCeti
