/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.ParityDimension
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.PeriodRelation
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Parity
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Eisenstein

import TauCeti.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.LFunction
import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.LValue
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.TraceReduction
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The Eichler–Shimura period-polynomial isomorphism at level one

Let `k = w + 2` be an integer weight with `w : ℕ`. For a cusp form `f ∈ S_k(SL(2, ℤ))`, its even
and odd period polynomials `r_f^+ ∈ W_w^+` and `r_f^- ∈ W_w^-` collect the critical `L`-values of
`f` of the two parities (`TauCeti.evenPeriodPolynomial`, `TauCeti.oddPeriodPolynomial`). This file
proves that at level one:

1. **Injectivity on cusp forms.** Both `evenPeriodPolynomial hk` and `oddPeriodPolynomial hk` are
   injective (`evenPeriodPolynomial_injective`, `oddPeriodPolynomial_injective`). For odd `w`,
   `S_{w+2}(SL(2, ℤ)) = 0` (`CuspForm.levelOne_odd_weight_eq_zero`). For even `w`, the kernel of
   each map is stable under every prime Hecke operator `T_p` because `PeriodRelation ℂ p` has a
   solution (`exists_periodRelation`) that intertwines `T_p` with `periodAction`
   (`PeriodRelation.periodAction_evenPeriodPolynomial`,
   `PeriodRelation.periodAction_oddPeriodPolynomial`). By `injective_of_heckeTCuspLevelOne_mem_ker`,
   injectivity reduces to nonvanishing on `levelOneNewformBasis k`: any level-one newform `f`
   forces `k ≥ 12` (`w ≥ 10`), where `s = w` and `s = w + 1` lie strictly inside the Euler-product
   half-plane `Re s > k/2 + 1` where `L(f, s) ≠ 0`.
2. **The odd Eichler–Shimura isomorphism.** Since `dim W_w^- = dim S_{w+2}(SL(2, ℤ))`
   (`finrank_oddPeriodPolynomials_eq_finrank_cuspForm`), `oddPeriodPolynomial hk` upgrades to a
   Hecke-equivariant linear equivalence `oddPeriodPolynomialEquiv hk : CuspForm 𝒮ℒ k ≃ₗ[ℂ] W_w^-`.
3. **Disjointness of `X^w - Y^w` and the even Eichler–Shimura isomorphism.** Since every solution
   `ξ` of `PeriodRelation R n ξ` (`n ≥ 1`) scales the Eisenstein period polynomial `X^w - Y^w` by
   `σ_{w+1}(n)` (`PeriodRelation.periodAction_eisensteinPeriodPolynomial`), a cusp form whose even
   period polynomial were `X^w - Y^w` would be a nonzero cusp form with Hecke eigenvalues
   `σ_{w+1}(n)`, contradicting the absolute convergence of its Dirichlet series at `s = w + 1` for
   `w ≥ 10`. Hence `W_w^+` is the internal direct sum of `range (evenPeriodPolynomial hk)` and
   `ℂ · (X^w - Y^w)` for positive even `w`, giving a Hecke-equivariant linear equivalence
   `extendedEvenPeriodPolynomialEquiv hk : ModularForm 𝒮ℒ k ≃ₗ[ℂ] W_w^+` and the full
   Eichler–Shimura isomorphism
   `periodPolynomialEquiv hk : (ModularForm 𝒮ℒ k × CuspForm 𝒮ℒ k) ≃ₗ[ℂ] W_w`.
4. **Trace identity for the Eichler–Selberg trace formula.** Conjugating along
   `periodPolynomialEquiv hk` identifies the trace on `W_w` of any element `ξ` satisfying both the
   period relation (A) and the exchange relations (B) — in particular Popa–Zagier's explicit element
   `popaZagierElement ℂ n` — with `2 Tr(Tₙ | S_k) + σ_{w+1}(n)`. Combined with Popa–Zagier's trace
   reduction `Tr(ξ | W_w) = Tr(ξ | V_w)` (`ExchangeRelations.trace_periodActionRestrict_eq_trace`),
   this expresses `Tr(Tₙ | S_k)` directly in terms of the binary-form trace `Tr(ξ | V_w)`.

## Main definitions

* `TauCeti.oddPeriodPolynomialEquiv`: the `ℂ`-linear isomorphism `CuspForm 𝒮ℒ k ≃ₗ[ℂ] W_w^-`.
* `TauCeti.extendedEvenPeriodPolynomialEquiv`: the `ℂ`-linear isomorphism
  `ModularForm 𝒮ℒ k ≃ₗ[ℂ] W_w^+` extending `evenPeriodPolynomial hk` and sending `ModularForm.E` to
  `X^w - Y^w` in positive even degree.
* `TauCeti.periodPolynomialEquiv`: the full `ℂ`-linear Eichler–Shimura isomorphism
  `(ModularForm 𝒮ℒ k × CuspForm 𝒮ℒ k) ≃ₗ[ℂ] W_w`.

## Main results

* `TauCeti.evenPeriodPolynomial_injective`, `TauCeti.oddPeriodPolynomial_injective`: injectivity of
  the even and odd period maps on `CuspForm 𝒮ℒ k`.
* `TauCeti.isCompl_range_evenPeriodPolynomial_span_eisensteinPeriodPolynomial`: for positive even
  `w`, `W_w^+ = r^+(S_k) ⊕ ℂ · (X^w - Y^w)`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_extendedEvenPeriodPolynomialEquiv`:
  Hecke equivariance of `extendedEvenPeriodPolynomialEquiv`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.trace_periodAction_eq`,
  `TauCeti.TraceFormulaMatrixModule.trace_heckeTCuspLevelOne_eq_trace_popaZagierElement`:
  reduction of `Tr(Tₙ | S_k)` to the ambient binary-form trace of `popaZagierElement ℂ n` on `V_w`.

## References

* M. Eichler, *Eine Verallgemeinerung der Abelschen Integrale*, Math. Z. **67** (1957), 267–298.
* G. Shimura, *Sur les intégrales attachées aux formes automorphes*, J. Math. Soc. Japan **11**
  (1959), 291–311.
* Y. I. Manin, *Periods of parabolic forms and p-adic Hecke series*, Mat. Sb. **92** (1973),
  378–401.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2, Propositions 2 and 3.
-/

public noncomputable section

open CongruenceSubgroup EisensteinSeries Filter HeckeRing.GL2 ModularForm Module MonoidAlgebra
  MvPolynomial Topology UpperHalfPlane
open scoped ArithmeticFunction.sigma MatrixGroups ModularForm

namespace TauCeti

/-! ### Nonvanishing on level-one newforms and injectivity of `r_f^+` and `r_f^-` -/

/-- **The even period polynomial of a level-one newform is nonzero.** -/
theorem evenPeriodPolynomial_levelOneNewformBasis_ne_zero {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (f : Newform 1 k) :
    evenPeriodPolynomial hk (levelOneNewformBasis k f) ≠ 0 := by
  have hk12 : 12 ≤ k := f.twelve_le_weight
  refine evenPeriodPolynomial_ne_zero hk _ (L_levelOneNewformBasis_ne_zero (by omega) f ?_)
  have hw10_nat : 10 ≤ w := by omega
  have hw10 : (10 : ℝ) ≤ w := by exact_mod_cast hw10_nat
  have hk_cast : (k : ℝ) = (w : ℝ) + 2 := by exact_mod_cast hk
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, hk_cast]
  linarith

/-- **The odd period polynomial of a level-one newform is nonzero.** -/
theorem oddPeriodPolynomial_levelOneNewformBasis_ne_zero {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (f : Newform 1 k) :
    oddPeriodPolynomial hk (levelOneNewformBasis k f) ≠ 0 := by
  have hk12 : 12 ≤ k := f.twelve_le_weight
  refine oddPeriodPolynomial_ne_zero hk _ (by omega)
    (L_levelOneNewformBasis_ne_zero (by omega) f ?_)
  have hw10_nat : 10 ≤ w := by omega
  have hw10 : (10 : ℝ) ≤ w := by exact_mod_cast hw10_nat
  have hk_cast : (k : ℝ) = (w : ℝ) + 2 := by exact_mod_cast hk
  simp only [Complex.natCast_re, hk_cast]
  linarith

/-- **The even period-polynomial map is injective on `CuspForm 𝒮ℒ k`** at every degree `w`. -/
theorem evenPeriodPolynomial_injective {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    Function.Injective (evenPeriodPolynomial hk) :=
  injective_of_heckeTCuspLevelOne_mem_ker (R := ℂ) (M := evenPeriodPolynomials ℂ w)
    (L := evenPeriodPolynomial hk)
    (fun p h hh ↦ by
      rcases Nat.even_or_odd w with hw | hw
      · obtain ⟨ξ, hξ⟩ := TraceFormulaMatrixModule.exists_periodRelation ℂ (p.1 : ℤ)
        rw [LinearMap.mem_ker] at hh ⊢
        apply Subtype.ext
        rw [← hξ.periodAction_evenPeriodPolynomial hk hw p.1 h, hh, ZeroMemClass.coe_zero, map_zero]
      · obtain ⟨m, rfl⟩ := hw
        rw [CuspForm.levelOne_odd_weight_eq_zero ⟨m + 1, by omega⟩ (heckeTCuspLevelOne k p.1 h)]
        exact zero_mem _)
    (evenPeriodPolynomial_levelOneNewformBasis_ne_zero hk)

/-- **The odd period-polynomial map is injective on `CuspForm 𝒮ℒ k`** at every degree `w`. -/
theorem oddPeriodPolynomial_injective {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    Function.Injective (oddPeriodPolynomial hk) :=
  injective_of_heckeTCuspLevelOne_mem_ker (R := ℂ) (M := oddPeriodPolynomials ℂ w)
    (L := oddPeriodPolynomial hk)
    (fun p h hh ↦ by
      rcases Nat.even_or_odd w with hw | hw
      · obtain ⟨ξ, hξ⟩ := TraceFormulaMatrixModule.exists_periodRelation ℂ (p.1 : ℤ)
        rw [LinearMap.mem_ker] at hh ⊢
        apply Subtype.ext
        rw [← hξ.periodAction_oddPeriodPolynomial hk hw p.1 h, hh, ZeroMemClass.coe_zero, map_zero]
      · obtain ⟨m, rfl⟩ := hw
        rw [CuspForm.levelOne_odd_weight_eq_zero ⟨m + 1, by omega⟩ (heckeTCuspLevelOne k p.1 h)]
        exact zero_mem _)
    (oddPeriodPolynomial_levelOneNewformBasis_ne_zero hk)

/-! ### The odd Eichler–Shimura isomorphism `CuspForm 𝒮ℒ k ≃ₗ[ℂ] oddPeriodPolynomials ℂ w` -/

/-- **The odd period-polynomial map is surjective** onto `oddPeriodPolynomials ℂ w`. -/
theorem oddPeriodPolynomial_surjective {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    Function.Surjective (oddPeriodPolynomial hk) := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
    .of_injective _ CuspForm.toModularFormₗ_injective
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (K := ℂ) (V := oddPeriodPolynomials ℂ w)
    (S := LinearMap.range (oddPeriodPolynomial hk))
    ((LinearMap.finrank_range_of_inj (oddPeriodPolynomial_injective hk)).trans
      (finrank_oddPeriodPolynomials_eq_finrank_cuspForm w).symm)

/-- **The odd period-polynomial map is bijective.** -/
theorem oddPeriodPolynomial_bijective {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    Function.Bijective (oddPeriodPolynomial hk) :=
  ⟨oddPeriodPolynomial_injective hk, oddPeriodPolynomial_surjective hk⟩

/-- **The odd Eichler–Shimura isomorphism** `S_k(SL(2, ℤ)) ≃ₗ[ℂ] W_w^-` (`k = w + 2`). -/
def oddPeriodPolynomialEquiv {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    CuspForm 𝒮ℒ k ≃ₗ[ℂ] oddPeriodPolynomials ℂ w :=
  LinearEquiv.ofBijective (oddPeriodPolynomial hk) (oddPeriodPolynomial_bijective hk)

/-- Applying `oddPeriodPolynomialEquiv hk` computes `oddPeriodPolynomial hk`. -/
@[simp]
theorem oddPeriodPolynomialEquiv_apply {k : ℤ} {w : ℕ} (hk : k = w + 2) (f : CuspForm 𝒮ℒ k) :
    oddPeriodPolynomialEquiv hk f = oddPeriodPolynomial hk f := (rfl)

/-- The underlying linear map of `oddPeriodPolynomialEquiv hk` is `oddPeriodPolynomial hk`. -/
@[simp]
theorem oddPeriodPolynomialEquiv_toLinearMap {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    (oddPeriodPolynomialEquiv hk).toLinearMap = oddPeriodPolynomial hk := (rfl)

/-! ### Disjointness of `X^w - Y^w` and the even Eichler–Shimura isomorphism -/

/-- No level-one newform of weight `k = w + 2` has Fourier coefficients `σ_{w+1}(n)` for all
`n ≥ 1`: its Dirichlet series converges absolutely at `s = w + 1` (`10 ≤ w`), whereas the general
term `σ_{w+1}(n) / n^{w+1}` is at least `1`. -/
private theorem not_forall_qExpansion_coeff_eq_sigma {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (f : Newform 1 k) (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (qExpansion 1 f.toCuspForm).coeff n = (σ (w + 1) n : ℂ)) : False := by
  have hk12 : 12 ≤ k := f.twelve_le_weight
  have hw10_nat : 10 ≤ w := by omega
  have hw10 : (10 : ℝ) ≤ w := by exact_mod_cast hw10_nat
  have hk_cast : (k : ℝ) = (w : ℝ) + 2 := by exact_mod_cast hk
  have hsum := CuspForm.LSeriesSummable_qExpansion_coeff f.toCuspForm (s := ((w + 1 : ℕ) : ℂ))
    (by simp only [Nat.cast_add, Nat.cast_one, Complex.add_re, Complex.natCast_re, Complex.one_re,
          hk_cast]; linarith)
  rw [strictWidthInfty_Gamma1] at hsum
  have htend : Tendsto
      (fun n : ℕ ↦ (LSeries.term (fun m ↦ (qExpansion 1 f.toCuspForm).coeff m)
        ((w + 1 : ℕ) : ℂ) n).re) atTop (𝓝 0) :=
    (Complex.continuous_re.tendsto 0).comp hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp htend).2 1 zero_lt_one)
  set n := N + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero N
  have hlt : (LSeries.term (fun m ↦ (qExpansion 1 f.toCuspForm).coeff m)
      ((w + 1 : ℕ) : ℂ) n).re < 1 := hN n (Nat.le_succ N)
  have hge : 1 ≤ (LSeries.term (fun m ↦ (qExpansion 1 f.toCuspForm).coeff m)
      ((w + 1 : ℕ) : ℂ) n).re := by
    have hcast : ((σ (w + 1) n : ℂ) / ((n ^ (w + 1) : ℕ) : ℂ)) =
        (((σ (w + 1) n : ℝ) / ((n ^ (w + 1) : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [LSeries.term_of_ne_zero hn, hcoeff n hn, Complex.cpow_natCast, ← Nat.cast_pow, hcast,
      Complex.ofReal_re, one_le_div (by positivity)]
    exact_mod_cast Finset.single_le_sum (f := fun d ↦ d ^ (w + 1)) (fun _ _ ↦ Nat.zero_le _)
      (Nat.mem_divisors_self n hn)
  linarith

/-- **The Eisenstein period polynomial `X^w - Y^w` is not the even period polynomial of any cusp
form** in positive even degree `w`. -/
theorem eisensteinPeriodPolynomial_notMem_range_evenPeriodPolynomial {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (hw₀ : w ≠ 0) :
    (⟨eisensteinPeriodPolynomial ℂ w, mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw⟩ :
        evenPeriodPolynomials ℂ w) ∉ LinearMap.range (evenPeriodPolynomial hk) := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact eisensteinPeriodPolynomial_ne_zero hw₀ (by simpa using (congrArg Subtype.val hg).symm)
  obtain ⟨f, hf⟩ : ∃ f : Newform 1 k, (levelOneNewformBasis k).repr g f ≠ 0 := by
    by_contra! hall
    exact hg0 ((levelOneNewformBasis k).repr.injective (by ext f; simp [hall f]))
  refine not_forall_qExpansion_coeff_eq_sigma hk f fun n hn ↦ ?_
  let : NeZero n := ⟨hn⟩
  obtain ⟨ξ, hξ⟩ := TraceFormulaMatrixModule.exists_periodRelation ℂ (n : ℤ)
  have heig : heckeTCuspLevelOne k n g = (σ (w + 1) n : ℂ) • g := by
    apply evenPeriodPolynomial_injective hk
    apply Subtype.ext
    rw [← hξ.periodAction_evenPeriodPolynomial hk hw n g, map_smul, Submodule.coe_smul, hg,
      hξ.periodAction_eisensteinPeriodPolynomial (by exact_mod_cast NeZero.ne n) hw,
      Int.natAbs_natCast]
  have hcoord := congrArg (fun h ↦ (levelOneNewformBasis k).repr h f) heig
  rw [(levelOneNewformBasis k).repr_apply_of_apply_basis
    (heckeTCuspLevelOne_levelOneNewformBasis k n) g f,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
  exact mul_right_cancel₀ hf hcoord

/-- **In positive even degree `w`, `W_w^+` is the internal direct sum of `r^+(S_{w+2})` and
`ℂ · (X^w - Y^w)`** (Manin; Kohnen–Zagier, §1.1; Popa–Zagier, §2). -/
theorem isCompl_range_evenPeriodPolynomial_span_eisensteinPeriodPolynomial {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (hw₀ : w ≠ 0) :
    IsCompl (LinearMap.range (evenPeriodPolynomial hk))
      (ℂ ∙ (⟨eisensteinPeriodPolynomial ℂ w,
        mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw⟩ : evenPeriodPolynomials ℂ w)) := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  have hP₀ : (⟨eisensteinPeriodPolynomial ℂ w,
      mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw⟩ : evenPeriodPolynomials ℂ w) ≠ 0 :=
    fun h ↦ eisensteinPeriodPolynomial_ne_zero hw₀ (congrArg Subtype.val h)
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
    .of_injective _ CuspForm.toModularFormₗ_injective
  refine (Submodule.isCompl_iff_disjoint (K := ℂ) (V := evenPeriodPolynomials ℂ w) _ _ ?_).mpr
    (Submodule.disjoint_span_singleton_of_notMem (K := ℂ) (V := evenPeriodPolynomials ℂ w)
      (eisensteinPeriodPolynomial_notMem_range_evenPeriodPolynomial hk hw hw₀))
  exact le_of_eq (by
    rw [finrank_evenPeriodPolynomials_eq_finrank_oddPeriodPolynomials_add_one (K := ℂ) hw hw₀,
      finrank_oddPeriodPolynomials_eq_finrank_cuspForm w,
      LinearMap.finrank_range_of_inj (f := evenPeriodPolynomial hk)
        (evenPeriodPolynomial_injective hk),
      finrank_span_singleton (K := ℂ) (V := evenPeriodPolynomials ℂ w) hP₀])

/-- Auxiliary definition of `extendedEvenPeriodPolynomialEquiv` in positive even degree `w`, built
by matching the complementary decompositions `M_k = S_k ⊕ ℂ · E_k` and
`W_w^+ = r^+(S_k) ⊕ ℂ · (X^w - Y^w)`. -/
private def extendedEvenPeriodPolynomialEquivOfPosEven {w : ℕ} (hw : Even w) (hw₀ : w ≠ 0) :
    ModularForm 𝒮ℒ (w + 2 : ℕ) ≃ₗ[ℂ] evenPeriodPolynomials ℂ w :=
  let hk : ((w + 2 : ℕ) : ℤ) = (w : ℤ) + 2 := Nat.cast_add w 2
  let hk3 : 3 ≤ w + 2 := by omega
  let hk2 : Even (w + 2) := hw.add even_two
  let P₀ : evenPeriodPolynomials ℂ w :=
    ⟨eisensteinPeriodPolynomial ℂ w, mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw⟩
  have hP₀ : P₀ ≠ 0 := fun h ↦ eisensteinPeriodPolynomial_ne_zero hw₀ (congrArg Subtype.val h)
  let eDom := Submodule.prodEquivOfIsCompl (R := ℂ) (E := ModularForm 𝒮ℒ (w + 2 : ℕ)) _ _
    (isCompl_cuspFormSubmodule_span_E hk3)
  let eCod := Submodule.prodEquivOfIsCompl (R := ℂ) (E := evenPeriodPolynomials ℂ w) _ _
    (isCompl_range_evenPeriodPolynomial_span_eisensteinPeriodPolynomial hk hw hw₀)
  eDom.symm ≪≫ₗ
    ((ModularForm.CuspForm.equivCuspFormSubmodule 𝒮ℒ (w + 2 : ℕ)).symm ≪≫ₗ
      LinearEquiv.ofInjective (evenPeriodPolynomial hk)
        (evenPeriodPolynomial_injective hk)).prodCongr
      (LinearEquiv.coord ℂ _ (ModularForm.E hk3) (E_ne_zero hk3 hk2) ≪≫ₗ
        LinearEquiv.toSpanNonzeroSingleton ℂ (evenPeriodPolynomials ℂ w) P₀ hP₀) ≪≫ₗ
    eCod

private theorem evenPeriodPolynomials_eq_bot_of_not_pos_even {w : ℕ}
    (hw : ¬ (Even w ∧ w ≠ 0)) : evenPeriodPolynomials ℂ w = ⊥ := by
  rw [eq_bot_iff, evenPeriodPolynomials_def]
  refine inf_le_left.trans ?_
  rcases Nat.even_or_odd w with hwe | hwo
  · obtain rfl : w = 0 := not_not.mp fun hw0 ↦ hw ⟨hwe, hw0⟩
    rw [periodPolynomials_zero]
  · rw [periodPolynomials_eq_bot_of_odd (mul_right_injective₀ (two_ne_zero : (2 : ℂ) ≠ 0)) hwo]

/-- **The extended even Eichler–Shimura isomorphism** `M_k(SL(2, ℤ)) ≃ₗ[ℂ] W_w^+` (`k = w + 2`),
restricting to `evenPeriodPolynomial hk` on `CuspForm 𝒮ℒ k` and sending `ModularForm.E` to
`X^w - Y^w` in positive even degree `w` (and identifying the zero spaces when `w = 0` or `w` is
odd). -/
def extendedEvenPeriodPolynomialEquiv {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    ModularForm 𝒮ℒ k ≃ₗ[ℂ] evenPeriodPolynomials ℂ w := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  classical
  exact if hw : Even w ∧ w ≠ 0 then
    extendedEvenPeriodPolynomialEquivOfPosEven hw.1 hw.2
  else
    have hdimW : finrank ℂ (evenPeriodPolynomials ℂ w) = 0 := by
      rw [evenPeriodPolynomials_eq_bot_of_not_pos_even hw]
      exact finrank_bot ℂ (homogeneousSubmodule (Fin 2) ℂ w)
    have hdimM : finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) = 0 :=
      (finrank_evenPeriodPolynomials_eq_finrank_modularForm w).symm.trans hdimW
    have : Subsingleton (ModularForm 𝒮ℒ (w + 2 : ℕ)) := finrank_zero_iff.mp hdimM
    have : Subsingleton (evenPeriodPolynomials ℂ w) := finrank_zero_iff.mp hdimW
    LinearEquiv.ofBijective (0 : ModularForm 𝒮ℒ (w + 2 : ℕ) →ₗ[ℂ] evenPeriodPolynomials ℂ w)
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- On a cusp form `g`, `extendedEvenPeriodPolynomialEquiv hk` agrees with `evenPeriodPolynomial hk`
in every degree `w`. -/
@[simp]
theorem extendedEvenPeriodPolynomialEquiv_coe_cuspForm {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (g : CuspForm 𝒮ℒ k) :
    extendedEvenPeriodPolynomialEquiv hk (g : ModularForm 𝒮ℒ k) = evenPeriodPolynomial hk g := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  classical
  rw [extendedEvenPeriodPolynomialEquiv]
  split_ifs with hw
  · dsimp only [extendedEvenPeriodPolynomialEquivOfPosEven, LinearEquiv.trans_apply]
    have hg : (g : ModularForm 𝒮ℒ (w + 2 : ℕ)) =
        ModularForm.CuspForm.equivCuspFormSubmodule 𝒮ℒ (w + 2 : ℕ) g := rfl
    rw [hg, Submodule.prodEquivOfIsCompl_symm_apply_left (R := ℂ)
      (E := ModularForm 𝒮ℒ (w + 2 : ℕ))]
    simp [Submodule.coe_prodEquivOfIsCompl']
  · have hdimW : finrank ℂ (evenPeriodPolynomials ℂ w) = 0 := by
      rw [evenPeriodPolynomials_eq_bot_of_not_pos_even hw]
      exact finrank_bot ℂ (homogeneousSubmodule (Fin 2) ℂ w)
    have : Subsingleton (evenPeriodPolynomials ℂ w) := finrank_zero_iff.mp hdimW
    exact Subsingleton.elim _ _

/-- In positive even degree `w`, `extendedEvenPeriodPolynomialEquiv` sends the normalized Eisenstein
series `ModularForm.E` to the Eisenstein period polynomial `X^w - Y^w`. -/
@[simp]
theorem extendedEvenPeriodPolynomialEquiv_E {k w : ℕ} (hk : (k : ℤ) = w + 2)
    (hw : Even w) (hw₀ : w ≠ 0) (hk3 : 3 ≤ k) :
    extendedEvenPeriodPolynomialEquiv hk (ModularForm.E hk3) =
      ⟨eisensteinPeriodPolynomial ℂ w,
        mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw⟩ := by
  obtain rfl : k = w + 2 := by omega
  classical
  rw [extendedEvenPeriodPolynomialEquiv]
  split_ifs with hcond
  · dsimp only [extendedEvenPeriodPolynomialEquivOfPosEven, LinearEquiv.trans_apply]
    have hsymm :
        (Submodule.prodEquivOfIsCompl (R := ℂ) (E := ModularForm 𝒮ℒ (w + 2 : ℕ))
          (ModularForm.cuspFormSubmodule 𝒮ℒ (w + 2 : ℕ)) (ℂ ∙ ModularForm.E hk3)
          (isCompl_cuspFormSubmodule_span_E hk3)).symm
          (ModularForm.E hk3) =
        (0, ⟨ModularForm.E hk3, Submodule.mem_span_singleton_self _⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right (R := ℂ) (E := ModularForm 𝒮ℒ (w + 2 : ℕ))
        _ _ _ ⟨ModularForm.E hk3, Submodule.mem_span_singleton_self _⟩
    rw [hsymm]
    simp [LinearEquiv.coord_self, Submodule.coe_prodEquivOfIsCompl']
  · exact False.elim (hcond ⟨hw, hw₀⟩)

/-! ### The full Eichler–Shimura isomorphism onto `periodPolynomials ℂ w` -/

/-- **The full Eichler–Shimura period-polynomial isomorphism**
`(M_k(SL(2, ℤ)) × S_k(SL(2, ℤ))) ≃ₗ[ℂ] W_w` (`k = w + 2`), combining
`extendedEvenPeriodPolynomialEquiv hk` and `oddPeriodPolynomialEquiv hk`. -/
def periodPolynomialEquiv {k : ℤ} {w : ℕ} (hk : k = w + 2) :
    (ModularForm 𝒮ℒ k × CuspForm 𝒮ℒ k) ≃ₗ[ℂ] periodPolynomials ℂ w :=
  have hevenLe : evenPeriodPolynomials ℂ w ≤ periodPolynomials ℂ w :=
    fun _ hP ↦ (mem_evenPeriodPolynomials_iff.mp hP).1
  have hoddLe : oddPeriodPolynomials ℂ w ≤ periodPolynomials ℂ w :=
    fun _ hP ↦ (mem_oddPeriodPolynomials_iff.mp hP).1
  let : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  let eCod := Submodule.prodEquivOfIsCompl (R := ℂ) (E := periodPolynomials ℂ w) _ _
    (isCompl_evenPeriodPolynomials_oddPeriodPolynomials (R := ℂ) w)
  ((extendedEvenPeriodPolynomialEquiv hk ≪≫ₗ
      (Submodule.comapSubtypeEquivOfLe hevenLe).symm).prodCongr
    (oddPeriodPolynomialEquiv hk ≪≫ₗ
      (Submodule.comapSubtypeEquivOfLe hoddLe).symm)) ≪≫ₗ
    eCod

/-- In `homogeneousSubmodule (Fin 2) ℂ w`, `periodPolynomialEquiv hk (f, g)` is the sum of the
extended even period polynomial of `f` and the odd period polynomial of `g`. -/
@[simp]
theorem coe_periodPolynomialEquiv_apply {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (fg : ModularForm 𝒮ℒ k × CuspForm 𝒮ℒ k) :
    (periodPolynomialEquiv hk fg : homogeneousSubmodule (Fin 2) ℂ w) =
      (extendedEvenPeriodPolynomialEquiv hk fg.1 : homogeneousSubmodule (Fin 2) ℂ w) +
        oddPeriodPolynomialEquiv hk fg.2 := by
  simp [periodPolynomialEquiv]

/-- On the diagonal `(g, g)` of a cusp form `g`, `periodPolynomialEquiv hk` recovers the full
period polynomial `r_g = r_g^+ + r_g^-`. -/
@[simp]
theorem periodPolynomialEquiv_coe_cuspForm_same {k : ℤ} {w : ℕ} (hk : k = w + 2)
    (g : CuspForm 𝒮ℒ k) :
    periodPolynomialEquiv hk ((g : ModularForm 𝒮ℒ k), g) = periodPolynomial hk g := by
  apply Subtype.ext
  rw [coe_periodPolynomialEquiv_apply, extendedEvenPeriodPolynomialEquiv_coe_cuspForm,
    oddPeriodPolynomialEquiv_apply, coe_evenPeriodPolynomial_add_coe_oddPeriodPolynomial]

/-! ### Hecke equivariance and trace transfer to the Eichler–Selberg trace formula -/

namespace TraceFormulaMatrixModule

/-- **Hecke equivariance of `extendedEvenPeriodPolynomialEquiv`.** Every solution `ξ` of
Popa–Zagier's period relation (A) intertwines `heckeTLevelOne k n` on `ModularForm 𝒮ℒ k` with
`periodAction hw ξ` on `evenPeriodPolynomials ℂ w`. -/
theorem PeriodRelation.periodAction_extendedEvenPeriodPolynomialEquiv {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℂ n ξ) (F : ModularForm 𝒮ℒ k) :
    periodAction hw ξ
        (extendedEvenPeriodPolynomialEquiv hk F : homogeneousSubmodule (Fin 2) ℂ w) =
      extendedEvenPeriodPolynomialEquiv hk (heckeTLevelOne k n F) := by
  rcases eq_or_ne w 0 with rfl | hw₀
  · have hbot : evenPeriodPolynomials ℂ 0 = ⊥ :=
      evenPeriodPolynomials_eq_bot_of_not_pos_even (by simp)
    have h0 (Q : evenPeriodPolynomials ℂ 0) : (Q : homogeneousSubmodule (Fin 2) ℂ 0) = 0 :=
      (Submodule.mem_bot ℂ).mp (hbot ▸ Q.2)
    rw [h0, h0, map_zero]
  · -- Reduce to `k = (w + 2 : ℕ)` and split along `M_k = S_k ⊕ ℂ · E_k`.
    obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
    have hk3 : 3 ≤ w + 2 := by omega
    have hk2 : Even (w + 2) := hw.add even_two
    have hw1 : w + 2 - 1 = w + 1 := by omega
    have hmem : F ∈ ModularForm.cuspFormSubmodule 𝒮ℒ (w + 2 : ℕ) ⊔ (ℂ ∙ ModularForm.E hk3) := by
      rw [(isCompl_cuspFormSubmodule_span_E hk3).sup_eq_top]
      trivial
    obtain ⟨_, ⟨g, rfl⟩, _, hE, rfl⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hE
    have hcusp :
        periodAction hw ξ
            (extendedEvenPeriodPolynomialEquiv hk (g : ModularForm 𝒮ℒ (w + 2 : ℕ)) :
              homogeneousSubmodule (Fin 2) ℂ w) =
          extendedEvenPeriodPolynomialEquiv hk
            (heckeTLevelOne (w + 2 : ℕ) n (g : ModularForm 𝒮ℒ (w + 2 : ℕ))) := by
      rw [heckeTLevelOne_coe_cuspForm, extendedEvenPeriodPolynomialEquiv_coe_cuspForm,
        extendedEvenPeriodPolynomialEquiv_coe_cuspForm,
        h.periodAction_evenPeriodPolynomial hk hw n g]
    have heis :
        periodAction hw ξ
            (extendedEvenPeriodPolynomialEquiv hk (ModularForm.E hk3) :
              homogeneousSubmodule (Fin 2) ℂ w) =
          extendedEvenPeriodPolynomialEquiv hk
            (heckeTLevelOne (w + 2 : ℕ) n (ModularForm.E hk3)) := by
      rw [heckeTLevelOne_E hk3 n, map_smul, Submodule.coe_smul,
        extendedEvenPeriodPolynomialEquiv_E hk hw hw₀ hk3,
        h.periodAction_eisensteinPeriodPolynomial (by exact_mod_cast NeZero.ne n) hw,
      Int.natAbs_natCast, hw1]
    simp only [CuspForm.toModularFormₗ_eq_coe, map_add, map_smul, Submodule.coe_add,
      Submodule.coe_smul, hcusp, heis]

/-- **Hecke equivariance of `periodPolynomialEquiv`.** Every solution `ξ` of Popa–Zagier's period
relation (A) intertwines `heckeTLevelOne k n × heckeTCuspLevelOne k n` with `periodAction hw ξ` on
`periodPolynomials ℂ w`. -/
theorem PeriodRelation.periodAction_periodPolynomialEquiv {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℂ n ξ) (fg : ModularForm 𝒮ℒ k × CuspForm 𝒮ℒ k) :
    periodAction hw ξ (periodPolynomialEquiv hk fg : homogeneousSubmodule (Fin 2) ℂ w) =
      periodPolynomialEquiv hk (heckeTLevelOne k n fg.1, heckeTCuspLevelOne k n fg.2) := by
  rw [coe_periodPolynomialEquiv_apply, coe_periodPolynomialEquiv_apply, map_add,
    h.periodAction_extendedEvenPeriodPolynomialEquiv hk hw n fg.1,
    oddPeriodPolynomialEquiv_apply, oddPeriodPolynomialEquiv_apply,
    h.periodAction_oddPeriodPolynomial hk hw n fg.2]

/-- Every solution `ξ` of Popa–Zagier's period relation (A) preserves `periodPolynomials ℂ w`. -/
theorem PeriodRelation.periodAction_mem_periodPolynomials {w : ℕ} (hw : Even w) (n : ℕ) [NeZero n]
    {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    {P : homogeneousSubmodule (Fin 2) ℂ w} (hP : P ∈ periodPolynomials ℂ w) :
    periodAction hw ξ P ∈ periodPolynomials ℂ w := by
  obtain ⟨fg, hfg⟩ := (periodPolynomialEquiv (k := (w + 2 : ℤ)) rfl).surjective ⟨P, hP⟩
  have hval : P = periodPolynomialEquiv (k := (w + 2 : ℤ)) rfl fg :=
    (congrArg Subtype.val hfg).symm
  rw [hval, h.periodAction_periodPolynomialEquiv rfl hw n fg]
  exact (periodPolynomialEquiv (k := (w + 2 : ℤ)) rfl _).2

/-- **Trace of a solution of the period relation (A) on `periodPolynomials ℂ w`.** Across the
Eichler–Shimura isomorphism `periodPolynomialEquiv hk`, the restriction of `periodAction hw ξ` to
`W_w` is conjugate to `heckeTLevelOne k n × heckeTCuspLevelOne k n`, so its trace is
`Tr(Tₙ | M_k) + Tr(Tₙ | S_k)`. -/
theorem PeriodRelation.trace_periodAction_restrict {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℂ n ξ)
    (hsub : ∀ P ∈ periodPolynomials ℂ w, periodAction hw ξ P ∈ periodPolynomials ℂ w :=
      fun _ hP ↦ h.periodAction_mem_periodPolynomials hw n hP) :
    LinearMap.trace ℂ (periodPolynomials ℂ w) ((periodAction hw ξ).restrict hsub) =
      LinearMap.trace ℂ (ModularForm 𝒮ℒ k) (heckeTLevelOne k n) +
        LinearMap.trace ℂ (CuspForm 𝒮ℒ k) (heckeTCuspLevelOne k n) := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
    .of_injective _ CuspForm.toModularFormₗ_injective
  have hconj :
      (periodAction hw ξ).restrict hsub =
        (periodPolynomialEquiv hk).conj
          (LinearMap.prodMap (heckeTLevelOne (w + 2 : ℕ) n)
            (heckeTCuspLevelOne (w + 2 : ℕ) n)) := by
    refine LinearMap.ext fun P ↦ Subtype.ext ?_
    obtain ⟨fg, rfl⟩ := (periodPolynomialEquiv hk).surjective P
    rw [LinearMap.coe_restrict_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      (periodPolynomialEquiv hk).symm_apply_apply]
    exact h.periodAction_periodPolynomialEquiv hk hw n fg
  exact (congrArg (LinearMap.trace ℂ (periodPolynomials ℂ w)) hconj).trans
    ((LinearMap.trace_conj' (R := ℂ) (N := periodPolynomials ℂ w)
      (LinearMap.prodMap (heckeTLevelOne (w + 2 : ℕ) n) (heckeTCuspLevelOne (w + 2 : ℕ) n))
      (periodPolynomialEquiv hk)).trans
      (LinearMap.trace_prodMap' (heckeTLevelOne (w + 2 : ℕ) n)
        (heckeTCuspLevelOne (w + 2 : ℕ) n)))

/-- **Popa–Zagier's ambient trace identity** (Popa–Zagier, §2, Propositions 2 and 3): for positive
even `w`, `k = w + 2`, `n ≥ 1`, and any `ξ ∈ ℂ[ℳₙ]` satisfying both the period relation (A) and
the exchange relations (B), the trace of `ξ` on the ambient space `V_w` of degree-`w` binary forms
is `2 Tr(Tₙ | S_k(SL(2, ℤ))) + σ_{w+1}(n)`. -/
theorem PeriodRelation.trace_periodAction_eq {k : ℤ}
    {w : ℕ} (hk : k = w + 2) (hw : Even w) (hw₀ : w ≠ 0) (n : ℕ) [NeZero n]
    {ξ : ℂ[TraceFormulaMatrixModule n]} (hP : PeriodRelation ℂ n ξ)
    (hX : ExchangeRelations ℂ n ξ) :
    LinearMap.trace ℂ (homogeneousSubmodule (Fin 2) ℂ w) (periodAction hw ξ) =
      2 * LinearMap.trace ℂ (CuspForm 𝒮ℒ k) (heckeTCuspLevelOne k n) + (σ (w + 1) n : ℂ) := by
  obtain rfl : k = ((w + 2 : ℕ) : ℤ) := by omega
  have hw1 : w + 2 - 1 = w + 1 := by omega
  have hrest : hX.periodActionRestrict hw =
      (periodAction hw ξ).restrict fun _ hQ ↦ hP.periodAction_mem_periodPolynomials hw n hQ :=
    LinearMap.ext fun Q ↦ Subtype.ext (hX.coe_periodActionRestrict_apply hw Q)
  rw [← hX.trace_periodActionRestrict_eq_trace hw hw₀, hrest,
    hP.trace_periodAction_restrict hk hw n,
    trace_heckeTLevelOne (k := w + 2) (by omega) (hw.add even_two) n, hw1]
  ring

/-- **Reduction of the level-one cusp-form Hecke trace to Popa–Zagier's explicit element**: for
positive even `w`, `k = w + 2`, and `n ≥ 1`,
`Tr(Tₙ | S_k(SL(2, ℤ))) = (Tr(popaZagierElement ℂ n | V_w) - σ_{w+1}(n)) / 2`. -/
theorem trace_heckeTCuspLevelOne_eq_trace_popaZagierElement {k : ℤ} {w : ℕ}
    (hk : k = w + 2) (hw : Even w) (hw₀ : w ≠ 0) (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ (CuspForm 𝒮ℒ k) (heckeTCuspLevelOne k n) =
      (LinearMap.trace ℂ (homogeneousSubmodule (Fin 2) ℂ w)
        (periodAction hw (popaZagierElement ℂ n)) - (σ (w + 1) n : ℂ)) / 2 := by
  have hn : (0 : ℤ) < n := Nat.cast_pos.mpr (Nat.pos_of_neZero n)
  have htr := (periodRelation_popaZagierElement (k := ℂ) (by norm_num) hn).trace_periodAction_eq
    hk hw hw₀ n (exchangeRelations_popaZagierElement ℂ n)
  linear_combination -htr / 2

end TraceFormulaMatrixModule

end TauCeti
