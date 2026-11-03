/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.ParityDimension
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Parity
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.LValue
import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
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

/-! ### Newforms of level one as cusp forms on `SL(2, ℤ)` -/

/-- Cusp forms for `Γ₁(1)` are cusp forms on `SL(2, ℤ)`, the two groups having the same image in
`GL(2, ℝ)`. -/
private def ofGamma1One : CuspForm ((Gamma1 1).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun F := CuspForm.mcast rfl F Gamma1_one_map_eq_SL.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coe_ofGamma1One (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) :
    ⇑(ofGamma1One F) = ⇑F :=
  funext (CuspForm.mcast_apply rfl F Gamma1_one_map_eq_SL.symm)

private theorem ofGamma1One_surjective : Function.Surjective (ofGamma1One (k := k)) := fun f ↦
  ⟨CuspForm.mcast rfl f Gamma1_one_map_eq_SL, CuspForm.ext fun z ↦ by
    rw [coe_ofGamma1One, CuspForm.mcast_apply rfl f Gamma1_one_map_eq_SL]⟩

/-- A newform `g` of level one is an eigenvector of every `Tₙ` on `S_k(SL(2, ℤ))`, with eigenvalue
`aₙ(g)`: both operators have the divisor-sum coefficient formula, the nebentypus being trivial. -/
private theorem heckeTCuspLevelOne_ofGamma1One (g : Newform 1 k) (n : ℕ+) :
    heckeTCuspLevelOne k n (ofGamma1One g.toCuspForm) =
      (qExpansion 1 g.toCuspForm).coeff n • ofGamma1One g.toCuspForm := by
  refine CuspForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
    (PowerSeries.ext fun m ↦ ?_)
  have h := congrArg (fun F : cuspFormCharSpace k g.χ ↦
      (qExpansion 1 (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k)).coeff m)
    (Newform.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_qExpansion_coeff_smul g n)
  dsimp only at h ⊢
  rw [qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 n.ne_zero,
    Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map 1),
    PowerSeries.coeff_smul, smul_eq_mul] at h
  rw [qExpansion_coeff_heckeTCuspLevelOne, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, coe_ofGamma1One,
    PowerSeries.coeff_smul, smul_eq_mul, ← h]
  -- the character of `g` is trivial, as is every Dirichlet character modulo `1`
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [DirichletCharacter.level_one (MulChar.ofUnitHom g.χ),
    MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- Newforms of level one are determined by their eigenvalues `aₙ`, `n ≥ 1`. -/
private theorem injective_qExpansion_coeff_pnat :
    Function.Injective fun (g : Newform 1 k) (n : ℕ+) ↦ (qExpansion 1 g.toCuspForm).coeff n := by
  refine fun g h hgh ↦ Newform.ext <| CuspForm.qExpansion_injective one_pos
    (one_mem_strictPeriods_Gamma1_map 1) (PowerSeries.ext fun m ↦ ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map 1),
      CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map 1)]
  · exact congrFun hgh ⟨m, hm⟩

/-- The newforms of level one span `S_k(SL(2, ℤ))`, every cusp form of level one being new. -/
private theorem span_range_ofGamma1One_toCuspForm :
    Submodule.span ℂ (Set.range fun g : Newform 1 k ↦ ofGamma1One g.toCuspForm) = ⊤ := by
  rw [Set.range_comp' ofGamma1One, Submodule.span_image,
    Newform.span_range_toCuspForm_eq_cuspFormsNew, cuspFormsNew_one, Submodule.map_top,
    LinearMap.range_eq_top_of_surjective _ ofGamma1One_surjective]

/-- The `L`-function of a newform of level one does not vanish on `Re s > k/2 + 1`. -/
private theorem L_ofGamma1One_ne_zero (g : Newform 1 k) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) : ModularForm.L hk (ofGamma1One g.toCuspForm) s ≠ 0 := by
  intro hL
  have h := CuspForm.LSeries_qExpansion_coeff_eq hk (ofGamma1One g.toCuspForm) hs
  rw [hL, mul_zero, Subgroup.strictWidthInfty_SL2Z, coe_ofGamma1One] at h
  exact g.LSeries_ne_zero_of_lt_re (by linarith) h

/-! ### Injectivity of Hecke-equivariant maps -/

/-- A linear map out of `S_k(SL(2, ℤ))` that intertwines every `Tₙ` with some endomorphism of its
target and is nonzero on every newform is injective. -/
private theorem injective_of_forall_newform {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Φ : CuspForm 𝒮ℒ k →ₗ[ℂ] V) (A : ℕ+ → Module.End ℂ V)
    (hΦ : ∀ (n : ℕ+) (f : CuspForm 𝒮ℒ k), Φ (heckeTCuspLevelOne k n f) = A n (Φ f))
    (hne : ∀ g : Newform 1 k, Φ (ofGamma1One g.toCuspForm) ≠ 0) : Function.Injective Φ := by
  -- the images of the newforms are joint eigenvectors of the `A n` with distinct eigenvalues
  have hmem (g : Newform 1 k) : Φ (ofGamma1One g.toCuspForm) ∈
      ⨅ n, (A n).eigenspace ((qExpansion 1 g.toCuspForm).coeff n) :=
    Submodule.mem_iInf _ |>.2 fun n ↦ Module.End.mem_eigenspace_iff.2 <| by
      rw [← hΦ, heckeTCuspLevelOne_ofGamma1One, map_smul]
  have hli : LinearIndependent ℂ fun g : Newform 1 k ↦ Φ (ofGamma1One g.toCuspForm) :=
    ((iSupIndep_iInf_eigenspace A).comp injective_qExpansion_coeff_pnat).linearIndependent _
      hmem hne
  -- every cusp form is a combination of newforms, on which `Φ` is injective
  have hsurj : Function.Surjective
      (Finsupp.linearCombination ℂ fun g : Newform 1 k ↦ ofGamma1One g.toCuspForm) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
      span_range_ofGamma1One_toCuspForm]
  intro f f' hff'
  obtain ⟨c, rfl⟩ := hsurj f
  obtain ⟨c', rfl⟩ := hsurj f'
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination] at hff'
  rw [hli hff']

/-- In odd weight or below weight `12` there are no nonzero cusp forms on `SL(2, ℤ)`. -/
private theorem subsingleton_cuspForm (hk : k = w + 2) (h : ¬(Even w ∧ 12 ≤ k)) :
    Subsingleton (CuspForm 𝒮ℒ k) := by
  by_cases hw : Even w
  · exact rank_zero_iff.1 (CuspForm.rank_eq_zero_of_weight_lt_twelve
      (not_le.1 fun h12 ↦ h ⟨hw, h12⟩))
  · have hk' : Odd k := by
      rw [hk]
      exact (Nat.not_even_iff_odd.1 hw).natCast.add_even even_two
    refine ⟨fun f g ↦ CuspForm.toModularFormₗ_injective ?_⟩
    rw [ModularForm.levelOne_odd_weight_eq_zero hk' (CuspForm.toModularFormₗ f),
      ModularForm.levelOne_odd_weight_eq_zero hk' (CuspForm.toModularFormₗ g)]

/-- A linear map from `S_k(SL(2, ℤ))`, `k = w + 2`, to a space of binary forms of degree `w`
that intertwines every `Tₙ` with the action of every solution of the period relation (A), and
is nonzero on every newform of weight `k ≥ 12`, is injective. -/
private theorem injective_of_periodAction (hk : k = w + 2)
    {p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ w)} (Φ : CuspForm 𝒮ℒ k →ₗ[ℂ] p)
    (hΦ : ∀ (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]},
      PeriodRelation ℂ n ξ → ∀ f, periodAction hw ξ (Φ f) = Φ (heckeTCuspLevelOne k n f))
    (hne : ∀ g : Newform 1 k, 10 ≤ w → Φ (ofGamma1One g.toCuspForm) ≠ 0) :
    Function.Injective Φ := by
  by_cases h : Even w ∧ 12 ≤ k
  · obtain ⟨hw, h12⟩ := h
    choose ξ hξ using fun n : ℕ+ ↦ exists_periodRelation ℂ ((n : ℕ) : ℤ)
    refine fun f f' hff' ↦ injective_of_forall_newform (p.subtype ∘ₗ Φ)
      (fun n ↦ periodAction hw (ξ n)) (fun n f ↦ (hΦ hw n (hξ n) f).symm)
      (fun g h0 ↦ hne g (by omega) (Subtype.ext h0)) (by simp [hff'])
  · have := subsingleton_cuspForm hk h
    exact Function.injective_of_subsingleton _

/-! ### Injectivity of the even and odd period maps -/

/-- **The odd period polynomial determines the cusp form**: `f ↦ r_f^-` is injective on
`S_k(SL(2, ℤ))`. -/
theorem oddPeriodPolynomial_injective (hk : k = w + 2) :
    Function.Injective (oddPeriodPolynomial hk) :=
  injective_of_periodAction hk _ (fun hw n _ _ h f ↦ h.periodAction_oddPeriodPolynomial hk hw n f)
    fun g hw ↦ oddPeriodPolynomial_ne_zero hk _ (by omega) <|
      L_ofGamma1One_ne_zero g (by omega) <| by
        have : (k : ℝ) = w + 2 := by exact_mod_cast hk
        have : (10 : ℝ) ≤ w := by exact_mod_cast hw
        rw [Complex.natCast_re]
        linarith

/-- **The even period polynomial determines the cusp form**: `f ↦ r_f^+` is injective on
`S_k(SL(2, ℤ))`. -/
theorem evenPeriodPolynomial_injective (hk : k = w + 2) :
    Function.Injective (evenPeriodPolynomial hk) :=
  injective_of_periodAction hk _ (fun hw n _ _ h f ↦ h.periodAction_evenPeriodPolynomial hk hw n f)
    fun g hw ↦ evenPeriodPolynomial_ne_zero hk _ <| L_ofGamma1One_ne_zero g (by omega) <| by
      have : (k : ℝ) = w + 2 := by exact_mod_cast hk
      have : (10 : ℝ) ≤ w := by exact_mod_cast hw
      rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
      linarith

/-! ### The odd period map is an isomorphism -/

/-- **Every odd period polynomial is the odd period polynomial of a cusp form**: `f ↦ r_f^-` is
an injective linear map between spaces of the same dimension. -/
theorem oddPeriodPolynomial_surjective (hk : k = w + 2) :
    Function.Surjective (oddPeriodPolynomial hk) := by
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) := .of_injective _ CuspForm.toModularFormₗ_injective
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
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply,
    oddPeriodPolynomialEquiv_apply, oddPeriodPolynomialEquiv_apply,
    h.periodAction_oddPeriodPolynomial hk hw n f]

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
