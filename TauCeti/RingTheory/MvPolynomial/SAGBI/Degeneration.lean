/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.BoundedPresentation
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Criterion
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic

/-!
# Nonmonic SAGBI degenerations via diagonal rescaling

This file extends the flat weight presentations of
`TauCeti.RingTheory.MvPolynomial.SAGBI.BoundedPresentation` to unnormalized (possibly nonmonic)
families over a field `k`.

For an unnormalized family `b : ι → MvPolynomial σ k` over a field `k` with leading coefficients
`ℓ i = m.leadingCoeff (b i)` and monic normalizations `c i = m.monicNormalize (b i)` for a
monomial order `m`, the Rees presentation map of `b` factors through that of `c` by the diagonal
rescaling `D_ℓ = MvPolynomial.rescale ℓ` in the presentation variables
(`MonomialOrder.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale`), leaving the image
unchanged (`MonomialOrder.range_weightReesAeval_monicNormalize`). When every `b i` is nonzero, the
Rees relations of `b` are obtained from the Rees kernel of `c` by applying
`D_ℓ⁻¹ = MvPolynomial.rescale ℓ⁻¹` (`MonomialOrder.ker_weightReesAeval_eq_map`).

Under *monic toric weight certificates*—where each `c i` has `w`-weight at most
`d i = Finsupp.weight w (m.degree (b i))` with weight-`d i` component `X^(m.degree (b i))` (forcing
`b i ≠ 0`), binomials `Y^(u j) - Y^(v j)` generate `toricIdeal k (m.degree ∘ b)`, and polynomials
`Q j` of `d`-weight strictly below `Finsupp.weight d (u j)` satisfy
`aeval c (Q j) = aeval c (Y^(u j) - Y^(v j))`—transport along `D_ℓ⁻¹` yields the homogenized Rees
relations (`MonomialOrder.ker_weightReesAeval_eq_span_rescale`), retaining `∏ i, (ℓ i)⁻¹ ^ x i` on
every monomial `Y^x` while presenting `A.weightReesAlgebra w` flatly over `k[t]`
(`MonomialOrder.quotientSpanWeightHomogenizationRescaleEquiv`,
`MonomialOrder.flat_quotient_span_weightHomogenization_rescale`). Finally,
`MonomialOrder.IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval` packages the positive-weight
toric certificates and degeneration for any finite family of nonzero SAGBI generators of a
subalgebra `A` over a field, with no monicity or finite-variable hypothesis.

## Main declarations

* `MonomialOrder.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale`,
  `MonomialOrder.range_weightReesAeval_monicNormalize`, `MonomialOrder.ker_weightReesAeval_eq_map`,
  and `MonomialOrder.ker_weightReesAeval_eq_span_rescale`: range invariance under `monicNormalize`
  and `D_ℓ⁻¹` transport of Rees relations for nonzero nonmonic families.
* `MonomialOrder.weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span`,
  `MonomialOrder.weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span`,
  `MonomialOrder.map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span`,
  `MonomialOrder.quotientSpanWeightHomogenizationRescaleEquiv`, and
  `MonomialOrder.flat_quotient_span_weightHomogenization_rescale`: certificate-level nonmonic
  initial ideal, initial algebra, `k[t]`-presentation, and flatness.
* `MonomialOrder.IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval`: existence of toric binomial
  witnesses, bounded monic subduction certificates, and positive integral weights realizing the
  initial algebra, presentation initial ideal, `D_ℓ⁻¹`-transported Rees presentation, and induced
  subalgebra Rees algebra for any finite nonzero SAGBI basis.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
* W. Bruns, A. Conca, M. Lembo, *SAGBI combinatorics of maximal minors and a SAGBI algorithm*,
  2025, arXiv:2504.10019, Section 2.
-/

public section

open scoped Polynomial

namespace MonomialOrder

open _root_.MvPolynomial TauCeti TauCeti.MvPolynomial

variable {σ ι J k : Type*} [Field k] (m : MonomialOrder σ)

/-- The Rees presentation map of `b` factors through that of the monic normalization
`m.monicNormalize ∘ b` by the diagonal rescaling `Y i ↦ m.leadingCoeff (b i) * Y i` on the
presentation variables. -/
theorem weightReesAeval_monicNormalize_comp_mapAlgHom_rescale
    (b : ι → MvPolynomial σ k) (d : ι → ℕ) :
    (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d).comp
        (Polynomial.mapAlgHom (rescale fun i ↦ m.leadingCoeff (b i))) =
      weightReesAeval b d := by
  rw [weightReesAeval_comp_mapAlgHom_rescale]
  congr 1
  funext i
  rw [Algebra.smul_def, algebraMap_eq, m.C_leadingCoeff_mul_monicNormalize]

/-- Normalizing the generators of a polynomial family over a field does not change the image of the
Rees presentation map. -/
theorem range_weightReesAeval_monicNormalize (b : ι → MvPolynomial σ k) (d : ι → ℕ) :
    (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d).range = (weightReesAeval b d).range := by
  classical
  let a : ι → k := fun i ↦ if b i = 0 then 1 else m.leadingCoeff (b i)
  have ha : ∀ i, IsUnit (a i) := fun i ↦ by
    dsimp only [a]
    split_ifs with hb
    · exact isUnit_one
    · exact (m.leadingCoeff_ne_zero_iff.mpr hb).isUnit
  have hsmul : (fun i ↦ a i • m.monicNormalize (b i)) = b := funext fun i ↦ by
    dsimp only [a]
    split_ifs with hb
    · simp [hb]
    · rw [Algebra.smul_def, algebraMap_eq, m.C_leadingCoeff_mul_monicNormalize]
  conv_rhs => rw [← hsmul]
  exact (range_weightReesAeval_smul_eq ha (fun i ↦ m.monicNormalize (b i)) d).symm

variable {m}

/-- **Nonmonic Rees kernel transport.** For a family of nonzero polynomials `b`, the kernel of
`weightReesAeval b d` is the image of the Rees kernel of the monic normalization under the inverse
leading-coefficient rescaling `Y i ↦ (m.leadingCoeff (b i))⁻¹ * Y i`. -/
theorem ker_weightReesAeval_eq_map {b : ι → MvPolynomial σ k} (hb : ∀ i, b i ≠ 0) (d : ι → ℕ) :
    RingHom.ker (weightReesAeval b d) =
      (RingHom.ker (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d)).map
        (Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹)) := by
  have hsmul : b = fun i ↦ m.leadingCoeff (b i) • m.monicNormalize (b i) :=
    funext fun i ↦ by rw [Algebra.smul_def, algebraMap_eq, m.C_leadingCoeff_mul_monicNormalize]
  conv_lhs => rw [hsmul]
  exact ker_weightReesAeval_smul_eq_map
    (fun i ↦ mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (hb i))) _ d

section MonicToric

variable {b : ι → MvPolynomial σ k} {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}

attribute [local instance] Polynomial.algebra

variable {A : Subalgebra k (MvPolynomial σ k)} (hA : A = Algebra.adjoin k (Set.range b))
  (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
  (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
    (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
  (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
    Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
  (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
    (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
  (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
    aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1))
include hc ha hJ hQ hQc

private theorem nonmonic_certificates :
    (∀ i, b i ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i)))) ∧
    (∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i))) (b i) =
      m.leadingTerm (b i)) ∧
    RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) =
      Ideal.span (Set.range fun j ↦ rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial (u j) (1 : k) - monomial (v j) 1)) ∧
    (∀ j, (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial (u j) (1 : k) - monomial (v j) 1)).IsWeightedHomogeneous
      (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))) ∧
    (∀ j, rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (Q j) ∈
      weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
        (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))) ∧
    (∀ j, aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (Q j)) =
      aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial (u j) (1 : k) - monomial (v j) 1))) := by
  have hb : ∀ i, b i ≠ 0 :=
    fun i ↦ m.ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq (ha i)
  refine ⟨fun i ↦ m.monicNormalize_mem_iff.mp (hc i),
    fun i ↦ m.weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize (ha i), ?_,
    fun j ↦ (TauCeti.isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal
      (deg := Finsupp.weight w) (hJ.symm ▸ Ideal.subset_span (Set.mem_range_self j))).rescale _,
    fun j ↦ rescale_mem_weightFiltrationLT (hQ j),
    fun j ↦ by simp only [m.aeval_rescale_leadingCoeff_inv, hQc]⟩
  rw [m.ker_aeval_leadingTerm_eq_map hb, hJ, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def]

/-- **Nonmonic Rees presentation via `D_ℓ⁻¹` transport.** If toric binomials `Y^(u j) - Y^(v j)` and
monic subduction certificates `Q j` satisfy the monic toric weight hypotheses for
`m.monicNormalize ∘ b`, then the kernel of `weightReesAeval b` is generated by the homogenizations
of the `D_ℓ⁻¹`-rescaled relations `rescale ℓ⁻¹ (Y^(u j) - Y^(v j) - Q j)`, retaining
`∏ i, (ℓ i)⁻¹ ^ x i` on every monomial `Y^x`. -/
theorem ker_weightReesAeval_eq_span_rescale :
    RingHom.ker (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))) =
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j))) := by
  rw [ker_weightReesAeval_eq_map
      (fun i ↦ m.ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq (ha i)),
    ker_weightReesAeval_eq_span_of_toricIdeal_eq_span hc ha hJ hQ hQc, Ideal.map_span,
    ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  rw [Function.comp_apply, Polynomial.coe_mapAlgHom, MvPolynomial.map_rescale_weightHomogenization]

/-- **Weight-initial presentation ideal for nonmonic generators.** Under monic toric weight
certificates, the `d`-weight-initial ideal of `RingHom.ker (aeval b)` is the presentation kernel of
the actual leading terms `m.leadingTerm ∘ b`. -/
theorem weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span :
    (RingHom.ker (aeval (R := k) b)).weightInitialIdeal
        (fun i ↦ Finsupp.weight w (m.degree (b i))) =
      RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) := by
  obtain ⟨hc', hg', hJ', hr', hQ', hQc'⟩ := nonmonic_certificates hc ha hJ hQ hQc
  exact weightInitialIdeal_ker_aeval hc' hg' hJ' hr' hQ' hQc'

/-- **Weight-initial algebra for nonmonic generators.** Under monic toric weight certificates, the
weight-initial algebra of `Algebra.adjoin k (Set.range b)` is the subalgebra generated by the
leading terms `m.leadingTerm ∘ b`. -/
theorem weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span :
    (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
      Algebra.adjoin k (Set.range fun i ↦ m.leadingTerm (b i)) := by
  obtain ⟨hc', hg', hJ', hr', hQ', hQc'⟩ := nonmonic_certificates hc ha hJ hQ hQc
  exact weightInitialAlgebra_adjoin_eq hc' hg' hJ' hr' hQ' hQc'

include hA in
/-- Under monic toric weight certificates for a family `b` generating `A`, the image of
`weightReesAeval b` is the embedded induced weight Rees algebra of `A`. -/
theorem map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) =
      (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range := by
  obtain ⟨hc', hg', hJ', hr', hQ', hQc'⟩ := nonmonic_certificates hc ha hJ hQ hQc
  exact A.map_weightReesAlgebra_eq_range_weightReesAeval w hA hc' hg' hJ' hr' hQ' hQc'

/-- **`k[t]`-algebra Rees presentation for nonmonic generators.** Under monic toric weight
certificates for a family `b` generating `A`, quotienting `(MvPolynomial ι k)[t]` by the
`D_ℓ⁻¹`-transported homogenized relations presents the induced weight Rees algebra
`A.weightReesAlgebra w`. -/
noncomputable def quotientSpanWeightHomogenizationRescaleEquiv :
    ((MvPolynomial ι k)[X] ⧸
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j)))) ≃ₐ[k[X]]
      A.weightReesAlgebra w :=
  have hcert := nonmonic_certificates hc ha hJ hQ hQc
  have hspan : Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j))) =
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (monomial (u j) 1 - monomial (v j) 1) -
            rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (Q j))) := by
    simp only [map_sub]
  (Ideal.quotientEquivAlgOfEq k[X] hspan).trans
    (quotientSpanWeightHomogenizationEquiv hA
      hcert.1 hcert.2.1 hcert.2.2.1 hcert.2.2.2.1 hcert.2.2.2.2.1 hcert.2.2.2.2.2)

@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_mk (f : (MvPolynomial ι k)[X]) :
    quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc (Ideal.Quotient.mk _ f) =
      weightReesAevalLift (fun i ↦ hA ▸ Algebra.subset_adjoin (Set.mem_range_self i))
        (fun i ↦ m.monicNormalize_mem_iff.mp (hc i)) f := by
  simp [quotientSpanWeightHomogenizationRescaleEquiv]

@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_weightReesAevalLift
    {hbA : ∀ i, b i ∈ A}
    {hbw : ∀ i, b i ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i)))}
    (f : (MvPolynomial ι k)[X]) :
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (weightReesAevalLift hbA hbw f) = Ideal.Quotient.mk _ f := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk]

@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_monomial
    (i : ι) (hbAi : b i ∈ A)
    (hbi : ⟨b i, hbAi⟩ ∈ A.weightFiltration w (Finsupp.weight w (m.degree (b i)))) :
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (coeffSubalgebra.monomial (A.weightFiltration w) (Finsupp.weight w (m.degree (b i)))
        ⟨b i, hbAi⟩ hbi) = Ideal.Quotient.mk _ (Polynomial.C (X i : MvPolynomial ι k)) := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk,
    weightReesAevalLift_C, aeval_X]

@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_X :
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)) =
      Ideal.Quotient.mk _ Polynomial.X := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk,
    weightReesAevalLift_X]

/-- **Flatness of the `D_ℓ⁻¹`-transported homogenized presentation.** Under monic toric weight
certificates, the quotient of `(MvPolynomial ι k)[t]` by the `D_ℓ⁻¹`-rescaled homogenized
relations is flat over `k[t]`. -/
theorem flat_quotient_span_weightHomogenization_rescale :
    Module.Flat k[X]
      ((MvPolynomial ι k)[X] ⧸
        Ideal.span (Set.range fun j ↦
          weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
            (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
            (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
              (monomial (u j) 1 - monomial (v j) 1 - Q j)))) := by
  rw [← ker_weightReesAeval_eq_span_rescale hc ha hJ hQ hQc, ker_weightReesAeval_eq_weightReesIdeal]
  exact Ideal.flat_quotient_weightReesIdeal _ _

end MonicToric

/-- **Positive-weight degeneration of a finite nonzero SAGBI basis.** Let `b : ι → MvPolynomial σ k`
be a finite family of nonzero polynomials over a field `k` forming a SAGBI basis of a subalgebra `A`
(not assumed monic, and with no finiteness assumption on `σ`). Then there exist a finite set `B` of
toric binomial exponent pairs, monic subduction certificates `Q : B → MvPolynomial ι k`, and
strictly positive integral weights `w : σ → ℕ` such that, for the generator weights
`d i = Finsupp.weight w (m.degree (b i))`:
1. the binomials `Y^(j.val.1) - Y^(j.val.2)` for `j : B` generate the toric ideal of `m.degree ∘ b`,
   and each `Q j` satisfies `aeval (m.monicNormalize ∘ b) (Q j) =
   aeval (m.monicNormalize ∘ b) (Y^(j.val.1) - Y^(j.val.2))` with strict monomial-order and
   `d`-weight bounds below `j.val.1`;
2. each `b i` has weight at most `d i` with top component `m.leadingTerm (b i)`, and
   `m.monicNormalize (b i)` has top component `X^(m.degree (b i))`;
3. `A.weightInitialAlgebra w = m.initialAlgebra A`;
4. `(RingHom.ker (aeval b)).weightInitialIdeal d = RingHom.ker (aeval (m.leadingTerm ∘ b))`;
5. `RingHom.ker (weightReesAeval b d)` is generated by the homogenizations of the `D_ℓ⁻¹`-rescaled
   lifted toric relations; and
6. `(weightReesAeval b d).range` is the embedded weight Rees algebra `A.weightReesAlgebra w`. -/
theorem IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval [Finite ι]
    {b : ι → MvPolynomial σ k} {A : Subalgebra k (MvPolynomial σ k)}
    (hb : ∀ i, b i ≠ 0) (h : m.IsSAGBIBasis (Set.range b) A) :
    ∃ (B : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) (Q : B → MvPolynomial ι k) (w : σ → ℕ),
      (∀ s, 0 < w s) ∧
      TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
        Ideal.span (Set.range fun j : B ↦ monomial j.val.1 (1 : k) - monomial j.val.2 1) ∧
      (∀ j : B, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
        aeval (fun i ↦ m.monicNormalize (b i)) (monomial j.val.1 (1 : k) - monomial j.val.2 1)) ∧
      (∀ j : B, ∀ x ∈ (Q j).support,
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) x ≺[m]
          Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) j.val.1) ∧
      (∀ j : B, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
        (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) j.val.1)) ∧
      (∀ i, b i ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))) ∧
        weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i))) (b i) =
          m.leadingTerm (b i) ∧
        weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
          (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1) ∧
      A.weightInitialAlgebra w = m.initialAlgebra A ∧
      (RingHom.ker (aeval (R := k) b)).weightInitialIdeal
          (fun i ↦ Finsupp.weight w (m.degree (b i))) =
        RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) ∧
      RingHom.ker (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))) =
        Ideal.span (Set.range fun j : B ↦
          weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
            (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) j.val.1)
            (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
              (monomial j.val.1 1 - monomial j.val.2 1 - Q j))) ∧
      (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) =
        (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range := by
  classical
  obtain rfl := h.adjoin_eq
  set c : ι → MvPolynomial σ k := fun i ↦ m.monicNormalize (b i)
  have hc_monic (i : ι) : m.Monic (c i) := m.monic_monicNormalize (hb i)
  have hrc : Set.range c = m.monicNormalize '' Set.range b := Set.range_comp _ _
  have hadj : Algebra.adjoin k (Set.range c) = Algebra.adjoin k (Set.range b) := by
    rw [hrc, m.adjoin_image_monicNormalize]
  have hsagbi : m.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range c)) := by
    rwa [hadj, hrc, m.isSAGBIBasis_image_monicNormalize_iff]
  obtain ⟨B, hB, hspan⟩ := TauCeti.exists_finset_toricIdeal_eq_span fun i ↦ m.degree (b i)
  have hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j : B ↦ monomial j.val.1 (1 : k) - monomial j.val.2 1) := by
    rw [hspan k, Set.image_eq_range]
    rfl
  have hB' (j : B) :
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) j.val.1 =
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) j.val.2 := by
    simpa [c] using hB j.val j.property
  choose Q hQc hQ using fun j : B ↦ hsagbi.exists_aeval_eq_aeval_sub hc_monic (hB' j)
  obtain ⟨w, hw, hcw, hgw, hQw⟩ := exists_pos_weight_forall_mem_weightFiltrationLT hc_monic hQ
  simp only [c, m.degree_monicNormalize] at hcw hgw hQw hQ
  have hinit : (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
      m.initialAlgebra (Algebra.adjoin k (Set.range b)) := by
    rw [weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span hcw hgw hJ hQw hQc,
      ← h.adjoin_leadingTerm, ← Set.range_comp]
    rfl
  exact ⟨B, Q, w, hw, hJ, hQc, hQ, hQw,
    fun i ↦ ⟨m.monicNormalize_mem_iff.mp (hcw i),
      m.weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize (hgw i), hgw i⟩,
    hinit,
    weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span hcw hgw hJ hQw hQc,
    ker_weightReesAeval_eq_span_rescale hcw hgw hJ hQw hQc,
    map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span rfl hcw hgw hJ hQw hQc⟩

end MonomialOrder
