/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Initial.Degeneration
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Criterion
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Weight
import TauCeti.RingTheory.MvPolynomial.ToricIdeal.HilbertFunction

/-!
# Flat weight presentations and nonmonic SAGBI degenerations

Give the variable `X s` of `MvPolynomial σ R` the weight `w s ∈ ℕ` and the presentation variable
`Y i` of `MvPolynomial ι R` the weight `d i ∈ ℕ`. When each `c i` belongs to a subalgebra `A` and
has ambient `w`-weight at most `d i`, the Rees presentation map `weightReesAeval c d`
(`Y i ↦ c i * t ^ d i`, `t ↦ t`) lifts to the `R[t]`-algebra homomorphism
`TauCeti.MvPolynomial.weightReesAevalLift` into `A.weightReesAlgebra w`
(`TauCeti.RingTheory.MvPolynomial.Subalgebra.WeightFiltration`), with kernel
`(RingHom.ker (aeval c)).weightReesIdeal d`
(`TauCeti.MvPolynomial.ker_weightReesAeval_eq_weightReesIdeal`).

Suppose `c : ι → MvPolynomial σ R` and `d : ι → ℕ` carry *bounded relation certificates*: each
`c i` has `w`-weight at most `d i` with weight-`d i` homogeneous component `g i`, `d`-homogeneous
polynomials `r j` of weight `e j` generate `RingHom.ker (aeval g)`, and polynomials `Q j` of
`d`-weight strictly below `e j` satisfy `aeval c (Q j) = aeval c (r j)`. Combining
`TauCeti.MvPolynomial.ker_weightReesAeval_eq_weightReesIdeal` with
`TauCeti.MvPolynomial.ker_weightReesAeval_eq_span` and the ideal degeneration results of
`TauCeti.RingTheory.MvPolynomial.Initial.Degeneration` yields, over any commutative ring `R`:

* **Weight-initial presentation ideal**: `(RingHom.ker (aeval c)).weightInitialIdeal d =
  RingHom.ker (aeval g)` (`TauCeti.MvPolynomial.weightInitialIdeal_ker_aeval`), and setting `t = 0`
  in the homogenized lifted relations recovers `RingHom.ker (aeval g)`.
* **General-fibre presentation ideal**: the lifted relations `r j - Q j` generate
  `RingHom.ker (aeval c)` (`TauCeti.MvPolynomial.ker_aeval_eq_span_sub`), recovered by setting
  `t = 1` in the homogenized lifted relations.
* **`R[t]`-algebra Rees presentation**: for any subalgebra `A = Algebra.adjoin R (Set.range c)`,
  `weightReesAevalLift` is surjective (`TauCeti.MvPolynomial.weightReesAevalLift_surjective`), so
  the quotient of `(MvPolynomial ι R)[t]` by the homogenized lifted relations is isomorphic as an
  `R[t]`-algebra to `A.weightReesAlgebra w`
  (`TauCeti.MvPolynomial.quotientSpanWeightHomogenizationEquiv`), and over a field `k` this
  explicit quotient is flat over `k[t]`
  (`TauCeti.MvPolynomial.flat_quotient_span_weightHomogenization`).

For an unnormalized family `b : ι → MvPolynomial σ k` over a field `k` with leading coefficients
`ℓ i = m.leadingCoeff (b i)` and monic normalizations `c i = m.monicNormalize (b i)` for a
monomial order `m`, the Rees presentation map of `b` factors through that of `c` by the diagonal
rescaling `D_ℓ = MvPolynomial.rescale ℓ` in the presentation variables
(`MonomialOrder.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale`), leaving the image
unchanged (`MonomialOrder.range_weightReesAeval_monicNormalize`). When every `b i` is nonzero, the
Rees relations of `b` are obtained from the Rees kernel of `c` by applying
`D_ℓ⁻¹ = MvPolynomial.rescale ℓ⁻¹` (`MonomialOrder.ker_weightReesAeval_eq_map`). Under *monic toric
weight certificates*—where each `c i` has `w`-weight at most
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

* `TauCeti.MvPolynomial.weightReesAevalLift_surjective` and
  `TauCeti.MvPolynomial.quotientSpanWeightHomogenizationEquiv`: surjectivity of
  `weightReesAevalLift` and the homogenized `R[t]`-algebra presentation of
  `A.weightReesAlgebra w` under bounded relation certificates.
* `TauCeti.MvPolynomial.weightInitialIdeal_ker_aeval`,
  `TauCeti.MvPolynomial.ker_aeval_eq_span_sub`, and
  `TauCeti.MvPolynomial.flat_quotient_span_weightHomogenization`: the `t = 0` initial ideal,
  `t = 1` presentation kernel, and `k[t]`-flatness under bounded relation certificates.
* `MonomialOrder.range_weightReesAeval_monicNormalize`, `MonomialOrder.ker_weightReesAeval_eq_map`,
  and `MonomialOrder.ker_weightReesAeval_eq_span_rescale`: range invariance under `monicNormalize`
  and `D_ℓ⁻¹` transport of Rees relations for nonzero nonmonic families.
* `MonomialOrder.weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span`,
  `MonomialOrder.weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span`,
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

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial TauCeti

section Certificates

variable {σ ι J R : Type*} [CommRing R] {w : σ → ℕ} {c g : ι → MvPolynomial σ R} {d : ι → ℕ}
  {r Q : J → MvPolynomial ι R} {e : J → ℕ}

/-- Under bounded relation certificates, the weight Rees ideal of `RingHom.ker (aeval c)` is
generated by the homogenizations in degree `e j` of the lifted relations `r j - Q j`. -/
theorem weightReesIdeal_ker_aeval_eq_span
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (RingHom.ker (aeval (R := R) c)).weightReesIdeal d =
      Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j)) := by
  rw [← ker_weightReesAeval_eq_weightReesIdeal, ker_weightReesAeval_eq_span hc hg hJ hr hQ hQc]

/-- **Special fibre of the homogenized relation ideal.** If `d`-homogeneous polynomials `r j` of
weight `e j` generate `RingHom.ker (aeval g)` and each `Q j` has `d`-weight strictly below `e j`,
setting `t = 0` in the ideal generated by the homogenized lifted relations `r j - Q j` recovers
`RingHom.ker (aeval g)`. -/
theorem map_constantCoeff_span_weightHomogenization
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j)) :
    (Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j))).map
        Polynomial.constantCoeff =
      RingHom.ker (aeval (R := R) g) := by
  rw [Ideal.map_span, hJ, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  rw [Function.comp_apply, Polynomial.constantCoeff_apply,
    coeff_zero_weightHomogenization_sub (hr j) (hQ j)]

/-- **Weight-initial ideal of the presentation kernel.** Under bounded relation certificates, the
`d`-weight-initial ideal of `RingHom.ker (aeval c)` is the presentation kernel
`RingHom.ker (aeval g)` of the initial forms. -/
theorem weightInitialIdeal_ker_aeval
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (RingHom.ker (aeval (R := R) c)).weightInitialIdeal d = RingHom.ker (aeval (R := R) g) := by
  rw [← Ideal.map_constantCoeff_weightReesIdeal (RingHom.ker (aeval (R := R) c)) d,
    weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc,
    map_constantCoeff_span_weightHomogenization hJ hr hQ]

/-- **Presentation kernel from bounded weight certificates.** Under bounded relation certificates,
the lifted relations `r j - Q j` generate `RingHom.ker (aeval c)`. -/
theorem ker_aeval_eq_span_sub
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    RingHom.ker (aeval (R := R) c) = Ideal.span (Set.range fun j ↦ r j - Q j) := by
  -- Evaluate the Rees-ideal equality at `t = 1`.
  rw [← Ideal.map_evalRingHom_one_weightReesIdeal (RingHom.ker (aeval (R := R) c)) d,
    weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  simp

/-- **General fibre of the homogenized relation ideal.** Under bounded relation certificates,
setting `t = 1` in the ideal generated by the homogenized lifted relations recovers
`RingHom.ker (aeval c)`. -/
theorem map_evalRingHom_one_span_weightHomogenization
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j))).map
        (Polynomial.evalRingHom 1) =
      RingHom.ker (aeval (R := R) c) := by
  rw [← weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc,
    Ideal.map_evalRingHom_one_weightReesIdeal (RingHom.ker (aeval (R := R) c)) d]

attribute [local instance] Polynomial.algebra in
/-- Under bounded relation certificates, `weightReesAevalLift` surjects onto the induced weight
Rees algebra `A.weightReesAlgebra w` whenever the `c i` generate `A`. -/
theorem weightReesAevalLift_surjective {A : Subalgebra R (MvPolynomial σ R)}
    (hcA : ∀ i, c i ∈ A) (hA : A ≤ Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    Function.Surjective (weightReesAevalLift hcA hc) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  have hAeq : A = Algebra.adjoin R (Set.range c) :=
    le_antisymm hA (Algebra.adjoin_le (Set.range_subset_iff.mpr hcA))
  intro y
  have hy : ((A.weightReesInclusion w y : weightReesAlgebra R w) : (MvPolynomial σ R)[X]) ∈
      (weightReesAeval c d).range := by
    rw [← A.map_weightReesAlgebra_eq_range_weightReesAeval w hAeq hc hg hJ hr hQ hQc]
    exact ⟨y, y.2, (A.coe_weightReesInclusion w y).symm⟩
  obtain ⟨f, hf⟩ := (weightReesAeval c d).mem_range.mp hy
  refine ⟨f, A.weightReesInclusion_injective w (Subtype.ext ?_)⟩
  rwa [A.coe_weightReesInclusion, map_val_coe_weightReesAevalLift]

attribute [local instance] Polynomial.algebra in
/-- **`R[t]`-algebra Rees presentation.** Under bounded relation certificates for a family `c`
generating `A`, the quotient of `(MvPolynomial ι R)[t]` by the homogenized lifted relations is
isomorphic as an `R[t]`-algebra to the induced weight Rees algebra `A.weightReesAlgebra w`. -/
noncomputable def quotientSpanWeightHomogenizationEquiv {A : Subalgebra R (MvPolynomial σ R)}
    (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    ((MvPolynomial ι R)[X] ⧸
      Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j))) ≃ₐ[R[X]]
      A.weightReesAlgebra w :=
  letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  let hcA : ∀ i, c i ∈ A := fun i ↦ hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)
  have hker : RingHom.ker (weightReesAevalLift hcA hc) =
      Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j)) :=
    (ker_weightReesAevalLift hcA hc).trans (ker_weightReesAeval_eq_span hc hg hJ hr hQ hQc)
  (Ideal.quotientEquivAlgOfEq R[X] hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (weightReesAevalLift_surjective hcA hA.le hc hg hJ hr hQ hQc))

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationEquiv_mk {A : Subalgebra R (MvPolynomial σ R)}
    (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    quotientSpanWeightHomogenizationEquiv hA hc hg hJ hr hQ hQc (Ideal.Quotient.mk _ f) =
      weightReesAevalLift (fun i ↦ hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)) hc f := by
  simp [quotientSpanWeightHomogenizationEquiv]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationEquiv_symm_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} (hA : A = Algebra.adjoin R (Set.range c))
    {hcA : ∀ i, c i ∈ A}
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationEquiv hA hc hg hJ hr hQ hQc).symm
      (weightReesAevalLift hcA hc f) = Ideal.Quotient.mk _ f := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationEquiv_mk]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationEquiv_symm_monomial
    {A : Subalgebra R (MvPolynomial σ R)} (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    (i : ι) (hcAi : c i ∈ A) (hci : ⟨c i, hcAi⟩ ∈ A.weightFiltration w (d i)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationEquiv hA hc hg hJ hr hQ hQc).symm
      (coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcAi⟩ hci) =
      Ideal.Quotient.mk _ (Polynomial.C (X i : MvPolynomial ι R)) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationEquiv_mk, weightReesAevalLift_C_X]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationEquiv_symm_X
    {A : Subalgebra R (MvPolynomial σ R)} (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationEquiv hA hc hg hJ hr hQ hQc).symm
      (coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)) =
      Ideal.Quotient.mk _ Polynomial.X := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationEquiv_mk, weightReesAevalLift_X]

attribute [local instance] Polynomial.algebra in
/-- **Flatness of the explicit homogenized presentation over a field.** Under bounded relation
certificates over a field `k`, the quotient of `(MvPolynomial ι k)[t]` by the homogenized lifted
relations is flat over `k[t]`. -/
theorem flat_quotient_span_weightHomogenization {k : Type*} [Field k]
    {c g : ι → MvPolynomial σ k} {r Q : J → MvPolynomial ι k}
    (hc : ∀ i, c i ∈ weightFiltration k w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    Module.Flat k[X]
      ((MvPolynomial ι k)[X] ⧸
        Ideal.span (Set.range fun j ↦ weightHomogenization k d (e j) (r j - Q j))) := by
  rw [← weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc]
  exact Ideal.flat_quotient_weightReesIdeal _ _

end Certificates

end TauCeti.MvPolynomial

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
  let aInv : ι → k := fun i ↦ if b i = 0 then 1 else (m.leadingCoeff (b i))⁻¹
  have ha : ∀ i, a i * aInv i = 1 := fun i ↦ by
    dsimp only [a, aInv]
    split_ifs with hb
    · exact mul_one 1
    · exact mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hb)
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

private theorem ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq
    {b : ι → MvPolynomial σ k} {w : σ → ℕ}
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1) :
    ∀ i, b i ≠ 0 :=
  fun i h0 ↦ by simpa [h0] using (ha i).symm

private theorem weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize
    {b : ι → MvPolynomial σ k} {w : σ → ℕ}
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1) (i : ι) :
    weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i))) (b i) =
      m.leadingTerm (b i) := by
  nth_rw 2 [← m.C_leadingCoeff_mul_monicNormalize (b i)]
  rw [← smul_eq_C_mul, map_smul, ha i, smul_monomial, smul_eq_mul, mul_one, leadingTerm]

private theorem ker_aeval_leadingTerm_eq_span_rescale
    {b : ι → MvPolynomial σ k} {u v : J → ι →₀ ℕ} (hb : ∀ i, b i ≠ 0)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1)) :
    RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) =
      Ideal.span (Set.range fun j ↦ rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial (u j) (1 : k) - monomial (v j) 1)) := by
  rw [m.ker_aeval_leadingTerm_eq_map hb, hJ, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def]

private theorem isWeightedHomogeneous_rescale_of_toricIdeal_eq_span
    {b : ι → MvPolynomial σ k} {w : σ → ℕ} {u v : J → ι →₀ ℕ}
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1)) (j : J) :
    (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
      (monomial (u j) (1 : k) - monomial (v j) 1)).IsWeightedHomogeneous
      (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)) :=
  (TauCeti.isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal (deg := Finsupp.weight w)
    (hJ.symm ▸ Ideal.subset_span (Set.mem_range_self j))).rescale _

private theorem aeval_rescale_eq_of_monicNormalize
    {b : ι → MvPolynomial σ k} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hb : ∀ i, b i ≠ 0)
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1))
    (j : J) :
    aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (Q j)) =
      aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial (u j) (1 : k) - monomial (v j) 1)) := by
  have hscale (P : MvPolynomial ι k) :
      aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) P) =
        aeval (fun i ↦ m.monicNormalize (b i)) P := by
    rw [← m.aeval_monicNormalize_comp_rescale b, AlgHom.comp_apply,
      rescale_rescale_of_mul_eq_one
        (fun i ↦ inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (hb i)))]
  rw [hscale, hscale, hQc]

/-- **Nonmonic Rees presentation via `D_ℓ⁻¹` transport.** If toric binomials `Y^(u j) - Y^(v j)` and
monic subduction certificates `Q j` satisfy the monic toric weight hypotheses for
`m.monicNormalize ∘ b`, then the kernel of `weightReesAeval b` is generated by the homogenizations
of the `D_ℓ⁻¹`-rescaled relations `rescale ℓ⁻¹ (Y^(u j) - Y^(v j) - Q j)`, retaining
`∏ i, (ℓ i)⁻¹ ^ x i` on every monomial `Y^x`. -/
theorem ker_weightReesAeval_eq_span_rescale {b : ι → MvPolynomial σ k} {w : σ → ℕ}
    {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    RingHom.ker (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))) =
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j))) := by
  rw [ker_weightReesAeval_eq_map (ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha),
    ker_weightReesAeval_eq_span_of_toricIdeal_eq_span hc ha hJ hQ hQc, Ideal.map_span,
    ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  rw [Function.comp_apply, Polynomial.coe_mapAlgHom, MvPolynomial.map_rescale_weightHomogenization]

/-- **Weight-initial presentation ideal for nonmonic generators.** Under monic toric weight
certificates, the `d`-weight-initial ideal of `RingHom.ker (aeval b)` is the presentation kernel of
the actual leading terms `m.leadingTerm ∘ b`. -/
theorem weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    (RingHom.ker (aeval (R := k) b)).weightInitialIdeal
        (fun i ↦ Finsupp.weight w (m.degree (b i))) =
      RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) :=
  have hb := ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha
  weightInitialIdeal_ker_aeval
    (fun i ↦ m.monicNormalize_mem_iff.mp (hc i))
    (weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize ha)
    (ker_aeval_leadingTerm_eq_span_rescale hb hJ)
    (isWeightedHomogeneous_rescale_of_toricIdeal_eq_span hJ)
    (fun j ↦ rescale_mem_weightFiltrationLT (hQ j))
    (aeval_rescale_eq_of_monicNormalize hb hQc)

/-- **Weight-initial algebra for nonmonic generators.** Under monic toric weight certificates, the
weight-initial algebra of `Algebra.adjoin k (Set.range b)` is the subalgebra generated by the
leading terms `m.leadingTerm ∘ b`. -/
theorem weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
      Algebra.adjoin k (Set.range fun i ↦ m.leadingTerm (b i)) :=
  have hb := ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha
  weightInitialAlgebra_adjoin_eq
    (fun i ↦ m.monicNormalize_mem_iff.mp (hc i))
    (weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize ha)
    (ker_aeval_leadingTerm_eq_span_rescale hb hJ)
    (isWeightedHomogeneous_rescale_of_toricIdeal_eq_span hJ)
    (fun j ↦ rescale_mem_weightFiltrationLT (hQ j))
    (aeval_rescale_eq_of_monicNormalize hb hQc)

/-- Under monic toric weight certificates for a family `b` generating `A`, the image of
`weightReesAeval b` is the embedded induced weight Rees algebra of `A`. -/
theorem map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) =
      (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range :=
  have hb := ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha
  A.map_weightReesAlgebra_eq_range_weightReesAeval w hA
    (fun i ↦ m.monicNormalize_mem_iff.mp (hc i))
    (weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize ha)
    (ker_aeval_leadingTerm_eq_span_rescale hb hJ)
    (isWeightedHomogeneous_rescale_of_toricIdeal_eq_span hJ)
    (fun j ↦ rescale_mem_weightFiltrationLT (hQ j))
    (aeval_rescale_eq_of_monicNormalize hb hQc)

attribute [local instance] Polynomial.algebra in
/-- **`k[t]`-algebra Rees presentation for nonmonic generators.** Under monic toric weight
certificates for a family `b` generating `A`, quotienting `(MvPolynomial ι k)[t]` by the
`D_ℓ⁻¹`-transported homogenized relations presents the induced weight Rees algebra
`A.weightReesAlgebra w`. -/
noncomputable def quotientSpanWeightHomogenizationRescaleEquiv
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    ((MvPolynomial ι k)[X] ⧸
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j)))) ≃ₐ[k[X]]
      A.weightReesAlgebra w :=
  letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  have hb := ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha
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
      (fun i ↦ m.monicNormalize_mem_iff.mp (hc i))
      (weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize ha)
      (ker_aeval_leadingTerm_eq_span_rescale hb hJ)
      (isWeightedHomogeneous_rescale_of_toricIdeal_eq_span hJ)
      (fun j ↦ rescale_mem_weightFiltrationLT (hQ j))
      (aeval_rescale_eq_of_monicNormalize hb hQc))

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_mk
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1))
    (f : (MvPolynomial ι k)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc (Ideal.Quotient.mk _ f) =
      weightReesAevalLift (fun i ↦ hA ▸ Algebra.subset_adjoin (Set.mem_range_self i))
        (fun i ↦ m.monicNormalize_mem_iff.mp (hc i)) f := by
  simp [quotientSpanWeightHomogenizationRescaleEquiv]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_weightReesAevalLift
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    {hbA : ∀ i, b i ∈ A}
    {hbw : ∀ i, b i ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i)))}
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1))
    (f : (MvPolynomial ι k)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (weightReesAevalLift hbA hbw f) = Ideal.Quotient.mk _ f := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_monomial
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1))
    (i : ι) (hbAi : b i ∈ A)
    (hbi : ⟨b i, hbAi⟩ ∈ A.weightFiltration w (Finsupp.weight w (m.degree (b i)))) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (coeffSubalgebra.monomial (A.weightFiltration w) (Finsupp.weight w (m.degree (b i)))
        ⟨b i, hbAi⟩ hbi) = Ideal.Quotient.mk _ (Polynomial.C (X i : MvPolynomial ι k)) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk,
    weightReesAevalLift_C_X]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_symm_X
    {A : Subalgebra k (MvPolynomial σ k)} {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hA : A = Algebra.adjoin k (Set.range b))
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (quotientSpanWeightHomogenizationRescaleEquiv hA hc ha hJ hQ hQc).symm
      (coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w)) =
      Ideal.Quotient.mk _ Polynomial.X := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [AlgEquiv.symm_apply_eq, quotientSpanWeightHomogenizationRescaleEquiv_mk,
    weightReesAevalLift_X]

attribute [local instance] Polynomial.algebra in
/-- **Flatness of the `D_ℓ⁻¹`-transported homogenized presentation.** Under monic toric weight
certificates, the quotient of `(MvPolynomial ι k)[t]` by the `D_ℓ⁻¹`-rescaled homogenized
relations is flat over `k[t]`. -/
theorem flat_quotient_span_weightHomogenization_rescale {b : ι → MvPolynomial σ k}
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
    (hc : ∀ i, m.monicNormalize (b i) ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))))
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1)
    (hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
      (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j)))
    (hQc : ∀ j, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
      aeval (fun i ↦ m.monicNormalize (b i)) (monomial (u j) (1 : k) - monomial (v j) 1)) :
    Module.Flat k[X]
      ((MvPolynomial ι k)[X] ⧸
        Ideal.span (Set.range fun j ↦
          weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
            (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
            (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
              (monomial (u j) 1 - monomial (v j) 1 - Q j)))) := by
  rw [← ker_weightReesAeval_eq_span_rescale hc ha hJ hQ hQc, ker_weightReesAeval_eq_weightReesIdeal]
  exact Ideal.flat_quotient_weightReesIdeal _ _

/-- **Positive-weight degeneration of a finite nonzero SAGBI basis.** Let `b : ι → MvPolynomial σ k`
be a finite family of nonzero polynomials over a field `k` forming a SAGBI basis of a subalgebra `A`
(not assumed monic, and with no finiteness assumption on `σ`). Then there exist a finite set `B` of
toric binomial exponent pairs, monic subduction certificates `Q : B → MvPolynomial ι k`, and
strictly positive integral weights `w : σ → ℕ` such that, for the generator weights
`d i = Finsupp.weight w (m.degree (b i))`:
1. the binomials `Y^(j.1.1) - Y^(j.1.2)` for `j : B` generate the toric ideal of `m.degree ∘ b`,
   and each `Q j` satisfies `aeval (m.monicNormalize ∘ b) (Q j) =
   aeval (m.monicNormalize ∘ b) (Y^(j.1.1) - Y^(j.1.2))` with strict monomial-order and `d`-weight
   bounds below `j.1.1`;
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
        Ideal.span (Set.range fun j : B ↦ monomial j.1.1 (1 : k) - monomial j.1.2 1) ∧
      (∀ j : B, aeval (fun i ↦ m.monicNormalize (b i)) (Q j) =
        aeval (fun i ↦ m.monicNormalize (b i)) (monomial j.1.1 (1 : k) - monomial j.1.2 1)) ∧
      (∀ j : B, ∀ x ∈ (Q j).support,
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) x ≺[m]
          Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) j.1.1) ∧
      (∀ j : B, Q j ∈ weightFiltrationLT k (fun i ↦ Finsupp.weight w (m.degree (b i)))
        (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) j.1.1)) ∧
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
            (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) j.1.1)
            (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
              (monomial j.1.1 1 - monomial j.1.2 1 - Q j))) ∧
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
      Ideal.span (Set.range fun j : B ↦ monomial j.1.1 (1 : k) - monomial j.1.2 1) := by
    rw [hspan k, Set.image_eq_range]
    rfl
  have hB' (j : B) :
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) j.1.1 =
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) j.1.2 := by
    simpa [c] using hB j.1 j.2
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
      weightedHomogeneousComponent_eq_leadingTerm_of_monicNormalize hgw i, hgw i⟩,
    hinit,
    weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span hcw hgw hJ hQw hQc,
    ker_weightReesAeval_eq_span_rescale hcw hgw hJ hQw hQc,
    map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span rfl hcw hgw hJ hQw hQc⟩

end MonomialOrder
