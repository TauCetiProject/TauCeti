/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Initial.Degeneration
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Weight
import TauCeti.Data.Finsupp.Weight

/-!
# Flat weight presentations and nonmonic SAGBI degenerations

Give the variable `X s` of `MvPolynomial σ R` the weight `w s ∈ ℕ` and the presentation variable
`Y i` of `MvPolynomial ι R` the weight `d i ∈ ℕ`. Over any commutative semiring, when each `c i`
belongs to a subalgebra `A` and has ambient `w`-weight at most `d i`, the Rees presentation map
`weightReesAeval c d` (`Y i ↦ c i * t ^ d i`, `t ↦ t`) lifts to an `R[t]`-algebra homomorphism
`TauCeti.MvPolynomial.weightReesAevalLift` into the induced subalgebra Rees algebra
`A.weightReesAlgebra w`, with the same kernel `(RingHom.ker (aeval c)).weightReesIdeal d`
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

* `TauCeti.MvPolynomial.weightReesAevalLift` and
  `TauCeti.MvPolynomial.quotientSpanWeightHomogenizationEquiv`: the `R[t]`-algebra lift into and
  homogenized presentation of `A.weightReesAlgebra w`.
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

section ReesLift

variable {σ ι R : Type*} [CommSemiring R]

/-- The `R`-algebra lift of `weightReesAeval c d` into `A.weightReesAlgebra w` when each `c i`
lies in `A` and has weight at most `d i`. -/
private noncomputable def weightReesAevalLiftAux {A : Subalgebra R (MvPolynomial σ R)}
    {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) :
    (MvPolynomial ι R)[X] →ₐ[R] A.weightReesAlgebra w :=
  Polynomial.aevalTower
    (aeval fun i ↦ coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
      ((A.mem_weightFiltration_iff w).mpr (hc i)))
    (coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w))

private theorem coe_weightReesInclusion_weightReesAevalLiftAux
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (f : (MvPolynomial ι R)[X]) :
    (A.weightReesInclusion w (weightReesAevalLiftAux hcA hc f) : (MvPolynomial σ R)[X]) =
      weightReesAeval c d f := by
  have h : (weightReesAlgebra R w).val.comp
        ((A.weightReesInclusion w).comp (weightReesAevalLiftAux hcA hc)) =
      weightReesAeval c d := by
    refine Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun i ↦ ?_) ?_
    · simp [weightReesAevalLiftAux, Polynomial.C_mul_X_pow_eq_monomial]
    · simp [weightReesAevalLiftAux]
  exact congr($h f)

attribute [local instance] Polynomial.algebra in
/-- When each `c i` belongs to `A` and has ambient weight at most `d i`, the Rees presentation map
`weightReesAeval c d` lifts to an `R[t]`-algebra homomorphism from `(MvPolynomial ι R)[t]` into
`A.weightReesAlgebra w`. -/
noncomputable def weightReesAevalLift {A : Subalgebra R (MvPolynomial σ R)}
    {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (MvPolynomial ι R)[X] →ₐ[R[X]] A.weightReesAlgebra w :=
  letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  AlgHom.mk (weightReesAevalLiftAux hcA hc).toRingHom fun p ↦ by
    let := coeffSubalgebra.isScalarTower (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    let : IsScalarTower R R[X] (MvPolynomial ι R)[X] := IsScalarTower.of_algebraMap_eq fun r ↦ by
      simp [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    have h : (weightReesAevalLiftAux hcA hc).comp
          (IsScalarTower.toAlgHom R R[X] (MvPolynomial ι R)[X]) =
        IsScalarTower.toAlgHom R R[X] (A.weightReesAlgebra w) := by
      ext
      simp [weightReesAevalLiftAux]
    exact congr($h p)

attribute [local instance] Polynomial.algebra in
theorem coe_weightReesInclusion_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (A.weightReesInclusion w (weightReesAevalLift hcA hc f) : (MvPolynomial σ R)[X]) =
      weightReesAeval c d f :=
  coe_weightReesInclusion_weightReesAevalLiftAux hcA hc f

attribute [local instance] Polynomial.algebra in
@[simp]
theorem map_val_coe_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    ((weightReesAevalLift hcA hc f : A.weightReesAlgebra w) : A[X]).map A.val =
      weightReesAeval c d f :=
  (A.coe_weightReesInclusion w _).symm.trans (coe_weightReesInclusion_weightReesAevalLift hcA hc f)

attribute [local instance] Polynomial.algebra in
@[simp]
theorem weightReesAevalLift_C
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (p : MvPolynomial ι R) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc (Polynomial.C p) =
      aeval (fun i ↦ coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
        ((A.mem_weightFiltration_iff w).mpr (hc i))) p := by
  simp [weightReesAevalLift, weightReesAevalLiftAux]

attribute [local instance] Polynomial.algebra in
theorem weightReesAevalLift_C_X
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) (i : ι) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc (Polynomial.C (X i)) =
      coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
        ((A.mem_weightFiltration_iff w).mpr (hc i)) := by
  simp

attribute [local instance] Polynomial.algebra in
@[simp]
theorem weightReesAevalLift_X
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc Polynomial.X =
      coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w) := by
  simp [weightReesAevalLift, weightReesAevalLiftAux]

attribute [local instance] Polynomial.algebra in
/-- On a polynomial `P` of weight at most `n`, `weightReesAevalLift` sends the homogenization of
`P` in degree `n` to `aeval c P * tⁿ` in `A.weightReesAlgebra w`. -/
theorem weightReesAevalLift_weightHomogenization
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    {n : ℕ} {P : MvPolynomial ι R} (hP : P ∈ weightFiltration R d n) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc (weightHomogenization R d n P) =
      coeffSubalgebra.monomial (A.weightFiltration w) n
        ⟨aeval c P, Algebra.adjoin_le (Set.range_subset_iff.mpr hcA)
          (by rw [← aeval_range]; exact ⟨P, rfl⟩)⟩
        ((A.mem_weightFiltration_iff w).mpr (aeval_mem_weightFiltration hc hP)) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  apply A.weightReesInclusion_injective w
  apply Subtype.ext
  rw [coe_weightReesInclusion_weightReesAevalLift, weightReesAeval_weightHomogenization hP,
    A.weightReesInclusion_monomial, coeffSubalgebra.coe_monomial]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem weightReesSymbol_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    A.weightReesSymbol w (weightReesAevalLift hcA hc f) =
      aeval (fun i ↦ weightedHomogeneousComponent w (d i) (c i)) (f.coeff 0) := by
  have h : (A.weightReesSymbol w).comp (weightReesAevalLiftAux hcA hc) =
      (aeval fun i ↦ weightedHomogeneousComponent w (d i) (c i)).comp
        ((Polynomial.aeval (0 : MvPolynomial ι R)).restrictScalars R) := by
    refine Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun i ↦ ?_) ?_ <;>
      simp [weightReesAevalLiftAux]
  simpa [weightReesAevalLift, ← Polynomial.coeff_zero_eq_eval_zero] using congr($h f)

attribute [local instance] Polynomial.algebra in
@[simp]
theorem coe_eval_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (r : R) (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (coeffSubalgebra.eval (A.weightFiltration w) r (weightReesAevalLift hcA hc f) :
      MvPolynomial σ R) = (weightReesAeval c d f).eval (C r) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  rw [← A.eval_weightReesInclusion w r, coeffSubalgebra.eval_apply,
    coe_weightReesInclusion_weightReesAevalLift, MvPolynomial.algebraMap_eq]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem coe_evalOne_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    (coeffSubalgebra.evalOne (A.weightFiltration w) (weightReesAevalLift hcA hc f) :
      MvPolynomial σ R) = aeval c (f.eval 1) := by
  have h : A.val.comp ((coeffSubalgebra.evalOne (A.weightFiltration w)).comp
        (weightReesAevalLiftAux hcA hc)) =
      (aeval c).comp ((Polynomial.aeval (1 : MvPolynomial ι R)).restrictScalars R) := by
    refine Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun i ↦ ?_) ?_ <;>
      simp [weightReesAevalLiftAux]
  simpa [weightReesAevalLift] using congr($h f)

attribute [local instance] Polynomial.algebra in
/-- The kernel of `weightReesAevalLift hcA hc` equals the kernel of `weightReesAeval c d`. -/
theorem ker_weightReesAevalLift
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    RingHom.ker (weightReesAevalLift hcA hc) = RingHom.ker (weightReesAeval c d) := by
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  ext f
  simp only [RingHom.mem_ker, ← coe_weightReesInclusion_weightReesAevalLift hcA hc f]
  exact ⟨fun h ↦ by rw [h, map_zero, ZeroMemClass.coe_zero],
    fun h ↦ A.weightReesInclusion_injective w (Subtype.ext (by simpa using h))⟩

end ReesLift

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
    weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc, Ideal.map_span, hJ, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  rw [Function.comp_apply, Polynomial.constantCoeff_apply,
    coeff_zero_weightHomogenization_sub (hr j) (hQ j)]

/-- **Special fibre of the homogenized relation ideal.** Under bounded relation certificates,
setting `t = 0` in the ideal generated by the homogenized lifted relations recovers
`RingHom.ker (aeval g)`. -/
theorem map_constantCoeff_span_weightHomogenization
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j))).map
        Polynomial.constantCoeff =
      RingHom.ker (aeval (R := R) g) := by
  rw [← weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc,
    Ideal.map_constantCoeff_weightReesIdeal (RingHom.ker (aeval (R := R) c)) d,
    weightInitialIdeal_ker_aeval hc hg hJ hr hQ hQc]

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
  rwa [coe_weightReesInclusion_weightReesAevalLift]

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
  have h₁ : (weightReesAeval b d).comp
        (Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹)) =
      weightReesAeval (fun i ↦ m.monicNormalize (b i)) d := by
    rw [weightReesAeval_comp_mapAlgHom_rescale]
    congr 1
    funext i
    rw [Algebra.smul_def, algebraMap_eq, ← m.monicNormalize_def]
  apply le_antisymm
  · rw [← h₁]
    exact AlgHom.range_comp_le_range _ _
  · rw [← m.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale b d]
    exact AlgHom.range_comp_le_range _ _

variable {m}

/-- **Nonmonic Rees kernel transport.** For a family of nonzero polynomials `b`, the kernel of
`weightReesAeval b d` is the image of the Rees kernel of the monic normalization under the inverse
leading-coefficient rescaling `Y i ↦ (m.leadingCoeff (b i))⁻¹ * Y i`. -/
theorem ker_weightReesAeval_eq_map {b : ι → MvPolynomial σ k} (hb : ∀ i, b i ≠ 0) (d : ι → ℕ) :
    RingHom.ker (weightReesAeval b d) =
      (RingHom.ker (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d)).map
        (Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹)) := by
  let u : ι → kˣ := fun i ↦
    Units.mk0 (m.leadingCoeff (b i)) (m.leadingCoeff_ne_zero_iff.mpr (hb i))
  let e := Polynomial.mapAlgEquiv (rescaleEquiv u)
  have he : (e : (MvPolynomial ι k)[X] →ₐ[k] (MvPolynomial ι k)[X]) =
      Polynomial.mapAlgHom (rescale fun i ↦ m.leadingCoeff (b i)) := by
    simp [e, u]
  have he_symm : (e.symm : (MvPolynomial ι k)[X] →ₐ[k] (MvPolynomial ι k)[X]) =
      Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹) := by
    have hsymm : e.symm = Polynomial.mapAlgEquiv (rescaleEquiv u⁻¹) := by
      refine AlgEquiv.ext fun p ↦ e.injective ?_
      rw [e.apply_symm_apply]
      dsimp only [e]
      rw [← AlgEquiv.trans_apply, Polynomial.mapAlgEquiv_comp _ _, ← rescaleEquiv_symm,
        AlgEquiv.symm_trans_self, Polynomial.mapAlgEquiv_id, AlgEquiv.coe_refl, id_eq]
    simp [hsymm, u]
  have he' : (e.toRingEquiv : (MvPolynomial ι k)[X] →+* (MvPolynomial ι k)[X]) =
      Polynomial.mapAlgHom (rescale fun i ↦ m.leadingCoeff (b i)) :=
    RingHom.ext fun p ↦ DFunLike.congr_fun he p
  have he_symm' : (e.toRingEquiv.symm : (MvPolynomial ι k)[X] →+* (MvPolynomial ι k)[X]) =
      Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹) :=
    RingHom.ext fun p ↦ DFunLike.congr_fun he_symm p
  rw [← m.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale b d, ← AlgHom.comap_ker,
    ← Ideal.comap_coe, ← he', Ideal.comap_coe, ← Ideal.map_symm, ← Ideal.map_coe, he_symm',
    Ideal.map_coe]

private theorem ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq
    {b : ι → MvPolynomial σ k} {w : σ → ℕ}
    (ha : ∀ i, weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i)))
      (m.monicNormalize (b i)) = monomial (m.degree (b i)) 1) :
    ∀ i, b i ≠ 0 :=
  fun i h0 ↦ by simpa [h0] using (ha i).symm

/-- Transporting monic toric binomial certificates along `D_ℓ⁻¹` produces bounded weight
certificates directly for the unnormalized family `b` and its actual leading terms
`m.leadingTerm ∘ b`. -/
private theorem nonmonic_certificates {b : ι → MvPolynomial σ k} {w : σ → ℕ}
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
    let d := fun i ↦ Finsupp.weight w (m.degree (b i))
    let ℓinv := fun i ↦ (m.leadingCoeff (b i))⁻¹
    (∀ i, b i ∈ weightFiltration k w (d i)) ∧
      (∀ i, weightedHomogeneousComponent w (d i) (b i) = m.leadingTerm (b i)) ∧
      RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) =
        Ideal.span (Set.range fun j ↦ rescale ℓinv (monomial (u j) (1 : k) - monomial (v j) 1)) ∧
      (∀ j, (rescale ℓinv (monomial (u j) (1 : k) - monomial (v j) 1)).IsWeightedHomogeneous
        d (Finsupp.weight d (u j))) ∧
      (∀ j, rescale ℓinv (Q j) ∈ weightFiltrationLT k d (Finsupp.weight d (u j))) ∧
      ∀ j, aeval b (rescale ℓinv (Q j)) =
        aeval b (rescale ℓinv (monomial (u j) (1 : k) - monomial (v j) 1)) := by
  have hb := ne_zero_of_weightedHomogeneousComponent_monicNormalize_eq ha
  set d := fun i ↦ Finsupp.weight w (m.degree (b i))
  set ℓinv := fun i ↦ (m.leadingCoeff (b i))⁻¹
  refine ⟨fun i ↦ m.monicNormalize_mem_iff.mp (hc i), fun i ↦ ?_, ?_, fun j ↦ ?_,
    fun j ↦ rescale_mem_weightFiltrationLT (hQ j), fun j ↦ ?_⟩
  · nth_rw 1 [← m.C_leadingCoeff_mul_monicNormalize (b i)]
    rw [← smul_eq_C_mul, map_smul, ha i, smul_monomial, smul_eq_mul, mul_one, leadingTerm]
  · rw [m.ker_aeval_leadingTerm_eq_map hb, hJ, Ideal.map_span, ← Set.range_comp]
    rfl
  · have hbin := isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal (w := w)
      (hJ.symm ▸ Ideal.subset_span (Set.mem_range_self j))
    exact fun x hx ↦ hbin (mem_support_iff.mp (support_rescale_subset _ _ (mem_support_iff.mpr hx)))
  · have hscale (P : MvPolynomial ι k) :
        aeval b (rescale ℓinv P) = aeval (fun i ↦ m.monicNormalize (b i)) P := by
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
      RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) := by
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hc ha hJ hQ hQc
  exact weightInitialIdeal_ker_aeval hcb hgb hJb hrb hQb hQcb

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
      Algebra.adjoin k (Set.range fun i ↦ m.leadingTerm (b i)) := by
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hc ha hJ hQ hQc
  exact weightInitialAlgebra_adjoin_eq hcb hgb hJb hrb hQb hQcb

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
      (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range := by
  have hAc : A = Algebra.adjoin k (Set.range fun i ↦ m.monicNormalize (b i)) := by
    rw [hA, ← m.adjoin_image_monicNormalize (Set.range b), ← Set.range_comp]
    rfl
  have hker : RingHom.ker (aeval fun i ↦ monomial (m.degree (b i)) (1 : k)) =
      Ideal.span (Set.range fun j ↦ monomial (u j) (1 : k) - monomial (v j) 1) := by
    rw [← TauCeti.toricIdeal_eq_ker_aeval_monomial, hJ]
  have hbin (j : J) := isWeightedHomogeneous_monomial_sub_monomial_of_mem_toricIdeal (w := w)
    (hJ.symm ▸ Ideal.subset_span (Set.mem_range_self j))
  rw [← m.range_weightReesAeval_monicNormalize]
  exact A.map_weightReesAlgebra_eq_range_weightReesAeval w hAc hc ha hker hbin hQ hQc

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
    (quotientSpanWeightHomogenizationEquiv hA hcert.1 hcert.2.1 hcert.2.2.1 hcert.2.2.2.1
      hcert.2.2.2.2.1 hcert.2.2.2.2.2)

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
  obtain ⟨hcb, hgb, -, -, -, -⟩ := nonmonic_certificates hcw hgw hJ hQw hQc
  have hinit : (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
      m.initialAlgebra (Algebra.adjoin k (Set.range b)) := by
    rw [weightInitialAlgebra_adjoin_eq_of_toricIdeal_eq_span hcw hgw hJ hQw hQc,
      ← h.adjoin_leadingTerm, ← Set.range_comp]
    rfl
  exact ⟨B, Q, w, hw, hJ, hQc, hQ, hQw, fun i ↦ ⟨hcb i, hgb i, hgw i⟩, hinit,
    weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span hcw hgw hJ hQw hQc,
    ker_weightReesAeval_eq_span_rescale hcw hgw hJ hQw hQc,
    map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span rfl hcw hgw hJ hQw hQc⟩

end MonomialOrder
