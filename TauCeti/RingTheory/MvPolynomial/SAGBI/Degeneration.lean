/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Initial.Degeneration
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.Degeneration
import TauCeti.Data.Finsupp.Weight

/-!
# Flat weight presentations and nonmonic SAGBI degenerations

Give the variable `X s` of `MvPolynomial σ R` the weight `w s ∈ ℕ` and the presentation variable
`Y i` of `MvPolynomial ι R` the weight `d i ∈ ℕ`. Over any commutative semiring, the kernel of the
Rees presentation map `weightReesAeval c d` (`Y i ↦ c i * t ^ d i`, `t ↦ t`) coincides with the
weight Rees ideal `(RingHom.ker (aeval c)).weightReesIdeal d` of the presentation kernel
(`TauCeti.MvPolynomial.ker_weightReesAeval_eq_weightReesIdeal`). When each `c i` belongs to a
subalgebra `A` and has weight at most `d i`, `weightReesAeval c d` lifts to an `R[t]`-algebra
homomorphism `TauCeti.MvPolynomial.weightReesAevalLift` into the induced subalgebra Rees algebra
`A.weightReesAlgebra w`.

Combining this Rees-ideal identity with the bounded certificate presentation
`TauCeti.MvPolynomial.ker_weightReesAeval_eq_span` and the ideal degeneration results of
`TauCeti.RingTheory.MvPolynomial.Initial.Degeneration` yields, over any commutative ring `R`:

* **Weight-initial presentation ideal**: `(RingHom.ker (aeval c)).weightInitialIdeal d =
  RingHom.ker (aeval g)` (`TauCeti.MvPolynomial.weightInitialIdeal_ker_aeval`), and setting `t = 0`
  in the homogenized lifted relations recovers `RingHom.ker (aeval g)`.
* **General-fibre presentation ideal**: setting `t = 1` in the homogenized lifted relations recovers
  `RingHom.ker (aeval c) = Ideal.span (Set.range fun j ↦ r j - Q j)`
  (`TauCeti.MvPolynomial.ker_aeval_eq_span_sub`).
* **`R[t]`-algebra Rees presentation**: the quotient of `(MvPolynomial ι R)[t]` by the homogenized
  lifted relations is isomorphic as an `R[t]`-algebra to
  `(Algebra.adjoin R (Set.range c)).weightReesAlgebra w`
  (`TauCeti.MvPolynomial.quotientSpanWeightHomogenizationEquiv`), and over a field `k` this
  explicit quotient is flat over `k[t]`
  (`TauCeti.MvPolynomial.flat_quotient_span_weightHomogenization`).

For an unnormalized family `b : ι → MvPolynomial σ k` of nonzero polynomials over a field `k` with
leading coefficients `ℓ i = m.leadingCoeff (b i)` and monic normalizations
`c i = m.monicNormalize (b i)` for a monomial order `m`, the Rees presentation map of `b` factors
through that of `c` by the diagonal rescaling `D_ℓ = MvPolynomial.rescale ℓ` in the presentation
variables (`MonomialOrder.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale`). Consequently the
Rees relations of `b` are obtained from the monic toric homogenized relations by applying
`D_ℓ⁻¹ = MvPolynomial.rescale ℓ⁻¹` (`MonomialOrder.ker_weightReesAeval_eq_span_rescale`), retaining
the inverse leading-coefficient product `∏ i, (ℓ i)⁻¹ ^ x i` on every monomial `Y^x` while keeping
the generated subalgebra `Algebra.adjoin k (Set.range b)` and its induced Rees algebra unchanged.
Finally, `MonomialOrder.IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval` packages the complete
positive-weight degeneration for any finite family of nonzero SAGBI generators over a field, with
no monicity or finite-variable hypothesis.

## Main declarations

* `TauCeti.MvPolynomial.ker_weightReesAeval_eq_weightReesIdeal`: the kernel of `weightReesAeval c d`
  is `(RingHom.ker (aeval c)).weightReesIdeal d`.
* `TauCeti.MvPolynomial.weightReesAevalLift` and
  `TauCeti.MvPolynomial.quotientSpanWeightHomogenizationEquiv`: the `R[t]`-algebra presentation of
  `(Algebra.adjoin R (Set.range c)).weightReesAlgebra w`.
* `TauCeti.MvPolynomial.weightInitialIdeal_ker_aeval` and
  `TauCeti.MvPolynomial.ker_aeval_eq_span_sub`: the `t = 0` initial ideal and `t = 1` kernel.
* `MonomialOrder.ker_weightReesAeval_eq_map` and
  `MonomialOrder.ker_weightReesAeval_eq_span_rescale`: `D_ℓ⁻¹` transport of Rees relations for
  nonzero nonmonic families.
* `MonomialOrder.IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval`: existence of positive integral
  weights realizing the initial algebra, presentation initial ideal, `D_ℓ⁻¹`-transported Rees
  presentation, and induced subalgebra Rees algebra for any finite nonzero SAGBI basis.

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

section ReesIdeal

variable {σ ι R : Type*} [CommSemiring R]

/-- **Kernel of the Rees presentation as a weight Rees ideal.** Over any commutative semiring and
for any family `c` and generator weights `d`, the kernel of `weightReesAeval c d` is the weight
Rees ideal of the presentation kernel `RingHom.ker (aeval c)` for the weights `d`. -/
theorem ker_weightReesAeval_eq_weightReesIdeal (c : ι → MvPolynomial σ R) (d : ι → ℕ) :
    RingHom.ker (weightReesAeval c d) = (RingHom.ker (aeval (R := R) c)).weightReesIdeal d := by
  ext f
  rw [RingHom.mem_ker, weightReesAeval_eq_comp, AlgHom.comp_apply, Polynomial.coe_mapAlgHom,
    Ideal.mem_weightReesIdeal_iff]
  simp [AddMonoidAlgebra.ext_iff, DFunLike.ext_iff, RingHom.mem_ker]

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
  { __ := (weightReesAevalLiftAux hcA hc).toRingHom
    commutes' p := by
      apply A.weightReesInclusion_injective w
      apply Subtype.ext
      change (A.weightReesInclusion w
          (weightReesAevalLiftAux hcA hc (p.map (algebraMap R (MvPolynomial ι R)))) :
          (MvPolynomial σ R)[X]) = _
      rw [coe_weightReesInclusion_weightReesAevalLiftAux, weightReesAeval_eq_comp,
        AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Subalgebra.coe_weightReesInclusion,
        coeffSubalgebra.coe_algebraMap, Polynomial.map_map, MvPolynomial.algebraMap_eq,
        Polynomial.weightReesHom_map_C, Polynomial.map_map]
      congr 1
      ext r
      simp [MvPolynomial.algebraMap_eq] }

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
theorem weightReesAevalLift_C_X
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) (i : ι) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc (Polynomial.C (X i)) =
      coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
        ((A.mem_weightFiltration_iff w).mpr (hc i)) := by
  change weightReesAevalLiftAux hcA hc (Polynomial.C (X i)) = _
  simp [weightReesAevalLiftAux]

attribute [local instance] Polynomial.algebra in
@[simp]
theorem weightReesAevalLift_X
    {A : Subalgebra R (MvPolynomial σ R)} {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
    (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i)) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    weightReesAevalLift hcA hc Polynomial.X =
      coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w) := by
  change weightReesAevalLiftAux hcA hc Polynomial.X = _
  simp [weightReesAevalLiftAux]

attribute [local instance] Polynomial.algebra in
/-- Because `A.weightReesInclusion w` embeds `A.weightReesAlgebra w` injectively into the ambient
polynomial ring, the kernel of `weightReesAevalLift` equals the kernel of `weightReesAeval c d`. -/
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

end ReesIdeal

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

/-- **Special fibre of the homogenized relation ideal.** Setting `t = 0` in the ideal generated by
the homogenized lifted relations recovers `RingHom.ker (aeval g)`. -/
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

/-- **Presentation kernel from bounded weight certificates.** Setting `t = 1` in the Rees
presentation shows that the lifted relations `r j - Q j` generate `RingHom.ker (aeval c)`. -/
theorem ker_aeval_eq_span_sub
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    RingHom.ker (aeval (R := R) c) = Ideal.span (Set.range fun j ↦ r j - Q j) := by
  rw [← Ideal.map_evalRingHom_one_weightReesIdeal (RingHom.ker (aeval (R := R) c)) d,
    weightReesIdeal_ker_aeval_eq_span hc hg hJ hr hQ hQc, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  simp

/-- **General fibre of the homogenized relation ideal.** Setting `t = 1` in the ideal generated by
the homogenized lifted relations recovers `RingHom.ker (aeval c)`. -/
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

/-- Under bounded relation certificates, the weight-initial algebra of `Algebra.adjoin R (range c)`
is `Algebra.adjoin R (range g)`. -/
theorem weightInitialAlgebra_adjoin_eq
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (Algebra.adjoin R (Set.range c)).weightInitialAlgebra w = Algebra.adjoin R (Set.range g) := by
  rw [Subalgebra.weightInitialAlgebra_def]
  exact adjoin_weightInitialForm_eq hc hg hJ hr hQ hQc

attribute [local instance] Polynomial.algebra in
/-- Under bounded relation certificates, `weightReesAevalLift` surjects onto the induced weight
Rees algebra of `Algebra.adjoin R (Set.range c)`. -/
theorem weightReesAevalLift_surjective
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    letI := coeffSubalgebra.algebra
      ((Algebra.adjoin R (Set.range c)).weightFiltration w)
      ((Algebra.adjoin R (Set.range c)).one_mem_weightFiltration_one w)
    Function.Surjective
      (weightReesAevalLift (fun i ↦ Algebra.subset_adjoin (Set.mem_range_self i)) hc) := by
  let A := Algebra.adjoin R (Set.range c)
  let := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
  intro y
  have hy : ((A.weightReesInclusion w y : weightReesAlgebra R w) : (MvPolynomial σ R)[X]) ∈
      (weightReesAeval c d).range := by
    rw [← A.map_weightReesAlgebra_eq_range_weightReesAeval w rfl hc hg hJ hr hQ hQc]
    exact ⟨y, y.2, (A.coe_weightReesInclusion w y).symm⟩
  obtain ⟨f, hf⟩ := (weightReesAeval c d).mem_range.mp hy
  refine ⟨f, A.weightReesInclusion_injective w (Subtype.ext ?_)⟩
  rwa [coe_weightReesInclusion_weightReesAevalLift]

attribute [local instance] Polynomial.algebra in
/-- **`R[t]`-algebra Rees presentation.** Under bounded relation certificates, the quotient of
`(MvPolynomial ι R)[t]` by the homogenized lifted relations is isomorphic as an `R[t]`-algebra to
the induced weight Rees algebra `(Algebra.adjoin R (Set.range c)).weightReesAlgebra w`. -/
noncomputable def quotientSpanWeightHomogenizationEquiv
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    letI := coeffSubalgebra.algebra
      ((Algebra.adjoin R (Set.range c)).weightFiltration w)
      ((Algebra.adjoin R (Set.range c)).one_mem_weightFiltration_one w)
    ((MvPolynomial ι R)[X] ⧸
      Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j))) ≃ₐ[R[X]]
      (Algebra.adjoin R (Set.range c)).weightReesAlgebra w :=
  letI := coeffSubalgebra.algebra
    ((Algebra.adjoin R (Set.range c)).weightFiltration w)
    ((Algebra.adjoin R (Set.range c)).one_mem_weightFiltration_one w)
  have hker : RingHom.ker
        (weightReesAevalLift (fun i ↦ Algebra.subset_adjoin (Set.mem_range_self i)) hc) =
      Ideal.span (Set.range fun j ↦ weightHomogenization R d (e j) (r j - Q j)) :=
    (ker_weightReesAevalLift _ hc).trans (ker_weightReesAeval_eq_span hc hg hJ hr hQ hQc)
  (Ideal.quotientEquivAlgOfEq R[X] hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (weightReesAevalLift_surjective hc hg hJ hr hQ hQc))

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationEquiv_mk
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    (f : (MvPolynomial ι R)[X]) :
    letI := coeffSubalgebra.algebra
      ((Algebra.adjoin R (Set.range c)).weightFiltration w)
      ((Algebra.adjoin R (Set.range c)).one_mem_weightFiltration_one w)
    quotientSpanWeightHomogenizationEquiv hc hg hJ hr hQ hQc (Ideal.Quotient.mk _ f) =
      weightReesAevalLift (fun i ↦ Algebra.subset_adjoin (Set.mem_range_self i)) hc f := by
  simp [quotientSpanWeightHomogenizationEquiv]

attribute [local instance] Polynomial.algebra in
/-- **Flatness of the explicit homogenized presentation over a field.** Over a field `k`, the
quotient of `(MvPolynomial ι k)[t]` by the homogenized lifted relations is flat over `k[t]`. -/
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

section NonzeroFamily

variable {m} {b : ι → MvPolynomial σ k} (hb : ∀ i, b i ≠ 0)
include hb

private theorem mapAlgHom_rescale_inv_leadingCoeff (f : (MvPolynomial ι k)[X]) :
    (Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹))
      ((Polynomial.mapAlgHom (rescale fun i ↦ m.leadingCoeff (b i))) f) = f := by
  have hid :
      ((rescale fun i ↦ (m.leadingCoeff (b i))⁻¹ : MvPolynomial ι k →+* MvPolynomial ι k).comp
        (rescale fun i ↦ m.leadingCoeff (b i) : MvPolynomial ι k →+* MvPolynomial ι k)) =
      RingHom.id _ :=
    RingHom.ext fun p ↦ rescale_rescale_of_mul_eq_one
      (fun i ↦ mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (hb i))) p
  rw [Polynomial.coe_mapAlgHom, Polynomial.coe_mapAlgHom, Polynomial.map_map, hid,
    Polynomial.map_id]

private theorem mapAlgHom_rescale_leadingCoeff_inv (f : (MvPolynomial ι k)[X]) :
    (Polynomial.mapAlgHom (rescale fun i ↦ m.leadingCoeff (b i)))
      ((Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹)) f) = f := by
  have hid :
      ((rescale fun i ↦ m.leadingCoeff (b i) : MvPolynomial ι k →+* MvPolynomial ι k).comp
        (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹ : MvPolynomial ι k →+* MvPolynomial ι k)) =
      RingHom.id _ :=
    RingHom.ext fun p ↦ rescale_rescale_of_mul_eq_one
      (fun i ↦ inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (hb i))) p
  rw [Polynomial.coe_mapAlgHom, Polynomial.coe_mapAlgHom, Polynomial.map_map, hid,
    Polynomial.map_id]

/-- For a family of nonzero polynomials over a field, normalizing the generators does not change
the image of the Rees presentation map. -/
theorem range_weightReesAeval_monicNormalize (d : ι → ℕ) :
    (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d).range = (weightReesAeval b d).range := by
  rw [← m.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale b d]
  ext g
  simp only [AlgHom.mem_range, AlgHom.comp_apply]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨_, (congrArg _ (mapAlgHom_rescale_leadingCoeff_inv hb f)).trans hf⟩,
    fun ⟨q, hq⟩ ↦ ⟨_, hq⟩⟩

/-- **Nonmonic Rees kernel transport.** For a family of nonzero polynomials `b`, the kernel of
`weightReesAeval b d` is the image of the Rees kernel of the monic normalization under the inverse
leading-coefficient rescaling `Y i ↦ (m.leadingCoeff (b i))⁻¹ * Y i`. -/
theorem ker_weightReesAeval_eq_map (d : ι → ℕ) :
    RingHom.ker (weightReesAeval b d) =
      (RingHom.ker (weightReesAeval (fun i ↦ m.monicNormalize (b i)) d)).map
        (Polynomial.mapAlgHom (rescale fun i ↦ (m.leadingCoeff (b i))⁻¹)) := by
  rw [← m.weightReesAeval_monicNormalize_comp_mapAlgHom_rescale b d, ← AlgHom.comap_ker]
  exact le_antisymm (Ideal.comap_le_map_of_inverse _ _ _ (mapAlgHom_rescale_inv_leadingCoeff hb))
    (Ideal.map_le_comap_of_inverse _ _ _ (mapAlgHom_rescale_leadingCoeff_inv hb))

/-- Transporting monic toric binomial certificates along `D_ℓ⁻¹` produces bounded weight
certificates directly for the unnormalized nonzero family `b` and its actual leading terms
`m.leadingTerm ∘ b`. -/
private theorem nonmonic_certificates {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
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
  set d := fun i ↦ Finsupp.weight w (m.degree (b i))
  set ℓinv := fun i ↦ (m.leadingCoeff (b i))⁻¹
  refine ⟨fun i ↦ m.monicNormalize_mem_iff.mp (hc i), fun i ↦ ?_, ?_, fun j ↦ ?_,
    fun j ↦ rescale_mem_weightFiltrationLT (hQ j), fun j ↦ ?_⟩
  · nth_rw 1 [← m.C_leadingCoeff_mul_monicNormalize (b i)]
    rw [← smul_eq_C_mul, map_smul, ha i, smul_monomial, smul_eq_mul, mul_one, leadingTerm]
  · rw [m.ker_aeval_leadingTerm_eq_map hb, hJ, Ideal.map_span, ← Set.range_comp]
    rfl
  · have huv : Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) (u j) =
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) (v j) :=
      TauCeti.monomial_sub_monomial_mem_toricIdeal_iff.mp
        (by rw [hJ]; exact Ideal.subset_span ⟨j, rfl⟩)
    have hw (x : ι →₀ ℕ) : Finsupp.weight d x =
        Finsupp.weight w (Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) x) :=
      Finsupp.weight_comp_eq_apply_linearCombination (Finsupp.weight w) _ x
    have hbin : (monomial (u j) (1 : k) - monomial (v j) 1).IsWeightedHomogeneous
        d (Finsupp.weight d (u j)) :=
      (isWeightedHomogeneous_monomial _ _ _ rfl).sub
        (isWeightedHomogeneous_monomial _ _ _ (by rw [hw, hw, huv]))
    exact fun x hx ↦ hbin (mem_support_iff.mp (support_rescale_subset _ _ (mem_support_iff.mpr hx)))
  · have hscale (P : MvPolynomial ι k) :
        aeval b (rescale ℓinv P) = aeval (fun i ↦ m.monicNormalize (b i)) P := by
      rw [← m.aeval_monicNormalize_comp_rescale b, AlgHom.comp_apply,
        rescale_rescale_of_mul_eq_one
          (fun i ↦ inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr (hb i)))]
    rw [hscale, hscale, hQc]

/-- **Nonmonic Rees presentation via `D_ℓ⁻¹` transport.** For a family of nonzero polynomials `b`,
if toric binomials `Y^(u j) - Y^(v j)` and monic subduction certificates `Q j` satisfy the weight
hypotheses for the normalized family `m.monicNormalize ∘ b`, then the kernel of `weightReesAeval b`
is generated by the homogenizations of the `D_ℓ⁻¹`-rescaled relations
`rescale ℓ⁻¹ (Y^(u j) - Y^(v j) - Q j)`, retaining `∏ i, (ℓ i)⁻¹ ^ x i` on every monomial `Y^x`. -/
theorem ker_weightReesAeval_eq_span_rescale {w : σ → ℕ} {u v : J → ι →₀ ℕ}
    {Q : J → MvPolynomial ι k}
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
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hb hc ha hJ hQ hQc
  simpa only [map_sub] using ker_weightReesAeval_eq_span hcb hgb hJb hrb hQb hQcb

/-- **Weight-initial presentation ideal for nonzero nonmonic generators.** Under monic toric weight
certificates, the `d`-weight-initial ideal of `RingHom.ker (aeval b)` is the presentation kernel of
the actual leading terms `m.leadingTerm ∘ b`. -/
theorem weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span {w : σ → ℕ} {u v : J → ι →₀ ℕ}
    {Q : J → MvPolynomial ι k}
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
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hb hc ha hJ hQ hQc
  exact weightInitialIdeal_ker_aeval hcb hgb hJb hrb hQb hQcb

/-- Under monic toric weight certificates for a nonzero family `b`, the image of `weightReesAeval b`
is the embedded induced weight Rees algebra of `Algebra.adjoin k (Set.range b)`, without changing
the subalgebra `Algebra.adjoin k (Set.range b)`. -/
theorem map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span
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
    ((Algebra.adjoin k (Set.range b)).weightReesAlgebra w).map
        (Polynomial.mapAlgHom (Algebra.adjoin k (Set.range b)).val) =
      (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range := by
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hb hc ha hJ hQ hQc
  exact (Algebra.adjoin k (Set.range b)).map_weightReesAlgebra_eq_range_weightReesAeval w rfl
    hcb hgb hJb hrb hQb hQcb

attribute [local instance] Polynomial.algebra in
/-- **`k[t]`-algebra Rees presentation for nonzero nonmonic generators.** Quotienting
`(MvPolynomial ι k)[t]` by the `D_ℓ⁻¹`-transported homogenized relations presents the induced
weight Rees algebra of `Algebra.adjoin k (Set.range b)`. -/
noncomputable def quotientSpanWeightHomogenizationRescaleEquiv
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
    letI := coeffSubalgebra.algebra
      ((Algebra.adjoin k (Set.range b)).weightFiltration w)
      ((Algebra.adjoin k (Set.range b)).one_mem_weightFiltration_one w)
    ((MvPolynomial ι k)[X] ⧸
      Ideal.span (Set.range fun j ↦
        weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
          (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) (u j))
          (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
            (monomial (u j) 1 - monomial (v j) 1 - Q j)))) ≃ₐ[k[X]]
      (Algebra.adjoin k (Set.range b)).weightReesAlgebra w :=
  letI := coeffSubalgebra.algebra
    ((Algebra.adjoin k (Set.range b)).weightFiltration w)
    ((Algebra.adjoin k (Set.range b)).one_mem_weightFiltration_one w)
  have hcert := nonmonic_certificates hb hc ha hJ hQ hQc
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
    (quotientSpanWeightHomogenizationEquiv hcert.1 hcert.2.1 hcert.2.2.1 hcert.2.2.2.1
      hcert.2.2.2.2.1 hcert.2.2.2.2.2)

attribute [local instance] Polynomial.algebra in
@[simp]
theorem quotientSpanWeightHomogenizationRescaleEquiv_mk
    {w : σ → ℕ} {u v : J → ι →₀ ℕ} {Q : J → MvPolynomial ι k}
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
    letI := coeffSubalgebra.algebra
      ((Algebra.adjoin k (Set.range b)).weightFiltration w)
      ((Algebra.adjoin k (Set.range b)).one_mem_weightFiltration_one w)
    quotientSpanWeightHomogenizationRescaleEquiv hb hc ha hJ hQ hQc (Ideal.Quotient.mk _ f) =
      weightReesAevalLift (fun i ↦ Algebra.subset_adjoin (Set.mem_range_self i))
        (fun i ↦ m.monicNormalize_mem_iff.mp (hc i)) f := by
  simp [quotientSpanWeightHomogenizationRescaleEquiv]

/-- **Positive-weight degeneration of a finite nonzero SAGBI basis.** Let `b : ι → MvPolynomial σ k`
be a finite family of nonzero polynomials over a field `k` forming a SAGBI basis of
`A = Algebra.adjoin k (Set.range b)` (not assumed monic, and with no finiteness assumption on `σ`).
Then there exist a finite set `B` of toric binomial exponent pairs, monic subduction certificates
`Q : B → MvPolynomial ι k`, and strictly positive integral weights `w : σ → ℕ` such that, for the
generator weights `d i = Finsupp.weight w (m.degree (b i))`:
1. each `b i` has weight at most `d i` with top component `m.leadingTerm (b i)`;
2. `A.weightInitialAlgebra w = m.initialAlgebra A`;
3. `(RingHom.ker (aeval b)).weightInitialIdeal d = RingHom.ker (aeval (m.leadingTerm ∘ b))`;
4. `RingHom.ker (weightReesAeval b d)` is generated by the homogenizations of the `D_ℓ⁻¹`-rescaled
   lifted toric relations; and
5. `(weightReesAeval b d).range` is the embedded weight Rees algebra `A.weightReesAlgebra w`. -/
theorem IsSAGBIBasis.exists_pos_weight_ker_weightReesAeval [Finite ι]
    (h : m.IsSAGBIBasis (Set.range b) (Algebra.adjoin k (Set.range b))) :
    ∃ (B : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) (Q : B → MvPolynomial ι k) (w : σ → ℕ),
      (∀ s, 0 < w s) ∧
      (∀ i, b i ∈ weightFiltration k w (Finsupp.weight w (m.degree (b i))) ∧
        weightedHomogeneousComponent w (Finsupp.weight w (m.degree (b i))) (b i) =
          m.leadingTerm (b i)) ∧
      (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
        m.initialAlgebra (Algebra.adjoin k (Set.range b)) ∧
      (RingHom.ker (aeval (R := k) b)).weightInitialIdeal
          (fun i ↦ Finsupp.weight w (m.degree (b i))) =
        RingHom.ker (aeval (R := k) fun i ↦ m.leadingTerm (b i)) ∧
      RingHom.ker (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))) =
        Ideal.span (Set.range fun j : B ↦
          weightHomogenization k (fun i ↦ Finsupp.weight w (m.degree (b i)))
            (Finsupp.weight (fun i ↦ Finsupp.weight w (m.degree (b i))) j.1.1)
            (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
              (monomial j.1.1 1 - monomial j.1.2 1 - Q j))) ∧
      ((Algebra.adjoin k (Set.range b)).weightReesAlgebra w).map
          (Polynomial.mapAlgHom (Algebra.adjoin k (Set.range b)).val) =
        (weightReesAeval b fun i ↦ Finsupp.weight w (m.degree (b i))).range := by
  classical
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
  simp only [c, m.degree_monicNormalize] at hcw hgw hQw
  obtain ⟨hcb, hgb, hJb, hrb, hQb, hQcb⟩ := nonmonic_certificates hb hcw hgw hJ hQw hQc
  have hinit : (Algebra.adjoin k (Set.range b)).weightInitialAlgebra w =
      m.initialAlgebra (Algebra.adjoin k (Set.range b)) := by
    rw [weightInitialAlgebra_adjoin_eq hcb hgb hJb hrb hQb hQcb, ← h.adjoin_leadingTerm,
      ← Set.range_comp]
    rfl
  exact ⟨B, Q, w, hw, fun i ↦ ⟨hcb i, hgb i⟩, hinit,
    weightInitialIdeal_ker_aeval_of_toricIdeal_eq_span hb hcw hgw hJ hQw hQc,
    ker_weightReesAeval_eq_span_rescale hb hcw hgw hJ hQw hQc,
    map_weightReesAlgebra_eq_range_weightReesAeval_of_toricIdeal_eq_span hb hcw hgw hJ hQw hQc⟩

end NonzeroFamily

end MonomialOrder
