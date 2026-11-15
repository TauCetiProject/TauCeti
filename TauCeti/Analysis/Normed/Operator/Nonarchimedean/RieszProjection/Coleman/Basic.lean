/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.Algebra.Polynomial.DivX
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# Riesz–Coleman projections: algebraic splitting, functoriality, and retracts

Let `R` be a normed commutative ring with Tate scalars and `M` a seminormed `R`-module with a
bounded scalar action. Over a coefficient ring that is not an algebraically closed field, a
coprime polynomial factor `Q ∈ R[X]` of a Fredholm series need not split into linear factors, so
single-point Riesz projectors cannot isolate individual roots of `Q`; instead one isolates the
entire factor `Q` at once via its reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u : M →L[R] M` for `Q`
(`ContinuousLinearMap.IsRieszColemanProjection`) is an idempotent `E`, commuting with `u` and
lying in the operator-norm closure of `R[u]`, such that `Q*(u) * E = 0` and `Q*(u)` is invertible
on the complementary summand `ker E = range (1 - E)`, with inverse again in the operator-norm
closure of `R[u]`. Without any compactness or model-space assumption:

* `E` decomposes `M` into topological complements `range E = ker Q*(u)` and `ker E = range Q*(u)`
  (`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`);
* `Q*(u)` restricts to a continuous linear automorphism of `ker E`
  (`ContinuousLinearMap.IsRieszColemanProjection.equivKer`), and when `Q.leadingCoeff` is a unit,
  `u` restricts to a continuous linear automorphism of `range E`
  (`ContinuousLinearMap.IsRieszColemanProjection.equivRange`);
* a Riesz–Coleman projection for a given `(u, Q)` is unique
  (`ContinuousLinearMap.IsRieszColemanProjection.unique`);
* linear intertwiners (not necessarily continuous) intertwine Riesz–Coleman projections and their
  complementary inverses (`ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.semiconj_inverse`);
* Riesz–Coleman projections compress along continuous linear retracts
  (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the finite spectral projector of `u` attached to
  a polynomial `Q`, cutting out `ker Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on `ker E`,
  extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`,
  `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: the induced continuous linear
  automorphisms `Q*(u)|_{ker E}` and `u|_{range E}`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

section Module

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` for a
polynomial `Q : R[X]`: an idempotent `E` commuting with `u` and lying in the operator-norm closure
of the polynomials in `u`, such that `Q*(u) * E = 0` for the reversal `Q* = Q.reverse` and `Q*(u)`
is invertible on the complementary summand `range (1 - E)`, with inverse again in the closure of
the polynomials in `u`. When `H_u = Q · S` is a coprime factorisation of the Fredholm series of a
row-compact `u` with `Q(0) = 1` and `IsUnit Q.leadingCoeff`, `E` is the unique spectral projector
onto `ker Q*(u)` splitting off the factor `Q`. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop where
  /-- A Riesz–Coleman projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz–Coleman projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz–Coleman projection is an operator-norm limit of polynomials in the operator. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- `Q*(u)` vanishes on the range of a Riesz–Coleman projection. -/
  aeval_reverse_mul_eq_zero : Polynomial.aeval u Q.reverse * E = 0
  /-- `Q*(u)` is invertible on the complementary summand, with inverse an operator-norm limit of
  polynomials in the operator. -/
  exists_inverse : ∃ w : M →L[R] M,
    Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- A Riesz–Coleman projection for the polynomial `1` is zero. -/
theorem eq_zero_of_eq_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  have h1 : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C]
  simpa only [h1, map_one, one_mul] using hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E := by
  rw [Commute, SemiconjBy, mul_def, mul_def]
  apply ContinuousLinearMap.coe_injective
  simpa only [toLinearMap_comp, toLinearMap_aeval] using
    Module.End.aeval_comp_of_comp_eq (f := E.toLinearMap) (g := u.toLinearMap)
      (g₂ := u.toLinearMap) (congrArg ContinuousLinearMap.toLinearMap hE.commute.eq) Q.reverse

/-- The operator preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using congr($(hE.commute.eq.symm) x)

/-- The operator preserves the range of its Riesz–Coleman projection. -/
theorem mapsTo_range (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE.commute.eq.symm) x)

/-- The polynomial operator `Q*(u)` preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo (Polynomial.aeval u Q.reverse) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($(hE.commute_aeval_reverse.eq.symm) x)

/-- The polynomial operator `Q*(u)` preserves the range of its Riesz–Coleman projection. -/
theorem mapsTo_range_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo (Polynomial.aeval u Q.reverse) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE.commute_aeval_reverse.eq.symm) x)

/-- The **complementary inverse** of a Riesz–Coleman projection: the inverse of `Q*(u)` on the
complementary summand `range (1 - E)`, extended by zero on `range E`, chosen from
`IsRieszColemanProjection.exists_inverse`. -/
noncomputable def inverse (hE : IsRieszColemanProjection u Q E) : M →L[R] M :=
  hE.exists_inverse.choose

/-- The complementary inverse is a right inverse of `Q*(u)` up to `1 - E`. -/
theorem aeval_reverse_mul_inverse (hE : IsRieszColemanProjection u Q E) :
    Polynomial.aeval u Q.reverse * hE.inverse = 1 - E :=
  hE.exists_inverse.choose_spec.1

/-- The complementary inverse is a left inverse of `Q*(u)` up to `1 - E`. -/
theorem inverse_mul_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    hE.inverse * Polynomial.aeval u Q.reverse = 1 - E :=
  hE.exists_inverse.choose_spec.2.1

/-- The complementary inverse takes values in the kernel of the Riesz–Coleman projection. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsRieszColemanProjection u Q E) : E * hE.inverse = 0 :=
  hE.exists_inverse.choose_spec.2.2.1

/-- The complementary inverse vanishes on the range of the Riesz–Coleman projection. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) : hE.inverse * E = 0 :=
  hE.exists_inverse.choose_spec.2.2.2.1

/-- The complementary inverse is an operator-norm limit of polynomials in the operator. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) :=
  hE.exists_inverse.choose_spec.2.2.2.2

/-- The complementary inverse is the unique right inverse of `Q*(u)` up to `1 - E` taking values
in the kernel of the Riesz–Coleman projection. -/
theorem eq_inverse (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Polynomial.aeval u Q.reverse * w = 1 - E) (hEw : E * w = 0) : w = hE.inverse := by
  calc w = (1 - E) * w := by
        rw [sub_mul (α := M →L[R] M), one_mul, hEw, sub_zero w]
    _ = hE.inverse * (Polynomial.aeval u Q.reverse * w) := by
        rw [← mul_assoc, hE.inverse_mul_aeval_reverse]
    _ = hE.inverse := by
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero, sub_zero hE.inverse]

/-- The complementary inverse preserves the kernel of the Riesz–Coleman projection. -/
theorem mapsTo_ker_inverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using congr($(hE.mul_inverse_eq_zero) x)

/-- On the complementary summand, the complementary inverse is a left inverse of `Q*(u)`. -/
theorem inverse_aeval_reverse_apply (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    hE.inverse (Polynomial.aeval u Q.reverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_aeval_reverse) x)

/-- On the complementary summand, the complementary inverse is a right inverse of `Q*(u)`. -/
theorem aeval_reverse_apply_inverse (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    Polynomial.aeval u Q.reverse (hE.inverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.aeval_reverse_mul_inverse) x)

/-- **The range of a Riesz–Coleman projection is the kernel of `Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm

/-- **The range of `Q*(u)` is the kernel of its Riesz–Coleman projection.** -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  have hzero : E * Polynomial.aeval u Q.reverse = 0 :=
    hE.commute_aeval_reverse.eq.symm.trans hE.aeval_reverse_mul_eq_zero
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨hE.inverse x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($hzero y)
  · simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, sub_zero] using
      congr($(hE.aeval_reverse_mul_inverse) x)

/-- The kernel and range of `Q*(u)` are topological complements. -/
theorem isTopCompl_ker_range (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The range of `Q*(u)` is closed whenever `M` has closed points. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) :
      Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- The polynomial operator `Q*(u)` as a continuous linear automorphism of the complementary
summand `ker E = range Q*(u)`, with inverse the restriction of
`IsRieszColemanProjection.inverse`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval_reverse hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))
    (fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))

/-- The complementary automorphism acts by `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x :=
  (rfl)

/-- The inverse complementary automorphism acts by `IsRieszColemanProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- **Invertibility of the operator on the finite spectral summand.** When `Q.leadingCoeff` is a
unit (the constant term of `Q*`), `Q*(u) E = 0` expresses `E` as `u` times a polynomial in `u` on
either side, so `u` restricts to a continuous linear automorphism of `range E`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  let invOp : M →L[R] M := (-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u (divX Q.reverse)
  have hmaps : Set.MapsTo invOp E.range E.range := by
    rintro _ ⟨y, rfl⟩
    have hcomm : Commute invOp E := by
      rw [Commute, SemiconjBy, mul_def, mul_def]
      apply ContinuousLinearMap.coe_injective
      simpa only [invOp, toLinearMap_comp, toLinearMap_smul, toLinearMap_aeval,
        LinearMap.smul_comp, LinearMap.comp_smul] using
        congrArg ((-Ring.inverse Q.leadingCoeff) • ·)
          (Module.End.aeval_comp_of_comp_eq (f := E.toLinearMap) (g := u.toLinearMap)
            (g₂ := u.toLinearMap) (congrArg ContinuousLinearMap.toLinearMap hE.commute.eq)
            (divX Q.reverse))
    exact ⟨invOp y, congr($(hcomm.eq.symm) y)⟩
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hzero (x : E.range) : Polynomial.aeval u Q.reverse x = 0 := by
    simpa [hfix x] using congr($(hE.aeval_reverse_mul_eq_zero) (x : M))
  refine ContinuousLinearEquiv.equivOfInverse
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx))
    (invOp.restrict (fun _ hx ↦ hmaps hx))
    (fun x ↦ Subtype.ext ?_) (fun x ↦ Subtype.ext ?_)
  · have h := congrArg (fun p ↦ Ring.inverse Q.leadingCoeff • (Polynomial.aeval u p (x : M)))
      (divX_mul_X_add Q.reverse)
    simp only [map_add, map_mul, aeval_X, aeval_C, coeff_zero_reverse, add_apply,
      mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hzero x,
      smul_zero, smul_add, smul_smul, Ring.inverse_mul_cancel _ hQ, one_smul] at h
    simpa [invOp, neg_smul] using neg_eq_iff_add_eq_zero.mpr h
  · have h := congrArg (fun p ↦ Ring.inverse Q.leadingCoeff • (Polynomial.aeval u p (x : M)))
      (X_mul_divX_add Q.reverse)
    simp only [map_add, map_mul, aeval_X, aeval_C, coeff_zero_reverse, add_apply,
      mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hzero x,
      smul_zero, smul_add, smul_smul, Ring.inverse_mul_cancel _ hQ, one_smul] at h
    simpa [invOp, neg_smul] using neg_eq_iff_add_eq_zero.mpr h

/-- The automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- When `Q.leadingCoeff` is a unit, the Riesz–Coleman projection factors through `u` via the
identity `Q* = X · divX Q* + Q.leadingCoeff`. -/
theorem eq_neg_inverse_smul_mul_aeval_divX (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    E = (-Ring.inverse Q.leadingCoeff) • (u * (Polynomial.aeval u (divX Q.reverse) * E)) := by
  ext x
  have h := congrArg (fun p ↦ Ring.inverse Q.leadingCoeff • (Polynomial.aeval u p (E x)))
    (X_mul_divX_add Q.reverse)
  have hzero : Polynomial.aeval u Q.reverse (E x) = 0 := congr($(hE.aeval_reverse_mul_eq_zero) x)
  simp only [map_add, map_mul, aeval_X, aeval_C, coeff_zero_reverse, add_apply, mul_apply_eq_comp,
    Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hzero, smul_zero, smul_add,
    smul_smul, Ring.inverse_mul_cancel _ hQ, one_smul] at h
  simpa only [mul_apply_eq_comp, smul_apply, neg_smul, neg_apply] using
    (neg_eq_iff_add_eq_zero.mpr h).symm

/-- When `Q.leadingCoeff` is a unit, the restriction of `u` to `range E` is an invertible linear
endomorphism. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit ((u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap : Module.End R E.range) := by
  let : AddCommGroup E.range := inferInstance
  exact isUnit_iff_exists.mpr ⟨(hE.equivRange hQ).symm.toLinearMap,
    LinearMap.ext fun x ↦ (hE.equivRange hQ).right_inv x,
    LinearMap.ext fun x ↦ (hE.equivRange hQ).left_inv x⟩

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` for the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero (h := 1) hE'.isIdempotentElem
    (by simpa using hE.aeval_reverse_mul_eq_zero) (by simpa using hE'.aeval_reverse_mul_eq_zero)
    hw hw' hw₂ hw₂'

end IsRieszColemanProjection

end Module

section Intertwining

variable {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : R[X]}

omit [TauCeti.NormedRing.IsTate R] in
/-- A linear map intertwining `u` and `v` intertwines `P(u)` and `P(v)` for every polynomial `P`. -/
private theorem semiconj_aeval (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) (P : R[X]) :
    Function.Semiconj f (Polynomial.aeval u P) (Polynomial.aeval v P) := fun x ↦ by
  have h : v.toLinearMap.comp f = f.comp u.toLinearMap := LinearMap.ext fun y ↦ (hf y).symm
  simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using
    (LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq h P) x).symm

namespace IsRieszColemanProjection

/-- **Functoriality of Riesz–Coleman projections.** A linear map (not necessarily continuous)
intertwining two operators also intertwines their Riesz–Coleman projections for the same
polynomial. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) : Function.Semiconj f E F := by
  have hQ := semiconj_aeval f hf Q.reverse
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hQ]
    have hz := congr($(hE.aeval_reverse_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      apply LinearMap.mem_ker.mpr
      have hid := congr($(hE.isIdempotentElem.eq) x)
      simpa only [coe_coe, map_sub, mul_apply_eq_comp, sub_eq_zero] using hid.symm
    rw [← hE.range_aeval_reverse_eq_ker] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [coe_coe] at hy
    apply LinearMap.mem_ker.mp
    rw [← hF.range_aeval_reverse_eq_ker]
    exact ⟨f y, (hQ y).symm.trans (congrArg f hy)⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the finite spectral summand into the corresponding summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner sends the complementary spectral summand into the corresponding summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners also intertwine the complementary inverses of `Q*(u)` and `Q*(v)`. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hQ := semiconj_aeval f hf Q.reverse
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse (Polynomial.aeval v Q.reverse (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f (Polynomial.aeval u Q.reverse (hE.inverse x))) := by rw [hQ]
    _ = hF.inverse (f (x - E x)) :=
        congrArg (fun y ↦ hF.inverse (f y)) congr($(hE.aeval_reverse_mul_inverse) x)
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E)
    {w : M →L[R] M} (hw : Commute w u) : Commute w E :=
  ContinuousLinearMap.ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E)
    {w : M →L[R] M} (hw : Commute w u) : Commute w hE.inverse :=
  ContinuousLinearMap.ext fun x ↦
    hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end IsRieszColemanProjection

end Intertwining

section Retract

variable {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] {i : M →L[R] N} {r : N →L[R] M}
  {u : M →L[R] M}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a normed module `N`. If `E` is a Riesz–Coleman projection of `i ∘ u ∘ r` for `Q`, then
`r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr := semiconj_aeval (u := i.comp (u.comp r)) (v := u) (r : N →ₗ[R] M)
    (fun y ↦ by simp [hri']) Q.reverse
  have hi := semiconj_aeval (u := u) (v := i.comp (u.comp r)) (i : M →ₗ[R] N)
    (fun x ↦ by simp [hri']) Q.reverse
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hzero (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simpa [hE', hzero] using (hr (E (i x))).symm
  · ext x
    simpa [hri'] using (hr (w (i x))).symm.trans congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    have hiQ : i (Polynomial.aeval u Q.reverse x) =
        Polynomial.aeval (i.comp (u.comp r)) Q.reverse (i x) := hi x
    simpa [hiQ, hri'] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x
    simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x
    simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

end Retract

end ContinuousLinearMap
