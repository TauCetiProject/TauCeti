/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Riesz–Coleman projections and closed polynomial spectral splittings

Let `R` be a normed commutative ring with Tate scalars, `M` a seminormed `R`-module with bounded
scalar action, `u : M →L[R] M` a bounded endomorphism, and `Q : R[X]` a polynomial with reversal
`Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
an idempotent `E` commuting with `u` and lying in the operator-norm closure of `R[u]`, such that
`Q*(u) * E = 0` and `Q*(u)` has a two-sided inverse `w` on the complementary summand `ker E =
range (1 - E)` with `w` again in the closure of `R[u]`. It yields a topological direct-sum
decomposition

  `M = ker Q*(u) ⊕ range Q*(u)`

into `u`-stable submodules (`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range_aeval_reverse`), on which
`Q*(u)` vanishes on the first summand and restricts to a continuous linear automorphism of the
second (`ContinuousLinearMap.IsRieszColemanProjection.equivKer`). Such a projection is unique
(`ContinuousLinearMap.IsRieszColemanProjection.unique`); for `Q = 1` it is zero
(`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_one`,
`ContinuousLinearMap.isRieszColemanProjection_one_zero`).

When the leading coefficient of `Q` is a unit, the constant term of `Q*` is `Q.leadingCoeff`, so
dividing `Q* - Q*(0)` by `X` expresses `E = u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E)`. Consequently:

* `u` restricts to a continuous linear automorphism of `range E = ker Q*(u)`
  (`ContinuousLinearMap.IsRieszColemanProjection.equivRange`);
* on a model space `C₀(I, R)`, if `u` is row compact then `E` is row compact and `ker Q*(u)` is
  finitely generated and projective over `R`
  (`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse`), without assuming
  `R` Noetherian or reduced;
* Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id`, and when
  `lc(Q)` is a unit the extension `i ∘ E ∘ r` recovers the ambient projection on `N`
  (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`).

Finally, any linear map intertwining two endomorphisms intertwines their Riesz–Coleman projections
and complementary inverses for the same polynomial `Q`, so every bounded operator commuting with
`u` commutes with `E` and preserves both spectral summands
(`ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
`ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector onto `ker Q*(u)` along a
  closed `u`-stable complement on which `Q*(u)` is invertible.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on `ker E`,
  extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `IsUnit Q.leadingCoeff`, `u` as a
  continuous linear automorphism of `range E`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A3–A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial
open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R M : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` attached
to a polynomial `Q : R[X]`: an idempotent `E` commuting with `u` and lying in the operator-norm
closure of `R[u]`, such that `Q*(u) * E = 0` for `Q* = Q.reverse` and `Q*(u)` has a two-sided
inverse on `range (1 - E)` which also lies in the closure of `R[u]`. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop where
  /-- A Riesz–Coleman projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz–Coleman projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz–Coleman projection is an operator-norm limit of polynomials in the operator. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- The reversed polynomial `Q*(u)` vanishes on the range of a Riesz–Coleman projection. -/
  aeval_reverse_mul_eq_zero : Polynomial.aeval u Q.reverse * E = 0
  /-- `Q*(u)` is invertible on the complementary summand, with inverse an operator-norm limit of
  polynomials in `u`. -/
  exists_inverse : ∃ w : M →L[R] M, Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

/-- For `Q = 1`, the zero operator is a Riesz–Coleman projection of `u`. -/
theorem isRieszColemanProjection_one_zero (u : M →L[R] M) :
    IsRieszColemanProjection u 1 0 := by
  have hrev : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C, C_1]
  refine ⟨.zero, Commute.zero_right u, subset_closure (Subalgebra.zero_mem _), by simp,
    ⟨1, ?_, ?_, by simp, by simp, subset_closure (Subalgebra.one_mem _)⟩⟩ <;> simp [hrev]

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- For `Q = 1`, the finite spectral summand is zero: any Riesz–Coleman projection for `1` is
`0`. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  have hrev : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C, C_1]
  simpa [hrev] using hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left a E).mul_left (hE.commute.pow_left n)

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

/-- `E * Q*(u) = 0`: `Q*(u)` takes values in `ker E`. -/
theorem mul_aeval_reverse_eq_zero (hE : IsRieszColemanProjection u Q E) :
    E * Polynomial.aeval u Q.reverse = 0 :=
  hE.commute_aeval_reverse.eq.symm.trans hE.aeval_reverse_mul_eq_zero

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

/-- Every polynomial in `u` preserves `ker E`. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval P).eq.symm) x)

/-- Every polynomial in `u` preserves `range E`. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval P).eq.symm) x)

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

/-- The complementary inverse takes values in `ker E`. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsRieszColemanProjection u Q E) : E * hE.inverse = 0 :=
  hE.exists_inverse.choose_spec.2.2.1

/-- The complementary inverse vanishes on `range E`. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) : hE.inverse * E = 0 :=
  hE.exists_inverse.choose_spec.2.2.2.1

/-- The complementary inverse lies in the operator-norm closure of `R[u]`. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) :=
  hE.exists_inverse.choose_spec.2.2.2.2

/-- Uniqueness of the complementary inverse among right inverses up to `1 - E` valued in
`ker E`. -/
theorem eq_inverse (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Polynomial.aeval u Q.reverse * w = 1 - E) (hEw : E * w = 0) : w = hE.inverse := by
  calc w = (1 - E) * w := by
        rw [sub_mul (α := M →L[R] M), one_mul, hEw, sub_zero w]
    _ = hE.inverse * (Polynomial.aeval u Q.reverse * w) := by
        rw [← mul_assoc, hE.inverse_mul_aeval_reverse]
    _ = hE.inverse := by
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero, sub_zero hE.inverse]

/-- The complementary inverse preserves `ker E`. -/
theorem mapsTo_ker_inverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using congr($(hE.mul_inverse_eq_zero) x)

/-- On `ker E`, `inverse` is a left inverse of `Q*(u)`. -/
theorem inverse_aeval_reverse_apply (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    hE.inverse (Polynomial.aeval u Q.reverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_aeval_reverse) x)

/-- On `ker E`, `inverse` is a right inverse of `Q*(u)`. -/
theorem aeval_reverse_apply_inverse (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    Polynomial.aeval u Q.reverse (hE.inverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.aeval_reverse_mul_inverse) x)

/-- **The range of a Riesz–Coleman projection is `ker Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have h := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, hx, map_zero, sub_apply, one_apply_eq_self] at h
    rw [eq_comm, sub_eq_zero] at h
    exact h.symm

/-- **The range of `Q*(u)` is the complementary summand `ker E`.** -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨hE.inverse x, hE.aeval_reverse_apply_inverse hx⟩⟩
  rintro ⟨y, rfl⟩
  simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.mul_aeval_reverse_eq_zero) y)

/-- **Topological decomposition `M = ker Q*(u) ⊕ range Q*(u)`.** -/
theorem isTopCompl_ker_range_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- In a Hausdorff module, the complementary summand `range Q*(u) = ker E` is closed. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))
    (fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))

/-- The complementary automorphism `equivKer` acts by `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x :=
  (rfl)

/-- The inverse complementary automorphism `equivKer.symm` acts by
`IsRieszColemanProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` for the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  have h₁ : (1 - E') * E = 0 := by
    rw [← hE'.inverse_mul_aeval_reverse, mul_assoc, hE.aeval_reverse_mul_eq_zero, mul_zero]
  have h₂ : E' * (1 - E) = 0 := by
    rw [← hE.aeval_reverse_mul_inverse, ← mul_assoc, hE'.mul_aeval_reverse_eq_zero, zero_mul]
  rw [sub_mul (α := M →L[R] M), one_mul, sub_eq_zero] at h₁
  rw [mul_sub (α := M →L[R] M), mul_one, sub_eq_zero] at h₂
  exact h₁.trans h₂.symm

/-- When `Q.leadingCoeff` is a unit, `E` factors on the left through `u`: specifically,
`u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E) = E`. -/
theorem mul_smul_aeval_divX_reverse_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    u * ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) = E := by
  -- Evaluating `X * Q*.divX + C (Q*(0)) = Q*` at `u` and right-multiplying by `E` kills the RHS.
  have hdiv : Polynomial.aeval u (X * Q.reverse.divX + C (Q.reverse.coeff 0)) * E = 0 := by
    rw [X_mul_divX_add]
    exact hE.aeval_reverse_mul_eq_zero
  rw [map_add, map_mul, aeval_X, aeval_C, coeff_zero_reverse, Algebra.algebraMap_eq_smul_one,
    add_mul, smul_mul_assoc, one_mul, add_eq_zero_iff_eq_neg] at hdiv
  calc u * ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E)
      = (-Ring.inverse Q.leadingCoeff) • (u * Polynomial.aeval u Q.reverse.divX * E) := by
        rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
    _ = (Ring.inverse Q.leadingCoeff * Q.leadingCoeff) • E := by
        rw [hdiv, neg_smul, smul_neg, neg_neg, smul_smul]
    _ = E := by rw [Ring.inverse_mul_cancel _ hQ, one_smul]

/-- Symmetric form of `mul_smul_aeval_divX_reverse_mul`: `((-lc(Q)⁻¹) • (Q*.divX)(u) * E) * u =
E`. -/
theorem smul_aeval_divX_reverse_mul_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) * u = E := by
  have huP (P : R[X]) : Commute u (Polynomial.aeval u P) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_right hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact (Algebra.commute_algebraMap_right a u).mul_right ((Commute.refl u).pow_right n)
  have hcomm : Commute u ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) :=
    ((huP Q.reverse.divX).smul_right _).mul_right hE.commute
  exact hcomm.eq.symm.trans (hE.mul_smul_aeval_divX_reverse_mul hQ)

/-- On `range E`, `(-lc(Q)⁻¹) • (Q*.divX)(u)` is a left inverse of `u`. -/
theorem neg_inverse_smul_aeval_divX_reverse_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {x : M} (hx : x ∈ E.range) :
    ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) (u x) = x := by
  have hfix : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp hx
  have hcomm : E (u x) = u (E x) := congr($(hE.commute.eq.symm) x)
  have h := congr($(hE.smul_aeval_divX_reverse_mul_mul hQ) x)
  simp only [mul_apply_eq_comp] at h
  rwa [hcomm, hfix] at h

/-- On `range E`, `(-lc(Q)⁻¹) • (Q*.divX)(u)` is a right inverse of `u`. -/
theorem apply_neg_inverse_smul_aeval_divX_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {x : M} (hx : x ∈ E.range) :
    u (((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x) = x := by
  have hfix : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp hx
  have h := congr($(hE.mul_smul_aeval_divX_reverse_mul hQ) x)
  simp only [mul_apply_eq_comp] at h
  rwa [hfix] at h

/-- **Invertibility of `u` on `ker Q*(u) = range E`.** When the leading coefficient of `Q` is a
unit, `u` restricts to a continuous linear automorphism of `range E`. This includes `Q = 1`, when
`range E = 0`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E.range :=
  ContinuousLinearEquiv.equivOfInverse
    (u.restrict hE.mapsTo_range)
    (((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX).restrict
      fun _ hx ↦ E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx))
    (fun x ↦ Subtype.ext (hE.neg_inverse_smul_aeval_divX_reverse_apply hQ x.property))
    (fun x ↦ Subtype.ext (hE.apply_neg_inverse_smul_aeval_divX_reverse hQ x.property))

/-- The finite-summand automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- The inverse finite-summand automorphism `equivRange.symm` acts by `-lc(Q)⁻¹ • (Q*/X)(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x :=
  (rfl)

/-- When `Q.leadingCoeff` is a unit, the restriction of `u` to `range E` is a unit of
`E.range →L[R] E.range`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict hE.mapsTo_range) :=
  ⟨{ val := u.restrict hE.mapsTo_range
     inv := (hE.equivRange hQ).symm.toContinuousLinearMap
     val_inv := ContinuousLinearMap.ext (hE.equivRange hQ).apply_symm_apply
     inv_val := ContinuousLinearMap.ext (hE.equivRange hQ).symm_apply_apply }, rfl⟩

/-- When `Q.leadingCoeff` is a unit, the `R`-linear restriction of `u` to `range E` is a unit of
`Module.End R E.range`. -/
theorem isUnit_toLinearMap_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit ((u : M →ₗ[R] M).restrict hE.mapsTo_range) :=
  (hE.isUnit_restrict_range hQ).map toLinearMapRingHom

end IsRieszColemanProjection

end Module

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M} {Q : R[X]}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a normed module `N`. If `E` is a Riesz–Coleman projection of `i ∘ u ∘ r` for `Q`,
then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  -- `r` intertwines `i ∘ u ∘ r` with `u`, and `i` intertwines `u` with `i ∘ u ∘ r`, on all
  -- polynomials in `R[X]`.
  have hrP (P : R[X]) (y : N) :
      r (Polynomial.aeval (i.comp (u.comp r)) P y) = Polynomial.aeval u P (r y) := by
    have hr : u.toLinearMap.comp r.toLinearMap =
        r.toLinearMap.comp (i.comp (u.comp r)).toLinearMap := by
      ext z; simp [hri']
    have h := (LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hr P) y).symm
    simp only [LinearMap.comp_apply, ← toLinearMap_aeval] at h
    exact h
  have hiP (P : R[X]) (x : M) :
      Polynomial.aeval (i.comp (u.comp r)) P (i x) = i (Polynomial.aeval u P x) := by
    have hi : (i.comp (u.comp r)).toLinearMap.comp i.toLinearMap =
        i.toLinearMap.comp u.toLinearMap := by
      ext z; simp [hri']
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hi P) x
    simp only [LinearMap.comp_apply, ← toLinearMap_aeval] at h
    exact h
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hzero (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x; simp [hE', hri', hEE]
  · ext x; simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x; simp [← hrP, hzero]
  · ext x
    simpa [hri'] using
      (hrP Q.reverse (w (i x))).symm.trans congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    simpa [hri', ← hiP] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x; simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x; simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

omit [IsBoundedSMul R M] in
/-- When `Q.leadingCoeff` is a unit, the Riesz–Coleman projection `E'` of the extension
`i ∘ u ∘ r` vanishes on `ker r` and takes values in `range i`: extending its compression
`E = r ∘ E' ∘ i` back to `N` recovers `E' = i ∘ E ∘ r`. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M) {E' : N →L[R] N}
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E') (hQ : IsUnit Q.leadingCoeff) :
    i.comp ((r.comp (E'.comp i)).comp r) = E' := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hcomm := apply_comp_apply_of_mem_closure_adjoin hri hE'.mem_closure_adjoin
  have hfac := hE'.mul_smul_aeval_divX_reverse_mul hQ
  ext y
  -- Since `E' = (i ∘ u ∘ r) * (...)`, `E' y` already lies in `range i`, so `i (r (E' y)) = E' y`.
  have hirE : i (r (E' y)) = E' y := by
    have hy := congr($hfac y).symm
    simp only [mul_apply_eq_comp, comp_apply] at hy
    rw [hy, hri']
  calc i (r (E' (i (r y)))) = i (r (i (r (E' y)))) := by rw [← hcomm y]
    _ = i (r (E' y)) := by rw [hri']
    _ = E' y := hirE

end Retract

section Intertwining

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : R[X]}

namespace IsRieszColemanProjection

/-- A linear map (not assumed continuous) intertwining `u` and `v` intertwines their
Riesz–Coleman projections for the same polynomial `Q`. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  have hfP : (Polynomial.aeval v Q.reverse).toLinearMap.comp f =
      f.comp (Polynomial.aeval u Q.reverse).toLinearMap := by
    rw [toLinearMap_aeval, toLinearMap_aeval]
    exact Module.End.aeval_comp_of_comp_eq (LinearMap.ext fun x ↦ (hf x).symm) Q.reverse
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) :=
    (LinearMap.congr_fun hfP x).symm
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker, LinearMap.mem_ker, coe_coe, ← hfQ]
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using
      congr(f $(congr($(hE.aeval_reverse_mul_eq_zero) x)))
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      apply LinearMap.mem_ker.mpr
      simpa only [coe_coe, map_sub, mul_apply_eq_comp, sub_eq_zero] using
        (congr($(hE.isIdempotentElem.eq) x)).symm
    rw [← hE.range_aeval_reverse_eq_ker] at hx
    obtain ⟨y, hy⟩ := hx
    apply LinearMap.mem_ker.mp
    rw [← hF.range_aeval_reverse_eq_ker]
    exact ⟨f y, (hfQ y).symm.trans (congrArg f hy)⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the finite spectral summand `range E` into `range F`. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner sends the complementary summand `ker E` into `ker F`. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [coe_coe, ← hE.semiconj hF f hf x, hx', map_zero]

/-- An intertwiner also intertwines the complementary inverses of `Q*(u)` and `Q*(v)`. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hfP : (Polynomial.aeval v Q.reverse).toLinearMap.comp f =
      f.comp (Polynomial.aeval u Q.reverse).toLinearMap := by
    rw [toLinearMap_aeval, toLinearMap_aeval]
    exact Module.End.aeval_comp_of_comp_eq (LinearMap.ext fun x ↦ (hf x).symm) Q.reverse
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) :=
    (LinearMap.congr_fun hfP x).symm
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    rw [coe_coe, ← hEF (hE.inverse x)]
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using
      congr(f $(congr($(hE.mul_inverse_eq_zero) x)))
  calc f (hE.inverse x) = hF.inverse (Polynomial.aeval v Q.reverse (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f (Polynomial.aeval u Q.reverse (hE.inverse x))) := by rw [hfQ]
    _ = hF.inverse (f (x - E x)) :=
        congrArg (fun y ↦ hF.inverse (f y)) (congr($(hE.aeval_reverse_mul_inverse) x))
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- Every bounded operator commuting with `u` commutes with its Riesz–Coleman projection. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {g : M →L[R] M}
    (hg : Commute g u) : Commute g E :=
  ContinuousLinearMap.ext fun x ↦ hE.semiconj hE g.toLinearMap (fun y ↦ congr($(hg.eq) y)) x

/-- Every bounded operator commuting with `u` commutes with the complementary inverse. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {g : M →L[R] M}
    (hg : Commute g u) : Commute g hE.inverse :=
  ContinuousLinearMap.ext fun x ↦
    hE.semiconj_inverse hE g.toLinearMap (fun y ↦ congr($(hg.eq) y)) x

end IsRieszColemanProjection

end Intertwining

section RowCompact

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}

namespace IsRieszColemanProjection

/-- When `Q.leadingCoeff` is a unit, every Riesz–Coleman projection of a row-compact operator is
row compact, including when `Q = 1`. -/
theorem isRowCompact (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : E.IsRowCompact := by
  rw [← hE.mul_smul_aeval_divX_reverse_mul hQ, mul_def]
  exact hu.comp_clm _

variable [CompleteSpace R]

/-- When `Q.leadingCoeff` is a unit, the finite spectral summand `range E` of a row-compact
operator is finitely generated over `R`. -/
theorem finite_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : Module.Finite R E.range :=
  (hE.isRowCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, the finite spectral summand `range E` of a row-compact
operator is projective over `R`. -/
theorem projective_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : Module.Projective R E.range :=
  (hE.isRowCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is finitely generated over `R`. -/
theorem finite_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range hQ hu

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is projective over `R`. -/
theorem projective_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range hQ hu

end IsRieszColemanProjection

end RowCompact

end ContinuousLinearMap
