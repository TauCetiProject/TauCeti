/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Algebra.Polynomial.Div
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Algebra.Ring.Commute
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projections attached to polynomial spectral factors

Let `R` be a normed commutative ring with Tate scalars, `M` a seminormed `R`-module with a bounded
scalar action, `u : M →L[R] M` a continuous linear endomorphism, and `Q : R[X]` a polynomial with
reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
an idempotent `E`, commuting with `u` and lying in the operator-norm closure of the polynomials in
`u`, such that `Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand
`range (1 - E)`, with inverse again in the operator-norm closure of the polynomials in `u`.

Thus `E` decomposes `M` into the topological direct sum of `range E = ker Q*(u)`
(`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`) and `ker E = range Q*(u)`
(`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`). Such a projection is
unique (`ContinuousLinearMap.IsRieszColemanProjection.unique`), invariant under scaling `Q` by any
unit of `R`, and agrees for `Q = (X - a) ^ h` (`h > 0`) with Serre's Riesz projection at `a` of
order `h` (`ContinuousLinearMap.isRieszColemanProjection_X_sub_C_pow_iff`). When the leading
coefficient of `Q` is a unit, `u` itself restricts to a continuous linear automorphism of `range E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`), because `1 - c Q*` has zero constant
term and hence factors through `X`.

All algebraic, topological-splitting, intertwining and retract-compression properties are developed
in full generality on seminormed modules. On a model space `C₀(I, R)`, any Riesz–Coleman projection
of a row-compact operator for a polynomial with invertible leading coefficient is row compact
(`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`), so `ker Q*(u)` is a finitely
generated projective `R`-module without any completeness assumption on `R` for compactness, and
without any field, Noetherian or reducedness assumption on `R` for finite projectivity.

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector of `u` cutting out
  `ker Q*(u)` along a topological direct-sum complement on which `Q*(u)` is invertible.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on `ker E`,
  extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: `u` as a continuous linear
  automorphism of `range E` when `IsUnit Q.leadingCoeff`.

## Main results

* `ContinuousLinearMap.isRieszColemanProjection_X_sub_C_iff`,
  `ContinuousLinearMap.isRieszColemanProjection_X_sub_C_pow_iff`: comparison with
  `ContinuousLinearMap.IsRieszProjection`.
* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`: the closed topological
  splitting `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of the Riesz–Coleman
  projection.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`: linear intertwiners between operators
  intertwine their Riesz–Coleman projections and complementary inverses.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`: compression along continuous
  linear retracts.
* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse`: row compactness and
  finite projectivity of `ker Q*(u)` on model spaces.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory **13** (2019), 93–158, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u : M →L[R] M` for a polynomial `Q : R[X]`:
an idempotent `E` commuting with `u` and lying in the operator-norm closure of `R[u]`, such that
`Q*(u) * E = 0` for the reversal `Q* = Q.reverse`, and `Q*(u)` has a two-sided inverse modulo `E`
which also lies in the operator-norm closure of `R[u]`. No normalization on the constant term of
`Q` is imposed. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop where
  /-- A Riesz–Coleman projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz–Coleman projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz–Coleman projection lies in the operator-norm closure of `R[u]`. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- `Q*(u)` vanishes on the range of a Riesz–Coleman projection. -/
  aeval_reverse_mul_eq_zero : Polynomial.aeval u Q.reverse * E = 0
  /-- `Q*(u)` is invertible on the complementary summand, with inverse in the closure of `R[u]`. -/
  exists_inverse : ∃ w : M →L[R] M,
    Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- For `Q = 1`, the reversal is `1`, so any Riesz–Coleman projection is zero. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  have h1 : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C, C_1]
  simpa [h1] using hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_left hq
  | monomial n r =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (hE.commute.pow_left n).smul_left r

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

/-- Scaling `Q` by a unit of `R` preserves Riesz–Coleman projections. -/
theorem units_smul (hE : IsRieszColemanProjection u Q E) (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E := by
  have hrev : (c • Q).reverse = c • Q.reverse := by
    have hdeg : (c • Q).natDegree = Q.natDegree := by
      rw [Units.smul_def, smul_eq_C_mul]
      exact natDegree_C_mul_eq_of_mul_eq_one c.inv_mul
    rw [reverse, hdeg, Units.smul_def, smul_eq_C_mul, reflect_C_mul, ← smul_eq_C_mul,
      ← Units.smul_def, ← reverse]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have : IsTopologicalSemiring (M →L[R] M) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : M →L[R] M) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_,
    ⟨(↑c⁻¹ : R) • w, ?_, ?_, ?_, ?_, (hT _).1 (T.smul_mem ((hT _).2 hw) _)⟩⟩
  · rw [hrev, Units.smul_def, map_smul, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero, smul_zero]
  · rw [hrev, Units.smul_def, map_smul, smul_mul_smul_comm, c.mul_inv, one_smul, hw₁]
  · rw [hrev, Units.smul_def, map_smul, smul_mul_smul_comm, c.inv_mul, one_smul, hw₂]
  · rw [mul_smul_comm, hw₃, smul_zero]
  · rw [smul_mul_assoc, hw₄, smul_zero]

/-- The operator preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($(hE.commute.eq.symm) x)

/-- The operator preserves the range of its Riesz–Coleman projection. -/
theorem mapsTo_range (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE.commute.eq.symm) x)

/-- Every polynomial in `u` preserves the kernel of a Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P : M →L[R] M) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval P).eq.symm) x)

/-- Every polynomial in `u` preserves the range of a Riesz–Coleman projection. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P : M →L[R] M) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval P).eq.symm) x)

/-- `Q*(u)` preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo (Polynomial.aeval u Q.reverse : M →L[R] M) E.ker E.ker :=
  hE.mapsTo_ker_aeval Q.reverse

/-- `Q*(u)` preserves the range of its Riesz–Coleman projection. -/
theorem mapsTo_range_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo (Polynomial.aeval u Q.reverse : M →L[R] M) E.range E.range :=
  hE.mapsTo_range_aeval Q.reverse

/-- The **complementary inverse** of a Riesz–Coleman projection: the inverse of `Q*(u)` on the
complementary summand `ker E = range (1 - E)`, extended by zero on `range E`, chosen from
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

/-- The complementary inverse lies in the operator-norm closure of `R[u]`. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) :=
  hE.exists_inverse.choose_spec.2.2.2.2

/-- The complementary inverse is the unique right inverse of `Q*(u)` up to `1 - E` taking values
in `ker E`. -/
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

/-- On `ker E`, the complementary inverse is a left inverse of `Q*(u)`. -/
theorem inverse_aeval_reverse_apply (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    hE.inverse (Polynomial.aeval u Q.reverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_aeval_reverse) x)

/-- On `ker E`, the complementary inverse is a right inverse of `Q*(u)`. -/
theorem aeval_reverse_apply_inverse (hE : IsRieszColemanProjection u Q E)
    {x : M} (hx : x ∈ E.ker) :
    Polynomial.aeval u Q.reverse (hE.inverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.aeval_reverse_mul_inverse) x)

/-- **The range of a Riesz–Coleman projection is the polynomial kernel** `ker Q*(u)`. -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, hx, map_zero, sub_apply, one_apply_eq_self] at this
    exact (sub_eq_zero.mp this.symm).symm

/-- **The range of `Q*(u)` is the complementary summand** `ker E`. -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (Polynomial.aeval u Q.reverse : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  have hzero : E * Polynomial.aeval u Q.reverse = 0 :=
    hE.commute_aeval_reverse.eq.symm.trans hE.aeval_reverse_mul_eq_zero
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨hE.inverse x, hE.aeval_reverse_apply_inverse hx⟩⟩
  rintro ⟨y, rfl⟩
  simpa only [mul_apply_eq_comp, zero_apply] using congr($hzero y)

/-- The polynomial kernel `ker Q*(u)` and the image `range Q*(u)` are topological complements. -/
theorem isTopCompl_ker_range (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker (Polynomial.aeval u Q.reverse : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range (Polynomial.aeval u Q.reverse : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The image `range Q*(u)` is closed in any `T₁` module, even in infinite dimension. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed (LinearMap.range (Polynomial.aeval u Q.reverse : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval_reverse hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))
    (fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))

/-- `equivKer` acts on `E.ker` as `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x :=
  (rfl)

/-- `equivKer.symm` acts on `E.ker` as `hE.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- When `Q` has invertible leading coefficient, the polynomial `B = 1 - c Q*` (`c` the inverse of
`Q.leadingCoeff`) has zero constant term, so `B = X * divX B` and `u * (divX B)(u)` acts as the
identity on `range E`: `u * (divX B)(u) * E = E`. -/
theorem mul_aeval_divX_mul_eq_self (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    u * Polynomial.aeval u
      (Polynomial.divX (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)) * E = E := by
  set c := Ring.inverse Q.leadingCoeff
  set B := 1 - C c * Q.reverse
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have hB0 : B.coeff 0 = 0 := by simp [B, coeff_zero_reverse, hc]
  have hB : X * B.divX = B := by
    simpa [hB0] using X_mul_divX_add B
  have huB : u * Polynomial.aeval u B.divX = Polynomial.aeval u B := by
    conv_rhs => rw [← hB]
    rw [map_mul, aeval_X]
  rw [huB]
  simp only [B, map_sub, map_one, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, sub_mul, hE.aeval_reverse_mul_eq_zero, smul_zero, sub_zero]

/-- **Invertibility of `u` on the Riesz–Coleman summand.** When `Q` has invertible leading
coefficient, `u` restricts to a continuous linear automorphism of `range E`, with inverse given by
evaluating `divX (1 - c Q*)` at `u` for `c = Ring.inverse Q.leadingCoeff`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  set P := Polynomial.divX (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hright (x : E.range) : u (Polynomial.aeval u P x) = x := by
    have hx := congr($(hE.mul_aeval_divX_mul_eq_self hQ) x)
    simpa only [P, mul_apply_eq_comp, hfix] using hx
  have hcomm : Commute u (Polynomial.aeval u P) := by
    simpa only [aeval_X] using (Commute.all X P).map (Polynomial.aeval u)
  have hleft (x : E.range) : Polynomial.aeval u P (u x) = x := by
    have hc := congr($(hcomm.symm.eq) x)
    simpa only [mul_apply_eq_comp, hright x] using hc
  exact ContinuousLinearEquiv.equivOfInverse
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx))
    ((Polynomial.aeval u P).restrict (fun _ hx ↦ hE.mapsTo_range_aeval P hx))
    (fun x ↦ Subtype.ext (hleft x))
    (fun x ↦ Subtype.ext (hright x))

/-- `equivRange` acts on `E.range` as `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- `equivRange.symm` acts on `E.range` by evaluating `divX (1 - c Q*)` at `u`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      Polynomial.aeval u
        (Polynomial.divX (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)) x :=
  (rfl)

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` for the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero (h := 1) hE'.isIdempotentElem
    (by simpa only [pow_one] using hE.aeval_reverse_mul_eq_zero)
    (by simpa only [pow_one] using hE'.aeval_reverse_mul_eq_zero)
    hw hw' hw₂ hw₂'

section Intertwining

variable {N : Type*} [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {v F : N →L[R] N}

/-- A linear map intertwining two operators intertwines their Riesz–Coleman projections for the
same polynomial `Q`. Continuity of the intertwiner is not required. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  have hfu : (v : Module.End R N).comp f = f.comp (u : Module.End R M) :=
    LinearMap.ext fun x ↦ (hf x).symm
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hfu Q.reverse) x
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe, ← hfQ]
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
    exact ⟨f y, (hfQ y).symm.trans (congrArg f hy)⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- A linear intertwiner sends the Riesz–Coleman summand into the corresponding target summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- A linear intertwiner sends the complementary summand into the corresponding target summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [coe_coe, ← hE.semiconj hF f hf x, hx', map_zero]

/-- Linear intertwiners also intertwine the complementary inverses of `Q*(u)` and `Q*(v)`. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hfu : (v : Module.End R N).comp f = f.comp (u : Module.End R M) :=
    LinearMap.ext fun x ↦ (hf x).symm
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hfu Q.reverse) x
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    rw [coe_coe, ← hEF (hE.inverse x)]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse (Polynomial.aeval v Q.reverse (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f (Polynomial.aeval u Q.reverse (hE.inverse x))) := by rw [hfQ]
    _ = hF.inverse (f (x - E x)) := by
        have hz := congr($(hE.aeval_reverse_mul_inverse) x)
        exact congrArg (fun y ↦ hF.inverse (f y)) hz
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- Any continuous linear endomorphism commuting with `u` commutes with every Riesz–Coleman
projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E :=
  ContinuousLinearMap.ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- Any continuous linear endomorphism commuting with `u` commutes with the complementary inverse
of every Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse :=
  ContinuousLinearMap.ext fun x ↦
    hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end Intertwining

end IsRieszColemanProjection

/-- Scaling `Q` by a unit of `R` gives an equivalent Riesz–Coleman projection condition. -/
@[simp]
theorem isRieszColemanProjection_units_smul_iff {u E : M →L[R] M} {Q : R[X]} (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E ↔ IsRieszColemanProjection u Q E :=
  ⟨fun h ↦ by simpa using h.units_smul c⁻¹, fun h ↦ h.units_smul c⟩

/-- Every Riesz projection of `u` at `a` of order `h` is a Riesz–Coleman projection for
`(X - C a) ^ h`. -/
theorem IsRieszProjection.isRieszColemanProjection_X_sub_C_pow {u E : M →L[R] M} {a : R} {h : ℕ}
    (hE : IsRieszProjection u a h E) :
    IsRieszColemanProjection u ((X - C a) ^ h) E := by
  have := NormOneClass.nontrivial (G := R)
  have hrev : Polynomial.aeval u ((X - C a) ^ h).reverse = (1 - a • u) ^ h := by
    rw [reverse_X_sub_C_pow, map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have : IsTopologicalSemiring (M →L[R] M) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : M →L[R] M) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  have hCw : Commute (1 - a • u) w := hw₁.trans hw₂.symm
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_, ?_⟩
  · rw [hrev]
    exact hE.pow_mul_eq_zero
  · rcases Nat.eq_zero_or_pos h with rfl | hh
    · have h1 : (1 : R[X]).reverse = 1 := by rw [← C_1, reverse_C, C_1]
      refine ⟨1, ?_, ?_, ?_, ?_, (hT _).1 T.one_mem⟩ <;>
        simp [h1, hE.eq_zero_of_order_zero]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
      refine ⟨w ^ (k + 1), ?_, ?_, ?_, ?_, (hT _).1 (T.pow_mem ((hT _).2 hw) (k + 1))⟩
      · rw [hrev, ← hCw.mul_pow, hw₁, hE.isIdempotentElem.one_sub.pow_succ_eq]
      · rw [hrev, ← hCw.symm.mul_pow, hw₂, hE.isIdempotentElem.one_sub.pow_succ_eq]
      · rw [pow_succ', ← mul_assoc, hw₃, zero_mul]
      · rw [pow_succ, mul_assoc, hw₄, mul_zero]

/-- For a positive exponent `h`, Riesz–Coleman projections for `(X - C a) ^ h` coincide with Riesz
projections at `a` of order `h`. -/
theorem isRieszColemanProjection_X_sub_C_pow_iff {u E : M →L[R] M} {a : R} {h : ℕ} (hh : 0 < h) :
    IsRieszColemanProjection u ((X - C a) ^ h) E ↔ IsRieszProjection u a h E := by
  refine ⟨fun hE ↦ ?_, fun hE ↦ hE.isRieszColemanProjection_X_sub_C_pow⟩
  have := NormOneClass.nontrivial (G := R)
  have hrev : Polynomial.aeval u ((X - C a) ^ h).reverse = (1 - a • u) ^ h := by
    rw [reverse_X_sub_C_pow, map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  rw [hrev] at hw₁ hw₂
  set C₀ : M →L[R] M := 1 - a • u
  have hCE : Commute C₀ E := hE.commute.one_sub_smul_left (A := M →L[R] M) a
  have hECw : E * (C₀ ^ k * w) = 0 := by
    rw [← mul_assoc, ← (hCE.pow_left k).eq, mul_assoc, hw₃, mul_zero]
  have hwCE : w * C₀ ^ k * E = 0 := by
    rw [mul_assoc, (hCE.pow_left k).eq, ← mul_assoc, hw₄, zero_mul]
  have hCw_eq : C₀ ^ k * w = w * C₀ ^ k := by
    calc C₀ ^ k * w = (1 - E) * (C₀ ^ k * w) := by
          rw [sub_mul (α := M →L[R] M), one_mul, hECw, sub_zero]
      _ = w * C₀ ^ (k + 1) * (C₀ ^ k * w) := by rw [hw₂]
      _ = w * C₀ ^ k * (C₀ ^ (k + 1) * w) := by
          conv_lhs => rw [pow_succ C₀ k]
          conv_rhs => rw [pow_succ' C₀ k]
          simp only [mul_assoc]
      _ = w * C₀ ^ k * (1 - E) := by rw [hw₁]
      _ = w * C₀ ^ k := by rw [mul_sub (α := M →L[R] M), mul_one, hwCE, sub_zero]
  have : IsTopologicalSemiring (M →L[R] M) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : M →L[R] M) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  have hCS : C₀ ^ k ∈ T := T.pow_mem
    (Subalgebra.le_topologicalClosure _ <|
      Subalgebra.sub_mem (A := M →L[R] M) _ (Subalgebra.one_mem _)
        (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton R u) a)) k
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin,
    hrev ▸ hE.aeval_reverse_mul_eq_zero,
    ⟨C₀ ^ k * w, ?_, ?_, hECw, ?_, (hT _).1 (T.mul_mem hCS ((hT _).2 hw))⟩⟩
  · rwa [← mul_assoc, ← pow_succ']
  · rwa [hCw_eq, mul_assoc, ← pow_succ]
  · rw [mul_assoc, hw₄, mul_zero]

/-- Riesz–Coleman projections for a linear polynomial `X - C a` are exactly Riesz projections at
`a` of order `1`. -/
@[simp]
theorem isRieszColemanProjection_X_sub_C_iff {u E : M →L[R] M} {a : R} :
    IsRieszColemanProjection u (X - C a) E ↔ IsRieszProjection u a 1 E := by
  simpa only [pow_one] using
    isRieszColemanProjection_X_sub_C_pow_iff (u := u) (E := E) (a := a) Nat.one_pos

end Module

section Retract

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as a
retract of a seminormed module `N`. If `E` is a Riesz–Coleman projection of `i ∘ u ∘ r` for `Q`,
then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hru : (u : Module.End R M).comp (r : N →ₗ[R] M) =
      (r : N →ₗ[R] M).comp ((i.comp (u.comp r)) : Module.End R N) :=
    LinearMap.ext fun y ↦ by simp [hri']
  have hrQ (y : N) :
      r (Polynomial.aeval (i.comp (u.comp r)) Q.reverse y) =
        Polynomial.aeval u Q.reverse (r y) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hru Q.reverse) y
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  have hp : Commute (i.comp r) (i.comp (u.comp r)) := by
    ext y; simp [mul_apply_eq_comp, hri']
  set w := hE.inverse
  have hE' (y : N) : i (r (E y)) = E (i (r y)) := congr($((hE.commute_of_commute hp).eq) y)
  have hw' (y : N) : i (r (w y)) = w (i (r y)) :=
    congr($((hE.commute_inverse_of_commute hp).eq) y)
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hzero (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  have hw₃ (y : N) : E (w y) = 0 := congr($hE.mul_inverse_eq_zero y)
  have hw₄ (y : N) : w (E y) = 0 := congr($hE.inverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_,
      comp_comp_mem_closure_adjoin hri hE.inverse_mem_closure_adjoin⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simpa [hzero] using (hrQ (E (i x))).symm
  · ext x
    simpa [hri'] using
      (hrQ (w (i x))).symm.trans congr(r $(DFunLike.congr_fun hE.aeval_reverse_mul_inverse (i x)))
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self]
    rw [← hri' x, ← hrQ (i x), ← hw', hri', hri' x]
    simpa [hri'] using congr(r $(DFunLike.congr_fun hE.inverse_mul_aeval_reverse (i x)))
  · ext x
    simp [hw', hri', hw₃]
  · ext x
    simp [hE', hri', hw₄]

end Retract

section ModelSpace

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}

/-- Every Riesz–Coleman projection of a row-compact operator on `C₀(I, R)` for a polynomial with
invertible leading coefficient is row compact, including when `deg Q = 0` (`E = 0`). -/
theorem IsRieszColemanProjection.isRowCompact (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    E.IsRowCompact := by
  rw [← hE.mul_aeval_divX_mul_eq_self hQ]
  simpa only [mul_def] using (hu.comp_clm _).comp_clm E

variable [CompleteSpace R]

/-- The polynomial kernel `ker Q*(u)` of a row-compact operator on `C₀(I, R)` admitting a
Riesz–Coleman projection is finitely generated over `R`. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    Module.Finite R (LinearMap.ker (Polynomial.aeval u Q.reverse :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact (hE.isRowCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The polynomial kernel `ker Q*(u)` of a row-compact operator on `C₀(I, R)` admitting a
Riesz–Coleman projection is projective over `R`. No Noetherian or reducedness hypothesis on `R` is
needed. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    Module.Projective R (LinearMap.ker (Polynomial.aeval u Q.reverse :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact (hE.isRowCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

end ModelSpace

end ContinuousLinearMap
