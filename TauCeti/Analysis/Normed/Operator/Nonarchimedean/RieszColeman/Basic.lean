/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import TauCeti.Algebra.Ring.Commute
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projectors attached to polynomial factors

Let `R` be a seminormed commutative Tate ring, `M` a seminormed `R`-module with a bounded scalar
action, `u : M →L[R] M` a bounded endomorphism, and `Q : Polynomial R` a polynomial with reversal
`Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` at `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is an
idempotent `E`, commuting with `u` and lying in the operator-norm closure of `R[u]`, such that
`Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand `ker E`: there is `w`, again
in the closure of `R[u]`, with `Q*(u) * w = w * Q*(u) = 1 - E` and `E * w = w * E = 0`. Thus `E`
splits `M` topologically as

`M = ker Q*(u) ⊕ range Q*(u)`

(`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`), with `Q*(u)` restricting to a
continuous linear automorphism of `ker E` (`ContinuousLinearMap.IsRieszColemanProjection.equivKer`,
`ContinuousLinearMap.IsRieszColemanProjection.isUnit_restrict_ker`). When `Q` has invertible
leading coefficient, `Q* = lc(Q) + X · (Q*).divX` yields an explicit polynomial inverse
`-lc(Q)⁻¹ · (Q*).divX(u)` to `u` on `range E = ker Q*(u)`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`,
`ContinuousLinearMap.IsRieszColemanProjection.isUnit_restrict_range`), and makes `E` row compact
whenever `u` is (`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`).

Such a projector is unique (`ContinuousLinearMap.IsRieszColemanProjection.unique`) and invariant
under scaling `Q` by a unit of `R` (`ContinuousLinearMap.IsRieszColemanProjection.C_mul_iff`,
`ContinuousLinearMap.rieszColemanProjection_C_mul`); for `Q = 1` it is zero
(`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_one`,
`ContinuousLinearMap.isRieszColemanProjection_one_zero`). Any linear map intertwining two operators
intertwines their Riesz–Coleman projections and complementary inverses, without requiring
continuity (`ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
`ContinuousLinearMap.IsRieszColemanProjection.semiconj_inverse`). In particular every bounded
operator commuting with `u` commutes with `E` and `hE.inverse`.

Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id` of `M` through any
seminormed module `N` without any hypothesis on `Q`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`). Over a normed commutative
Tate ring on a model space `C₀(I, R)`, `ContinuousLinearMap.rieszColemanProjection` defines the
explicit candidate projector by passing to the Riesz projector at `1` of order `deg Q` for `B(u)`,
where `B = 1 - lc(Q)⁻¹ Q*`.

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: predicate for the Riesz–Coleman spectral
  projector of `u` attached to a polynomial `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on the
  complementary summand `ker E`, extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `Q` has unit leading coefficient,
  `u` as a continuous linear automorphism of `range E`.
* `ContinuousLinearMap.rieszColemanProjection`: the explicit candidate projector on `C₀(I, R)`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of Riesz–Coleman projections.
* `ContinuousLinearMap.IsRieszColemanProjection.C_mul_iff`,
  `ContinuousLinearMap.rieszColemanProjection_C_mul`: invariance under unit scalar multiples of `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`: topological splitting
  `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`: intertwining and compatibility
  with commuting operators.
* `ContinuousLinearMap.IsRieszColemanProjection.of_isRieszProjection`: lifting a Riesz projection
  of `B(u)` at `1` once `Q*(u) * E = 0` is known.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`: compression along continuous
  linear retracts.
* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`: row compactness on model spaces.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Projection

variable {R : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]

section Module

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` attached
to a polynomial `Q`: an idempotent `E` commuting with `u` and lying in the operator-norm closure of
`R[u]`, such that `Q*(u) * E = 0` for the reversal `Q* = Q.reverse`, and `Q*(u)` is invertible on
the complementary summand `ker E` with inverse again in the closure of `R[u]`.

Its range is `ker Q*(u)` and its kernel is `range Q*(u)`, yielding the closed stable splitting
`M = ker Q*(u) ⊕ range Q*(u)`. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : Polynomial R) (E : M →L[R] M) : Prop where
  /-- A Riesz–Coleman projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz–Coleman projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz–Coleman projection is an operator-norm limit of polynomials in the operator. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- `Q*(u)` vanishes on the range of the projection. -/
  aeval_reverse_mul_eq_zero : Polynomial.aeval u Q.reverse * E = 0
  /-- `Q*(u)` is invertible on the complementary summand, with inverse an operator-norm limit of
  polynomials in the operator. -/
  exists_inverse : ∃ w : M →L[R] M, Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

/-- Zero is always a Riesz–Coleman projection for the constant polynomial `1`, since `1*(u) = 1`. -/
theorem isRieszColemanProjection_one_zero (u : M →L[R] M) :
    IsRieszColemanProjection u 1 0 := by
  have hrev : (1 : Polynomial R).reverse = 1 := by rw [← C_1, reverse_C, C_1]
  refine ⟨IsIdempotentElem.zero, Commute.zero_right u,
    subset_closure (Subalgebra.zero_mem _), by simp [hrev], 1, ?_⟩
  simp [hrev, subset_closure (Subalgebra.one_mem _)]

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : Polynomial R}

/-- A Riesz–Coleman projection for the constant polynomial `1` is zero. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  have hrev : (1 : Polynomial R).reverse = 1 := by rw [← C_1, reverse_C, C_1]
  simpa [hrev] using hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection commutes with every polynomial in the operator. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Commute (Polynomial.aeval u p) E := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (hE.commute.pow_left n).smul_left a

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

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

/-- Every polynomial in `u` preserves the kernel of the Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Set.MapsTo (Polynomial.aeval u p) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval p).eq.symm) x)

/-- Every polynomial in `u` preserves the range of the Riesz–Coleman projection. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Set.MapsTo (Polynomial.aeval u p) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval p).eq.symm) x)

/-- The **complementary inverse** of a Riesz–Coleman projection: the inverse of `Q*(u)` on the
complementary summand `ker E`, extended by zero on `range E`, chosen from
`IsRieszColemanProjection.exists_inverse`. -/
noncomputable def inverse (hE : IsRieszColemanProjection u Q E) : M →L[R] M :=
  hE.exists_inverse.choose

/-- The complementary inverse is a right inverse of `Q*(u)` up to `1 - E`. -/
theorem aeval_reverse_mul_inverse (hE : IsRieszColemanProjection u Q E) :
    Polynomial.aeval u Q.reverse * hE.inverse = 1 - E := by
  obtain ⟨hw, -, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is a left inverse of `Q*(u)` up to `1 - E`. -/
theorem inverse_mul_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    hE.inverse * Polynomial.aeval u Q.reverse = 1 - E := by
  obtain ⟨-, hw, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse takes values in the kernel of the projection. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsRieszColemanProjection u Q E) : E * hE.inverse = 0 := by
  obtain ⟨-, -, hw, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse vanishes on the range of the projection. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) : hE.inverse * E = 0 := by
  obtain ⟨-, -, -, hw, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is an operator-norm limit of polynomials in the operator. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  obtain ⟨-, -, -, -, hw⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is the unique right inverse of `Q*(u)` up to `1 - E` taking values
in the kernel of the projection. -/
theorem eq_inverse (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Polynomial.aeval u Q.reverse * w = 1 - E) (hEw : E * w = 0) : w = hE.inverse := by
  calc w = (1 - E) * w := by
        rw [sub_mul (α := M →L[R] M), one_mul, hEw, sub_zero w]
    _ = hE.inverse * (Polynomial.aeval u Q.reverse * w) := by
        rw [← mul_assoc, hE.inverse_mul_aeval_reverse]
    _ = hE.inverse := by
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero, sub_zero hE.inverse]

/-- The complementary inverse preserves the kernel of the projection. -/
theorem mapsTo_ker_inverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using congr($(hE.mul_inverse_eq_zero) x)

/-- On the complementary summand, the complementary inverse is a left inverse of `Q*(u)`. -/
theorem inverse_aeval_reverse_apply (hE : IsRieszColemanProjection u Q E) {x : M}
    (hx : x ∈ E.ker) : hE.inverse (Polynomial.aeval u Q.reverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_aeval_reverse) x)

/-- On the complementary summand, the complementary inverse is a right inverse of `Q*(u)`. -/
theorem aeval_reverse_apply_inverse (hE : IsRieszColemanProjection u Q E) {x : M}
    (hx : x ∈ E.ker) : Polynomial.aeval u Q.reverse (hE.inverse x) = x := by
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
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm

/-- **The kernel of a Riesz–Coleman projection is `range Q*(u)`.** -/
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

/-- The range of `Q*(u)` is closed, even when the ambient module is infinite-dimensional. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- **The operator `Q*(u)` is a continuous linear automorphism of the complementary summand
`ker E`.** Its inverse is the restriction of `IsRieszColemanProjection.inverse`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx))
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

/-- The restriction of `Q*(u)` to the complementary summand `ker E` is a unit in the continuous
endomorphism ring of `ker E`. -/
theorem isUnit_restrict_ker (hE : IsRieszColemanProjection u Q E) :
    IsUnit ((Polynomial.aeval u Q.reverse).restrict
      (fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx)) := by
  refine isUnit_iff_exists.mpr ⟨hE.equivKer.symm.toContinuousLinearMap, ?_, ?_⟩
  · ext x
    exact congrArg Subtype.val (hE.equivKer.apply_symm_apply x)
  · ext x
    exact congrArg Subtype.val (hE.equivKer.symm_apply_apply x)

/-- From `Q* = lc(Q) + X · (Q*).divX` and `Q*(u) * E = 0`, we express `E` as `u` times a
polynomial in `u` times `E` whenever `lc(Q)` is a unit. -/
theorem eq_mul_aeval_divX_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    E = u * (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) * E := by
  have hrev : Q.reverse = C Q.leadingCoeff + X * Q.reverse.divX := by
    rw [← coeff_zero_reverse, add_comm, X_mul_divX_add]
  have hzero : Q.leadingCoeff • E + u * Polynomial.aeval u Q.reverse.divX * E = 0 := by
    have h := hE.aeval_reverse_mul_eq_zero
    rw [hrev, map_add, aeval_C, map_mul, aeval_X, Algebra.algebraMap_eq_smul_one,
      add_mul (R := M →L[R] M), smul_mul_assoc, one_mul] at h
    exact h
  have hc : Ring.inverse Q.leadingCoeff * Q.leadingCoeff = 1 :=
    Ring.inverse_mul_cancel Q.leadingCoeff hQ
  have h1 := congrArg (Ring.inverse Q.leadingCoeff • ·) hzero
  rw [smul_add, smul_smul, hc, one_smul, smul_zero, add_eq_zero_iff_eq_neg] at h1
  simpa [mul_smul_comm, smul_mul_assoc, neg_smul] using h1

/-- **Invertibility of `u` on `range E`.** When `Q` has invertible leading coefficient, `u`
restricts to a continuous linear automorphism of `range E = ker Q*(u)`, with explicit polynomial
inverse `-lc(Q)⁻¹ • (Q*).divX(u)`. Works also for `Q = 1` (`range E = ⊥`). -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp x.property
  have hmul : u * (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) * E = E :=
    (hE.eq_mul_aeval_divX_mul hQ).symm
  have hcomm : Commute u (Polynomial.aeval u Q.reverse.divX) := by
    simpa only [aeval_X] using (Commute.all X Q.reverse.divX).map (aeval u)
  refine ContinuousLinearEquiv.equivOfInverse
    (u.restrict fun _ hx ↦ hE.mapsTo_range hx)
    ((-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX).restrict fun x hx ↦
      E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx))
    (fun x ↦ Subtype.ext ?_) (fun x ↦ Subtype.ext ?_)
  · have hmul' :
        (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) * u * E = E := by
      calc (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) * u * E
          = -(Ring.inverse Q.leadingCoeff) • (Polynomial.aeval u Q.reverse.divX * u) * E := by
              rw [smul_mul_assoc]
        _ = -(Ring.inverse Q.leadingCoeff) • (u * Polynomial.aeval u Q.reverse.divX) * E := by
              rw [hcomm.eq]
        _ = u * (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) * E := by
              rw [mul_smul_comm]
        _ = E := hmul
    simpa only [restrict_apply, mul_apply_eq_comp, hfix] using congr($hmul' (x : M))
  · simpa only [restrict_apply, mul_apply_eq_comp, hfix] using congr($hmul (x : M))

/-- The range automorphism acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- The inverse range automorphism acts by `-lc(Q)⁻¹ • (Q*).divX(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      -(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX x :=
  (rfl)

/-- When `Q` has invertible leading coefficient, the restriction of `u` to `range E` is a unit
in the continuous endomorphism ring of `range E`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)) := by
  refine isUnit_iff_exists.mpr ⟨(hE.equivRange hQ).symm.toContinuousLinearMap, ?_, ?_⟩
  · ext x
    exact congrArg Subtype.val ((hE.equivRange hQ).apply_symm_apply x)
  · ext x
    exact congrArg Subtype.val ((hE.equivRange hQ).symm_apply_apply x)

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` for the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero (h := 1) hE'.isIdempotentElem
    (by simpa using hE.aeval_reverse_mul_eq_zero)
    (by simpa using hE'.aeval_reverse_mul_eq_zero)
    hw hw' hw₂ hw₂'

/-- Scaling `Q` by a unit of `R` preserves a Riesz–Coleman projection. -/
theorem C_mul_of_isUnit {a : R} (ha : IsUnit a) (hE : IsRieszColemanProjection u Q E) :
    IsRieszColemanProjection u (C a * Q) E := by
  obtain ⟨b, hab⟩ := ha.exists_left_inv
  have hrev : (C a * Q).reverse = C a * Q.reverse := by
    rw [reverse, reverse, natDegree_C_mul_eq_of_mul_eq_one hab, reflect_C_mul]
  have hae : Polynomial.aeval u (C a * Q).reverse = a • Polynomial.aeval u Q.reverse := by
    rw [hrev, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hwT : hE.inverse ∈ T := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
    exact hE.inverse_mem_closure_adjoin
  have hbw : b • hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    rw [← Subalgebra.topologicalClosure_coe]
    exact T.smul_mem hwT b
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_,
    b • hE.inverse, ?_, ?_, ?_, ?_, hbw⟩
  · rw [hae, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero, smul_zero]
  · rw [hae, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm a b, hab, one_smul]
    exact hE.aeval_reverse_mul_inverse
  · rw [hae, smul_mul_assoc, mul_smul_comm, smul_smul, hab, one_smul]
    exact hE.inverse_mul_aeval_reverse
  · rw [mul_smul_comm, hE.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hE.inverse_mul_eq_zero, smul_zero]

/-- Scaling `Q` by a unit of `R` does not change `IsRieszColemanProjection u Q E`. -/
theorem C_mul_iff {a : R} (ha : IsUnit a) :
    IsRieszColemanProjection u (C a * Q) E ↔ IsRieszColemanProjection u Q E := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.C_mul_of_isUnit ha⟩
  obtain ⟨b, hab⟩ := ha.exists_left_inv
  have hb : IsUnit b := IsUnit.of_mul_eq_one a hab
  have hQ : C b * (C a * Q) = Q := by rw [← mul_assoc, ← map_mul, hab, map_one, one_mul]
  exact hQ ▸ h.C_mul_of_isUnit hb

end IsRieszColemanProjection

end Module

section Intertwining

variable {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : Polynomial R}

namespace IsRieszColemanProjection

/-- **Intertwining Riesz–Coleman projections.** A linear map intertwining two operators also
intertwines their Riesz–Coleman projections for the same polynomial `Q`. The intertwiner need not
be continuous. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) : Function.Semiconj f E F := by
  have hlin : v.toLinearMap.comp f = f.comp u.toLinearMap := by
    ext x
    exact (hf x).symm
  have hQ : Function.Semiconj f (Polynomial.aeval u Q.reverse) (Polynomial.aeval v Q.reverse) := by
    intro x
    have := congr($(Module.End.aeval_comp_of_comp_eq hlin Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using this.symm
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hQ]
    have hz := congr($(hE.aeval_reverse_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero, coe_coe] using congr(f $hz)
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      apply LinearMap.mem_ker.mpr
      have hid := congr($(hE.isIdempotentElem.eq) x)
      simpa only [coe_coe, map_sub, mul_apply_eq_comp, sub_eq_zero] using hid.symm
    rw [← hE.range_aeval_reverse_eq_ker] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [coe_coe] at hy
    have hy' : f (x - E x) = (Polynomial.aeval v Q.reverse) (f y) := by
      rw [← hQ, hy]
    apply LinearMap.mem_ker.mp
    rw [← hF.range_aeval_reverse_eq_ker]
    exact ⟨f y, hy'.symm⟩
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
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners also carry the complementary inverses of `Q*(u)` and `Q*(v)` to one another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hlin : v.toLinearMap.comp f = f.comp u.toLinearMap := by
    ext x
    exact (hf x).symm
  have hQ : Function.Semiconj f (Polynomial.aeval u Q.reverse) (Polynomial.aeval v Q.reverse) := by
    intro x
    have := congr($(Module.End.aeval_comp_of_comp_eq hlin Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using this.symm
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
    _ = hF.inverse (f (x - E x)) := by
        have hz := congr($(hE.aeval_reverse_mul_inverse) x)
        exact congrArg (fun y ↦ hF.inverse (f y)) hz
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E := by
  ext x
  exact hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse := by
  ext x
  exact hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end IsRieszColemanProjection

end Intertwining

section Retract

variable {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] {i : M →L[R] N} {r : N →L[R] M}
  {u : M →L[R] M} {Q : Polynomial R}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a seminormed module `N`. If `E` is a Riesz–Coleman projection of the extension
`i ∘ u ∘ r` at `Q`, then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` at `Q`. No leading-unit
hypothesis on `Q` and no Hausdorffness of `N` are required. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v : N →L[R] N := i.comp (u.comp r)
  have hrv : u.toLinearMap.comp r.toLinearMap = r.toLinearMap.comp v.toLinearMap := by
    ext y; simp [v, hri']
  have hvi : v.toLinearMap.comp i.toLinearMap = i.toLinearMap.comp u.toLinearMap := by
    ext x; simp [v, hri']
  have hQr (y : N) :
      Polynomial.aeval u Q.reverse (r y) = r (Polynomial.aeval v Q.reverse y) := by
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using
      congr($(Module.End.aeval_comp_of_comp_eq hrv Q.reverse) y)
  have hQi (x : M) :
      Polynomial.aeval v Q.reverse (i x) = i (Polynomial.aeval u Q.reverse x) := by
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using
      congr($(Module.End.aeval_comp_of_comp_eq hvi Q.reverse) x)
  have hcomm_ir : Commute (i.comp r) v := by ext y; simp [v, hri']
  have hE' (y : N) : i (r (E y)) = E (i (r y)) :=
    congr($((hE.commute_of_commute hcomm_ir).eq) y)
  have hw' (y : N) : i (r (hE.inverse y)) = hE.inverse (i (r y)) :=
    congr($((hE.commute_inverse_of_commute hcomm_ir).eq) y)
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (v y) = v (E y) := congr($hE.commute.eq y).symm
  have hzero (y : N) : Polynomial.aeval v Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (hE.inverse.comp i), ?_, ?_, ?_, ?_,
      comp_comp_mem_closure_adjoin hri hE.inverse_mem_closure_adjoin⟩⟩
  · ext x; simp [hE', hri', hEE]
  · ext x; simpa [v, hri'] using congr(r $(hEv (i x))).symm
  · ext x; simpa [hzero] using hQr (E (i x))
  · ext x
    simpa [hri'] using
      (hQr (hE.inverse (i x))).trans (congr(r $(congr($(hE.aeval_reverse_mul_inverse) (i x)))))
  · ext x
    simpa [hQi, hri'] using congr(r $(congr($(hE.inverse_mul_aeval_reverse) (i x))))
  · ext x
    simpa only [mul_apply_eq_comp, comp_apply, hw', hri', zero_apply, map_zero] using
      congr(r $(congr($(hE.mul_inverse_eq_zero) (i x))))
  · ext x
    simpa only [mul_apply_eq_comp, comp_apply, hE', hri', zero_apply, map_zero] using
      congr(r $(congr($(hE.inverse_mul_eq_zero) (i x))))

end Retract

end Projection

section NormedRing

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

section Lift

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : Polynomial R}

namespace IsRieszColemanProjection

/-- If `u` commutes with `v` and `E` is a Riesz projection of `v` at `a` of order `h`, then `u`
commutes with `E` (valid on any seminormed module). -/
private theorem commute_of_isRieszProjection {v : M →L[R] M} {a : R} {h : ℕ}
    (hE : IsRieszProjection v a h E) (huv : Commute u v) : Commute u E := by
  set C_op : M →L[R] M := 1 - a • v
  have huC : Commute u C_op := huv.one_sub_smul_right (A := M →L[R] M) a
  ext x
  have hfixed : E (u (E x)) = u (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)).mp
    rw [hE.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    have hz := congr($(hE.pow_mul_eq_zero) x)
    have huc := congr($((huC.pow_right h).eq) (E x))
    simpa only [coe_coe, mul_apply_eq_comp, zero_apply, map_zero] using
      huc.symm.trans (congr(u $hz))
  have hkill : E (u (x - E x)) = 0 := by
    have h1 := hE.isIdempotentElem.one_sub_eq_pow_mul_pow (A := M →L[R] M)
      hE.pow_mul_eq_zero hE.one_sub_smul_mul_inverse hE.inverse_mul_one_sub_smul
    have hx : x - E x = (C_op ^ h) ((hE.inverse ^ h) x) := by
      simpa only [sub_apply, one_apply_eq_self, mul_apply_eq_comp] using congr($h1 x)
    have huc := congr($((huC.pow_right h).eq) ((hE.inverse ^ h) x))
    have hCE : E * C_op ^ h = 0 :=
      ((hE.commute_one_sub_smul.pow_left h).eq).symm.trans hE.pow_mul_eq_zero
    rw [hx]
    simpa only [mul_apply_eq_comp, zero_apply] using
      congr(E $huc).trans (congr($hCE (u ((hE.inverse ^ h) x))))
  have hsub : E (u x) - E (u (E x)) = 0 := by simpa only [map_sub] using hkill
  rw [hfixed, sub_eq_zero] at hsub
  exact hsub.symm

/-- **Lifting a Riesz projection of `B(u)` at `1`.** If `B = 1 - C c * Q*`, `E` is a Riesz
projection of `B(u)` at `1` of order `h`, and `Q*(u) * E = 0`, then `E` is a Riesz–Coleman
projection of `u` at `Q`. -/
theorem of_isRieszProjection {c : R} {h : ℕ}
    (hE : IsRieszProjection (Polynomial.aeval u (1 - C c * Q.reverse)) 1 h E)
    (hzero : Polynomial.aeval u Q.reverse * E = 0) :
    IsRieszColemanProjection u Q E := by
  set B : R[X] := 1 - C c * Q.reverse
  set v : M →L[R] M := Polynomial.aeval u B
  have hCop : (1 : M →L[R] M) - (1 : R) • v = c • Polynomial.aeval u Q.reverse := by
    simp [v, B, Algebra.algebraMap_eq_smul_one]
  -- `Algebra.adjoin R {v} ≤ Algebra.adjoin R {u}` because `v = B(u)`.
  have hadj : (Algebra.adjoin R {v} : Set (M →L[R] M)) ⊆
      (Algebra.adjoin R {u} : Set (M →L[R] M)) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Polynomial.aeval_mem_adjoin_singleton R u))
  have hcl : closure (Algebra.adjoin R {v} : Set (M →L[R] M)) ⊆
      closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := closure_mono hadj
  have huv : Commute u v := by simpa only [aeval_X] using (Commute.all X B).map (aeval u)
  -- Scale the Riesz complementary inverse `w` by `c`: `Q*(u) * (c • w) = (c • Q*(u)) * w = 1 - E`.
  set T := (Algebra.adjoin R {u}).topologicalClosure
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hwT : w ∈ T := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
    exact hcl hw
  have hcw : c • w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    rw [← Subalgebra.topologicalClosure_coe]
    exact T.smul_mem hwT c
  refine ⟨hE.isIdempotentElem, commute_of_isRieszProjection hE huv, hcl hE.mem_closure_adjoin,
    hzero, c • w, ?_, ?_, ?_, ?_, hcw⟩
  · rw [mul_smul_comm, ← smul_mul_assoc, ← hCop]
    exact hw₁
  · rw [smul_mul_assoc, ← mul_smul_comm, ← hCop]
    exact hw₂
  · rw [mul_smul_comm, hw₃, smul_zero]
  · rw [smul_mul_assoc, hw₄, smul_zero]

end IsRieszColemanProjection

end Lift

section ModelSpace

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- The explicit **Riesz–Coleman projector** of an endomorphism `u` of `C₀(I, R)` attached to a
polynomial `Q`: the Riesz projector at `1` of order `deg Q` of `B(u)`, where
`B = 1 - lc(Q)⁻¹ Q*`. When `u` is row compact and `H_u = Q * S` is a coprime factorisation with
`lc(Q)` a unit and `S` entire, this is the unique Riesz–Coleman projection of `u` at `Q`; otherwise
it is a junk value. -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : Polynomial R) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
    Q.natDegree

/-- Unfolding of `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : Polynomial R) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
        Q.natDegree :=
  (rfl)

/-- For `Q = 1`, the explicit Riesz–Coleman projector is zero. -/
@[simp]
theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  simp [rieszColemanProjection_def, rieszProjection_order_zero]

/-- Scaling `Q` by a unit of `R` leaves the explicit Riesz–Coleman projector unchanged (with no
leading-unit hypothesis on `Q`). -/
theorem rieszColemanProjection_C_mul {a : R} (ha : IsUnit a)
    (u : C₀(I, R) →L[R] C₀(I, R)) (Q : Polynomial R) :
    u.rieszColemanProjection (C a * Q) = u.rieszColemanProjection Q := by
  obtain ⟨b, hab⟩ := ha.exists_left_inv
  have hdeg : (C a * Q).natDegree = Q.natDegree := natDegree_C_mul_eq_of_mul_eq_one hab
  have hlc : (C a * Q).leadingCoeff = a * Q.leadingCoeff := by
    rw [leadingCoeff, hdeg, coeff_C_mul, ← leadingCoeff]
  have hrev : (C a * Q).reverse = C a * Q.reverse := by
    rw [reverse, reverse, hdeg, reflect_C_mul]
  have hinv : Ring.inverse (a * Q.leadingCoeff) * a = Ring.inverse Q.leadingCoeff := by
    by_cases hQ : IsUnit Q.leadingCoeff
    · have h2 : Ring.inverse (a * Q.leadingCoeff) * (a * Q.leadingCoeff) = 1 :=
        Ring.inverse_mul_cancel _ (ha.mul hQ)
      calc Ring.inverse (a * Q.leadingCoeff) * a
          = Ring.inverse (a * Q.leadingCoeff) * a *
              (Q.leadingCoeff * Ring.inverse Q.leadingCoeff) := by
                rw [Ring.mul_inverse_cancel _ hQ, mul_one]
        _ = (Ring.inverse (a * Q.leadingCoeff) * (a * Q.leadingCoeff)) *
              Ring.inverse Q.leadingCoeff := by ring
        _ = Ring.inverse Q.leadingCoeff := by rw [h2, one_mul]
    · have hna : ¬ IsUnit (a * Q.leadingCoeff) := fun h ↦ hQ (isUnit_of_mul_isUnit_right h)
      rw [Ring.inverse_non_unit _ hQ, Ring.inverse_non_unit _ hna, zero_mul]
  rw [rieszColemanProjection_def, rieszColemanProjection_def, hdeg, hlc, hrev, ← mul_assoc,
    ← map_mul, hinv]

variable [IsUltrametricDist R]

/-- **Row compactness of a Riesz–Coleman projection.** When `Q` has invertible leading coefficient,
every Riesz–Coleman projection of a row-compact operator on `C₀(I, R)` is row compact. -/
theorem IsRieszColemanProjection.isRowCompact {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [hE.eq_mul_aeval_divX_mul hQ]
  simpa only [mul_def] using (hu.comp_clm _).comp_clm E

variable [CompleteSpace R]

/-- The finite spectral summand `ker Q*(u)` of a row-compact operator on `C₀(I, R)` is finitely
generated whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact (hE.isRowCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The finite spectral summand `ker Q*(u)` of a row-compact operator on `C₀(I, R)` is projective
over `R` whenever `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact (hE.isRowCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

end ModelSpace

end NormedRing

end ContinuousLinearMap
