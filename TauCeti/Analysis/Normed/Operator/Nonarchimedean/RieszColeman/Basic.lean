/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
public import TauCeti.Analysis.Normed.Operator.RowCompact.PrModule
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# The Riesz–Coleman projection attached to a polynomial factor

Let `R` be a normed commutative ring with Tate scalars, `M` a seminormed `R`-module with bounded
scalar action, `u : M →L[R] M` a continuous endomorphism, and `Q : Polynomial R` a polynomial with
reversal `Q* = Q.reverse`. A **Riesz–Coleman projection** of `u` at `Q`
(`ContinuousLinearMap.IsRieszColemanProjection`) is an idempotent `E : M →L[R] M` commuting with
`u` and lying in the operator-norm closure of `R[u]`, such that `Q*(u) * E = 0` and `Q*(u)` is
invertible on the complementary summand `range (1 - E)`, with inverse again in the closure of
`R[u]`.

Such a projection splits `M` into the topological complements `ker Q*(u) = range E` and
`range Q*(u) = ker E` (`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range_aeval_reverse`), on the second
of which `Q*(u)` is a continuous linear automorphism
(`ContinuousLinearMap.IsRieszColemanProjection.equivKer`). It is unique
(`ContinuousLinearMap.IsRieszColemanProjection.unique`), and for `Q = 1` it is necessarily zero
(`ContinuousLinearMap.isRieszColemanProjection_one_iff`).

When the leading coefficient `Q*(0)` of `Q` is a unit, the identity
`1 - lc(Q)⁻¹ Q*(u) = u * (-lc(Q)⁻¹ Q*.divX(u))` yields two consequences at once: `u` restricts to
a continuous linear automorphism of the spectral summand `range E = ker Q*(u)`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`), and `E` factors through `u` so that
every Riesz–Coleman projection of a row-compact operator is row compact
(`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`); over a complete ultrametric Tate
ring, the projection of a `(Pr)`-compact operator therefore has finitely generated projective
range (`ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
`ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`).

Riesz–Coleman projections are functorial with respect to arbitrary (not necessarily continuous)
linear intertwiners (`ContinuousLinearMap.IsRieszColemanProjection.semiconj`), commute with every
bounded operator commuting with `u`
(`ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`), compress along continuous
linear retracts (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and commute
with bounded coefficient extension on model spaces when `Q` has unit leading coefficient
(`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector of `u` attached to a
  polynomial `Q` via its reversal `Q* = Q.reverse`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on `ker E`,
  extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `Q` has unit leading
  coefficient, `u` as a continuous linear automorphism of `range E`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range_aeval_reverse`: the closed
  stable splitting `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of the projection.
* `ContinuousLinearMap.isRieszColemanProjection_one_iff`: for `Q = 1`, the unique projection is
  zero.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`: functoriality and
  compatibility with commuting operators.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.eq_comp_comp_of_retract`: compression and
  extension along continuous linear retracts.
* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: compactness of the projection when
  `Q` has unit leading coefficient.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`: preservation under bounded base
  change on model spaces.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  Algebra Number Theory **13** (2019), §2.2.
-/

public section

open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` at a
polynomial `Q`: an idempotent `E` commuting with `u` and lying in the operator-norm closure of
`R[u]`, such that `Q*(u) * E = 0` for the reversal `Q* = Q.reverse`, and `Q*(u)` is invertible on
the complementary summand `range (1 - E)` with inverse again in the closure of `R[u]`. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : Polynomial R) (E : M →L[R] M) : Prop where
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
    w * Polynomial.aeval u Q.reverse = 1 - E ∧
    E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : Polynomial R}

/-- A Riesz–Coleman projection commutes with every polynomial in the operator. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Commute (Polynomial.aeval u p) E := by
  have hlin : (u : M →ₗ[R] M) ∘ₗ (E : M →ₗ[R] M) = (E : M →ₗ[R] M) ∘ₗ (u : M →ₗ[R] M) := by
    simpa only [← toLinearMap_comp, ← mul_def] using
      congrArg ContinuousLinearMap.toLinearMap hE.commute.eq
  have hp := Module.End.aeval_comp_of_comp_eq hlin p
  exact ContinuousLinearMap.coe_injective (by simpa only [mul_def, toLinearMap_comp,
    toLinearMap_aeval] using hp)

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

/-- If `Q*(u)` is already invertible on the whole module, its Riesz–Coleman projection is zero. -/
theorem eq_zero_of_isUnit_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (h : IsUnit (Polynomial.aeval u Q.reverse)) : E = 0 :=
  h.mul_right_eq_zero.mp hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection for `Q = 1` is zero. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 :=
  hE.eq_zero_of_isUnit_aeval_reverse (by
    rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1, map_one]
    exact isUnit_one)

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

/-- Every polynomial in the operator preserves the kernel of a Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Set.MapsTo (Polynomial.aeval u p) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval p).eq.symm) x)

/-- Every polynomial in the operator preserves the range of a Riesz–Coleman projection. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Set.MapsTo (Polynomial.aeval u p) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval p).eq.symm) x)

/-- The **complementary inverse** of a Riesz–Coleman projection: the inverse of `Q*(u)` on
`ker E = range (1 - E)`, extended by zero on `range E`, chosen from
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

/-- The complementary inverse takes values in the kernel of the Riesz–Coleman projection. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsRieszColemanProjection u Q E) : E * hE.inverse = 0 := by
  obtain ⟨-, -, hw, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse vanishes on the range of the Riesz–Coleman projection. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) : hE.inverse * E = 0 := by
  obtain ⟨-, -, -, hw, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is an operator-norm limit of polynomials in the operator. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  obtain ⟨-, -, -, -, hw⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is the unique right inverse of `Q*(u)` up to `1 - E` that takes
values in the kernel of the Riesz–Coleman projection. -/
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

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` at the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  obtain ⟨w, hw₁, hw₂, -⟩ := hE.exists_inverse
  obtain ⟨w', hw₁', hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero (h := 1) hE'.isIdempotentElem
    (by simpa using hE.aeval_reverse_mul_eq_zero) (by simpa using hE'.aeval_reverse_mul_eq_zero)
    hw₁ hw₂ hw₁' hw₂'

/-- **The range of a Riesz–Coleman projection is `ker Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have h := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm

/-- **The range of `Q*(u)` is the kernel of the Riesz–Coleman projection.** -/
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
  · exact hE.aeval_reverse_apply_inverse (LinearMap.mem_ker.mpr hx)

/-- **Topological splitting.** `ker Q*(u)` and `range Q*(u)` are topological complements. -/
theorem isTopCompl_ker_range_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The range of `Q*(u)` is closed, being the kernel of the continuous projection `E`. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- The operator `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`,
with inverse given by the restriction of `IsRieszColemanProjection.inverse`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx)
    (hE.inverse.restrict fun _ hx ↦ hE.mapsTo_ker_inverse hx)
    (fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))
    (fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))

/-- The complementary automorphism acts by `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x :=
  (rfl)

/-- The inverse of the complementary automorphism acts by `IsRieszColemanProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- **Invertibility of `u` on the spectral summand.** When `Q` has unit leading coefficient, `u`
restricts to a continuous linear automorphism of `range E = ker Q*(u)`, with inverse given by
`-lc(Q)⁻¹ Q*.divX(u)`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range :=
  let g : M →L[R] M := -(Ring.inverse Q.leadingCoeff • Polynomial.aeval u Q.reverse.divX)
  have hmaps_g : Set.MapsTo g E.range E.range := fun x hx ↦
    E.range.neg_mem (E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx))
  have hcomm_ug : Commute u g := by
    have hcomm : Commute u (Polynomial.aeval u Q.reverse.divX) := by
      simpa only [Polynomial.aeval_X] using
        (Commute.all Polynomial.X Q.reverse.divX).map (Polynomial.aeval u)
    exact (hcomm.smul_right _).neg_right
  have hmul : (1 : M →L[R] M) - Ring.inverse Q.leadingCoeff • Polynomial.aeval u Q.reverse =
      u * g := Polynomial.one_sub_smul_aeval_reverse_eq_mul (Ring.inverse_mul_cancel _ hQ) u
  have happly (x : E.range) : u (g x) = x := by
    have hzero : Polynomial.aeval u Q.reverse x = 0 := by
      have hx : (x : M) ∈ LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) :=
        hE.range_eq_ker ▸ x.property
      exact LinearMap.mem_ker.mp hx
    have h := congr($hmul (x : M))
    simpa only [sub_apply, one_apply_eq_self, smul_apply, hzero, smul_zero, sub_zero,
      mul_apply_eq_comp] using h.symm
  ContinuousLinearEquiv.equivOfInverse
    (u.restrict fun _ hx ↦ hE.mapsTo_range hx)
    (g.restrict fun _ hx ↦ hmaps_g hx)
    (fun x ↦ Subtype.ext (by
      have h := congr($(hcomm_ug.eq) (x : M))
      simpa only [restrict_apply, mul_apply_eq_comp, happly x] using h.symm))
    (fun x ↦ Subtype.ext (happly x))

/-- The spectral-summand automorphism acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- The inverse of `u` on the spectral summand acts by `-lc(Q)⁻¹ Q*.divX(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      -(Ring.inverse Q.leadingCoeff • Polynomial.aeval u Q.reverse.divX) x :=
  (rfl)

/-- When `Q` has unit leading coefficient, the restriction of `u` to `range E` is a unit in the
endomorphism ring of `range E`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict fun _ hx ↦ hE.mapsTo_range hx) := by
  refine isUnit_iff_exists.mpr ⟨((hE.equivRange hQ).symm : E.range →L[R] E.range), ?_, ?_⟩
  · ext x : 1
    exact (hE.equivRange hQ).apply_symm_apply x
  · ext x : 1
    exact (hE.equivRange hQ).symm_apply_apply x

/-- Factorisation `E = u * (-lc(Q)⁻¹ Q*.divX(u)) * E`, expressing a Riesz–Coleman projection as a
multiple of `u` whenever `Q` has unit leading coefficient. -/
theorem eq_mul_neg_smul_aeval_divX_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    E = u * (-(Ring.inverse Q.leadingCoeff • Polynomial.aeval u Q.reverse.divX)) * E := by
  rw [← Polynomial.one_sub_smul_aeval_reverse_eq_mul (Ring.inverse_mul_cancel _ hQ) u,
    sub_mul (α := M →L[R] M), one_mul, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero, smul_zero,
    sub_zero (G := M →L[R] M)]

end IsRieszColemanProjection

/-- For the constant polynomial `1`, zero is a Riesz–Coleman projection. -/
theorem isRieszColemanProjection_one_zero (u : M →L[R] M) :
    IsRieszColemanProjection u 1 0 where
  isIdempotentElem := IsIdempotentElem.zero
  commute := Commute.zero_right u
  mem_closure_adjoin := subset_closure (Subalgebra.zero_mem _)
  aeval_reverse_mul_eq_zero := mul_zero _
  exists_inverse := ⟨1, by rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]; simp,
    by rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]; simp, zero_mul _, mul_zero _,
    subset_closure (Subalgebra.one_mem _)⟩

/-- For `Q = 1`, the unique Riesz–Coleman projection is zero. -/
@[simp]
theorem isRieszColemanProjection_one_iff {u E : M →L[R] M} :
    IsRieszColemanProjection u 1 E ↔ E = 0 :=
  ⟨IsRieszColemanProjection.eq_zero_of_one, fun h ↦ h ▸ isRieszColemanProjection_one_zero u⟩

end Module

section Intertwining

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : Polynomial R}

namespace IsRieszColemanProjection

/-- **Functoriality of Riesz–Coleman projections.** Any linear map intertwining `u` and `v`
intertwines their Riesz–Coleman projections at the same polynomial `Q`. Continuity of the
intertwiner is not needed. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  have hf_comp : (v : N →ₗ[R] N) ∘ₗ f = f ∘ₗ (u : M →ₗ[R] M) := LinearMap.ext fun x ↦ (hf x).symm
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hf_comp Q.reverse) x
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  intro x
  -- `f` sends `E x ∈ ker Q*(u)` into `ker Q*(v) = range F`.
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hfQ]
    have hz := congr($(hE.aeval_reverse_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  -- `f` sends `x - E x ∈ ker E = range Q*(u)` into `range Q*(v) = ker F`.
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
    exact ⟨f y, by simp only [coe_coe, ← hfQ, hy]⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the spectral summand into the corresponding summand. -/
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

/-- An intertwiner carries complementary inverses to one another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hf_comp : (v : N →ₗ[R] N) ∘ₗ f = f ∘ₗ (u : M →ₗ[R] M) := LinearMap.ext fun x ↦ (hf x).symm
  have hfQ (x : M) : f (Polynomial.aeval u Q.reverse x) = Polynomial.aeval v Q.reverse (f x) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hf_comp Q.reverse) x
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse (Polynomial.aeval v Q.reverse (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f (Polynomial.aeval u Q.reverse (hE.inverse x))) := by rw [← hfQ]
    _ = hF.inverse (f (x - E x)) := by
        have hz := congr($(hE.aeval_reverse_mul_inverse) x)
        exact congrArg (fun y ↦ hF.inverse (f y)) hz
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj hE w.toLinearMap (fun x ↦ congr($(hw.eq) x)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of every
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj_inverse hE w.toLinearMap (fun x ↦ congr($(hw.eq) x)) x

end IsRieszColemanProjection

end Intertwining

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M} {Q : Polynomial R}

/-- **Extension identity along a retract.** For a retract `r ∘ i = id` and a polynomial `Q` with
unit leading coefficient, any Riesz–Coleman projection `E` of the extension `i ∘ u ∘ r` vanishes on
the complementary block `ker r` and is therefore the extension `i ∘ (r ∘ E ∘ i) ∘ r` of its
compression. -/
theorem IsRieszColemanProjection.eq_comp_comp_of_retract (hri : r.comp i = .id R M)
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    E = i.comp ((r.comp (E.comp i)).comp r) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hir_v : i.comp r * i.comp (u.comp r) = i.comp (u.comp r) := ext fun y ↦ by simp [hri']
  have hir_E : i.comp r * E = E := by
    have hEfac := hE.eq_mul_neg_smul_aeval_divX_mul hQ
    calc i.comp r * E = i.comp r * _ := congrArg (i.comp r * ·) hEfac
      _ = E := by rw [← mul_assoc, ← mul_assoc, hir_v, ← hEfac]
  have hcomm_E : Commute (i.comp r) E :=
    hE.commute_of_commute (ext fun y ↦ by simp [hri'])
  calc E = i.comp r * E := hir_E.symm
    _ = i.comp r * (i.comp r * E) := congrArg (i.comp r * ·) hir_E.symm
    _ = i.comp r * (E * i.comp r) := by rw [hcomm_E.eq]
    _ = i.comp ((r.comp (E.comp i)).comp r) := ext fun _ ↦ rfl

/-- Linear equivalence between the range of the compressed projection `r ∘ E ∘ i` and the range of
`E`, for a retract `r ∘ i = id` and a polynomial `Q` with unit leading coefficient. -/
noncomputable def IsRieszColemanProjection.rangeEquivOfRetract (hri : r.comp i = .id R M)
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    LinearMap.range ((r : N →ₗ[R] M) ∘ₗ (E : N →ₗ[R] N) ∘ₗ (i : M →ₗ[R] N)) ≃ₗ[R] E.range :=
  (ContinuousLinearMap.rangeEquivOfRetract (r.comp (E.comp i)) hri).trans
    (LinearEquiv.ofEq _ _ <| by
      simpa only [toLinearMap_comp] using
        congrArg (fun f : N →L[R] N ↦ f.range) (hE.eq_comp_comp_of_retract hri hQ).symm)

/-- The forward map of `rangeEquivOfRetract` is induced by `i`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_apply (hri : r.comp i = .id R M)
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E)
    (hQ : IsUnit Q.leadingCoeff)
    (x : LinearMap.range ((r : N →ₗ[R] M) ∘ₗ (E : N →ₗ[R] N) ∘ₗ (i : M →ₗ[R] N))) :
    (hE.rangeEquivOfRetract hri hQ x : N) = i x :=
  ContinuousLinearMap.coe_rangeEquivOfRetract_apply (r.comp (E.comp i)) hri x

/-- The inverse map of `rangeEquivOfRetract` is induced by `r`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_symm_apply (hri : r.comp i = .id R M)
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E)
    (hQ : IsUnit Q.leadingCoeff) (y : E.range) :
    ((hE.rangeEquivOfRetract hri hQ).symm y : M) = r y :=
  ContinuousLinearMap.coe_rangeEquivOfRetract_symm_apply (r.comp (E.comp i)) hri _

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a normed module `N`. If `E` is a Riesz–Coleman projection of the extension
`i ∘ u ∘ r` at `Q`, then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` at `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract [IsBoundedSMul R M]
    {N : Type*} [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
    {i : M →L[R] N} {r : N →L[R] M} (hri : r.comp i = .id R M) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr_lin : (u : M →ₗ[R] M) ∘ₗ (r : N →ₗ[R] M) =
      (r : N →ₗ[R] M) ∘ₗ (i.comp (u.comp r) : N →ₗ[R] N) :=
    LinearMap.ext fun y ↦ by simp [hri']
  have hi_lin : (i.comp (u.comp r) : N →ₗ[R] N) ∘ₗ (i : M →ₗ[R] N) =
      (i : M →ₗ[R] N) ∘ₗ (u : M →ₗ[R] M) :=
    LinearMap.ext fun x ↦ by simp [hri']
  have hrQ (y : N) :
      Polynomial.aeval u Q.reverse (r y) =
        r (Polynomial.aeval (i.comp (u.comp r)) Q.reverse y) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hr_lin Q.reverse) y
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  have hiQ (x : M) :
      Polynomial.aeval (i.comp (u.comp r)) Q.reverse (i x) =
        i (Polynomial.aeval u Q.reverse x) := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hi_lin Q.reverse) x
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hQE (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simp [hrQ, hQE]
  · ext x
    simpa [hrQ, hri'] using congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    simpa [← hiQ, hri'] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x
    simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x
    simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

end Retract

section Compact

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]

/-- A Riesz–Coleman projection of a row-compact operator on a model space is row compact whenever
`Q` has unit leading coefficient, including `Q = 1`. -/
theorem IsRieszColemanProjection.isRowCompact {I : Type*} [TopologicalSpace I]
    [DiscreteTopology I] [DecidableEq I] {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [hE.eq_mul_neg_smul_aeval_divX_mul hQ]
  simpa only [mul_def] using (hu.comp_clm _).comp_clm E

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : Polynomial R}

/-- A Riesz–Coleman projection of a row-compact endomorphism of a module with property (Pr) is row
compact whenever `Q` has unit leading coefficient, including `Q = 1`. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [hE.eq_mul_neg_smul_aeval_divX_mul hQ]
  simpa only [mul_def] using (hu.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source

variable [CompleteSpace R]

/-- The range of a Riesz–Coleman projection of a row-compact operator on a module with property
(Pr) is finitely generated whenever `Q` has unit leading coefficient. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) : Module.Finite R E.range :=
  (hE.isPrCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact operator on a module with property
(Pr) is projective over `R` whenever `Q` has unit leading coefficient. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isPrCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- For a Riesz–Coleman projection of a row-compact operator on a (Pr) module, `ker Q*(u)` is
finitely generated whenever `Q` has unit leading coefficient. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hu hQ

/-- For a Riesz–Coleman projection of a row-compact operator on a (Pr) module, `ker Q*(u)` is
projective over `R` whenever `Q` has unit leading coefficient. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hu hQ

end Compact

section BaseChange

variable {J R S : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- **Riesz–Coleman projections under bounded base change.** If `Q` has unit leading coefficient,
the coefficientwise extension of a Riesz–Coleman projection of `u` at `Q` is a Riesz–Coleman
projection of the extension of `u` at `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs [TauCeti.NormedRing.IsTate S]
    {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev := Polynomial.reverse_map_of_isUnit_leadingCoeff f hQ
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_eq_zero
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs [TauCeti.NormedRing.IsTate S]
    {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf := by
  have hrev := Polynomial.reverse_map_of_isUnit_leadingCoeff f hQ
  symm
  refine (hE.mapCoeffs hQ f hf).eq_inverse ?_ ?_
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_inverse
  · rw [← mapCoeffs_mul, hE.mul_inverse_eq_zero, mapCoeffs_zero]

end BaseChange

end ContinuousLinearMap
