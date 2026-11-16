/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
import Mathlib.Algebra.Polynomial.Inductions
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projections on seminormed modules

Let `R` be a seminormed commutative ring with Tate scalars (`TauCeti.NormedRing.IsTate R`), `M` a
seminormed `R`-module with bounded scalar multiplication, `u : M →L[R] M` a continuous linear
endomorphism, and `Q : Polynomial R` a polynomial with reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
an idempotent `E`, commuting with `u` and lying in the operator-norm closure of the polynomials in
`u`, such that `Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand
`range (1 - E)`, with complementary inverse again in the closure of the polynomials in `u`.

Every Riesz–Coleman projection splits `M` into the closed `u`-invariant topological complements
`range E = ker Q*(u)` and `ker E = range Q*(u)`
(`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range_aeval_reverse`), with `Q*(u)`
restricting to a continuous linear automorphism of `ker E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivKer`). When `Q` has invertible leading
coefficient, `u` itself restricts to a continuous linear automorphism of `range E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`).

Such a projection is unique (`ContinuousLinearMap.IsRieszColemanProjection.unique`), equals `0`
when `Q = 1`, is unchanged by scaling `Q` by a unit scalar, is intertwined by every linear map
intertwining the underlying operators (`ContinuousLinearMap.IsRieszColemanProjection.semiconj`),
commutes with every bounded operator commuting with `u`, and compresses along continuous linear
retracts (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector of `u` for a polynomial
  `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on the
  complementary summand `ker E`, extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `Q` has invertible leading
  coefficient, `u` as a continuous linear automorphism of `range E`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range_aeval_reverse`: the closed
  splitting `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of the projector.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`: functoriality under
  intertwiners and commuting operators.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`: compression and
  extension along continuous linear retracts.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` for a
polynomial `Q`: an idempotent `E` commuting with `u` and lying in the operator-norm closure of
the polynomials in `u`, such that `Q*(u) * E = 0` (for `Q* = Q.reverse`) and `Q*(u)` is
invertible on the complementary summand `range (1 - E)`, with inverse again in the closure of the
polynomials in `u`. -/
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

/-- For `Q = 1`, the zero projection is a Riesz–Coleman projection of every endomorphism. -/
theorem zero_one (u : M →L[R] M) : IsRieszColemanProjection u 1 0 := by
  have hrev : (1 : Polynomial R).reverse = 1 := by
    rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]
  refine ⟨IsIdempotentElem.zero, Commute.zero_right u,
    subset_closure (Subalgebra.zero_mem _), by simp [hrev], 1, ?_, ?_,
    zero_mul _, mul_zero _, subset_closure (Subalgebra.one_mem _)⟩
  · simp [hrev]
  · simp [hrev]

/-- For `Q = 1`, any Riesz–Coleman projection is zero. -/
theorem eq_zero_of_eq_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  have hrev : (1 : Polynomial R).reverse = 1 := by
    rw [← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]
  simpa [hrev] using hE.aeval_reverse_mul_eq_zero

/-- Scaling `Q` by a unit scalar preserves Riesz–Coleman projections. -/
theorem of_C_mul (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E := by
  obtain ⟨c', hc'⟩ := hc.exists_left_inv
  have hrev : (Polynomial.C c * Q).reverse = Polynomial.C c * Q.reverse := by
    rw [Polynomial.reverse, Polynomial.reverse,
      Polynomial.natDegree_C_mul_eq_of_mul_eq_one hc', Polynomial.reflect_C_mul]
  have haeval : Polynomial.aeval u (Polynomial.C c * Q).reverse =
      c • Polynomial.aeval u Q.reverse := by
    rw [hrev, map_mul, Polynomial.aeval_C, Algebra.smul_def]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have : IsTopologicalSemiring (M →L[R] M) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hwT : c' • w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
    have hmem : w ∈ T := by rwa [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
    have hsmul : c' • w ∈ T := T.smul_mem hmem c'
    rwa [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hsmul
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_,
    c' • w, ?_, ?_, ?_, ?_, hwT⟩
  · rw [haeval, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero, smul_zero]
  · rw [haeval, smul_mul_smul_comm, mul_comm c c', hc', one_smul, hw₁]
  · rw [haeval, smul_mul_smul_comm, hc', one_smul, hw₂]
  · rw [mul_smul_comm, hw₃, smul_zero]
  · rw [smul_mul_assoc, hw₄, smul_zero]

/-- Scaling `Q` by a unit scalar does not change the Riesz–Coleman projections of `u`. -/
theorem iff_C_mul {c : R} (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E ↔ IsRieszColemanProjection u Q E := by
  obtain ⟨c', hc'⟩ := hc.exists_left_inv
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_C_mul hc⟩
  have hQ : Polynomial.C c' * (Polynomial.C c * Q) = Q := by
    rw [← mul_assoc, ← Polynomial.C_mul, hc', Polynomial.C_1, one_mul]
  simpa only [hQ] using h.of_C_mul (IsUnit.of_mul_eq_one _ hc')

/-- A Riesz–Coleman projection commutes with every polynomial in the operator. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Commute (Polynomial.aeval u p) E := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_left hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (Algebra.commutes c E) (hE.commute.pow_left n)

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

/-- Every polynomial in the operator preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (p : Polynomial R) :
    Set.MapsTo (Polynomial.aeval u p) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval p).eq.symm) x)

/-- Every polynomial in the operator preserves the range of its Riesz–Coleman projection. -/
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
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero,
          sub_zero hE.inverse]

/-- The complementary inverse preserves the kernel of the Riesz–Coleman projection. -/
theorem mapsTo_ker_inverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using
    congr($(hE.mul_inverse_eq_zero) x)

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

/-- **The range of a Riesz–Coleman projection is `ker Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have h := congr($(hE.inverse_mul_aeval_reverse) x).symm
    simp only [mul_apply_eq_comp, hx, map_zero, sub_apply, one_apply_eq_self,
      sub_eq_zero] at h
    exact h.symm

/-- **The range of `Q*(u)` is the kernel of a Riesz–Coleman projection**, hence the complementary
spectral summand. -/
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
theorem isTopCompl_ker_range_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The range of `Q*(u)` is closed, as the kernel of the continuous Riesz–Coleman projection. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`, with inverse
the restriction of `IsRieszColemanProjection.inverse`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval _ hx))
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

/-- When `Q` has invertible leading coefficient, `E` factors through `u` via the quotient
polynomial `(1 - lc(Q)⁻¹ • Q*) / X`. -/
theorem mul_aeval_divX_mul_eq (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    u * Polynomial.aeval u
      (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse).divX * E = E := by
  have hc : Ring.inverse Q.leadingCoeff * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : Polynomial R := 1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse
  have hB0 : B.coeff 0 = 0 := by
    simp [B, hc]
  have hXB : Polynomial.X * B.divX = B := by
    simpa only [hB0, map_zero, add_zero] using Polynomial.X_mul_divX_add B
  have h1 : u * Polynomial.aeval u B.divX =
      1 - Ring.inverse Q.leadingCoeff • Polynomial.aeval u Q.reverse := by
    have := congrArg (Polynomial.aeval u) hXB
    simpa [B, Algebra.smul_def] using this
  rw [h1, sub_mul (α := M →L[R] M), one_mul, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero,
    smul_zero, sub_zero]

/-- When `Q` has invertible leading coefficient, `u` restricts to a continuous linear automorphism
of `range E = ker Q*(u)`, with inverse given by evaluating `(1 - lc(Q)⁻¹ • Q*) / X` at `u`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  set B₁ := (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse).divX
  have hmul : u * Polynomial.aeval u B₁ * E = E := hE.mul_aeval_divX_mul_eq hQ
  have hcomm : Commute u (Polynomial.aeval u B₁) := by
    simpa only [Polynomial.aeval_X] using (Commute.all Polynomial.X B₁).map (Polynomial.aeval u)
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
  exact ContinuousLinearEquiv.equivOfInverse
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx))
    ((Polynomial.aeval u B₁).restrict (fun _ hx ↦ hE.mapsTo_range_aeval B₁ hx))
    (fun x ↦ Subtype.ext (by
      have h := congr($hmul (x : M))
      rw [hcomm.eq] at h
      simpa only [restrict_apply, mul_apply_eq_comp, hfix] using h))
    (fun x ↦ Subtype.ext (by
      have h := congr($hmul (x : M))
      simpa only [restrict_apply, mul_apply_eq_comp, hfix] using h))

/-- On `range E`, the automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- On `range E`, the inverse of `equivRange` acts by evaluating `(1 - lc(Q)⁻¹ • Q*) / X` at
`u`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse).divX x :=
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

/-- A linear map intertwining two operators also intertwines their Riesz–Coleman projections for
the same polynomial `Q`. Continuity of the intertwiner is unnecessary. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  have hf' : v.toLinearMap ∘ₗ f = f ∘ₗ u.toLinearMap :=
    LinearMap.ext fun x ↦ (hf x).symm
  have hfa : Function.Semiconj f (Polynomial.aeval u Q.reverse) (Polynomial.aeval v Q.reverse) := by
    intro x
    have h := congr($(Module.End.aeval_comp_of_comp_eq hf' Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hfa]
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
    exact ⟨f y, by simpa only [coe_coe, hy] using (hfa y).symm⟩
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

/-- An intertwiner carries the complementary inverses of Riesz–Coleman projections to one
another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hf' : v.toLinearMap ∘ₗ f = f ∘ₗ u.toLinearMap :=
    LinearMap.ext fun x ↦ (hf x).symm
  have hfa : Function.Semiconj f (Polynomial.aeval u Q.reverse) (Polynomial.aeval v Q.reverse) := by
    intro x
    have h := congr($(Module.End.aeval_comp_of_comp_eq hf' Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm
  have hEF := hE.semiconj hF f hf
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse (Polynomial.aeval v Q.reverse (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f (Polynomial.aeval u Q.reverse (hE.inverse x))) := by rw [hfa]
    _ = hF.inverse (f (x - E x)) :=
        congrArg (fun y ↦ hF.inverse (f y)) (congr($(hE.aeval_reverse_mul_inverse) x))
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end Intertwining

end IsRieszColemanProjection

end Module

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a normed module `N`. If `E` is a Riesz–Coleman projection of the extension
`i ∘ u ∘ r` for `Q`, then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M)
    {Q : Polynomial R} {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v : N →L[R] N := i.comp (u.comp r)
  have hr : u.toLinearMap ∘ₗ r.toLinearMap = r.toLinearMap ∘ₗ v.toLinearMap :=
    LinearMap.ext fun y ↦ by simp [v, hri']
  have hi : v.toLinearMap ∘ₗ i.toLinearMap = i.toLinearMap ∘ₗ u.toLinearMap :=
    LinearMap.ext fun x ↦ by simp [v, hri']
  have hra (y : N) : Polynomial.aeval u Q.reverse (r y) = r (Polynomial.aeval v Q.reverse y) := by
    have h := congr($(Module.End.aeval_comp_of_comp_eq hr Q.reverse) y)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  have hia (x : M) : Polynomial.aeval v Q.reverse (i x) = i (Polynomial.aeval u Q.reverse x) := by
    have h := congr($(Module.End.aeval_comp_of_comp_eq hi Q.reverse) x)
    simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hQE (y : N) : Polynomial.aeval v Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simp [hra, hQE]
  · ext x
    simpa [hra, hri'] using congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    simpa [← hia, hri'] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x
    simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x
    simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

/-- For a retract `r ∘ i = id` of `M` through `N` and a polynomial `Q` with invertible leading
coefficient, the Riesz–Coleman projection `F` of the extension `i ∘ u ∘ r` equals the extension
`i ∘ E ∘ r` of the Riesz–Coleman projection `E` of `u`. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M)
    {Q : Polynomial R} (hQ : IsUnit Q.leadingCoeff) {E : M →L[R] M} {F : N →L[R] N}
    (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection (i.comp (u.comp r)) Q F) :
    i.comp (E.comp r) = F := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hEq : E = r.comp (F.comp i) := hE.unique (hF.comp_comp_of_retract hri)
  have hF_comm := apply_comp_apply_of_mem_closure_adjoin hri hF.mem_closure_adjoin
  have hF_fix (y : N) : i (r (F y)) = F y := by
    have hmul := congr($(hF.mul_aeval_divX_mul_eq hQ) y)
    have hval : F y = i (u (r (Polynomial.aeval (i.comp (u.comp r))
        (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse).divX (F y)))) := by
      simpa only [mul_apply_eq_comp, comp_apply] using hmul.symm
    conv_lhs => rw [hval]
    rw [hri', ← hval]
  ext y : 1
  simp [hEq, ← hF_comm, hF_fix]

end Retract

end ContinuousLinearMap
