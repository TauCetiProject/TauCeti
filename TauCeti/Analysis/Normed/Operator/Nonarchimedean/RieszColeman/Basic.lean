/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Smeval
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# The Riesz–Coleman projection for a polynomial factor

Let `R` be a seminormed commutative ring with Tate scalars (`TauCeti.NormedRing.IsTate R`), `M` a
seminormed `R`-module with bounded scalar action, `u : M →L[R] M` a continuous endomorphism, and
`Q : R[X]` a polynomial with reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
an idempotent `E` commuting with `u` and lying in the operator-norm closure of the polynomials in
`u`, such that `Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand
`range (1 - E)`, with complementary inverse `w` again in the operator-norm closure of `R[u]`.

Thus `E` splits `M` into the topological complements `range E = ker Q*(u)` and
`ker E = range Q*(u)` (`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`), both
`u`-stable, with `Q*(u)` zero on the first summand and a continuous linear automorphism of the
second (`ContinuousLinearMap.IsRieszColemanProjection.equivKer`). When `Q` has invertible leading
coefficient, the identity `X * Q*.divX + lc(Q) = Q*` expresses `E` as `u` times a polynomial in `u`
times `E` (`ContinuousLinearMap.IsRieszColemanProjection.eq_mul_aeval_divX_mul`), showing that `u`
itself restricts to a continuous linear automorphism of `range E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`).

Such a projection is unique (`ContinuousLinearMap.IsRieszColemanProjection.unique`); for `Q = 1`
(more generally, whenever `Q*(u)` is invertible) it is `E = 0`. Any linear map intertwining two
operators intertwines their Riesz–Coleman projections and complementary inverses for the same `Q`,
without continuity assumptions (`ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
`ContinuousLinearMap.IsRieszColemanProjection.semiconj_inverse`); in particular every bounded
operator commuting with `u` commutes with `E` and `w`.

Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id` of `M` through a
normed module `N` (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and when
`Q` has invertible leading coefficient the extension `i ∘ (r ∘ E ∘ i) ∘ r` recovers `E`
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`). On model spaces
`C₀(J, R)`, bounded coefficient extension preserves Riesz–Coleman projections whenever `f`
preserves the degree of `Q` (`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector of `u` for a polynomial
  factor `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on the
  complementary summand, extended by zero.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of the complementary summand `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: `u` as a continuous linear
  automorphism of the finite summand `range E`, when `Q` has invertible leading coefficient.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`: the topological splitting
  `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of the Riesz–Coleman
  projection.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`: intertwining and commuting
  operators preserve the splitting.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`: retract transport.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`: bounded base change on model spaces.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` for a
polynomial `Q`: an idempotent `E` commuting with `u` and lying in the operator-norm closure of the
polynomials in `u`, such that `Q*(u) * E = 0` for the reversal `Q* = Q.reverse` and `Q*(u)` is
invertible on the complementary summand `range (1 - E)`, with complementary inverse again in the
closure of the polynomials in `u`. -/
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
  exists_inverse : ∃ w : M →L[R] M, Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- If `Q*(u)` is invertible, any Riesz–Coleman projection for `Q` is zero. -/
theorem eq_zero_of_isUnit_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (h : IsUnit (Polynomial.aeval u Q.reverse)) : E = 0 :=
  h.mul_right_eq_zero.mp hE.aeval_reverse_mul_eq_zero

/-- A Riesz–Coleman projection for a degree-zero polynomial with invertible leading coefficient is
zero. -/
theorem eq_zero_of_natDegree_eq_zero (hE : IsRieszColemanProjection u Q E)
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) : E = 0 := by
  have hrev : Q.reverse = C Q.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp [Polynomial.leadingCoeff, hd]
  exact hE.eq_zero_of_isUnit_aeval_reverse <| by
    rw [hrev, Polynomial.aeval_C]
    exact hQ.map (algebraMap R (M →L[R] M))

/-- A Riesz–Coleman projection for `Q = 1` is zero. -/
theorem eq_zero_of_eq_one (hE : IsRieszColemanProjection u 1 E) : E = 0 :=
  hE.eq_zero_of_natDegree_eq_zero Polynomial.natDegree_one (by simp)

/-- Zero is a Riesz–Coleman projection for any degree-zero polynomial with invertible leading
coefficient. -/
theorem zero_of_natDegree_eq_zero (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection u Q 0 := by
  have hrev : Q.reverse = C Q.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp [Polynomial.leadingCoeff, hd]
  obtain ⟨c, hc⟩ := hQ.exists_left_inv
  have hmul : Q.leadingCoeff * c = 1 := mul_comm c Q.leadingCoeff ▸ hc
  refine ⟨IsIdempotentElem.zero, Commute.zero_right u, subset_closure (zero_mem _), mul_zero _,
    algebraMap R (M →L[R] M) c, ?_, ?_, zero_mul _, mul_zero _,
    subset_closure (Subalgebra.algebraMap_mem _ c)⟩
  · simp [hrev, ← map_mul, hmul]
  · simp [hrev, ← map_mul, hc]

/-- Zero is a Riesz–Coleman projection for `Q = 1`. -/
theorem zero_of_eq_one (u : M →L[R] M) : IsRieszColemanProjection u 1 0 :=
  zero_of_natDegree_eq_zero u Polynomial.natDegree_one (by simp)

/-- Scaling the polynomial `Q` by a unit of the coefficient ring does not change the Riesz–Coleman
projection. -/
theorem units_smul (hE : IsRieszColemanProjection u Q E) (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E := by
  have hdeg : (c • Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_smul_of_smul_regular Q (IsSMulRegular.all _)
  have hrev : (c • Q).reverse = (c : R) • Q.reverse := by
    ext i
    rw [Polynomial.coeff_reverse, hdeg, Units.smul_def, Polynomial.smul_eq_C_mul,
      Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_reverse]
  have haev : Polynomial.aeval u (c • Q).reverse = (c : R) • Polynomial.aeval u Q.reverse := by
    rw [hrev, map_smul]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_,
    ⟨(↑c⁻¹ : R) • w, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [haev, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero]
    ext x : 1; simp
  · rw [haev, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul, hw₁]
  · rw [haev, smul_mul_assoc, mul_smul_comm, smul_smul, Units.inv_mul, one_smul, hw₂]
  · rw [mul_smul_comm, hw₃]; ext x : 1; simp
  · rw [smul_mul_assoc, hw₄]; ext x : 1; simp
  · exact map_mem_closure (continuous_const_smul (↑c⁻¹ : R)) hw
      fun y hy ↦ (Algebra.adjoin R {u} : Subalgebra R _).smul_mem hy (↑c⁻¹ : R)

/-- Scaling the polynomial `Q` by a unit of the coefficient ring yields an equivalent Riesz–Coleman
projection predicate. -/
theorem units_smul_iff (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E ↔ IsRieszColemanProjection u Q E :=
  ⟨fun h ↦ by simpa using h.units_smul c⁻¹, fun h ↦ h.units_smul c⟩

/-- A Riesz–Coleman projection commutes with every polynomial in the operator. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  rw [Polynomial.aeval_eq_smeval]
  exact Polynomial.smeval_commute_left R P hE.commute

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

/-- `E * Q*(u) = 0`, matching `aeval_reverse_mul_eq_zero` by commutativity. -/
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

/-- Every polynomial in the operator preserves the kernel of a Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval P).eq.symm) x)

/-- Every polynomial in the operator preserves the range of a Riesz–Coleman projection. -/
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

/-- **The range of `Q*(u)` is the kernel of its Riesz–Coleman projection**, i.e., the complementary
summand `range (1 - E)`. -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨hE.inverse x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.mul_aeval_reverse_eq_zero) y)
  · simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, sub_zero] using
      congr($(hE.aeval_reverse_mul_inverse) x)

/-- **`ker Q*(u)` and `range Q*(u)` are topological complements.** -/
theorem isTopCompl_ker_range (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The range of `Q*(u)` is closed whenever `M` is `T₁` (in particular, normed). -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- The range of a Riesz–Coleman projection is closed whenever `M` is `T₁` (in particular,
normed). -/
theorem isClosed_range [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed (LinearMap.range (E : M →ₗ[R] M) : Set M) := by
  rw [hE.range_eq_ker]
  exact (Polynomial.aeval u Q.reverse).isClosed_ker

/-- The operator `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`,
identified with `range Q*(u)` by `range_aeval_reverse_eq_ker`. Its inverse is the restriction of
`IsRieszColemanProjection.inverse`. -/
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

/-- When `Q` has invertible leading coefficient, a Riesz–Coleman projection factors through `u` as
`E = u * (-lc(Q)⁻¹ • Q*.divX(u) * E)`. This yields both compactness of `E` and invertibility of `u`
on `range E`. -/
theorem eq_mul_aeval_divX_mul (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E = u * (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) := by
  have hdiv : u * Polynomial.aeval u Q.reverse.divX + Q.leadingCoeff • (1 : M →L[R] M) =
      Polynomial.aeval u Q.reverse := by
    have h := congrArg (Polynomial.aeval u) (Polynomial.X_mul_divX_add Q.reverse)
    simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.coeff_zero_reverse, Algebra.algebraMap_eq_smul_one] using h
  have hmul := congrArg (· * E) hdiv
  rw [add_mul (R := M →L[R] M), hE.aeval_reverse_mul_eq_zero, smul_mul_assoc, one_mul,
    add_eq_zero_iff_eq_neg'] at hmul
  have hscaled := congrArg (Ring.inverse Q.leadingCoeff • ·) hmul
  rw [smul_smul, Ring.inverse_mul_cancel _ hQ, one_smul, smul_neg, ← neg_smul,
    mul_assoc, ← mul_smul_comm] at hscaled
  exact hscaled

/-- **Invertibility of `u` on the finite summand.** When `Q` has invertible leading coefficient,
`u` restricts to a continuous linear automorphism of `range E`, with explicit inverse the
restriction of `-lc(Q)⁻¹ • Q*.divX(u)`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  let v : M →L[R] M := -(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX
  have hmaps : Set.MapsTo v E.range E.range := by
    intro x hx
    simpa only [v, smul_apply, SetLike.mem_coe] using
      E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx)
  have hcomm_uv : Commute u v := by
    have hX : Commute u (Polynomial.aeval u Q.reverse.divX) := by
      simpa only [Polynomial.aeval_X] using
        (Commute.all (X : R[X]) Q.reverse.divX).map (Polynomial.aeval u)
    exact hX.smul_right _
  have huvE : u * (v * E) = E := (hE.eq_mul_aeval_divX_mul hQ).symm
  have hvuE : v * (u * E) = E := by rw [← mul_assoc, ← hcomm_uv.eq, mul_assoc, huvE]
  exact ContinuousLinearEquiv.equivOfInverse
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx))
    (v.restrict (fun _ hx ↦ hmaps hx))
    (fun x ↦ Subtype.ext <| by
      have hfix : E x = x :=
        ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
      simpa only [restrict_apply, mul_apply_eq_comp, hfix] using congr($hvuE (x : M)))
    (fun x ↦ Subtype.ext <| by
      have hfix : E x = x :=
        ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
      simpa only [restrict_apply, mul_apply_eq_comp, hfix] using congr($huvE (x : M)))

/-- The finite-summand automorphism acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x :=
  (rfl)

/-- The inverse of `u` on `range E` acts by `-lc(Q)⁻¹ • Q*.divX(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      (-(Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x :=
  (rfl)

/-- When `Q` has invertible leading coefficient, the restriction of `u` to `range E` is a unit in
the bounded endomorphism algebra of `range E`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)) :=
  isUnit_iff_exists.mpr ⟨((hE.equivRange hQ).symm : E.range →L[R] E.range),
    ext fun x ↦ (hE.equivRange hQ).apply_symm_apply x,
    ext fun x ↦ (hE.equivRange hQ).symm_apply_apply x⟩

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

end IsRieszColemanProjection

end Module

section Intertwining

variable {R M N : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : R[X]}

namespace IsRieszColemanProjection

/-- **Functoriality of Riesz–Coleman projections.** A linear map intertwining two operators
intertwines their Riesz–Coleman projections for the same polynomial `Q`. Continuity of the
intertwiner is unnecessary. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  have hQ := hf.aeval Q.reverse
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
    exact ⟨f y, by simp only [coe_coe]; rw [← hQ y, hy]⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the finite summand `range E = ker Q*(u)` into the corresponding
summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner sends the complementary summand `ker E = range Q*(u)` into the corresponding
summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners carry the complementary inverses of Riesz–Coleman projections to one another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  have hQ := hf.aeval Q.reverse
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
        exact congrArg (fun y ↦ hF.inverse (f y)) (congr($(hE.aeval_reverse_mul_inverse) x))
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E :=
  ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of every
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse :=
  ext fun x ↦ hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end IsRieszColemanProjection

end Intertwining

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as a
retract of a normed module `N`. If `E` is a Riesz–Coleman projection of the extension `i ∘ u ∘ r`
for `Q`, then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr : Function.Semiconj (r : N →ₗ[R] M) (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi : Function.Semiconj (i : M →ₗ[R] N) u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  have hrQ := hr.aeval Q.reverse
  have hiQ := hi.aeval Q.reverse
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hQ0 (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x; simp [hE', hri', hEE]
  · ext x; simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x; simpa [hQ0] using (hrQ (E (i x))).symm
  · ext x
    simpa [hri'] using (hrQ (w (i x))).symm.trans congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    have hiQx : i (Polynomial.aeval u Q.reverse x) =
        Polynomial.aeval (i.comp (u.comp r)) Q.reverse (i x) := hiQ x
    simpa only [mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self, map_sub, hri',
      hiQx] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x; simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x; simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

omit [IsBoundedSMul R M] in
/-- **Recovery of an extended Riesz–Coleman projection from its compression.** Under a retract
`r ∘ i = id`, if `Q` has invertible leading coefficient, any Riesz–Coleman projection `E` of the
extension `i ∘ u ∘ r` vanishes on `ker r` and therefore equals the extension
`i ∘ (r ∘ E ∘ i) ∘ r` of its compression. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    i.comp ((r.comp (E.comp i)).comp r) = E := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  -- `E` factors through `i ∘ u ∘ r`, which vanishes on `y - i (r y) ∈ ker r`.
  have hfac := hE.eq_mul_aeval_divX_mul hQ
  ext y
  have hker : E (y - i (r y)) = 0 := by
    have hv : (i.comp (u.comp r)) (y - i (r y)) = 0 := by simp [hri']
    have h1 : E (y - i (r y)) = (-(Ring.inverse Q.leadingCoeff) •
        Polynomial.aeval (i.comp (u.comp r)) Q.reverse.divX * E)
        ((i.comp (u.comp r)) (y - i (r y))) := by
      have h' : E = -(Ring.inverse Q.leadingCoeff) •
          Polynomial.aeval (i.comp (u.comp r)) Q.reverse.divX * E * (i.comp (u.comp r)) := by
        conv_lhs => rw [hfac]
        have hX : Commute (i.comp (u.comp r))
            (Polynomial.aeval (i.comp (u.comp r)) Q.reverse.divX) := by
          simpa only [Polynomial.aeval_X] using
            (Commute.all (X : R[X]) Q.reverse.divX).map (Polynomial.aeval (i.comp (u.comp r)))
        rw [← mul_assoc, (hX.smul_right _).eq, mul_assoc, hE.commute.eq, ← mul_assoc]
      exact congr($h' (y - i (r y)))
    rw [h1, hv, map_zero]
  rw [map_sub, sub_eq_zero] at hker
  simp only [comp_apply]
  rw [hE', hri', hker]

end Retract

section BaseChange

variable {J R S : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** Coefficientwise extension along a
bounded unital ring homomorphism `f : R →+* S` carries a Riesz–Coleman projection of `u` for `Q`
to one of `u_S` for `Q.map f`, whenever `f` preserves the degree of `Q` (in particular, whenever
`Q` has invertible leading coefficient, via `Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff`).
No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (hdeg : (Q.map f).natDegree = Q.natDegree) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev : (Q.map f).reverse = Q.reverse.map f := by
    rw [Polynomial.reverse, hdeg, Polynomial.reflect_map, Polynomial.reverse]
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

end BaseChange

end ContinuousLinearMap
