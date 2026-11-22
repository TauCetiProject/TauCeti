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
import Mathlib.Algebra.Polynomial.Smeval
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# Riesz–Coleman projections and topological polynomial spectral splittings

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
(`ContinuousLinearMap.isRieszColemanProjection_one_iff`,
`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_one`,
`ContinuousLinearMap.isRieszColemanProjection_one_zero`); scaling `Q` by a unit constant leaves
the predicate unchanged (`ContinuousLinearMap.IsRieszColemanProjection.of_C_mul`,
`ContinuousLinearMap.IsRieszColemanProjection.iff_C_mul`).

When the leading coefficient of `Q` is a unit, the constant term of `Q*` is `Q.leadingCoeff`, so
dividing `Q* - Q*(0)` by `X` expresses `E = u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E)`. Consequently:

* `u` restricts to a continuous linear automorphism of `range E = ker Q*(u)`
  (`ContinuousLinearMap.IsRieszColemanProjection.equivRange`);
* on a model space `C₀(I, R)` over an ultrametric `R`, if `u` is row compact then `E` is row
  compact (`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`), and if `R` is also
  complete then `ker Q*(u)` is finitely generated and projective over `R`
  (`ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse`), without assuming
  `R` Noetherian or reduced;
* Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id`, and when
  `lc(Q)` is a unit the extension `i ∘ E ∘ r` recovers the ambient projection on `N` and `i`, `r`
  identify `range E` with `range E'`
  (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`).

Finally, any linear map intertwining two endomorphisms intertwines their Riesz–Coleman projections
and complementary inverses for the same polynomial `Q`, so every bounded operator commuting with
`u` commutes with `E` and preserves both spectral summands
(`ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
`ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the predicate characterising a spectral projector
  onto `ker Q*(u)` along a topological `u`-stable complement (closed when `M` is Hausdorff) on
  which `Q*(u)` is invertible.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on `ker E`,
  extended by zero on `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `IsUnit Q.leadingCoeff`, `u` as a
  continuous linear automorphism of `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`: when `IsUnit Q.leadingCoeff`,
  the continuous linear equivalence `E.range ≃L[R] E'.range` induced by a continuous linear retract
  `r ∘ i = id`.

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
  refine ⟨.zero, Commute.zero_right u, subset_closure (Subalgebra.zero_mem _), by simp,
    ⟨1, ?_, ?_, by simp, by simp, subset_closure (Subalgebra.one_mem _)⟩⟩ <;> simp

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- For `Q = 1`, the spectral summand is zero: any Riesz–Coleman projection for `1` is `0`. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 := by
  simpa using hE.aeval_reverse_mul_eq_zero

end IsRieszColemanProjection

/-- For `Q = 1`, `E` is a Riesz–Coleman projection of `u` if and only if `E = 0`. -/
@[simp]
theorem isRieszColemanProjection_one_iff {u E : M →L[R] M} :
    IsRieszColemanProjection u 1 E ↔ E = 0 :=
  ⟨IsRieszColemanProjection.eq_zero_of_one, fun h ↦ h ▸ isRieszColemanProjection_one_zero u⟩

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  simpa only [Polynomial.aeval_eq_smeval] using Polynomial.smeval_commute_left R P hE.commute

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

private theorem of_C_mul_aux (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    ∃ hE' : IsRieszColemanProjection u (Polynomial.C c * Q) E,
      hE'.inverse = Ring.inverse c • hE.inverse := by
  have haeval := Polynomial.aeval_C_mul_reverse u hc Q
  have hcc : Ring.inverse c * c = 1 := Ring.inverse_mul_cancel _ hc
  have hinv₁ : Polynomial.aeval u (Polynomial.C c * Q).reverse * (Ring.inverse c • hE.inverse) =
      1 - E := by
    rw [haeval, smul_mul_smul_comm, mul_comm c, hcc, one_smul, hE.aeval_reverse_mul_inverse]
  have hinv₂ : (Ring.inverse c • hE.inverse) * Polynomial.aeval u (Polynomial.C c * Q).reverse =
      1 - E := by
    rw [haeval, smul_mul_smul_comm, hcc, one_smul, hE.inverse_mul_aeval_reverse]
  have hinv₃ : E * (Ring.inverse c • hE.inverse) = 0 := by
    rw [mul_smul_comm, hE.mul_inverse_eq_zero, smul_zero]
  have hinv₄ : (Ring.inverse c • hE.inverse) * E = 0 := by
    rw [smul_mul_assoc, hE.inverse_mul_eq_zero, smul_zero]
  have hE' : IsRieszColemanProjection u (Polynomial.C c * Q) E :=
    ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin,
      by rw [haeval, smul_mul_assoc, hE.aeval_reverse_mul_eq_zero, smul_zero],
      ⟨Ring.inverse c • hE.inverse, hinv₁, hinv₂, hinv₃, hinv₄,
        (Algebra.adjoin R {u}).topologicalClosure.smul_mem hE.inverse_mem_closure_adjoin _⟩⟩
  exact ⟨hE', (hE'.eq_inverse hinv₁ hinv₃).symm⟩

/-- Scaling `Q` by a unit scalar preserves Riesz–Coleman projections. -/
theorem of_C_mul (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E :=
  (of_C_mul_aux hE hc).1

/-- Scaling `Q` by a unit scalar does not change the Riesz–Coleman projections of `u`. -/
@[simp]
theorem iff_C_mul {c : R} (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E ↔ IsRieszColemanProjection u Q E := by
  obtain ⟨c', hc'⟩ := hc.exists_left_inv
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_C_mul hc⟩
  have hQ : Polynomial.C c' * (Polynomial.C c * Q) = Q := by
    rw [← mul_assoc, ← Polynomial.C_mul, hc', Polynomial.C_1, one_mul]
  simpa only [hQ] using h.of_C_mul (IsUnit.of_mul_eq_one _ hc')

/-- Rescaling `Q` by a unit scalar `c` scales the complementary inverse by `Ring.inverse c`. -/
@[simp]
theorem inverse_of_C_mul (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    (hE.of_C_mul hc).inverse = Ring.inverse c • hE.inverse :=
  (of_C_mul_aux hE hc).2

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
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))

/-- The complementary automorphism `equivKer` acts by `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x := by
  simp [equivKer]

/-- The inverse complementary automorphism `equivKer.symm` acts by
`IsRieszColemanProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x := by
  simp [equivKer]

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` for the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' :=
  hE.isIdempotentElem.eq_of_pow_mul_eq_zero (C := Polynomial.aeval u Q.reverse) (h := 1)
    hE'.isIdempotentElem
    (by rw [pow_one]; exact hE.aeval_reverse_mul_eq_zero)
    (by rw [pow_one]; exact hE'.aeval_reverse_mul_eq_zero)
    hE.aeval_reverse_mul_inverse hE.inverse_mul_aeval_reverse
    hE'.aeval_reverse_mul_inverse hE'.inverse_mul_aeval_reverse

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
  have huP : Commute u (Polynomial.aeval u Q.reverse.divX) := by
    simpa only [Polynomial.aeval_eq_smeval] using
      (Polynomial.smeval_commute_left R Q.reverse.divX (Commute.refl u)).symm
  have hcomm : Commute u ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) :=
    (huP.smul_right _).mul_right hE.commute
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
  ContinuousLinearEquiv.ofContinuousLinearMap
    (u.restrict hE.mapsTo_range)
    (((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX).restrict
      fun _ hx ↦ E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx))
    (ContinuousLinearMap.ext fun x ↦
      Subtype.ext (hE.apply_neg_inverse_smul_aeval_divX_reverse hQ x.property))
    (ContinuousLinearMap.ext fun x ↦
      Subtype.ext (hE.neg_inverse_smul_aeval_divX_reverse_apply hQ x.property))

/-- The spectral-summand automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x := by
  simp [equivRange, coe_restrict_apply hE.mapsTo_range]

/-- The inverse spectral-summand automorphism `equivRange.symm` acts by `-lc(Q)⁻¹ • (Q*/X)(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x := by
  simp [equivRange]

/-- When `Q.leadingCoeff` is a unit, the restriction of `u` to `range E` is a unit of
`E.range →L[R] E.range`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict hE.mapsTo_range) :=
  (hE.equivRange hQ).toUnit.isUnit

/-- When `Q.leadingCoeff` is a unit, the `R`-linear restriction of `u` to `range E` is a unit of
`Module.End R E.range`. -/
theorem isUnit_toLinearMap_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit ((u : M →ₗ[R] M).restrict hE.mapsTo_range) :=
  (hE.isUnit_restrict_range hQ).map toLinearMapRingHom

end IsRieszColemanProjection

end Module

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
  have hfQ := hf.aeval Q.reverse
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

/-- An intertwiner sends the spectral summand `range E` into `range F`. -/
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
  have hfQ := hf.aeval Q.reverse
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

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M} {Q : R[X]}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a seminormed module `N`. If `E` is a Riesz–Coleman projection of `i ∘ u ∘ r` for `Q`,
then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr_semi : Function.Semiconj r.toLinearMap (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi_semi : Function.Semiconj i.toLinearMap u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  have hrQ (y : N) : r (Polynomial.aeval (i.comp (u.comp r)) Q.reverse y) =
      Polynomial.aeval u Q.reverse (r y) := hr_semi.aeval Q.reverse y
  have hiQ (x : M) : i (Polynomial.aeval u Q.reverse x) =
      Polynomial.aeval (i.comp (u.comp r)) Q.reverse (i x) := hi_semi.aeval Q.reverse x
  have hir_comm : Commute (i.comp r) (i.comp (u.comp r)) := by ext y; simp [hri']
  have hE' (y : N) : i (r (E y)) = E (i (r y)) :=
    congr($(hE.commute_of_commute hir_comm) y)
  have hw' (y : N) : i (r (hE.inverse y)) = hE.inverse (i (r y)) :=
    congr($(hE.commute_inverse_of_commute hir_comm) y)
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hzero (y : N) : Polynomial.aeval (i.comp (u.comp r)) Q.reverse (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (hE.inverse.comp i), ?_, ?_, ?_, ?_,
      comp_comp_mem_closure_adjoin hri hE.inverse_mem_closure_adjoin⟩⟩
  · ext x; simp [hE', hri', hEE]
  · ext x; simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x; simp [← hrQ, hzero]
  · ext x
    simpa [hri'] using
      (hrQ (hE.inverse (i x))).symm.trans congr(r $(congr($(hE.aeval_reverse_mul_inverse) (i x))))
  · ext x
    simpa [hri', ← hiQ] using congr(r $(congr($(hE.inverse_mul_aeval_reverse) (i x))))
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, hw', hri', zero_apply]
    rw [← mul_apply_eq_comp, hE.mul_inverse_eq_zero, zero_apply, map_zero]
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, hE', hri', zero_apply]
    rw [← mul_apply_eq_comp, hE.inverse_mul_eq_zero, zero_apply, map_zero]

/-- When `Q.leadingCoeff` is a unit, the Riesz–Coleman projection `E'` of the extension
`i ∘ u ∘ r` along a continuous linear retract `r ∘ i = id` vanishes on `ker r` and takes values in
`range i`, so extending any Riesz–Coleman projection `E` of `u` back to `N` recovers
`E' = i ∘ E ∘ r`. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E') (hQ : IsUnit Q.leadingCoeff) :
    i.comp (E.comp r) = E' := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr_semi : Function.Semiconj r.toLinearMap (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hfac := hE'.mul_smul_aeval_divX_reverse_mul hQ
  ext y
  -- Since `E' = (i ∘ u ∘ r) * (...)`, `E' y` already lies in `range i`, so `i (r (E' y)) = E' y`.
  have hirE : i (r (E' y)) = E' y := by
    have hy := congr($hfac y).symm
    simp only [mul_apply_eq_comp, comp_apply] at hy
    rw [hy, hri']
  calc (i.comp (E.comp r)) y = i (E (r y)) := by simp
    _ = i (r (E' y)) := congrArg i (hE'.semiconj hE r.toLinearMap hr_semi y).symm
    _ = E' y := hirE

/-- When `Q.leadingCoeff` is a unit, along a continuous linear retract `r ∘ i = id`, `i` and `r`
restrict to a continuous linear equivalence between the ranges of the Riesz–Coleman projections of
`u` and `i ∘ u ∘ r`. -/
noncomputable def IsRieszColemanProjection.rangeEquivOfRetract (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E'.range :=
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hi_semi : Function.Semiconj i u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  have hr_semi : Function.Semiconj r (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi : ∀ x ∈ E.range, i x ∈ E'.range :=
    fun _ hx ↦ hE.mapsTo_range_of_semiconj hE' i.toLinearMap hi_semi hx
  have hr : ∀ y ∈ E'.range, r y ∈ E.range :=
    fun _ hy ↦ hE'.mapsTo_range_of_semiconj hE r.toLinearMap hr_semi hy
  ContinuousLinearEquiv.ofContinuousLinearMap (i.restrict hi) (r.restrict hr)
    (ContinuousLinearMap.ext fun ⟨y, hy⟩ ↦ Subtype.ext <| by
      have hEy : E' y = y :=
        (LinearMap.IsIdempotentElem.mem_range_iff
          (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE'.isIdempotentElem)).mp hy
      have hy' := congr($(hE'.mul_smul_aeval_divX_reverse_mul hQ) y).symm
      simp only [mul_apply_eq_comp, comp_apply, hEy] at hy'
      simp only [comp_apply, id_apply, coe_restrict_apply]
      rw [hy', hri'])
    (ContinuousLinearMap.ext fun ⟨x, _⟩ ↦ Subtype.ext (hri' x))

/-- The retract range equivalence `rangeEquivOfRetract` acts in the forward direction by `i`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.rangeEquivOfRetract hri hE' hQ x : N)) = i x := by
  simp [rangeEquivOfRetract]

/-- The inverse retract range equivalence `rangeEquivOfRetract.symm` acts by `r`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_symm_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (y : E'.range) :
    (((hE.rangeEquivOfRetract hri hE' hQ).symm y : M)) = r y := by
  simp [rangeEquivOfRetract]

end Retract

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
