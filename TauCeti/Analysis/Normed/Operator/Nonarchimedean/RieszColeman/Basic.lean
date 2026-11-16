/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.SpectralProjection
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# The Riesz–Coleman projection for a polynomial factor

Let `R` be a seminormed commutative ring with Tate scalars (`TauCeti.NormedRing.IsTate R`), `M` a
seminormed `R`-module with bounded scalar action, `u : M →L[R] M` a continuous endomorphism, and
`Q : R[X]` a polynomial with reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
a spectral projection (`ContinuousLinearMap.IsSpectralProjection`) of `u` for `Q*(u)` of order `1`:
an idempotent `E` commuting with `u` and lying in the operator-norm closure of the polynomials in
`u`, such that `Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand
`range (1 - E)`, with complementary inverse `w` (`ContinuousLinearMap.IsSpectralProjection.inverse`)
again in the operator-norm closure of `R[u]`.

Thus `E` splits `M` into the topological complements `range E = ker Q*(u)` and
`ker E = range Q*(u)` (`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`), both
`u`-stable, with `Q*(u)` zero on the first summand and a continuous linear automorphism of the
second (`ContinuousLinearMap.IsSpectralProjection.equivKer`). When `Q` has invertible leading
coefficient, the identity `X * Q*.divX + lc(Q) = Q*` expresses `E` as `u` times a polynomial in `u`
times `E` (`ContinuousLinearMap.IsRieszColemanProjection.eq_mul_aeval_divX_mul`), showing that `u`
itself restricts to a continuous linear automorphism of `range E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`).

Such a projection is unique (`ContinuousLinearMap.IsSpectralProjection.unique`); for `Q = 1`
(`ContinuousLinearMap.IsRieszColemanProjection.one_iff`, or more generally whenever `Q*(u)` is
invertible) it is `E = 0`, and scaling `Q` by a unit of `R` leaves the predicate unchanged
(`ContinuousLinearMap.IsRieszColemanProjection.units_smul_iff`). Any linear map intertwining two
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
  factor `Q`, instantiating `ContinuousLinearMap.IsSpectralProjection` at `Q*(u)` with order `1`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: `u` as a continuous linear
  automorphism of the spectral summand `range E`, when `Q` has invertible leading coefficient.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.one_iff`,
  `ContinuousLinearMap.IsRieszColemanProjection.units_smul_iff`: normal-form equivalences for
  `Q = 1` and unit scaling.
* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`: the topological splitting
  `M = ker Q*(u) ⊕ range Q*(u)`.
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
polynomial `Q`: a spectral projection (`ContinuousLinearMap.IsSpectralProjection`) of `u` for the
reversed polynomial `Q*(u)` of order `1`. -/
@[expose] def IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop :=
  IsSpectralProjection u (Polynomial.aeval u Q.reverse) 1 E

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- `Q*(u)` vanishes on the range of a Riesz–Coleman projection. -/
theorem aeval_reverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) :
    Polynomial.aeval u Q.reverse * E = 0 := by
  simpa only [pow_one] using hE.pow_mul_eq_zero

/-- If `Q*(u)` is invertible, any Riesz–Coleman projection for `Q` is zero. -/
theorem eq_zero_of_isUnit_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (h : IsUnit (Polynomial.aeval u Q.reverse)) : E = 0 :=
  hE.eq_zero_of_isUnit h

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

/-- Zero is a Riesz–Coleman projection for any degree-zero polynomial with invertible leading
coefficient. -/
theorem zero_of_natDegree_eq_zero (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection u Q 0 := by
  have hrev : Q.reverse = C Q.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp [Polynomial.leadingCoeff, hd]
  have hunit : IsUnit (Polynomial.aeval u Q.reverse) := by
    rw [hrev, Polynomial.aeval_C]
    exact hQ.map (algebraMap R (M →L[R] M))
  refine IsSpectralProjection.zero_of_isUnit u hunit ?_
  have hinv : ((hunit.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) =
      algebraMap R (M →L[R] M) (hQ.unit⁻¹ : Rˣ) := by
    apply hunit.mul_left_cancel
    simp [hrev, ← map_mul]
  rw [hinv]
  exact subset_closure (Subalgebra.algebraMap_mem _ _)

/-- A Riesz–Coleman projection for `Q = 1` is equivalent to `E = 0`. -/
@[simp]
theorem one_iff : IsRieszColemanProjection u 1 E ↔ E = 0 :=
  ⟨fun hE ↦ hE.eq_zero_of_natDegree_eq_zero Polynomial.natDegree_one (by simp),
    fun h ↦ h ▸ zero_of_natDegree_eq_zero u Polynomial.natDegree_one (by simp)⟩

/-- A Riesz–Coleman projection for `Q = 1` is zero. -/
theorem eq_zero_of_eq_one (hE : IsRieszColemanProjection u 1 E) : E = 0 :=
  one_iff.mp hE

/-- Zero is a Riesz–Coleman projection for `Q = 1`. -/
theorem zero_of_eq_one (u : M →L[R] M) : IsRieszColemanProjection u 1 0 :=
  one_iff.mpr rfl

/-- Scaling the polynomial `Q` by a unit of the coefficient ring does not change the Riesz–Coleman
projection. -/
theorem units_smul (hE : IsRieszColemanProjection u Q E) (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E := by
  have hdeg : (c • Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_smul_of_smul_regular Q (IsSMulRegular.all _)
  have hrev : (c • Q).reverse = (c : R) • Q.reverse := by
    rw [Polynomial.reverse, hdeg]
    simp [Polynomial.reverse, Units.smul_def, Polynomial.smul_eq_C_mul]
  have haev : Polynomial.aeval u (c • Q).reverse = c • Polynomial.aeval u Q.reverse := by
    rw [hrev, map_smul, Units.smul_def]
  rw [IsRieszColemanProjection, haev]
  exact IsSpectralProjection.units_smul_spectral hE c

/-- Scaling the polynomial `Q` by a unit of the coefficient ring yields an equivalent Riesz–Coleman
projection predicate. -/
@[simp]
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
  IsSpectralProjection.commute_spectral hE

/-- `E * Q*(u) = 0`, matching `aeval_reverse_mul_eq_zero` by commutativity. -/
theorem mul_aeval_reverse_eq_zero (hE : IsRieszColemanProjection u Q E) :
    E * Polynomial.aeval u Q.reverse = 0 := by
  simpa only [pow_one] using hE.mul_pow_eq_zero

/-- Every polynomial in the operator preserves the kernel of a Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.ker E.ker :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hE.isIdempotentElem).mp
      (hE.commute_aeval P).symm).2

/-- Every polynomial in the operator preserves the range of a Riesz–Coleman projection. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.range E.range :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hE.isIdempotentElem).mp
      (hE.commute_aeval P).symm).1

/-- **The range of a Riesz–Coleman projection is `ker Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  simpa only [pow_one] using IsSpectralProjection.range_eq_ker hE

/-- **The range of `Q*(u)` is the kernel of its Riesz–Coleman projection**, i.e., the complementary
summand `range (1 - E)`. -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  simpa only [pow_one] using IsSpectralProjection.range_pow_eq_ker hE le_rfl

/-- **`ker Q*(u)` and `range Q*(u)` are topological complements.** -/
theorem isTopCompl_ker_range (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  simpa only [pow_one] using IsSpectralProjection.isTopCompl_ker_range_pow hE le_rfl

/-- The range of `Q*(u)` is closed whenever `M` is `T₁` (in particular, normed). -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  simpa only [pow_one] using IsSpectralProjection.isClosed_range_pow hE le_rfl

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

/-- **Invertibility of `u` on the spectral summand.** When `Q` has invertible leading coefficient,
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

/-- The spectral-summand automorphism acts by `u`. -/
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
    Function.Semiconj f E F :=
  IsSpectralProjection.semiconj hE hF f (hf.aeval Q.reverse)

/-- An intertwiner sends the spectral summand `range E = ker Q*(u)` into the corresponding
summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range :=
  IsSpectralProjection.mapsTo_range_of_semiconj hE hF f (hf.aeval Q.reverse)

/-- An intertwiner sends the complementary summand `ker E = range Q*(u)` into the corresponding
summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker :=
  IsSpectralProjection.mapsTo_ker_of_semiconj hE hF f (hf.aeval Q.reverse)

/-- Intertwiners carry the complementary inverses of Riesz–Coleman projections to one another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse :=
  IsSpectralProjection.semiconj_inverse hE hF f (hf.aeval Q.reverse)

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
  exact IsSpectralProjection.comp_comp_of_retract hri (hr.aeval Q.reverse) (hi.aeval Q.reverse) hE

end Retract

section RetractRecovery

variable {R M N : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

/-- **Recovery of an extended Riesz–Coleman projection from its compression.** Under a retract
`r ∘ i = id`, if `Q` has invertible leading coefficient, any Riesz–Coleman projection `E` of the
extension `i ∘ u ∘ r` takes values in `range i` and vanishes on `ker r`, and therefore equals the
extension `i ∘ (r ∘ E ∘ i) ∘ r` of its compression. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    i.comp ((r.comp (E.comp i)).comp r) = E := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  -- `E` factors through `i ∘ u ∘ r` on both sides.
  have hfac := hE.eq_mul_aeval_divX_mul hQ
  have hfac_right : E = -(Ring.inverse Q.leadingCoeff) •
      Polynomial.aeval (i.comp (u.comp r)) Q.reverse.divX * E * (i.comp (u.comp r)) := by
    conv_lhs => rw [hfac]
    have hX : Commute (i.comp (u.comp r))
        (Polynomial.aeval (i.comp (u.comp r)) Q.reverse.divX) := by
      simpa only [Polynomial.aeval_X] using
        (Commute.all (X : R[X]) Q.reverse.divX).map (Polynomial.aeval (i.comp (u.comp r)))
    rw [← mul_assoc, (hX.smul_right _).eq, mul_assoc, hE.commute.eq, ← mul_assoc]
  have hir_left (z : N) : i (r (E z)) = E z := by
    conv_lhs => rw [hfac]
    conv_rhs => rw [hfac]
    simp only [mul_apply_eq_comp, comp_apply, hri']
  have hir_right (y : N) : E (i (r y)) = E y := by
    conv_lhs => rw [hfac_right]
    conv_rhs => rw [hfac_right]
    simp only [mul_apply_eq_comp, comp_apply, hri']
  ext y
  simp only [comp_apply, hir_left, hir_right]

end RetractRecovery

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
  simpa only [IsRieszColemanProjection, mapCoeffsRingHom_apply, mapCoeffs_aeval, hrev] using
    IsSpectralProjection.map hE (mapCoeffsRingHom f hf)
      (fun hv ↦ by simpa only [mapCoeffsRingHom_apply] using mapCoeffs_mem_closure_adjoin f hf hv)

end BaseChange

end ContinuousLinearMap
