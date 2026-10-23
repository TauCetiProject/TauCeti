/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent
import TauCeti.Algebra.Ring.Commute
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# The Riesz projector of a row-compact operator at a good zero

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete index
type, and `u` a row-compact endomorphism of the model space `C₀(I, R)` with Fredholm determinant
`H_u(T) = det (1 - T u)`, the principal-minor series `u.matrixCoeff.charPowerSeries`. Suppose
that `a` is a *good zero* of order `h` of `H_u`: the Hasse derivatives `ΔʲH_u(a)` vanish for
`j < h` and `c = ΔʰH_u(a)` is a unit of `R`. Put `C = 1 - a • u`.

A **Riesz projection** of `u` at `a` of order `h` (`ContinuousLinearMap.IsRieszProjection`) is an
idempotent `E`, commuting with `u` and an operator-norm limit of polynomials in `u`, with
`C ^ h * E = 0`, such that `C` is invertible on the complementary summand: there is `w`, again a
limit of polynomials in `u`, with `C w = w C = 1 - E` and `E w = w E = 0`. Thus `E` splits
`C₀(I, R)` into the generalised eigenspace `range E = ker C ^ h`
(`ContinuousLinearMap.IsRieszProjection.range_eq_ker`), on which `C` is nilpotent, and a stable
complement `range (1 - E)` on which `C` is invertible. Such a splitting is unique
(`ContinuousLinearMap.IsRieszProjection.unique`); at order `0` it is `E = 0`.

The Riesz projector is constructed from the Hasse derivatives of the Fredholm resolvent
`V(T) = H_u(T) (1 - T u)⁻¹`: with `b = c⁻¹ • ΔʰV(a)` the differentiated resolvent identity gives
`C ^ (h + 1) b = C ^ h`, and

`E = 1 - (C b) ^ h` (`ContinuousLinearMap.rieszProjection`)

is a Riesz projection, with `w = b (C b) ^ h`
(`ContinuousLinearMap.IsRowCompact.isRieszProjection_rieszProjection`). For `h > 0` the operator
`1 - C b = -c⁻¹ • u Δʰ⁻¹V(a)` is row compact, so `E` is row compact
(`ContinuousLinearMap.IsRowCompact.isRowCompact_rieszProjection`). Hence its range is a finitely
generated projective `R`-module
(`ContinuousLinearMap.IsRowCompact.finite_range_of_isIdempotentElem`,
`ContinuousLinearMap.IsRowCompact.projective_range_of_isIdempotentElem`). The scalars may have
nilpotents and need not be Noetherian; over a ring the range need not be free.

## Main definitions

* `ContinuousLinearMap.IsRieszProjection`: the finite spectral projector of `u` at `a` of order
  `h`.
* `ContinuousLinearMap.rieszProjection`: the explicit projector `1 - (C b) ^ h`.

## Main results

* `ContinuousLinearMap.IsRieszProjection.range_eq_ker`: the range of a Riesz projection is the
  generalised eigenspace `ker (1 - a • u) ^ h`.
* `ContinuousLinearMap.IsRieszProjection.unique`: Riesz projections are unique.
* `ContinuousLinearMap.IsRowCompact.isRieszProjection_rieszProjection`: at a good zero, the
  explicit projector is a Riesz projection.
* `ContinuousLinearMap.IsRowCompact.isRowCompact_rieszProjection`: it is row compact.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

variable {I R : Type*} [TopologicalSpace I]

namespace ContinuousLinearMap

section Projection

variable [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

/-- A **Riesz projection** of an endomorphism `u` of `C₀(I, R)` at the scalar `a`, of order `h`:
an idempotent `E` commuting with `u` and lying in the operator-norm closure of the polynomials in
`u`, such that `(1 - a • u) ^ h * E = 0` and `1 - a • u` is invertible on the complementary summand
`range (1 - E)`, with inverse again in the closure of the polynomials in `u`. For a good zero `a`
of order `h` of the Fredholm determinant of a row-compact `u`, the range of `E` is the
generalised eigenspace `ker (1 - a • u) ^ h`, and `E` is the finite spectral projector onto it. -/
structure IsRieszProjection (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) (h : ℕ)
    (E : C₀(I, R) →L[R] C₀(I, R)) : Prop where
  /-- A Riesz projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz projection is an operator-norm limit of polynomials in the operator. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R)))
  /-- `(1 - a • u) ^ h` vanishes on the range of a Riesz projection. -/
  pow_mul_eq_zero : (1 - a • u) ^ h * E = 0
  /-- `1 - a • u` is invertible on the complementary summand, with inverse an operator-norm limit
  of polynomials in the operator. -/
  exists_inverse : ∃ w : C₀(I, R) →L[R] C₀(I, R), (1 - a • u) * w = 1 - E ∧
    w * (1 - a • u) = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R)))

namespace IsRieszProjection

variable {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h : ℕ}

/-- A Riesz projection of order `0` is zero. -/
theorem eq_zero_of_order_zero (hE : IsRieszProjection u a 0 E) : E = 0 := by
  simpa using hE.pow_mul_eq_zero

/-- A Riesz projection commutes with `1 - a • u`. -/
theorem commute_one_sub_smul (hE : IsRieszProjection u a h E) : Commute (1 - a • u) E :=
  hE.commute.one_sub_smul_left (A := C₀(I, R) →L[R] C₀(I, R)) a

/-- A Riesz projection remains one when its nilpotence bound is increased. -/
theorem of_le (hE : IsRieszProjection u a h E) {n : ℕ} (hn : h ≤ n) :
    IsRieszProjection u a n E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine { hE with pow_mul_eq_zero := ?_ }
  rw [add_comm h k, pow_add, mul_assoc, hE.pow_mul_eq_zero, mul_zero]

/-- The operator preserves the kernel of its Riesz projection. -/
theorem mapsTo_ker (hE : IsRieszProjection u a h E) : Set.MapsTo u E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($(hE.commute.eq.symm) x)

/-- The operator preserves the range of its Riesz projection. -/
theorem mapsTo_range (hE : IsRieszProjection u a h E) : Set.MapsTo u E.range E.range := by
  rintro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  exact LinearMap.mem_range.mpr ⟨u y, congr($(hE.commute.eq.symm) y)⟩

/-- The spectral operator preserves the kernel of its Riesz projection. -/
theorem mapsTo_ker_one_sub_smul (hE : IsRieszProjection u a h E) :
    Set.MapsTo (1 - a • u : C₀(I, R) →L[R] C₀(I, R)) E.ker E.ker := by
  intro x hx
  simpa only [sub_apply, one_apply_eq_self, smul_apply, SetLike.mem_coe] using
    E.ker.sub_mem hx (E.ker.smul_mem a (hE.mapsTo_ker hx))

/-- The spectral operator preserves the range of its Riesz projection. -/
theorem mapsTo_range_one_sub_smul (hE : IsRieszProjection u a h E) :
    Set.MapsTo (1 - a • u : C₀(I, R) →L[R] C₀(I, R)) E.range E.range := by
  intro x hx
  simpa only [sub_apply, one_apply_eq_self, smul_apply, SetLike.mem_coe] using
    E.range.sub_mem hx (E.range.smul_mem a (hE.mapsTo_range hx))

/-- The complementary inverse preserves the kernel of the Riesz projection. -/
theorem mapsTo_ker_inverse (hE : IsRieszProjection u a h E) :
    Set.MapsTo hE.exists_inverse.choose E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using
    congr($(hE.exists_inverse.choose_spec.2.2.1) x)

/-- On the complementary summand, the complementary inverse is a left inverse of the
spectral operator. -/
theorem inverse_one_sub_smul_apply (hE : IsRieszProjection u a h E)
    {x : C₀(I, R)} (hx : x ∈ E.ker) :
    hE.exists_inverse.choose ((1 - a • u) x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.exists_inverse.choose_spec.2.1) x)

/-- On the complementary summand, the complementary inverse is a right inverse of the
spectral operator. -/
theorem one_sub_smul_apply_inverse (hE : IsRieszProjection u a h E)
    {x : C₀(I, R)} (hx : x ∈ E.ker) :
    (1 - a • u) (hE.exists_inverse.choose x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.exists_inverse.choose_spec.1) x)

/-- **The range of a Riesz projection is the generalised eigenspace** `ker (1 - a • u) ^ h`. -/
theorem range_eq_ker (hE : IsRieszProjection u a h E) :
    LinearMap.range (E : C₀(I, R) →ₗ[R] C₀(I, R)) =
      LinearMap.ker (((1 - a • u) ^ h : C₀(I, R) →L[R] C₀(I, R)) : C₀(I, R) →ₗ[R] C₀(I, R)) := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  have hCw : Commute (1 - a • u) w := hw.trans hw'.symm
  -- `1 - E = w ^ h * (1 - a • u) ^ h` kills the generalised eigenspace.
  have h1 := hE.isIdempotentElem.one_sub_eq_pow_mul_pow (A := C₀(I, R) →L[R] C₀(I, R))
    hE.pow_mul_eq_zero hw hw'
  rw [(hCw.pow_pow h h).eq] at h1
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa using congr($(hE.pow_mul_eq_zero) y)
  · have := congr($h1 x)
    simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, hx, map_zero, sub_eq_zero] at this
    exact this.symm

/-- **Uniqueness of the Riesz projection.** Two Riesz projections of `u` at `a` of the same order
are equal. -/
theorem unique {E' : C₀(I, R) →L[R] C₀(I, R)} (hE : IsRieszProjection u a h E)
    (hE' : IsRieszProjection u a h E') : E = E' := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero hE'.isIdempotentElem hE.pow_mul_eq_zero
    hE'.pow_mul_eq_zero hw hw' hw₂ hw₂'

end IsRieszProjection

variable [DiscreteTopology I] [DecidableEq I]

/-- The **Riesz projector** `1 - (C b) ^ h` of an endomorphism `u` of `C₀(I, R)` at the scalar
`a`, of order `h`, where `C = 1 - a • u` and `b = c⁻¹ • ΔʰV(a)` is the value at `a` of the `h`-th
Hasse derivative of the Fredholm resolvent, normalised by `c = ΔʰH_u(a)`. When `u` is row compact
and `a` is a good zero of order `h` of the Fredholm determinant `H_u`, it is the unique Riesz
projection of `u` at `a` (`ContinuousLinearMap.IsRowCompact.isRieszProjection_rieszProjection`);
otherwise it is a junk value. -/
noncomputable def rieszProjection (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) (h : ℕ) :
    C₀(I, R) →L[R] C₀(I, R) :=
  1 - ((1 - a • u) * (Ring.inverse
    ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a) •
      u.resolventHasseDerivAt h a)) ^ h

theorem rieszProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) (h : ℕ) :
    u.rieszProjection a h = 1 - ((1 - a • u) * (Ring.inverse
      ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a) •
        u.resolventHasseDerivAt h a)) ^ h :=
  (rfl)

/-- The Riesz projector of order `0` is zero. -/
@[simp]
theorem rieszProjection_order_zero (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    u.rieszProjection a 0 = 0 := by
  rw [rieszProjection_def, pow_zero]
  exact sub_self (1 : C₀(I, R) →L[R] C₀(I, R))

section RowCompact

variable [IsUltrametricDist R]

/-- A Riesz projection of a row-compact operator is row compact, including when its
nilpotence bound is zero. -/
theorem IsRieszProjection.isRowCompact {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h : ℕ}
    (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) :
    E.IsRowCompact := by
  let C : C₀(I, R) →L[R] C₀(I, R) := 1 - a • u
  -- The geometric sum expresses E as a row-compact factor a • u followed by bounded maps.
  have hEq : E = (1 - C) * (∑ i ∈ Finset.range h, C ^ i) * E := by
    rw [mul_neg_geom_sum C h]
    simp only [C, sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul,
      hE.pow_mul_eq_zero, sub_zero (G := C₀(I, R) →L[R] C₀(I, R))]
  have hc : (1 - C).IsRowCompact := by
    simpa only [C, sub_sub_cancel (1 : C₀(I, R) →L[R] C₀(I, R)) (a • u)] using
      hu.smul a
  rw [hEq]
  simpa only [mul_def] using (hc.comp_clm _).comp_clm E

end RowCompact

variable [IsUltrametricDist R] [CompleteSpace R]

/-- **The Riesz projector at a good zero.** Let `u` be row compact, and let `a` be a good zero of
order `h` of its Fredholm determinant `H_u`: `ΔʲH_u(a) = 0` for `j < h` and `ΔʰH_u(a)` is a unit.
Then `1 - (C b) ^ h` is a Riesz projection of `u` at `a` of order `h`. -/
theorem IsRowCompact.isRieszProjection_rieszProjection {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} {h : ℕ}
    (hH : ∀ j < h, (PowerSeries.hasseDeriv j u.matrixCoeff.charPowerSeries).evalAt a = 0)
    (hc : IsUnit ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a)) :
    IsRieszProjection u a h (u.rieszProjection a h) := by
  set C := 1 - a • u
  set b := Ring.inverse ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a) •
    u.resolventHasseDerivAt h a
  have hCb : Commute C b := commute_one_sub_smul_inverse_smul_resolventHasseDerivAt u a _ h
  have hb : C ^ (h + 1) * b = C ^ h :=
    hu.one_sub_smul_pow_succ_mul_inverse_smul_resolventHasseDerivAt hH hc
  have hp := hCb.isIdempotentElem_mul_pow_of_pow_succ_mul_eq (M := C₀(I, R) →L[R] C₀(I, R)) hb
  have hbp : Commute b ((C * b) ^ h) := (hCb.symm.mul_right (Commute.refl b)).pow_right h
  have huC : Commute u C :=
    (Commute.refl u).one_sub_smul_right (A := C₀(I, R) →L[R] C₀(I, R)) a
  have hub : Commute u b := (u.commute_resolventHasseDerivAt h a).smul_right _
  -- Both `C` and `b`, hence `(C b) ^ h`, `1 - (C b) ^ h` and `b (C b) ^ h`, lie in the closure
  -- of `R[u]`, the carrier of the closure subalgebra `T` (`Subalgebra.topologicalClosure_coe`).
  -- The topological semiring structure is synthesized up front, as in
  -- `ContinuousLinearMap.commute_resolventHasseDerivAt`.
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : C₀(I, R) →L[R] C₀(I, R)) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  have hCS : C ∈ T := Subalgebra.le_topologicalClosure _ <|
    Subalgebra.sub_mem (A := C₀(I, R) →L[R] C₀(I, R)) _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton R u) a)
  have hbS : b ∈ T := T.smul_mem ((hT _).2 (u.resolventHasseDerivAt_mem_closure_adjoin h a)) _
  have hpS : (C * b) ^ h ∈ T := T.pow_mem (T.mul_mem hCS hbS) h
  have hES : 1 - (C * b) ^ h ∈ T :=
    Subalgebra.sub_mem (A := C₀(I, R) →L[R] C₀(I, R)) T T.one_mem hpS
  rw [rieszProjection_def]
  refine ⟨IsIdempotentElem.one_sub (R := C₀(I, R) →L[R] C₀(I, R)) hp,
    Commute.sub_right (R := C₀(I, R) →L[R] C₀(I, R)) (Commute.one_right u)
      ((huC.mul_right hub).pow_right h), (hT _).1 hES, ?_, b * (C * b) ^ h, ?_, ?_, ?_, ?_,
    (hT _).1 (T.mul_mem hbS hpS)⟩
  · rw [mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one,
      TauCeti.pow_mul_mul_pow_of_pow_succ_mul_eq (M := C₀(I, R) →L[R] C₀(I, R)) hb]
    exact sub_self _
  · rw [sub_sub_cancel (G := C₀(I, R) →L[R] C₀(I, R)),
      hCb.mul_mul_mul_pow_of_pow_succ_mul_eq (M := C₀(I, R) →L[R] C₀(I, R)) hb]
  · rw [sub_sub_cancel (G := C₀(I, R) →L[R] C₀(I, R)),
      hCb.mul_mul_pow_mul_of_pow_succ_mul_eq (M := C₀(I, R) →L[R] C₀(I, R)) hb]
  · rw [sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul, ← mul_assoc, ← hbp.eq, mul_assoc,
      hp.eq]
    exact sub_self _
  · rw [mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one, mul_assoc, hp.eq]
    exact sub_self _

/-- **The Riesz projector is row compact.** Let `u` be row compact and suppose `ΔʰH_u(a)` is a
unit. Then the Riesz projector `1 - (C b) ^ h` of `u` at `a` is row compact: for `h > 0` it is
`(1 - C b) * ∑ i < h, (C b) ^ i`, where `1 - C b = -ΔʰH_u(a)⁻¹ • u Δʰ⁻¹V(a)`. -/
theorem IsRowCompact.isRowCompact_rieszProjection {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} {h : ℕ}
    (hc : IsUnit ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a)) :
    (u.rieszProjection a h).IsRowCompact := by
  cases h with
  | zero => simp [isRowCompact_zero]
  | succ k =>
    have h1 : (1 - (1 + Ring.inverse
        ((PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a) •
          (u * u.resolventHasseDerivAt k a))).IsRowCompact := by
      rw [sub_add_cancel_left (G := C₀(I, R) →L[R] C₀(I, R)), mul_def]
      exact ((hu.comp_clm _).smul _).neg
    rw [rieszProjection_def, hu.one_sub_smul_mul_inverse_smul_resolventHasseDerivAt_succ hc,
      ← mul_neg_geom_sum (R := C₀(I, R) →L[R] C₀(I, R)), mul_def]
    exact h1.comp_clm _

/-- A Riesz projection of a row-compact `u` at a good zero `a` of order `h` of its Fredholm
determinant is the explicit Riesz projector `1 - (C b) ^ h`. -/
theorem IsRieszProjection.eq_rieszProjection {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h : ℕ}
    (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact)
    (hH : ∀ j < h, (PowerSeries.hasseDeriv j u.matrixCoeff.charPowerSeries).evalAt a = 0)
    (hc : IsUnit ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a)) :
    E = u.rieszProjection a h :=
  hE.unique (hu.isRieszProjection_rieszProjection hH hc)

end Projection

end ContinuousLinearMap
