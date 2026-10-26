/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint

/-!
# The zero-section divisor in the formal parameter

The formal point `[X : -1 : w(X)]` of a projective Weierstrass model pulls the ideal of the zero
section back to `(X)`. Consequently the divisor `n[0]` pulls back to `(Xⁿ)`, including over
nonreduced coefficient rings. These are identities of ideal sheaves, rather than statements about
their supports: they retain the multiplicities needed in formal subgroup calculations.

On the chart `D₊(Y)` the zero-section ideal is `(X/Y, Z/Y)`. At the formal point its generators
are `-X` and `-w(X)`; since `w(0) = 0`, the resulting ideal is `(X)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §5.3.
-/

public section

open CategoryTheory AlgebraicGeometry PowerSeries Scheme.IdealSheafData

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- Evaluation on the chart with middle coordinate one, at `[-X : 1 : -w(X)]`.
private noncomputable def formalChartHom : W.toProjective.ChartRing 1 →ₐ[R] R⟦X⟧ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![-X, 1, -W.formalW]) <| fun _ hp ↦
    RingHom.mem_ker.mp <| Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · have h := (W.toProjective.equation_neg_one_iff_wEquation X W.formalW).mpr
        W.formalW_wEquation
      have h' := (Projective.equation_smul _ (isUnit_neg_one : IsUnit (-1 : R⟦X⟧))).mpr h
      simpa using (W.toProjective.equation_map_iff_aeval _).mp h'
    · simp) hp

private theorem formalChartHom_mk_X (i : Fin 3) :
    W.formalChartHom (Ideal.Quotient.mk _ (MvPolynomial.X i)) = ![-X, 1, -W.formalW] i := by
  rw [formalChartHom, Ideal.Quotient.liftₐ_apply]
  exact MvPolynomial.aeval_X ![-X, 1, -W.formalW] i

private theorem SpecMap_formalChartHom_chartι :
    Spec.map (CommRingCat.ofHom W.formalChartHom.toRingHom) ≫ W.chartι 1 =
      W.projModelFormalPoint := by
  rw [W.SpecMap_chartι, projModelFormalPoint_def, projModelPoint_eq_projModelPoint_iff]
  refine ⟨by ext; simp, -1, funext fun i ↦ ?_⟩
  fin_cases i <;> simp [formalChartHom_mk_X]

/-- The ideal of the zero section at the formal point is `(X)`. This holds for every Weierstrass
equation, without an ellipticity hypothesis. -/
@[simp]
theorem zeroSectionDivisor_comap_projModelFormalPoint :
    W.zeroSectionDivisor.comap W.projModelFormalPoint =
      ofIdealTop ((Ideal.span {(X : R⟦X⟧)}).map (Scheme.ΓSpecIso (.of R⟦X⟧)).inv.hom) := by
  -- Pull back the known chart ideal, then transport evaluation through `ΓSpecIso`.
  rw [← W.SpecMap_formalChartHom_chartι, comap_comp,
    zeroSectionDivisor_comap_chartι_one, comap_ofIdealTop, Ideal.map_map]
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom W.formalChartHom.toRingHom)
  rw [← CommRingCat.hom_comp, ← hn, CommRingCat.hom_comp, ← Ideal.map_map]
  congr 1
  rw [Ideal.map_span, Set.image_pair]
  simp only [CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Projective.chartPoint_apply, formalChartHom_mk_X, Matrix.cons_val]
  congr 1
  -- The second generator lies in `(X)` because the `w`-expansion has zero constant term.
  rw [Ideal.span_insert, Ideal.span_singleton_neg, Ideal.span_singleton_neg]
  apply sup_eq_left.mpr
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
    (Ideal.mem_span_singleton.mpr (PowerSeries.X_dvd_iff.mpr W.constantCoeff_formalW)))

/-- The ideal of `n[0]` at the formal point is `(Xⁿ)`, with its scheme-theoretic multiplicity. -/
-- Use the coordinate formula before the general pullback-of-powers rule.
@[simp 1100]
theorem zeroSectionDivisor_pow_comap_projModelFormalPoint (n : ℕ) :
    (W.zeroSectionDivisor ^ n).comap W.projModelFormalPoint =
      ofIdealTop ((Ideal.span {(X : R⟦X⟧) ^ n}).map (Scheme.ΓSpecIso (.of R⟦X⟧)).inv.hom) := by
  rw [comap_pow, zeroSectionDivisor_comap_projModelFormalPoint, ← ofIdealTop_pow,
    ← Ideal.map_pow, Ideal.span_singleton_pow]

/-- After reparametrising the formal point by `X ↦ s`, the ideal of `n[0]` is `(sⁿ)`.
The series `s` need only admit substitution; it need not be an invertible parameter. -/
-- Compute the pullback before simplification changes the substitution morphism.
@[simp↓]
theorem zeroSectionDivisor_pow_comap_subst_projModelFormalPoint {s : R⟦X⟧} (hs : HasSubst s)
    (n : ℕ) :
    (W.zeroSectionDivisor ^ n).comap
        (Spec.map (CommRingCat.ofHom (substAlgHom hs).toRingHom) ≫ W.projModelFormalPoint) =
      ofIdealTop ((Ideal.span {s ^ n}).map (Scheme.ΓSpecIso (.of R⟦X⟧)).inv.hom) := by
  rw [comap_comp, zeroSectionDivisor_pow_comap_projModelFormalPoint, comap_ofIdealTop,
    Ideal.map_map, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp, ← Ideal.map_map]
  congr 1
  simp [Ideal.map_span, substAlgHom_X]

/-- An invertible formal parameter change `X ↦ X * v`, with `v` a unit, preserves the ideal
of every multiple of the zero section. No reducedness assumption on `R` is needed. -/
theorem zeroSectionDivisor_pow_comap_subst_unit_projModelFormalPoint (v : R⟦X⟧ˣ) (n : ℕ) :
    (W.zeroSectionDivisor ^ n).comap
        (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (substAlgHom
          (HasSubst.of_constantCoeff_zero' (by simp : constantCoeff (X * (v : R⟦X⟧)) = 0))))) ≫
            W.projModelFormalPoint) =
      (W.zeroSectionDivisor ^ n).comap W.projModelFormalPoint := by
  rw [zeroSectionDivisor_pow_comap_subst_projModelFormalPoint,
    zeroSectionDivisor_pow_comap_projModelFormalPoint, mul_pow,
    Ideal.span_singleton_mul_right_unit (v.isUnit.pow n)]

end WeierstrassCurve
