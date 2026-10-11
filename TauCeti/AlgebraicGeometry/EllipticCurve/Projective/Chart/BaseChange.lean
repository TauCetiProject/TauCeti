/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of the standard Weierstrass charts

The three standard affine charts of a projective Weierstrass cubic commute with arbitrary
extension of the coefficient ring. The comparison is an algebra equivalence
`S ⊗[R] ChartRing W i ≃ₐ[S] ChartRing (W.map (algebraMap R S)) i`, characterized on
pure tensors by coefficient extension. No flatness or ellipticity assumption is needed.

These comparisons give the affine pieces of base change for the projective cubic. The map
`chartRingMap` also makes coefficient extension available for arbitrary ring homomorphisms.
Its functoriality laws are `TauCeti.chartRingMap_id`,
`TauCeti.chartRingMap_comp_chartRingMap`, and `TauCeti.chartRingMap_chartRingMap`.

The construction uses Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv` and
`MvPolynomial.algebraTensorAlgEquiv`.

## References

* [R. Hartshorne, *Algebraic Geometry*, II.3 (fibre products)][hartshorne1977]
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
-/

public section

open MvPolynomial TensorProduct

namespace WeierstrassCurve.Projective

variable {R S : Type*} [CommRing R] [CommRing S]
variable (W : Projective R) (i : Fin 3) (f : R →+* S)

/-- The equations of a standard chart extend coefficientwise. -/
@[simp]
theorem map_chartRelation (k : Fin 2) :
    MvPolynomial.map f (W.chartRelation i k) = (W.map f).chartRelation i k := by
  fin_cases k <;> simp [map_polynomial]

/-- The defining ideal of a standard chart extends coefficientwise. -/
theorem map_span_chartRelation :
    (Ideal.span (Set.range (W.chartRelation i))).map (MvPolynomial.map f) =
      Ideal.span (Set.range ((W.map f).chartRelation i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, map_chartRelation]

/-- Coefficient extension on the coordinate ring of a standard Weierstrass chart. -/
noncomputable def chartRingMap : W.ChartRing i →+* (W.map f).ChartRing i :=
  Ideal.quotientMap _ (MvPolynomial.map f)
    (Ideal.map_le_iff_le_comap.mp (W.map_span_chartRelation i f).le)

/-- Coefficient extension sends the class of a polynomial to the class of its image. -/
@[simp]
theorem chartRingMap_mk (p : MvPolynomial (Fin 3) R) :
    W.chartRingMap i f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) :=
  Ideal.quotientMap_mk

/-- Coefficient extension respects the structure maps of the chart rings. -/
@[simp]
theorem chartRingMap_algebraMap (r : R) :
    W.chartRingMap i f (algebraMap R (W.ChartRing i) r) =
      algebraMap S ((W.map f).ChartRing i) (f r) := by
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
  simp only [MvPolynomial.algebraMap_eq, chartRingMap_mk, map_C]

section Algebra

variable [Algebra R S]

private theorem map_chartIdeal_tensor :
    Ideal.span (Set.range ((W.map (algebraMap R S)).chartRelation i)) =
      ((Ideal.span (Set.range (W.chartRelation i))).map
        (Algebra.TensorProduct.includeRight (A := S) (R := R))).map
          (↑(MvPolynomial.algebraTensorAlgEquiv (σ := Fin 3) R S) :
            S ⊗[R] MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) S) := by
  simp only [Ideal.map_span, ← Set.range_comp, Function.comp_def,
    Algebra.TensorProduct.includeRight_apply]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext k
  symm
  exact (MvPolynomial.algebraTensorAlgEquiv_tmul (σ := Fin 3) (R := R) (A := S)
    1 (W.chartRelation i k)).trans (by simp)

/-- Arbitrary scalar extension commutes with the coordinate ring of each standard affine chart
of the projective Weierstrass cubic. -/
noncomputable def chartRingBaseChangeEquiv :
    S ⊗[R] W.ChartRing i ≃ₐ[S] (W.map (algebraMap R S)).ChartRing i :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial (Fin 3) R) S
    (Ideal.span (Set.range (W.chartRelation i)))).trans
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
        (W.map_chartIdeal_tensor i))

/-- The chart comparison sends `s ⊗ [p]` to `s • [map p]`. -/
private theorem chartRingBaseChangeEquiv_tmul_mk (s : S) (p : MvPolynomial (Fin 3) R) :
    W.chartRingBaseChangeEquiv i (s ⊗ₜ[R] Ideal.Quotient.mk _ p) =
      s • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := by
  rw [chartRingBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact map_smul (Ideal.Quotient.mkₐ S _) s _

/-- On pure tensors, the comparison uses the coefficient-extension map on chart rings. -/
@[simp]
theorem chartRingBaseChangeEquiv_tmul (s : S) (x : W.ChartRing i) :
    W.chartRingBaseChangeEquiv i (s ⊗ₜ[R] x) =
      s • W.chartRingMap i (algebraMap R S) x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa only [chartRingMap_mk] using W.chartRingBaseChangeEquiv_tmul_mk i s p

/-- The inverse comparison recovers the original chart element as `1 ⊗ x` from its
coefficient extension. -/
@[simp]
theorem chartRingBaseChangeEquiv_symm_chartRingMap (x : W.ChartRing i) :
    (W.chartRingBaseChangeEquiv (S := S) i).symm
      (W.chartRingMap i (algebraMap R S) x) = 1 ⊗ₜ[R] x := by
  apply (W.chartRingBaseChangeEquiv i).injective
  simp

end Algebra

end WeierstrassCurve.Projective

namespace TauCeti

open WeierstrassCurve.Projective

variable {R S : Type*} [CommRing R] [CommRing S]
variable {W : WeierstrassCurve.Projective R} {i : Fin 3}

/-- Coefficient extension along the identity is the identity on the chart ring. -/
@[simp]
theorem chartRingMap_id : W.chartRingMap i (RingHom.id R) = RingHom.id (W.ChartRing i) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [chartRingMap_mk, MvPolynomial.map_id]
  exact (RingHom.id_apply _).symm

/-- Successive coefficient extensions compose to extension along the composite ring map. -/
theorem chartRingMap_comp_chartRingMap {T : Type*} [CommRing T]
    {f : R →+* S} {g : S →+* T} :
    ((W.map f).chartRingMap i g).comp (W.chartRingMap i f) =
      W.chartRingMap i (g.comp f) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply, chartRingMap_mk, chartRingMap_mk, MvPolynomial.map_map]
  exact (W.chartRingMap_mk i (g.comp f) p).symm

/-- Successive coefficient extensions on an element normalize to a single extension. -/
@[simp]
theorem chartRingMap_chartRingMap {T : Type*} [CommRing T]
    {f : R →+* S} {g : S →+* T} (x : W.ChartRing i) :
    (W.map f).chartRingMap i g (W.chartRingMap i f x) =
      W.chartRingMap i (g.comp f) x :=
  RingHom.congr_fun (chartRingMap_comp_chartRingMap (W := W) (i := i) (f := f) (g := g)) x

end TauCeti
