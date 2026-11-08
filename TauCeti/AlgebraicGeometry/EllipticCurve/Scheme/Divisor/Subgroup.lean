/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.FormalPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.GroupLaw
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.RingTheory.FormalGroup.CharP

/-!
# Multiples of the zero section which are subgroup schemes

For an elliptic Weierstrass equation over an arbitrary ring, if the divisor `pⁿ[0]` is a
subgroup scheme, with `p` prime and `n > 0`, then `p = 0` in the coefficient ring.
This is the characteristic assertion in the elliptic case of Katz–Mazur's scheme rigidity
engine. It applies over nonreduced rings and is not a statement about the abstract order of
the zero point.

More generally, closure of `q[0]` under addition forces the formal addition series to satisfy
`F(X,Y)^q ∈ (X^q,Y^q)`. The two universal truncated formal points lie on `q[0]`, so their sum
also lies on it. The formal-group characteristic theorem then applies.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Lemmas 5.3.3–5.3.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.IdealSheafData

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- A submonoid structure on the divisor `q[0]` implies closure of its formal equation
`X^q = 0` under the formal addition law. In particular, this applies to subgroup schemes. -/
theorem formalAdd_pow_mem_span_of_zeroSectionDivisor_submonoid (q : ℕ)
    (h : ∃ _ : MonObj (Over.mk ((W.zeroSectionDivisor ^ q).subschemeι ≫ W.projModelOver)),
      IsMonHom (Over.homMk (W.zeroSectionDivisor ^ q).subschemeι :
        Over.mk ((W.zeroSectionDivisor ^ q).subschemeι ≫ W.projModelOver) ⟶
          Over.mk W.projModelOver)) :
    W.formalAdd ^ q ∈ Ideal.span
      {MvPowerSeries.X (Sum.inl () : Unit ⊕ Unit) ^ q,
        MvPowerSeries.X (Sum.inr () : Unit ⊕ Unit) ^ q} := by
  -- Work with the two universal points annihilated by the divisor's formal equation.
  let A := MvPowerSeries (Unit ⊕ Unit) R
  let J : Ideal A := Ideal.span
    {MvPowerSeries.X (Sum.inl () : Unit ⊕ Unit) ^ q,
      MvPowerSeries.X (Sum.inr () : Unit ⊕ Unit) ^ q}
  let a : Spec (.of (A ⧸ J)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let I := W.zeroSectionDivisor ^ q
  let D := Over.mk (I.subschemeι ≫ W.projModelOver)
  let i : D ⟶ Over.mk W.projModelOver := Over.homMk I.subschemeι
  obtain ⟨hD, hi⟩ := h
  let : MonObj D := hD
  let : IsMonHom i := hi
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  let T := Over.mk (a ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let point (s : A) (hs : PowerSeries.HasSubst s) : T ⟶ Over.mk W.projModelOver :=
    Over.homMk (a ≫ Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom hs).toRingHom) ≫
      W.projModelFormalPoint) (by
        simp only [Over.mk_hom, Category.assoc, projModelFormalPoint_projModelOver, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, T])
  have hpoint (s : A) (hs : PowerSeries.HasSubst s) :
      I ≤ (point s hs).left.ker ↔ s ^ q ∈ J := by
    simp only [point, Over.homMk_left, I, a,
      W.zeroSectionDivisor_pow_le_ker_subst_projModelFormalPoint_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  let x := point (MvPowerSeries.X (Sum.inl ())) (PowerSeries.HasSubst.X _)
  let y := point (MvPowerSeries.X (Sum.inr ())) (PowerSeries.HasSubst.X _)
  have hx : I ≤ x.left.ker := (hpoint _ _).mpr (Ideal.subset_span (by simp))
  have hy : I ≤ y.left.ker := (hpoint _ _).mpr (Ideal.subset_span (by simp))
  -- Their product lies on the divisor because its inclusion is a monoid homomorphism.
  have hxy : I ≤ (x * y).left.ker := by
    simpa [i] using i.ker_le_mul_left x y
      (by simpa [i] using hx) (by simpa [i] using hy)
  -- The scheme addition comparison identifies the parameter of that product.
  have he : x * y = point W.formalAdd
      (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalAdd) := by
    apply Over.OverMorphism.ext
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, mul_projModelOver_left]
    simp only [x, y, point, Over.homMk_left]
    rw [← W.lift_projModelFormalPoint_additionMorphism]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  rw [he] at hxy
  exact (hpoint _ _).mp hxy

/-- If `pⁿ[0]` is a submonoid scheme of an elliptic Weierstrass model, with `p` prime and
`n > 0`, then `p` vanishes in the base ring. No reducedness or Noetherian hypothesis is needed. -/
theorem natCast_eq_zero_of_zeroSectionDivisor_submonoid {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ∃ _ : MonObj (Over.mk ((W.zeroSectionDivisor ^ p ^ n).subschemeι ≫ W.projModelOver)),
      IsMonHom (Over.homMk (W.zeroSectionDivisor ^ p ^ n).subschemeι :
        Over.mk ((W.zeroSectionDivisor ^ p ^ n).subschemeι ≫ W.projModelOver) ⟶
          Over.mk W.projModelOver)) :
    (p : R) = 0 := by
  apply W.formalGroup.natCast_eq_zero_of_pow_mem_span hp hn
  have H := Ideal.mem_map_of_mem (MvPowerSeries.rename TauCeti.unitSumUnitEquivFinTwo)
    (W.formalAdd_pow_mem_span_of_zeroSectionDivisor_submonoid (p ^ n) h)
  simpa [formalGroup_toPowerSeries, Ideal.map_span, Set.image_pair,
    MvPowerSeries.rename_X] using H

end WeierstrassCurve
