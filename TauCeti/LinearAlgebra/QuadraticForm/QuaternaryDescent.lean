/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

/-!
# Quaternary descent

Let `F` be a field of characteristic not two and `Q` a regular quadratic form of dimension four
over `F` whose discriminant is the square class of a nonsquare `d`. Let `E = F(√d)`, a quadratic
field extension of `F`. Then `Q` is isotropic over `F` exactly when its scalar extension to `E` is
isotropic (O'Meara 58:7).

This is what makes a quaternary form accessible to arguments over the discriminant field: over
`E` the discriminant of `Q` becomes a square, and the theorem descends isotropy back to `F`.

The hypotheses have the following roles.

* The dimension is exactly four. Over `F = ℚ(i)`, the binary form `⟨1, 2⟩` has discriminant `[2]`
  and is anisotropic, as `-2` is not a square in `ℚ(i)`, but it becomes isotropic over `F(√2)`,
  where `-2 = (i√2)²`.
* The discriminant is the plain discriminant `TauCeti.RegularFormClass.discr`; in dimension four
  the signed discriminant differs from it by the class of `-1`.
* `E` is a quadratic extension of `F` containing a square root `s` of the nonsquare `d`, which
  pins it down as `F(s)`. A larger field containing a square root of `d`, such as `F(√d, √e)`, is
  not covered.

## Main results

* `QuadraticForm.not_anisotropic_of_not_anisotropic_baseChange_quaternary`: quaternary descent of
  isotropy from `F(√d)` to `F`.
* `QuadraticForm.anisotropic_baseChange_iff_quaternary`: a quaternary form of nonsquare discriminant
  `d` is anisotropic over `F(√d)` exactly when it is anisotropic over `F`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), 58:7.
-/

public section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

section OrthogonalPair

variable [Invertible (2 : F)] [FiniteDimensional F V]

/-- The descent step: in a regular quaternary space of discriminant `[d]`, an orthogonal pair
`x, y` with `Q x = -d Q y ≠ 0` forces isotropy, because its orthogonal complement is a plane of
discriminant `[-1]`. -/
private theorem not_anisotropic_of_orthogonal_pair (Q : QuadraticForm F V) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank F V = 4) (d : Fˣ)
    (hd : RegularFormClass.discr (formClass Q hQ) = squareClass d) {x y : V} (e : Fˣ)
    (hy : Q y = e) (hx : Q x = ((-d * e : Fˣ) : F)) (hxy : polar Q x y = 0) :
    ¬Q.Anisotropic := by
  intro hA
  let W := LinearMap.range (Fintype.linearCombination F ![x, y])
  let eW := Q.orthogonalPairIsometryEquiv (-d * e) e hx hy hxy
  have hW : (Q.restrict W).Nondegenerate :=
    eW.nondegenerate_iff.mp (nondegenerate_presentedForm _)
  let P := LinearMap.BilinForm.orthogonal Q.polarBilin W
  have hP : (Q.restrict P).Nondegenerate := hQ.nondegenerate_restrict_orthogonal hW
  have hsplit : Q.Equivalent ((presentedForm ⟨2, ![-d * e, e]⟩).prod (Q.restrict P)) :=
    QuadraticMap.Equivalent.trans
      ⟨(QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q W hW.isCompl_orthogonal).symm⟩
      (QuadraticMap.Equivalent.prod ⟨eW.symm⟩ (QuadraticMap.Equivalent.refl _))
  obtain ⟨⟨n, v⟩, hv⟩ := exists_presentedForm_equivalent (Q.restrict P) hP
  have hclass : formClass Q hQ =
      Quotient.mk _ ⟨2, ![-d * e, e]⟩ + Quotient.mk (regularFormSetoid F) ⟨n, v⟩ := by
    rw [← formClass_presentedForm, ← formClass_mk _ hP _ hv, ← formClass_prod]
    exact (formClass_eq_iff _ _ _ _).mpr hsplit
  have hn : n = 2 := by
    have := congrArg RegularFormClass.rank hclass
    rw [rank_formClass, hdim, RegularFormClass.rank_add, RegularFormClass.rank_mk,
      RegularFormClass.rank_mk] at this
    simp only at this
    omega
  subst hn
  -- Comparing discriminants shows that `-(v 0 * v 1)` is a square.
  have hdisc := congrArg RegularFormClass.discr hclass
  rw [hd, RegularFormClass.discr_add, RegularFormClass.discr_mk, RegularFormClass.discr_mk,
    ← squareClass_mul, squareClass_eq_iff_isSquare_mul] at hdisc
  obtain ⟨r, hr⟩ := hdisc
  have hr' : (r : F) * r = d * (-d * e * e * (v 0 * v 1)) := by
    simpa [Fin.prod_univ_two, mul_assoc] using congrArg Units.val hr.symm
  -- The plane `⟨v 0, v 1⟩` is isotropic at `(r, d e v 0)`.
  have hiso : ¬(presentedForm ⟨2, v⟩).Anisotropic := by
    intro hA'
    have h0 := congrFun (hA' ![(r : F), d * e * v 0] (by
      rw [presentedForm_apply]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination (v 0 : F) * hr')) 1
    simp [d.ne_zero, e.ne_zero, (v 0).ne_zero] at h0
  exact hiso ((hv.anisotropic_iff).mp fun z hz => Subtype.ext (hA z hz))

end OrthogonalPair

variable [Invertible (2 : F)] [FiniteDimensional F V]
  {E : Type w} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- **Quaternary descent** (O'Meara 58:7). Let `Q` be a regular quadratic form of dimension four
over a field `F` of characteristic not two, whose discriminant is the square class of a nonsquare
`d`, and let `E` be a field of degree two over `F` containing a square root `s` of `d`, so that
`E = F(s)`. If `Q` is isotropic over `E`, then it is isotropic over `F`. -/
theorem _root_.QuadraticForm.not_anisotropic_of_not_anisotropic_baseChange_quaternary
    (Q : QuadraticForm F V)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank F V = 4) (d : Fˣ)
    (hd : RegularFormClass.discr (formClass Q hQ) = squareClass d) (hdsq : ¬IsSquare d)
    (s : E) (hs : s * s = algebraMap F E d)
    (h : ¬(Q.baseChange E).Anisotropic) : ¬Q.Anisotropic := by
  intro hA
  have hs' : s ∉ Set.range (algebraMap F E) := by
    rintro ⟨r, rfl⟩
    have hr : r * r = d := (algebraMap F E).injective (by rw [map_mul, hs])
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact d.ne_zero (by rw [← hr, mul_zero])
    exact hdsq ⟨Units.mk0 r hr0, Units.ext hr.symm⟩
  have hli := TauCeti.linearIndependent_one_of_notMem_range_algebraMap F E hs'
  -- Every vector of `E ⊗ V` is `1 ⊗ x + s ⊗ y`, using the basis `1, s` of `E`.
  have hdecomp (z : E ⊗[F] V) : ∃ x y : V, z = (1 : E) ⊗ₜ x + s ⊗ₜ y := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul e v =>
      obtain ⟨a, b, rfl⟩ :=
        Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul F E hs' e
      refine ⟨b • v, a • v, ?_⟩
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        TensorProduct.add_tmul]
    | add z z' hz hz' =>
      obtain ⟨x, y, rfl⟩ := hz
      obtain ⟨x', y', rfl⟩ := hz'
      exact ⟨x + x', y + y', by simp only [TensorProduct.tmul_add]; abel⟩
  rw [QuadraticMap.not_anisotropic_iff_exists] at h
  obtain ⟨z, hz0, hz⟩ := h
  obtain ⟨x, y, rfl⟩ := hdecomp z
  rw [QuadraticMap.map_add (Q.baseChange E), QuadraticForm.polar_baseChange_tmul,
    baseChange_tmul, baseChange_tmul] at hz
  -- Read off the coordinates of `Q_E (1 ⊗ x + s ⊗ y)` along the basis `1, s`.
  obtain ⟨hxy, hpolar⟩ := LinearIndependent.pair_iff.mp hli (Q x + d * Q y) (polar Q x y) (by
    simp only [Algebra.smul_def, one_mul, mul_one, map_add, map_mul] at hz ⊢
    linear_combination hz - algebraMap F E (Q y) * hs)
  have hy : Q y ≠ 0 := by
    intro hy
    have hx : Q x = 0 := by simpa [hy] using hxy
    exact hz0 (by rw [hA x hx, hA y hy]; simp)
  refine not_anisotropic_of_orthogonal_pair Q hQ hdim d hd (Units.mk0 _ hy) rfl ?_ hpolar hA
  simp only [Units.val_mul, Units.val_neg, Units.val_mk0]
  linear_combination hxy

/-- **Quaternary descent**, as an equivalence: a regular quaternary form whose discriminant is the
square class of a nonsquare `d` is anisotropic over `F(√d)` exactly when it is anisotropic over
`F`. -/
theorem _root_.QuadraticForm.anisotropic_baseChange_iff_quaternary
    (Q : QuadraticForm F V) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank F V = 4) (d : Fˣ)
    (hd : RegularFormClass.discr (formClass Q hQ) = squareClass d) (hdsq : ¬IsSquare d)
    (s : E) (hs : s * s = algebraMap F E d) :
    (Q.baseChange E).Anisotropic ↔ Q.Anisotropic :=
  ⟨fun h => by_contra fun hQ' => not_anisotropic_baseChange hQ' h,
    fun h => by_contra fun hE =>
      Q.not_anisotropic_of_not_anisotropic_baseChange_quaternary hQ hdim d hd hdsq s hs hE h⟩

end TauCeti
