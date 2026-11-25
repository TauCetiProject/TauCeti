/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.InverseTranspose
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic

/-!
# Inverse transpose on a transpose-stable closed subgroup of `GLₙ`

Let `G ⊆ GLₙ` be a closed subgroup over a commutative ring `R`, cut out by a Hopf ideal `I` of the
coordinate Hopf algebra of `GLₙ`. Inverse transpose `θ(g) = (g⁻¹)ᵀ` maps `I` onto itself exactly
when every group of algebra-valued points of `G` is stable under inverse transpose, equivalently
under transpose. Then `θ` restricts to an automorphism of `G`, an involution whose fixed points are
the points of `G` with orthogonal matrices.

## Main declarations

* `TauCeti.GeneralLinear.inverseTransposeQuotientIso`: inverse transpose restricted to a closed
  subgroup of `GLₙ` that it maps onto itself.

## Main results

* `TauCeti.GeneralLinear.comapOfSurjective_inverseTransposeCoordinateIso_eq_iff`: the Hopf ideal
  `I` is stable under inverse transpose exactly when every group of algebra-valued points of the
  subgroup it cuts out is stable under inverse transpose;
  `TauCeti.GeneralLinear.comapOfSurjective_inverseTransposeCoordinateIso_eq_iff_transpose_mem` is
  the same criterion for stability under transpose. Their forward directions, for algebras in
  any universe, are `TauCeti.GeneralLinear.inverseTranspose_mem_hopfIdealPointsSubgroup` and
  `TauCeti.GeneralLinear.unop_transposeMulEquiv_mem_hopfIdealPointsSubgroup`.
* `TauCeti.GeneralLinear.comp_inverseTransposeQuotientIso_eq_self_iff`: the fixed points of the
  restricted involution are the points of the subgroup with orthogonal matrices.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Precomposing a point with the inverse-transpose coordinate automorphism, read back from inverse
transpose of its matrix. -/
private theorem pointsMulEquiv_symm_inverseTranspose (A : Type v) [CommRing A] [Algebra R A]
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (pointsMulEquiv n).symm
        (Matrix.GeneralLinearGroup.inverseTranspose (pointsMulEquiv n f)) =
      toConv (f.ofConv.comp ((inverseTransposeCoordinateIso R n).hom.hom :
        coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n)) := by
  rw [← pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso, MulEquiv.symm_apply_apply]

/-- If the inverse-transpose coordinate automorphism of `GLₙ` maps the Hopf ideal `I` onto itself,
then for every commutative `R`-algebra `A` (in any universe) the subgroup of `GLₙ(A)` cut out by `I`
is stable under inverse transpose. -/
theorem inverseTranspose_mem_hopfIdealPointsSubgroup {I : HopfIdeal R (coordinateHopfAlgebra R n)}
    (hI : I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
      (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I)
    {A : Type v} [CommRing A] [Algebra R A] {g : GL (Fin n) A}
    (hg : g ∈ hopfIdealPointsSubgroup n I A) :
    Matrix.GeneralLinearGroup.inverseTranspose g ∈ hopfIdealPointsSubgroup n I A := by
  rw [mem_hopfIdealPointsSubgroup_iff] at hg ⊢
  intro x hx
  rw [← (pointsMulEquiv (R := R) n).apply_symm_apply g, pointsMulEquiv_symm_inverseTranspose]
  rw [← hI, HopfIdeal.mem_comapOfSurjective] at hx
  exact hg _ hx

/-- If the inverse-transpose coordinate automorphism of `GLₙ` maps the Hopf ideal `I` onto itself,
then for every commutative `R`-algebra `A` (in any universe) the subgroup of `GLₙ(A)` cut out by `I`
is stable under transpose. -/
theorem unop_transposeMulEquiv_mem_hopfIdealPointsSubgroup
    {I : HopfIdeal R (coordinateHopfAlgebra R n)}
    (hI : I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
      (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I)
    {A : Type v} [CommRing A] [Algebra R A] {g : GL (Fin n) A}
    (hg : g ∈ hopfIdealPointsSubgroup n I A) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈
      hopfIdealPointsSubgroup n I A := by
  -- Transpose is inverse transpose of the inverse, and the subgroup is closed under inverses.
  rw [Matrix.GeneralLinearGroup.unop_transposeMulEquiv_eq_inverseTranspose_inv]
  exact inverseTranspose_mem_hopfIdealPointsSubgroup hI (inv_mem hg)

/-- **Stability under inverse transpose, in coordinates and on points.** The inverse-transpose
coordinate automorphism of `GLₙ` maps the Hopf ideal `I` onto itself exactly when, for every
commutative `R`-algebra `A`, the subgroup of `GLₙ(A)` cut out by `I` is stable under inverse
transpose. For stability under transpose, see
`comapOfSurjective_inverseTransposeCoordinateIso_eq_iff_transpose_mem`. -/
theorem comapOfSurjective_inverseTransposeCoordinateIso_eq_iff
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) :
    I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
        (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A], ∀ g ∈ hopfIdealPointsSubgroup (R := R) n I A,
        Matrix.GeneralLinearGroup.inverseTranspose g ∈ hopfIdealPointsSubgroup n I A := by
  set θ := (inverseTransposeCoordinateIso R n).hom.hom
  refine ⟨fun hI A _ _ g hg ↦ inverseTranspose_mem_hopfIdealPointsSubgroup hI hg, fun h ↦ ?_⟩
  -- Test stability on the universal point of the subgroup, the quotient map.
  have hle : I.comapOfSurjective θ
      (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 ≤ I := by
    intro x hx
    let f : WithConv (coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n ⧸ I.toIdeal) :=
      toConv (Ideal.Quotient.mkₐ R I.toIdeal)
    have hf : pointsMulEquiv n f ∈ hopfIdealPointsSubgroup n I _ := by
      rw [mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply]
      intro y hy
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have hθf := h _ _ hf
    rw [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_symm_inverseTranspose] at hθf
    have := hθf _ (HopfIdeal.mem_comapOfSurjective.mp hx)
    have hθθ : θ (θ x) = x :=
      congr($(inverseTransposeCoordinateIso_hom_comp_self (R := R) (n := n)).hom x)
    simp only [AlgHom.comp_apply, f] at this
    rw [← hθθ]
    exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp this)
  exact HopfIdeal.comapOfSurjective_eq_of_hom_le_of_inv_le _ I hle
    (by simpa only [← Iso.symm_hom, inverseTransposeCoordinateIso_symm] using hle)

/-- **Stability under transpose, in coordinates and on points.** The inverse-transpose coordinate
automorphism of `GLₙ` maps the Hopf ideal `I` onto itself exactly when, for every commutative
`R`-algebra `A`, the subgroup of `GLₙ(A)` cut out by `I` is stable under transpose. -/
theorem comapOfSurjective_inverseTransposeCoordinateIso_eq_iff_transpose_mem
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) :
    I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
        (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A], ∀ g ∈ hopfIdealPointsSubgroup (R := R) n I A,
        (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈
          hopfIdealPointsSubgroup n I A := by
  refine ⟨fun hI A _ _ g hg ↦ unop_transposeMulEquiv_mem_hopfIdealPointsSubgroup hI hg,
    fun h ↦ ?_⟩
  -- Transpose is inverse transpose of the inverse, and the subgroup is closed under inverses.
  rw [comapOfSurjective_inverseTransposeCoordinateIso_eq_iff]
  intro A _ _ g hg
  simpa only [Matrix.GeneralLinearGroup.unop_transposeMulEquiv_eq_inverseTranspose_inv,
    inv_inv] using h A _ (inv_mem hg)

section GeneralRing

variable (I : HopfIdeal R (coordinateHopfAlgebra R n))
  (hI : I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
    (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I)

/-- **Inverse transpose on a transpose-stable closed subgroup of `GLₙ`.** The coordinate
automorphism of the closed subgroup cut out by a Hopf ideal `I` that is stable under inverse
transpose, induced by the inverse-transpose coordinate automorphism of `GLₙ`. -/
noncomputable def inverseTransposeQuotientIso :
    _root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I ≅
      _root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I :=
  CommHopfAlgCat.quotientIsoOfComapEq (inverseTransposeCoordinateIso R n) I hI

/-- Unfolding `TauCeti.GeneralLinear.inverseTransposeQuotientIso`. -/
theorem inverseTransposeQuotientIso_def :
    inverseTransposeQuotientIso I hI =
      CommHopfAlgCat.quotientIsoOfComapEq (inverseTransposeCoordinateIso R n) I hI :=
  (rfl)

/-- The restricted inverse transpose sends the class of `x` to the class of its inverse
transpose. -/
@[simp↓]
theorem inverseTransposeQuotientIso_hom_mk (x : coordinateHopfAlgebra R n) :
    (inverseTransposeQuotientIso I hI).hom.hom (Ideal.Quotient.mk I.toIdeal x) =
      Ideal.Quotient.mk I.toIdeal ((inverseTransposeCoordinateIso R n).hom.hom x) :=
  CommHopfAlgCat.quotientIsoOfComapEq_hom_mk _ I hI x

/-- The restricted inverse transpose is an involution. -/
@[reassoc (attr := simp)]
theorem inverseTransposeQuotientIso_hom_comp_self :
    (inverseTransposeQuotientIso I hI).hom ≫ (inverseTransposeQuotientIso I hI).hom =
      𝟙 (_root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) :=
  CommHopfAlgCat.quotientIsoOfComapEq_hom_comp_self inverseTransposeCoordinateIso_hom_comp_self I hI

/-- The restricted inverse transpose is its own inverse. -/
@[simp]
theorem inverseTransposeQuotientIso_symm :
    (inverseTransposeQuotientIso I hI).symm = inverseTransposeQuotientIso I hI :=
  CommHopfAlgCat.quotientIsoOfComapEq_symm_eq_self inverseTransposeCoordinateIso_hom_comp_self I hI

/-- The inverse of the restricted inverse transpose is the restricted inverse transpose. -/
@[simp]
theorem inverseTransposeQuotientIso_inv :
    (inverseTransposeQuotientIso I hI).inv = (inverseTransposeQuotientIso I hI).hom :=
  congrArg Iso.hom (inverseTransposeQuotientIso_symm I hI)

/-- The inverse of the restricted inverse transpose sends the class of `y` to the class of its
inverse transpose. -/
@[simp↓]
theorem inverseTransposeQuotientIso_inv_mk (y : coordinateHopfAlgebra R n) :
    (inverseTransposeQuotientIso I hI).inv.hom (Ideal.Quotient.mk I.toIdeal y) =
      Ideal.Quotient.mk I.toIdeal ((inverseTransposeCoordinateIso R n).hom.hom y) := by
  rw [inverseTransposeQuotientIso_inv, inverseTransposeQuotientIso_hom_mk]

/-- **The fixed points of the restricted inverse transpose are the orthogonal points.** A point `p`
of the closed subgroup cut out by `I` is fixed by inverse transpose exactly when the matrix of the
point `p ∘ (O(GLₙ) → O(GLₙ) ⧸ I)` of `GLₙ` is orthogonal. -/
theorem comp_inverseTransposeQuotientIso_eq_self_iff (A : Type v) [CommRing A]
    [Algebra R A] (p : coordinateHopfAlgebra R n ⧸ I.toIdeal →ₐ[R] A) :
    p.comp ((inverseTransposeQuotientIso I hI).hom.hom :
        coordinateHopfAlgebra R n ⧸ I.toIdeal →ₐ[R] coordinateHopfAlgebra R n ⧸ I.toIdeal) = p ↔
      pointsMulEquiv n (toConv (p.comp (Ideal.Quotient.mkₐ R I.toIdeal))) ∈
        GLOrthogonal (Fin n) A := by
  rw [← toConv_comp_inverseTransposeCoordinateIso_eq_self_iff, toConv_injective.eq_iff,
    ofConv_toConv]
  exact CommHopfAlgCat.comp_quotientIsoOfComapEq_eq_self_iff I hI p

end GeneralRing


end TauCeti.GeneralLinear
