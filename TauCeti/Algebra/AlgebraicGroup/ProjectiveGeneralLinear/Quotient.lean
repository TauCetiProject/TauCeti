/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# `PGLₙ` represents the fppf quotient of `GLₙ` by its center

Let `R` be a commutative ring. The automorphism group scheme `PGLₙ` of the matrix algebra `Mₙ`
receives the conjugation homomorphism `GLₙ → PGLₙ`. This file proves that `PGLₙ` is the fppf
quotient of `GLₙ` by the kernel of this homomorphism, and over a field by the center of `GLₙ`:

```text
GLₙ / Z(GLₙ) ≅ PGLₙ
```

as group objects in fppf sheaves, the quotient projection becoming the conjugation homomorphism.

The conjugation homomorphism is not surjective on points: an automorphism of `Mₙ(A)` need not be
inner. It is, however, inner Zariski-locally on `Spec A`
(`AlgEquiv.exists_span_eq_top_forall_map_eq_innerAut`), so every point of `PGLₙ` lifts to `GLₙ`
after the faithfully flat, finitely presented extension `A → ∏ A[1/c]` given by a finite Zariski
cover. This is the hypothesis of the fppf first isomorphism theorem
`TauCeti.CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift`. Over a field the kernel is
the center of `GLₙ` (`TauCeti.ProjectiveGeneralLinear.kernelHopfIdeal_conjugationMap`).

## Main declarations

* `TauCeti.ProjectiveGeneralLinear.exists_span_eq_top_forall_mapPoints_mem_range`: every point
  of `PGLₙ` lifts to `GLₙ` Zariski-locally.
* `TauCeti.ProjectiveGeneralLinear.kernelFppfQuotientIso`: `PGLₙ` is the fppf quotient of `GLₙ`
  by the kernel of the conjugation homomorphism, over any commutative ring.
* `TauCeti.ProjectiveGeneralLinear.centerQuotientFppfIso`: over a field, `PGLₙ` is the fppf
  quotient of `GLₙ` by its center.

## References

* J. S. Milne, *Algebraic Groups* (2017), where `PGLₙ` is the quotient of `GLₙ` by its center
  `𝔾ₘ` and is identified with the automorphism group functor of `Mₙ`.
* M.-A. Knus, M. Ojanguren, *Théorie de la descente et algèbres d'Azumaya*, Lecture Notes in
  Mathematics 389, Chapter IV, for the local innerness of automorphisms of matrix algebras.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u

noncomputable section

variable (n : ℕ) {R : Type u} [CommRing R]

/-- **Points of `PGLₙ` lift to `GLₙ` Zariski-locally.** For every point `q` of `PGLₙ` with values
in `A` there are finitely many elements of `A` generating the unit ideal such that, for each of
them `c`, the image of `q` in `A[1/c]` is the image of a point of `GLₙ` under the conjugation
homomorphism. -/
theorem exists_span_eq_top_forall_mapPoints_mem_range (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n R) A) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧ ∀ c ∈ s,
      HopfAlgebra.mapPoints
          (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (Localization.Away c))) q ∈
        Set.range ((CommHopfAlgCat.mapPointsFunctor (conjugationMap n R)).app
          (CommAlgCat.of R (Localization.Away c))) := by
  obtain ⟨s, hs, h⟩ := (pointsMulEquiv n R A q).exists_span_eq_top_forall_map_eq_innerAut
  refine ⟨s, hs, fun c hc => ?_⟩
  let ψ := CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (Localization.Away c))
  obtain ⟨g, hg⟩ := h c hc (algebraMap A (Localization.Away c))
    (IsLocalization.Away.algebraMap_isUnit c)
  refine ⟨(GeneralLinear.pointsMulEquiv n).symm g, (pointsMulEquiv n R _).injective ?_⟩
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply, pointsMulEquiv_conjugationMap,
    MulEquiv.apply_symm_apply]
  -- Both automorphisms of `Mₙ(A[1/c])` agree on the matrix units, which come from `Mₙ(A)`.
  refine AlgEquiv.toLinearMap_injective ((matrixUnitBasis n _).ext fun k => ?_)
  have hk : matrixUnitBasis n (Localization.Away c) k = (matrixUnitBasis n A k).map ψ := by
    simp [ψ, Matrix.map_single]
  rw [AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, hk, pointsMulEquiv_mapPoints]
  exact (hg _).symm

/-- Every point of `PGLₙ` lifts to `GLₙ` after a faithfully flat, finitely presented extension of
its value algebra, namely the product of the localizations of a finite Zariski cover. -/
private theorem exists_lift_conjugationMap (A : CommAlgCat.{u} R)
    (y : coordinateHopfAlgebra n R →ₐ[R] A) :
    ∃ (B : CommAlgCat.{u} R) (φ : A ⟶ B)
      (z : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] B),
      φ.hom.toRingHom.FaithfullyFlat ∧ φ.hom.toRingHom.FinitePresentation ∧
        z.comp (conjugationMap n R).hom.toAlgHom = φ.hom.comp y := by
  obtain ⟨s, hs, h⟩ := exists_span_eq_top_forall_mapPoints_mem_range n A (toConv y)
  choose g hg using h
  let S : s → Type u := fun c => Localization.Away (c : A)
  let φ : A →ₐ[R] ∀ c, S c := AlgHom.pi fun c => IsScalarTower.toAlgHom R A (S c)
  have hφ : φ.toRingHom = RingHom.pi fun c : s => algebraMap A (S c) := by
    ext
    simp [φ, S]
  refine ⟨CommAlgCat.of R (∀ c, S c), CommAlgCat.ofHom φ,
    AlgHom.pi fun c => (g c c.2).ofConv, ?_, ?_, ?_⟩
  · rw [CommAlgCat.hom_ofHom, hφ]
    refine RingHom.FaithfullyFlat.pi_algebraMap_localizationAway _ ?_
    rwa [Subtype.range_coe_subtype, Finset.setOfPred_mem]
  · have (c : s) : Algebra.FinitePresentation A (S c) :=
      IsLocalization.Away.finitePresentation (c : A)
    rw [CommAlgCat.hom_ofHom, hφ]
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  · ext x c
    have := DFunLike.congr_fun (congrArg ofConv (hg c c.2)) x
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply (conjugationMap n R)
      (CommAlgCat.of R (S c)) (g c c.2) x, HopfAlgebra.mapPoints_apply] at this
    simpa [φ, S] using this

/-- **`GLₙ → PGLₙ` is an fppf quotient map**: over any commutative ring, the comparison from the
fppf quotient of `GLₙ` by the kernel of the conjugation homomorphism to `PGLₙ` is an isomorphism
of group objects in fppf sheaves. -/
instance isIso_kernelFppfQuotientHom_conjugationMap :
    IsIso (CommHopfAlgCat.kernelFppfQuotientHom (conjugationMap n R)) :=
  CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift _ (exists_lift_conjugationMap n)

/-- **`PGLₙ` is the fppf quotient of `GLₙ` by the kernel of conjugation**, over any commutative
ring. -/
def kernelFppfQuotientIso :
    CommHopfAlgCat.fppfQuotientSheaf (GeneralLinear.coordinateHopfAlgebra R n)
        (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n R))
        (CommHopfAlgCat.isNormal_kernelHopfIdeal (conjugationMap n R)) ≅
      CommHopfAlgCat.pointsFppfGroupObject (coordinateHopfAlgebra n R) :=
  asIso (CommHopfAlgCat.kernelFppfQuotientHom (conjugationMap n R))

/-- The forward map of `kernelFppfQuotientIso` is the kernel-quotient comparison. -/
@[simp]
theorem kernelFppfQuotientIso_hom :
    (kernelFppfQuotientIso n (R := R)).hom =
      CommHopfAlgCat.kernelFppfQuotientHom (conjugationMap n R) :=
  (rfl)

section Field

variable (k : Type u) [Field k]

/-- **`PGLₙ` is the fppf quotient of `GLₙ` by its center**: over a field, the fppf center quotient
`GLₙ / Z(GLₙ)` is represented by the automorphism group scheme `PGLₙ` of the matrix algebra. -/
def centerQuotientFppfIso :
    CommHopfAlgCat.centerQuotientFppfSheaf (GeneralLinear.coordinateHopfAlgebra k n) ≅
      CommHopfAlgCat.pointsFppfGroupObject (coordinateHopfAlgebra n k) :=
  eqToIso (by simp only [kernelHopfIdeal_conjugationMap]) ≪≫ kernelFppfQuotientIso n

/-- Under `centerQuotientFppfIso`, the projection `GLₙ → GLₙ / Z(GLₙ)` is the conjugation
homomorphism `GLₙ → PGLₙ`. -/
@[reassoc (attr := simp)]
theorem centerQuotientFppfProjection_comp_centerQuotientFppfIso_hom :
    CommHopfAlgCat.centerQuotientFppfProjection (GeneralLinear.coordinateHopfAlgebra k n) ≫
        (centerQuotientFppfIso n k).hom =
      CommHopfAlgCat.pointsFppfGroupObjectMap (conjugationMap n k) := by
  rw [centerQuotientFppfIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    CommHopfAlgCat.centerQuotientFppfProjection_def]
  have transport (I J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k n)) (hI : I.IsNormal)
      (hJ : J.IsNormal) (h : J = I)
      (e : CommHopfAlgCat.fppfQuotientSheaf _ I hI = CommHopfAlgCat.fppfQuotientSheaf _ J hJ) :
      CommHopfAlgCat.fppfQuotientProjection _ I hI ≫ eqToHom e =
        CommHopfAlgCat.fppfQuotientProjection _ J hJ := by
    subst J
    simp
  rw [transport _ _ _ _ (kernelHopfIdeal_conjugationMap n k), kernelFppfQuotientIso_hom,
    CommHopfAlgCat.fppfQuotientProjection_comp_kernelFppfQuotientHom]

end Field

end

end TauCeti.ProjectiveGeneralLinear
