/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.Algebra.Category.Ring.AdjoinFinset
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Noetherian approximation of affine schemes

Every commutative ring `A` is the filtered colimit of its finitely generated subrings `ℤ[s]`,
`s` a finite subset of `A` (`TauCeti.CommRingCat.isColimitAdjoinFinsetCocone`), and each `ℤ[s]`
is of finite presentation over `ℤ`. Since `Spec` is a right adjoint, `Spec A` is therefore the
cofiltered limit of the affine schemes `Spec ℤ[s]`, which are of finite presentation over `ℤ`,
with affine transition maps. This is the affine case of absolute Noetherian approximation
(Stacks, Proposition 32.5.4 (01ZA)).

## Main declarations

* `AlgebraicGeometry.Scheme.exists_isLimit_finitePresentation_of_isAffine`: every
  affine scheme is a cofiltered limit, with affine transition maps, of affine schemes of finite
  presentation over `ℤ`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Every affine scheme `X` is a cofiltered limit, with affine transition maps, of affine schemes
of finite presentation over `ℤ`. This is the affine case of absolute Noetherian approximation.
Stacks, Proposition 32.5.4 (01ZA), affine case. -/
theorem Scheme.exists_isLimit_finitePresentation_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (π : (Functor.const I).obj X ⟶ D), Nonempty (IsLimit (Cone.mk X π)) ∧
      (∀ ⦃i j : I⦄ (f : i ⟶ j), IsAffineHom (D.map f)) ∧
      ∀ i, IsAffine (D.obj i) ∧ LocallyOfFinitePresentation (terminal.from (D.obj i)) := by
  let A := Γ(X, ⊤)
  let c := Scheme.Spec.mapCone (TauCeti.CommRingCat.adjoinFinsetCocone ℤ A).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec
    (TauCeti.CommRingCat.isColimitAdjoinFinsetCocone ℤ A).op
  refine ⟨(Finset A)ᵒᵖ, inferInstance, inferInstance,
    (TauCeti.CommRingCat.adjoinFinsetDiagram ℤ A).op ⋙ Scheme.Spec, (c.extend X.isoSpec.hom).π,
    ⟨hc.ofIsoLimit (c.extendIso X.isoSpec.symm)⟩, fun _ _ _ ↦ ?_, fun _ ↦ ⟨?_, ?_⟩⟩
  · dsimp; infer_instance
  · dsimp; infer_instance
  · dsimp
    rw [TauCeti.CommRingCat.adjoinFinsetDiagram_obj]
    infer_instance

end AlgebraicGeometry
