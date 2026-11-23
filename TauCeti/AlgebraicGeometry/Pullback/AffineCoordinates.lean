/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import TauCeti.AlgebraicGeometry.Pullback.Over
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Affine
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Affine coordinates in base-changed families

On affine source and target opens, pullback morphisms are identified with
tensor products of the corresponding algebra maps. The comparisons respect arbitrary further
base change and include empty affine opens.
-/


public section

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom


/-- Affine coordinates identify every further base change of a restricted over-morphism
with the spectrum of a tensor product map. -/
theorem affine_base_piece_tensor_base_change
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (R B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C)
    (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (eB : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ≅ Spec B)
    (eC : ((((Over.pullback d).map f₀).left) ⁻¹ᵁ
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)).toScheme ≅ Spec C)
    : letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∀ (φ : B →ₐ[R] C),
        eB.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ≫ e0.hom →
        eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          ((((Over.pullback d).map f₀).left) ∣_
            ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)) ≫ eB.hom →
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u})
          (aA : Algebra R A) (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
          t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          Nonempty
            (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  intro φ hB hC L t A aA e he
  let : Algebra R B := aB.toAlgebra
  let : Algebra R C := aC.toAlgebra
  let := aA
  obtain ⟨i⟩ := Scheme.Hom.restricted_composite_base_change d X₀ Y₀ f₀ V W q hq L t
  obtain ⟨j⟩ := Scheme.Hom.nonempty_pullbackMap_arrowIso_specMap_tensorProduct
    ((((Over.pullback d).map f₀).left) ∣_ ((pullback.fst Y₀.hom d) ⁻¹ᵁ V))
    q (t.resLE (d ⁻¹ᵁ W) _ le_rfl) R A B C φ e0 eB eC e hB.symm hC.symm he
  exact ⟨i ≪≫ j⟩
end AlgebraicGeometry.Scheme.Hom
end

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom


/-- Affine source and target pieces of a finite type morphism admit compatible tensor-product
coordinates under arbitrary further base change. -/
theorem exists_affine_base_piece_tensor_comparison
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀) (V : Y₀.left.Opens)
    (hVT : IsAffineOpen ((pullback.fst Y₀.hom d) ⁻¹ᵁ V))
    (hUT : IsAffineOpen (((Over.pullback d).map f₀).left ⁻¹ᵁ
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)))
    (hft : LocallyOfFiniteType ((((Over.pullback d).map f₀).left) ∣_
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)))
    (W : S.Opens) (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (R : CommRingCat.{u}) (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R) :
    ∃ (B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C),
      letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∃ φ : B →ₐ[R] C, φ.FiniteType ∧
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
            t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            Nonempty
              (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
                ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
                Arrow.mk (Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom)))  := by
  let fT := ((Over.pullback d).map f₀).left
  let VT := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  have : LocallyOfFiniteType (fT ∣_ VT) := hft
  let : IsAffine VT.toScheme := hVT
  let : IsAffine (fT ⁻¹ᵁ VT).toScheme := hUT
  have hVW' : VT ≤ (pullback.snd Y₀.hom d) ⁻¹ᵁ (d ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.fst Y₀.hom d).preimage_mono hVW
  let q := (pullback.snd Y₀.hom d).resLE (d ⁻¹ᵁ W) VT hVW'
  obtain ⟨aB, aC, φ, hφ, hB, hC⟩ :=
    Scheme.Hom.exists_finiteType_appTop_model (fT ∣_ VT) R (q ≫ e0.hom)
  let : Algebra R Γ(VT.toScheme, ⊤) := aB.toAlgebra
  let : Algebra R Γ((fT ⁻¹ᵁ VT).toScheme, ⊤) := aC.toAlgebra
  refine ⟨Γ(VT.toScheme, ⊤), Γ((fT ⁻¹ᵁ VT).toScheme, ⊤), aB, aC, φ, hφ, ?_⟩
  exact affine_base_piece_tensor_base_change d X₀ Y₀ f₀ V W R _ _ aB aC e0 q
    (Scheme.Hom.resLE_comp_ι _ _) VT.toScheme.isoSpec (fT ⁻¹ᵁ VT).toScheme.isoSpec
    φ hB hC

end AlgebraicGeometry.Scheme.Hom
end
