/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Pullback.AffineCoordinates
public import TauCeti.AlgebraicGeometry.Limits.Affine.Basic

/-!
# Tensor coordinates on affine-transition inverse limits

Affine pieces of a base-changed finite type morphism admit tensor-product coordinates
compatible with the directed system of their coefficient rings and its colimit.
-/

public section

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Functor

/-- Present an affine piece of a base-changed family by a finite type algebra map,
compatibly with its directed system and every later base change. -/
theorem exists_affine_base_piece_tensor_presentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens)
    (hVT : IsAffineOpen ((pullback.fst Y₀.hom (D.map (homOfLE hk).op)) ⁻¹ᵁ V))
    (hUT : IsAffineOpen (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left ⁻¹ᵁ
      ((pullback.fst Y₀.hom (D.map (homOfLE hk).op)) ⁻¹ᵁ V)))
    (hft : LocallyOfFiniteType
      ((((Over.pullback (D.map (homOfLE hk).op)).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (D.map (homOfLE hk).op)) ⁻¹ᵁ V)))
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    : ∃ (F : {i : I // k ≤ i} ⥤ CommRingCat.{u})
      (B C : CommRingCat.{u})
      (aB : F.obj ⟨k, le_rfl⟩ →+* B) (aC : F.obj ⟨k, le_rfl⟩ →+* C),
      letI : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
      letI : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
      ∃ φ : B →ₐ[F.obj ⟨k, le_rfl⟩] C, φ.FiniteType ∧
        (letI : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
          (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
        Nonempty
          (Arrow.mk
            ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V)) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map
                (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)))) ∧
        (∀ j : {i : I // k ≤ i},
          letI : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
            (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
          Nonempty
            (Arrow.mk
              ((((Over.pullback (D.map (homOfLE (hk.trans j.property)).op)).map f₀).left)
                ∣_ ((pullback.fst Y₀.hom
                  (D.map (homOfLE (hk.trans j.property)).op)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map
                  (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj j)) φ).toRingHom)))) := by
  let d := D.map (homOfLE hk).op
  have hWk : IsAffineOpen (d ⁻¹ᵁ W) := hW.preimage d
  obtain ⟨F, e0, hi, eL, hL⟩ :=
    exists_affineOpen_directedRingSystem D c hc k (d ⁻¹ᵁ W) hWk
  obtain ⟨B, C, aB, aC, φ, hφ, hcomp⟩ :=
    Scheme.Hom.exists_affine_base_piece_tensor_comparison d X₀ Y₀ f₀ V hVT hUT hft W hVW
      (F.obj ⟨k, le_rfl⟩) e0
  let := aB.toAlgebra
  let := aC.toAlgebra
  refine ⟨F, B, C, aB, aC, φ, hφ, ?_, ?_⟩
  · let aL : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
    have h := hcomp c.pt (c.π.app (op k)) (colimit F) aL eL hL
    have heq : c.π.app (op k) ≫ d = c.π.app (op i₀) :=
      c.w (homOfLE hk).op
    rw [heq] at h
    exact h
  · intro j
    let aj : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
      (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
    obtain ⟨ej, hej⟩ := hi j
    have h := hcomp (D.obj (op j.val)) (D.map (homOfLE j.property).op)
      (F.obj j) aj ej hej
    have heq : D.map (homOfLE j.property).op ≫ d =
        D.map (homOfLE (hk.trans j.property)).op := by
      rw [← D.map_comp]
      congr 1
    rw [heq] at h
    exact h

end CategoryTheory.Functor
end
