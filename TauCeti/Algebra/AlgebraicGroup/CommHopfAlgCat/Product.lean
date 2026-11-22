/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# Tensor products of commutative Hopf algebras

For commutative Hopf algebras `H` and `K` over `R`, the tensor product `H ⊗[R] K` is the coordinate
Hopf algebra of the direct product `Spec H × Spec K` of affine group schemes. This file collects
constructions on these tensor products in `CommHopfAlgCat R`.

For `H : CommHopfAlgCat R`, `CommHopfAlgCat.swapEnd H` swaps the two factors of `H ⊗[R] H`,
representing `(g₁, g₂) ↦ (g₂, g₁)` on `Spec H × Spec H`. For isomorphisms `e : H ≅ H'` and
`f : K ≅ K'`, `CommHopfAlgCat.tensorProductCongr e f` is the isomorphism `H ⊗[R] K ≅ H' ⊗[R] K'`
given by the tensor product of the two maps, representing the product `e × f` of the induced
isomorphisms of group schemes.

## Main declarations

* `CommHopfAlgCat.swapEnd`, `swapEnd_comp_swapEnd`, `swapEnd_comp_mulBialgHom`: the factor-swap
  endomorphism, its involutivity, and its invariance on multiplication `H ⊗[R] H ⟶ H`.
* `CommHopfAlgCat.tensorProductCongr`: the tensor product of two isomorphisms, with
  `tensorProductCongr_refl`, `tensorProductCongr_symm` and `tensorProductCongr_trans`.
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{v} R)

/-- The factor-swapping endomorphism `x ⊗ₜ y ↦ y ⊗ₜ x` of `H ⊗[R] H`. -/
noncomputable def swapEnd : CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H) :=
  CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.comm R H H).toBialgHom

/-- Underlying bialgebra morphism of `swapEnd H`. -/
@[simp]
theorem swapEnd_hom : (swapEnd H).hom = (Bialgebra.TensorProduct.comm R H H).toBialgHom :=
  CommHopfAlgCat.hom_ofHom _

/-- Swapping the two tensor factors twice is the identity. -/
@[reassoc (attr := simp)]
theorem swapEnd_comp_swapEnd : swapEnd H ≫ swapEnd H = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) :=
  CommHopfAlgCat.hom_ext <| BialgHom.coe_toAlgHom_injective <|
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- Multiplication `H ⊗[R] H →ₐc[R] H` is invariant under `swapEnd H`. -/
@[reassoc (attr := simp)]
theorem swapEnd_comp_mulBialgHom :
    swapEnd H ≫ CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) =
      CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) :=
  CommHopfAlgCat.hom_ext <| BialgHom.coe_toAlgHom_injective <|
    Algebra.TensorProduct.ext' fun x y ↦ mul_comm y x

section TensorProductCongr

variable {H H' H'' K K' K'' : CommHopfAlgCat.{v} R}

/-- **The tensor product of two isomorphisms of commutative Hopf algebras**: for `e : H ≅ H'`
and `f : K ≅ K'`, the isomorphism `H ⊗[R] K ≅ H' ⊗[R] K'` sending `x ⊗ₜ y` to `e x ⊗ₜ f y`. Its
inverse is the tensor product of the inverses. On affine group schemes it is the product of the
two isomorphisms. -/
noncomputable def tensorProductCongr (e : H ≅ H') (f : K ≅ K') :
    CommHopfAlgCat.of R (H ⊗[R] K) ≅ CommHopfAlgCat.of R (H' ⊗[R] K') where
  hom := CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.map e.hom.hom f.hom.hom)
  inv := CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.map e.inv.hom f.inv.hom)
  hom_inv_id := CommHopfAlgCat.hom_ext <| TauCeti.Bialgebra.TensorProduct.map_comp_map_eq_id
    (congrArg CommHopfAlgCat.Hom.hom e.hom_inv_id) (congrArg CommHopfAlgCat.Hom.hom f.hom_inv_id)
  inv_hom_id := CommHopfAlgCat.hom_ext <| TauCeti.Bialgebra.TensorProduct.map_comp_map_eq_id
    (congrArg CommHopfAlgCat.Hom.hom e.inv_hom_id) (congrArg CommHopfAlgCat.Hom.hom f.inv_hom_id)

/-- The bialgebra map underlying `tensorProductCongr e f` is the tensor product of the bialgebra
maps underlying `e` and `f`. -/
@[simp]
theorem tensorProductCongr_hom_hom (e : H ≅ H') (f : K ≅ K') :
    (tensorProductCongr e f).hom.hom = Bialgebra.TensorProduct.map e.hom.hom f.hom.hom :=
  CommHopfAlgCat.hom_ofHom _

/-- The bialgebra map underlying the inverse of `tensorProductCongr e f` is the tensor product of
the bialgebra maps underlying the inverses of `e` and `f`. -/
@[simp]
theorem tensorProductCongr_inv_hom (e : H ≅ H') (f : K ≅ K') :
    (tensorProductCongr e f).inv.hom = Bialgebra.TensorProduct.map e.inv.hom f.inv.hom :=
  CommHopfAlgCat.hom_ofHom _

/-- `tensorProductCongr e f` sends `x ⊗ₜ y` to `e x ⊗ₜ f y`. -/
theorem tensorProductCongr_hom_hom_tmul (e : H ≅ H') (f : K ≅ K') (x : H) (y : K) :
    (tensorProductCongr e f).hom.hom (x ⊗ₜ[R] y) = e.hom.hom x ⊗ₜ[R] f.hom.hom y := by
  simp

/-- The inverse of a tensor product of isomorphisms is the tensor product of the inverses. -/
@[simp]
theorem tensorProductCongr_symm (e : H ≅ H') (f : K ≅ K') :
    (tensorProductCongr e f).symm = tensorProductCongr e.symm f.symm :=
  (rfl)

/-- The tensor product of two identity isomorphisms is the identity. -/
@[simp]
theorem tensorProductCongr_refl (H K : CommHopfAlgCat.{v} R) :
    tensorProductCongr (Iso.refl H) (Iso.refl K) = Iso.refl (CommHopfAlgCat.of R (H ⊗[R] K)) := by
  ext : 2
  exact BialgHom.coe_toAlgHom_injective <| Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- Tensor products of isomorphisms compose factorwise. -/
theorem tensorProductCongr_trans (e : H ≅ H') (e' : H' ≅ H'') (f : K ≅ K') (f' : K' ≅ K'') :
    tensorProductCongr e f ≪≫ tensorProductCongr e' f' =
      tensorProductCongr (e ≪≫ e') (f ≪≫ f') := by
  ext : 2
  apply BialgHom.coe_toAlgHom_injective
  simp only [Iso.trans_hom, CommHopfAlgCat.hom_comp, tensorProductCongr_hom_hom,
    BialgHom.comp_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom, Algebra.TensorProduct.map_comp]

/-- **Products of involutions.** The tensor product `e ⊗ f` of two automorphisms is an involution
exactly when both `e` and `f` are. The reverse direction restricts to `H ⊗ 1` and `1 ⊗ K`, which
the counit projections retract. -/
theorem tensorProductCongr_hom_comp_self_iff (e : H ≅ H) (f : K ≅ K) :
    (tensorProductCongr e f).hom ≫ (tensorProductCongr e f).hom =
        𝟙 (CommHopfAlgCat.of R (H ⊗[R] K)) ↔
      e.hom ≫ e.hom = 𝟙 H ∧ f.hom ≫ f.hom = 𝟙 K := by
  constructor
  · intro h
    have h' (t : H ⊗[R] K) :=
      congrArg (fun φ : CommHopfAlgCat.of R (H ⊗[R] K) ⟶ _ ↦ φ.hom t) h
    refine ⟨CommHopfAlgCat.hom_ext <| BialgHom.ext fun x ↦ ?_,
      CommHopfAlgCat.hom_ext <| BialgHom.ext fun y ↦ ?_⟩
    · simpa using congrArg (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H)
        (H₂ := K)) (h' (x ⊗ₜ 1))
    · simpa using congrArg (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := H)
        (H₂ := K)) (h' (1 ⊗ₜ y))
  · rintro ⟨he, hf⟩
    refine CommHopfAlgCat.hom_ext <| BialgHom.coe_toAlgHom_injective <|
      Algebra.TensorProduct.ext' fun x y ↦ ?_
    have hx := congrArg (fun φ : H ⟶ H ↦ φ.hom x) he
    have hy := congrArg (fun φ : K ⟶ K ↦ φ.hom y) hf
    simp only [CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hx hy
    simp [hx, hy]

end TensorProductCongr

end CommHopfAlgCat
