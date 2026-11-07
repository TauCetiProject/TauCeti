/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Monoidal
public import TauCeti.Algebra.Category.HopfModuleCat.Basic

/-!
# The monoidal category of all bialgebra modules

For a bialgebra `H` over a field `k`, all left `H`-modules form a monoidal category. The tensor
product is the tensor product over `k`, on which `H` acts through its coproduct
(`BialgebraModule.Tensor`), so `h • (m ⊗ n) = ∑ h₁ • m ⊗ h₂ • n`. The unit is `k` with `H`
acting through its counit (`BialgebraModule.Trivial`). The associator and unitors are the usual
tensor-product equivalences, which are `H`-linear by coassociativity and the counit laws. No
finiteness and no antipode are needed.

This is a tensor product over `k`, not over `H`: even when `H` is commutative, the category
`ModuleCat H` has a different monoidal structure, which is not used here.

The coherence laws are pulled back along the faithful forgetful functor to `ModuleCat k` using
`Monoidal.induced`, exactly as for the finite-dimensional modules of `FiniteHopfModuleCat`. The
forgetful functor is therefore monoidal, and the structure is preadditive and `k`-linear.

The inclusion `FiniteHopfModuleCat.toHopfModuleCat` of the finite-dimensional modules is a
strict monoidal functor: its tensor and unit comparisons are identities. Together with
`FiniteHopfModuleCat.fullyFaithfulToHopfModuleCat`, this identifies the monoidal category of
finite-dimensional modules with a full monoidal subcategory of all modules.

## Main declarations

* `MonoidalCategory (TauCeti.HopfModuleCat k H)`: the monoidal structure.
* `(TauCeti.HopfModuleCat.forgetToModule k H).Monoidal`: the forgetful functor is monoidal.
* `TauCeti.HopfModuleCat.tensor_ext`, `tensorHom_tmul`, `associator_hom_tmul`,
  `leftUnitor_hom_tmul`, `rightUnitor_hom_tmul`: the monoidal structure on pure tensors.
* `(TauCeti.FiniteHopfModuleCat.toHopfModuleCat k H).Monoidal`: the inclusion of
  finite-dimensional modules is monoidal, with identity comparisons
  (`FiniteHopfModuleCat.toHopfModuleCat_μ`, `FiniteHopfModuleCat.toHopfModuleCat_ε`).

## References

See C. Kassel, *Quantum Groups*, Proposition III.5.1, for the tensor product of modules over a
bialgebra, and M. Khovanov, *Hopfological algebra and categorification at a root of unity: the
first steps*, §1, for its use on the category of all modules over a finite-dimensional Hopf
algebra.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti

open BialgebraModule

universe u v

namespace HopfModuleCat

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Bialgebra k H]

/-- The coproduct tensor product, counit unit, associator and unitors on all modules over a
bialgebra. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (HopfModuleCat k H) where
  tensorObj M N := of (Tensor k H M N)
  whiskerLeft _ _ _ g := ofHom (tensorMap k H LinearMap.id g.hom)
  whiskerRight f _ := ofHom (tensorMap k H f.hom LinearMap.id)
  tensorHom f g := ofHom (tensorMap k H f.hom g.hom)
  tensorUnit := of (Trivial k H)
  associator M N P := (assoc k H M N P).toHopfModuleCatIso
  leftUnitor M := (lid k H M).toHopfModuleCatIso
  rightUnitor M := (rid k H M).toHopfModuleCatIso

section Struct

variable {k H}
variable {M M' N N' P : HopfModuleCat k H}

/-- The tensor product of morphisms is the tensor product of the underlying intertwiners. -/
theorem tensorHom_hom (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g).hom = tensorMap k H f.hom g.hom := (rfl)

/-- Left whiskering tensors the underlying intertwiner with the identity on the left. -/
theorem whiskerLeft_hom (g : N ⟶ N') :
    (M ◁ g).hom = tensorMap k H LinearMap.id g.hom := (rfl)

/-- Right whiskering tensors the underlying intertwiner with the identity on the right. -/
theorem whiskerRight_hom (f : M ⟶ M') :
    (f ▷ N).hom = tensorMap k H f.hom LinearMap.id := (rfl)

/-- The associator is the reassociation equivalence `BialgebraModule.assoc`. -/
theorem associator_hom_hom : (α_ M N P).hom.hom = (assoc k H M N P).toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_hom_hom _

/-- The inverse associator is the inverse reassociation equivalence. -/
theorem associator_inv_hom : (α_ M N P).inv.hom = (assoc k H M N P).symm.toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_inv_hom _

/-- The left unitor is the left unit equivalence `BialgebraModule.lid`. -/
theorem leftUnitor_hom_hom : (λ_ M).hom.hom = (lid k H M).toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_hom_hom _

/-- The inverse left unitor is the inverse left unit equivalence. -/
theorem leftUnitor_inv_hom : (λ_ M).inv.hom = (lid k H M).symm.toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_inv_hom _

/-- The right unitor is the right unit equivalence `BialgebraModule.rid`. -/
theorem rightUnitor_hom_hom : (ρ_ M).hom.hom = (rid k H M).toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_hom_hom _

/-- The inverse right unitor is the inverse right unit equivalence. -/
theorem rightUnitor_inv_hom : (ρ_ M).inv.hom = (rid k H M).symm.toLinearMap := 
  LinearEquiv.toHopfModuleCatIso_inv_hom _

/-- Morphisms out of a tensor product are determined by their values on pure tensors. -/
@[ext]
theorem tensor_ext {X : HopfModuleCat k H} {f g : M ⊗ N ⟶ X}
    (h : ∀ (m : M) (n : N), f.hom (tmul k H m n) = g.hom (tmul k H m n)) : f = g :=
  hom_ext (Tensor.ext h)

/-- The tensor product of morphisms acts on pure tensors factorwise. -/
@[simp]
theorem tensorHom_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (f ⊗ₘ g).hom (tmul k H m n) = tmul k H (f.hom m) (g.hom n) :=
  tensorMap_tmul k H _ _ m n

/-- Left whiskering acts on the right factor of a pure tensor. -/
@[simp]
theorem whiskerLeft_tmul (g : N ⟶ N') (m : M) (n : N) :
    (M ◁ g).hom (tmul k H m n) = tmul k H m (g.hom n) :=
  tensorMap_tmul k H _ _ m n

/-- Right whiskering acts on the left factor of a pure tensor. -/
@[simp]
theorem whiskerRight_tmul (f : M ⟶ M') (m : M) (n : N) :
    (f ▷ N).hom (tmul k H m n) = tmul k H (f.hom m) n :=
  tensorMap_tmul k H _ _ m n

/-- The associator reassociates pure tensors. -/
@[simp]
theorem associator_hom_tmul (m : M) (n : N) (p : P) :
    (α_ M N P).hom.hom (tmul k H (tmul k H m n : ↑(M ⊗ N)) p) =
      tmul k H m (tmul k H n p : ↑(N ⊗ P)) :=
  (LinearMap.congr_fun associator_hom_hom _).trans (assoc_tmul k H m n p)

/-- The inverse associator reassociates pure tensors. -/
@[simp]
theorem associator_inv_tmul (m : M) (n : N) (p : P) :
    (α_ M N P).inv.hom (tmul k H m (tmul k H n p : ↑(N ⊗ P))) =
      tmul k H (tmul k H m n : ↑(M ⊗ N)) p :=
  (LinearMap.congr_fun associator_inv_hom _).trans (assoc_symm_tmul k H m n p)

/-- The left unitor scales by the element of the unit object. -/
@[simp]
theorem leftUnitor_hom_tmul (r : (𝟙_ (HopfModuleCat k H) : HopfModuleCat k H)) (m : M) :
    (λ_ M).hom.hom (tmul k H r m) = trivialEquiv k H r • m :=
  (LinearMap.congr_fun leftUnitor_hom_hom _).trans (lid_tmul k H r m)

/-- The inverse left unitor inserts the unit of the unit object. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) :
    (λ_ M).inv.hom m =
      tmul k H ((trivialEquiv k H).symm 1 : (𝟙_ (HopfModuleCat k H) : HopfModuleCat k H)) m :=
  (LinearMap.congr_fun leftUnitor_inv_hom _).trans (lid_symm_apply k H m)

/-- The right unitor scales by the element of the unit object. -/
@[simp]
theorem rightUnitor_hom_tmul (m : M) (r : (𝟙_ (HopfModuleCat k H) : HopfModuleCat k H)) :
    (ρ_ M).hom.hom (tmul k H m r) = trivialEquiv k H r • m :=
  (LinearMap.congr_fun rightUnitor_hom_hom _).trans (rid_tmul k H m r)

/-- The inverse right unitor inserts the unit of the unit object. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) :
    (ρ_ M).inv.hom m =
      tmul k H m ((trivialEquiv k H).symm 1 : (𝟙_ (HopfModuleCat k H) : HopfModuleCat k H)) :=
  (LinearMap.congr_fun rightUnitor_inv_hom _).trans (rid_symm_apply k H m)

end Struct

/-- The data inducing the monoidal structure along the forgetful functor to `k`-modules. The
tensor comparison is the inverse of `BialgebraModule.tensorEquiv`, and the unit comparison is
the inverse of `BialgebraModule.trivialEquiv`. -/
def inducingFunctorData : Monoidal.InducingFunctorData (forgetToModule k H) where
  μIso M N := (tensorEquiv k H M N).symm.toModuleIso
  whiskerLeft_eq _ _ _ g := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H LinearMap.id g.hom x)
  whiskerRight_eq f _ := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H f.hom LinearMap.id x)
  tensorHom_eq f g := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H f.hom g.hom x)
  εIso := (trivialEquiv k H).symm.toModuleIso
  associator_eq M N P := by
    ext x
    exact (LinearMap.congr_fun associator_hom_hom x).trans
      ((LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_assoc k H M N P x))
  leftUnitor_eq M := by
    ext x
    exact (LinearMap.congr_fun leftUnitor_hom_hom x).trans (lid_apply k H M x)
  rightUnitor_eq M := by
    ext x
    exact (LinearMap.congr_fun rightUnitor_hom_hom x).trans (rid_apply k H M x)

/-- All modules over a bialgebra form a monoidal category under the tensor product over the base
field, with `H` acting through its coproduct. -/
instance instMonoidalCategory : MonoidalCategory (HopfModuleCat k H) :=
  Monoidal.induced (forgetToModule k H) (inducingFunctorData k H)

/-- The forgetful functor to `k`-modules is monoidal. -/
instance : (forgetToModule k H).Monoidal :=
  Monoidal.fromInducedMonoidal (forgetToModule k H) (inducingFunctorData k H)

instance : MonoidalPreadditive (HopfModuleCat k H) :=
  monoidalPreadditive_of_faithful (forgetToModule k H)

instance : MonoidalLinear k (HopfModuleCat k H) :=
  MonoidalLinear.ofFaithful k (forgetToModule k H)

variable {k H}

/-- The tensor comparison of the forgetful functor identifies the native tensor product with
the coproduct tensor product. -/
@[simp]
theorem forgetToModule_μ (M N : HopfModuleCat k H) :
    Functor.LaxMonoidal.μ (forgetToModule k H) M N =
      ModuleCat.ofHom (tensorEquiv k H M N).symm.toLinearMap := (rfl)

/-- The unit comparison of the forgetful functor identifies `k` with the trivial module. -/
@[simp]
theorem forgetToModule_ε :
    Functor.LaxMonoidal.ε (forgetToModule k H) =
      ModuleCat.ofHom (trivialEquiv k H).symm.toLinearMap := (rfl)

end HopfModuleCat

namespace FiniteHopfModuleCat

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Bialgebra k H]

/-- The inclusion of finite-dimensional modules into all modules is strictly monoidal: the
tensor product and unit of finite-dimensional modules are those of all modules. -/
def coreMonoidalToHopfModuleCat : (toHopfModuleCat k H).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left _ _ := (rfl)
  μIso_hom_natural_right _ _ := (rfl)
  associativity _ _ _ := by
    simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    exact HopfModuleCat.hom_ext
      (FiniteHopfModuleCat.associator_hom_hom.trans HopfModuleCat.associator_hom_hom.symm)
  left_unitality _ := by
    simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp]
    exact HopfModuleCat.hom_ext
      (HopfModuleCat.leftUnitor_hom_hom.trans FiniteHopfModuleCat.leftUnitor_hom_hom.symm)
  right_unitality _ := by
    simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp]
    exact HopfModuleCat.hom_ext
      (HopfModuleCat.rightUnitor_hom_hom.trans FiniteHopfModuleCat.rightUnitor_hom_hom.symm)

/-- The inclusion of finite-dimensional modules into all modules is monoidal. -/
instance : (toHopfModuleCat k H).Monoidal := (coreMonoidalToHopfModuleCat k H).toMonoidal

variable {k H}

/-- The tensor comparison of the inclusion of finite-dimensional modules is the identity. -/
@[simp]
theorem toHopfModuleCat_μ (M N : FiniteHopfModuleCat k H) :
    Functor.LaxMonoidal.μ (toHopfModuleCat k H) M N = 𝟙 _ := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, coreMonoidalToHopfModuleCat]

/-- The unit comparison of the inclusion of finite-dimensional modules is the identity. -/
@[simp]
theorem toHopfModuleCat_ε : Functor.LaxMonoidal.ε (toHopfModuleCat k H) = 𝟙 _ := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_ε, coreMonoidalToHopfModuleCat]

end FiniteHopfModuleCat

end TauCeti
