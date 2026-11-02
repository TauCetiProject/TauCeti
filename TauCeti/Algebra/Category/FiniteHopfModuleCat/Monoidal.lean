/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Basic

/-!
# The monoidal category of finite-dimensional bialgebra modules

For a bialgebra `H` over a field `k`, finite-dimensional `H`-modules form a monoidal category.
The tensor product is the tensor product over `k`, on which `H` acts through its coproduct
(`BialgebraModule.Tensor`). The unit is `k` with `H` acting through its counit
(`BialgebraModule.Trivial`). The associator and unitors are the usual tensor-product
equivalences, which are `H`-linear by coassociativity and the counit laws.

This is a tensor product over `k`, not over `H`: even when `H` is commutative, the category
`ModuleCat H` has a different monoidal structure, which is not used here.

The coherence laws are pulled back along the faithful forgetful functor to `ModuleCat k`
using `Monoidal.induced`, which also makes this forgetful functor monoidal. Its tensor
comparison is the identification `BialgebraModule.tensorEquiv` of the coproduct tensor
product with the native one. The monoidal structure is preadditive and `k`-linear.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.inducingFunctorData`: the comparison data along the forgetful
  functor `forgetToModule k H`.
* `MonoidalCategory (TauCeti.FiniteHopfModuleCat k H)`: the monoidal structure.
* `(TauCeti.FiniteHopfModuleCat.forgetToModule k H).Monoidal`: the forgetful functor is monoidal.
* `TauCeti.FiniteHopfModuleCat.tensor_ext`, `tensorHom_tmul`, `associator_hom_tmul`,
  `leftUnitor_hom_tmul`, `rightUnitor_hom_tmul`: the monoidal structure on pure tensors.
* `TauCeti.FiniteHopfModuleCat.whiskerLeft_hom_hom`, `associator_hom_hom`,
  `leftUnitor_hom_hom`, and their companions: the underlying intertwiners of the monoidal
  structure, as module-level maps of `BialgebraModule`.

## References

See C. Kassel, *Quantum Groups*, Proposition III.5.1, for the tensor product of modules over a
bialgebra. The packaging follows Mathlib's monoidal structure on `CoalgCat`, which is also
induced along the forgetful functor to modules.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Bialgebra k H]

/-- The coproduct tensor product, counit unit, associator and unitors on finite-dimensional
modules over a bialgebra. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (FiniteHopfModuleCat k H) where
  tensorObj M N := of (Tensor k H M N)
  whiskerLeft _ _ _ g := ofHom (tensorMap k H LinearMap.id g.hom.hom)
  whiskerRight f _ := ofHom (tensorMap k H f.hom.hom LinearMap.id)
  tensorHom f g := ofHom (tensorMap k H f.hom.hom g.hom.hom)
  tensorUnit := of (Trivial k H)
  associator M N P := (assoc k H M N P).toFiniteHopfModuleCatIso
  leftUnitor M := (lid k H M).toFiniteHopfModuleCatIso
  rightUnitor M := (rid k H M).toFiniteHopfModuleCatIso

section Struct

variable {k H}
variable {M M' N N' P : FiniteHopfModuleCat k H}

/-- The tensor product of morphisms is the tensor product of the underlying intertwiners. -/
theorem tensorHom_hom_hom (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g).hom.hom = tensorMap k H f.hom.hom g.hom.hom := (rfl)

/-- Left whiskering tensors the underlying intertwiner with the identity on the left. -/
theorem whiskerLeft_hom_hom (g : N ⟶ N') :
    (M ◁ g).hom.hom = tensorMap k H LinearMap.id g.hom.hom := (rfl)

/-- Right whiskering tensors the underlying intertwiner with the identity on the right. -/
theorem whiskerRight_hom_hom (f : M ⟶ M') :
    (f ▷ N).hom.hom = tensorMap k H f.hom.hom LinearMap.id := (rfl)

/-- The associator is the reassociation equivalence `BialgebraModule.assoc`. -/
theorem associator_hom_hom :
    (α_ M N P).hom.hom.hom = (assoc k H M N P).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The inverse associator is the inverse reassociation equivalence. -/
theorem associator_inv_hom :
    (α_ M N P).inv.hom.hom = (assoc k H M N P).symm.toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_inv_hom _

/-- The left unitor is the left unit equivalence `BialgebraModule.lid`. -/
theorem leftUnitor_hom_hom : (λ_ M).hom.hom.hom = (lid k H M).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The inverse left unitor is the inverse left unit equivalence. -/
theorem leftUnitor_inv_hom : (λ_ M).inv.hom.hom = (lid k H M).symm.toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_inv_hom _

/-- The right unitor is the right unit equivalence `BialgebraModule.rid`. -/
theorem rightUnitor_hom_hom : (ρ_ M).hom.hom.hom = (rid k H M).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The inverse right unitor is the inverse right unit equivalence. -/
theorem rightUnitor_inv_hom : (ρ_ M).inv.hom.hom = (rid k H M).symm.toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_inv_hom _

/-- Morphisms out of a tensor product are determined by their values on pure tensors. -/
@[ext]
theorem tensor_ext {X : FiniteHopfModuleCat k H} {f g : M ⊗ N ⟶ X}
    (h : ∀ (m : M) (n : N), f.hom.hom (tmul k H m n) = g.hom.hom (tmul k H m n)) : f = g :=
  hom_ext (Tensor.ext h)

/-- The tensor product of morphisms acts on pure tensors factorwise. -/
@[simp]
theorem tensorHom_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (f ⊗ₘ g).hom.hom (tmul k H m n) = tmul k H (f.hom.hom m) (g.hom.hom n) :=
  tensorMap_tmul k H _ _ m n

/-- Left whiskering acts on the right factor of a pure tensor. -/
@[simp]
theorem whiskerLeft_tmul (g : N ⟶ N') (m : M) (n : N) :
    (M ◁ g).hom.hom (tmul k H m n) = tmul k H m (g.hom.hom n) :=
  tensorMap_tmul k H _ _ m n

/-- Right whiskering acts on the left factor of a pure tensor. -/
@[simp]
theorem whiskerRight_tmul (f : M ⟶ M') (m : M) (n : N) :
    (f ▷ N).hom.hom (tmul k H m n) = tmul k H (f.hom.hom m) n :=
  tensorMap_tmul k H _ _ m n

/-- The associator reassociates pure tensors. -/
@[simp]
theorem associator_hom_tmul (m : M) (n : N) (p : P) :
    (α_ M N P).hom.hom.hom (tmul k H (tmul k H m n : ↑(M ⊗ N)) p) =
      tmul k H m (tmul k H n p : ↑(N ⊗ P)) :=
  (LinearMap.congr_fun associator_hom_hom _).trans
    (assoc_tmul k H m n p)

/-- The inverse associator reassociates pure tensors. -/
@[simp]
theorem associator_inv_tmul (m : M) (n : N) (p : P) :
    (α_ M N P).inv.hom.hom (tmul k H m (tmul k H n p : ↑(N ⊗ P))) =
      tmul k H (tmul k H m n : ↑(M ⊗ N)) p :=
  (LinearMap.congr_fun associator_inv_hom _).trans
    (assoc_symm_tmul k H m n p)

/-- The left unitor scales by the element of the unit object. -/
@[simp]
theorem leftUnitor_hom_tmul (r : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H))
    (m : M) : (λ_ M).hom.hom.hom (tmul k H r m) = trivialEquiv k H r • m :=
  (LinearMap.congr_fun leftUnitor_hom_hom _).trans
    (lid_tmul k H r m)

/-- The inverse left unitor inserts the unit of the unit object. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) :
    (λ_ M).inv.hom.hom m =
      tmul k H ((trivialEquiv k H).symm 1 :
        (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) m :=
  (LinearMap.congr_fun leftUnitor_inv_hom _).trans
    (lid_symm_apply k H m)

/-- The right unitor scales by the element of the unit object. -/
@[simp]
theorem rightUnitor_hom_tmul (m : M)
    (r : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :
    (ρ_ M).hom.hom.hom (tmul k H m r) = trivialEquiv k H r • m :=
  (LinearMap.congr_fun rightUnitor_hom_hom _).trans
    (rid_tmul k H m r)

/-- The inverse right unitor inserts the unit of the unit object. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) :
    (ρ_ M).inv.hom.hom m =
      tmul k H m ((trivialEquiv k H).symm 1 :
        (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :=
  (LinearMap.congr_fun rightUnitor_inv_hom _).trans
    (rid_symm_apply k H m)

end Struct

/-- The data inducing the monoidal structure along the forgetful functor to `k`-modules. The
tensor comparison is the inverse of `BialgebraModule.tensorEquiv`, and the unit comparison is
the inverse of `BialgebraModule.trivialEquiv`. -/
def inducingFunctorData : Monoidal.InducingFunctorData (forgetToModule k H) where
  μIso M N := (tensorEquiv k H M N).symm.toModuleIso
  whiskerLeft_eq _ _ _ g := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H LinearMap.id g.hom.hom x)
  whiskerRight_eq f _ := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H f.hom.hom LinearMap.id x)
  tensorHom_eq f g := by
    ext x
    exact (LinearEquiv.eq_symm_apply _).mpr (tensorEquiv_tensorMap k H f.hom.hom g.hom.hom x)
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

/-- Finite-dimensional modules over a bialgebra form a monoidal category under the tensor
product over the base field, with `H` acting through its coproduct. -/
instance instMonoidalCategory : MonoidalCategory (FiniteHopfModuleCat k H) :=
  Monoidal.induced (forgetToModule k H) (inducingFunctorData k H)

/-- The forgetful functor to `k`-modules is monoidal. -/
instance : (forgetToModule k H).Monoidal :=
  Monoidal.fromInducedMonoidal (forgetToModule k H) (inducingFunctorData k H)

instance : MonoidalPreadditive (FiniteHopfModuleCat k H) :=
  monoidalPreadditive_of_faithful (forgetToModule k H)

instance : MonoidalLinear k (FiniteHopfModuleCat k H) :=
  MonoidalLinear.ofFaithful k (forgetToModule k H)

variable {k H}
variable {M M' N N' P : FiniteHopfModuleCat k H}

/-- The tensor comparison of the forgetful functor identifies the native tensor product with
the coproduct tensor product. -/
@[simp]
theorem forgetToModule_μ (M N : FiniteHopfModuleCat k H) :
    Functor.LaxMonoidal.μ (forgetToModule k H) M N =
      ModuleCat.ofHom (tensorEquiv k H M N).symm.toLinearMap := (rfl)

/-- The unit comparison of the forgetful functor identifies `k` with the trivial module. -/
@[simp]
theorem forgetToModule_ε :
    Functor.LaxMonoidal.ε (forgetToModule k H) =
      ModuleCat.ofHom (trivialEquiv k H).symm.toLinearMap := (rfl)

end TauCeti.FiniteHopfModuleCat
