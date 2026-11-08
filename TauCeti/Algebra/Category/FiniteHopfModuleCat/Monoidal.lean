/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.Algebra.Category.HopfModuleCat.Monoidal

/-!
# The monoidal category of finite-dimensional bialgebra modules

For a bialgebra `H` over a field `k`, finite-dimensional `H`-modules form a monoidal category.
The tensor product is the tensor product over `k`, on which `H` acts through its coproduct
(`BialgebraModule.Tensor`). The unit is `k` with `H` acting through its counit
(`BialgebraModule.Trivial`). The associator and unitors are the usual tensor-product
equivalences, which are `H`-linear by coassociativity and the counit laws.

This is a tensor product over `k`, not over `H`: even when `H` is commutative, the category
`ModuleCat H` has a different monoidal structure, which is not used here.

The structure is that of the full monoidal subcategory (Mathlib's
`ObjectProperty.fullMonoidalSubcategory`) of the monoidal category `TauCeti.HopfModuleCat k H` of
all modules: finite-dimensionality is closed under tensor products and holds for the unit. The
inclusion `toHopfModuleCat` is therefore strictly monoidal (`ObjectProperty.ι_μ`,
`ObjectProperty.ι_ε`), and the forgetful functor to `ModuleCat k`, its composite with the monoidal
forgetful functor of all modules, is monoidal. The monoidal structure is preadditive and
`k`-linear.

## Main declarations

* `MonoidalCategory (TauCeti.FiniteHopfModuleCat k H)`: the monoidal structure.
* `(TauCeti.FiniteHopfModuleCat.toHopfModuleCat k H).Monoidal`: the inclusion into all modules
  is monoidal.
* `(TauCeti.FiniteHopfModuleCat.forgetToModule k H).Monoidal`: the forgetful functor is monoidal.
* `TauCeti.FiniteHopfModuleCat.tensor_ext`, `tensorHom_tmul`, `associator_hom_tmul`,
  `leftUnitor_hom_tmul`, `rightUnitor_hom_tmul`: the monoidal structure on pure tensors.
* `TauCeti.FiniteHopfModuleCat.whiskerLeft_hom_hom`, `associator_hom_hom`,
  `leftUnitor_hom_hom`, and their companions: the underlying intertwiners of the monoidal
  structure, as module-level maps of `BialgebraModule`.
* `TauCeti.FiniteHopfModuleCat.trivialEquiv_smul_id_hom_hom` and
  `TauCeti.FiniteHopfModuleCat.eq_smul_id_iff`: the scalar multiple `c • 𝟙` of the identity of the
  unit object multiplies by `c`, and is the only endomorphism of the unit doing so.

## References

See C. Kassel, *Quantum Groups*, Proposition III.5.1, for the tensor product of modules over a
bialgebra.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Bialgebra k H]

/-- Finite-dimensional modules contain the trivial module and are closed under the coproduct
tensor product. -/
instance isMonoidal : ObjectProperty.IsMonoidal (C := HopfModuleCat k H)
    fun M : ModuleCat.{u} H => Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M)
    where
  prop_unit := (of (k := k) (H := H) (Trivial k H)).property
  prop_tensor M N hM hN :=
    have : Module.Finite k M := hM
    have : Module.Finite k N := hN
    (of (k := k) (H := H) (Tensor k H M N)).property

-- The property is given explicitly: instance search cannot infer it before unifying with the
-- type synonym `FiniteHopfModuleCat k H`.
/-- Finite-dimensional modules over a bialgebra form a monoidal category under the tensor
product over the base field, with `H` acting through its coproduct: the full monoidal
subcategory of all modules. -/
instance instMonoidalCategory : MonoidalCategory (FiniteHopfModuleCat k H) :=
  ObjectProperty.fullMonoidalSubcategory (C := HopfModuleCat k H) fun M : ModuleCat.{u} H =>
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M)

instance : MonoidalPreadditive (FiniteHopfModuleCat k H) :=
  ObjectProperty.instMonoidalPreadditiveFullSubcategory (C := HopfModuleCat k H)
    fun M : ModuleCat.{u} H => Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M)

instance : MonoidalLinear k (FiniteHopfModuleCat k H) :=
  ObjectProperty.instMonoidalLinearFullSubcategory (C := HopfModuleCat k H)
    (fun M : ModuleCat.{u} H =>
      Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M)) k

/-- The inclusion of finite-dimensional modules into all modules is monoidal. -/
instance : (toHopfModuleCat k H).Monoidal :=
  ObjectProperty.monoidalι (C := HopfModuleCat k H) fun M : ModuleCat.{u} H =>
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k H)).obj M)

/-- The forgetful functor to `k`-modules, the inclusion followed by the forgetful functor of all
modules, is monoidal. -/
instance : (forgetToModule k H).Monoidal :=
  inferInstanceAs (toHopfModuleCat k H ⋙ HopfModuleCat.forgetToModule k H).Monoidal

section Inclusion

variable {k H}

/-- The tensor comparison of the inclusion into all modules is the identity
(`ObjectProperty.ι_μ`). -/
@[simp]
theorem toHopfModuleCat_μ (M N : FiniteHopfModuleCat k H) :
    Functor.LaxMonoidal.μ (toHopfModuleCat k H) M N = 𝟙 _ :=
  (rfl)

/-- The unit comparison of the inclusion into all modules is the identity
(`ObjectProperty.ι_ε`). -/
@[simp]
theorem toHopfModuleCat_ε : Functor.LaxMonoidal.ε (toHopfModuleCat k H) = 𝟙 _ :=
  (rfl)

end Inclusion

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
    (α_ M N P).hom.hom.hom = (assoc k H M N P).toLinearMap := (rfl)

/-- The inverse associator is the inverse reassociation equivalence. -/
theorem associator_inv_hom :
    (α_ M N P).inv.hom.hom = (assoc k H M N P).symm.toLinearMap := (rfl)

/-- The left unitor is the left unit equivalence `BialgebraModule.lid`. -/
theorem leftUnitor_hom_hom : (λ_ M).hom.hom.hom = (lid k H M).toLinearMap := (rfl)

/-- The inverse left unitor is the inverse left unit equivalence. -/
theorem leftUnitor_inv_hom : (λ_ M).inv.hom.hom = (lid k H M).symm.toLinearMap := (rfl)

/-- The right unitor is the right unit equivalence `BialgebraModule.rid`. -/
theorem rightUnitor_hom_hom : (ρ_ M).hom.hom.hom = (rid k H M).toLinearMap := (rfl)

/-- The inverse right unitor is the inverse right unit equivalence. -/
theorem rightUnitor_inv_hom : (ρ_ M).inv.hom.hom = (rid k H M).symm.toLinearMap := (rfl)

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
  HopfModuleCat.associator_hom_tmul m n p

/-- The inverse associator reassociates pure tensors. -/
@[simp]
theorem associator_inv_tmul (m : M) (n : N) (p : P) :
    (α_ M N P).inv.hom.hom (tmul k H m (tmul k H n p : ↑(N ⊗ P))) =
      tmul k H (tmul k H m n : ↑(M ⊗ N)) p :=
  HopfModuleCat.associator_inv_tmul m n p

/-- The left unitor scales by the element of the unit object. -/
@[simp]
theorem leftUnitor_hom_tmul (r : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H))
    (m : M) : (λ_ M).hom.hom.hom (tmul k H r m) = trivialEquiv k H r • m :=
  HopfModuleCat.leftUnitor_hom_tmul r m

/-- The inverse left unitor inserts the unit of the unit object. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) :
    (λ_ M).inv.hom.hom m =
      tmul k H ((trivialEquiv k H).symm 1 :
        (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) m :=
  HopfModuleCat.leftUnitor_inv_apply m

/-- The right unitor scales by the element of the unit object. -/
@[simp]
theorem rightUnitor_hom_tmul (m : M)
    (r : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :
    (ρ_ M).hom.hom.hom (tmul k H m r) = trivialEquiv k H r • m :=
  HopfModuleCat.rightUnitor_hom_tmul m r

/-- The inverse right unitor inserts the unit of the unit object. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) :
    (ρ_ M).inv.hom.hom m =
      tmul k H m ((trivialEquiv k H).symm 1 :
        (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :=
  HopfModuleCat.rightUnitor_inv_apply m

end Struct

variable {k H}

/-- The scalar multiple `c • 𝟙` of the identity of the unit object multiplies by `c`. -/
@[simp]
theorem trivialEquiv_smul_id_hom_hom (c : k)
    (r : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :
    trivialEquiv k H ((c • 𝟙 (𝟙_ (FiniteHopfModuleCat k H))).hom.hom r) =
      c * trivialEquiv k H r := by
  -- The scalar `c` acts on the unit object through `algebraMap k H c`, which acts by its counit
  -- `c`; the scalar action of `k` on the carrier is by definition restriction of scalars.
  change trivialEquiv k H (algebraMap k H c • r) = _
  rw [trivialEquiv_smul, Bialgebra.counit_algebraMap]

/-- An endomorphism of the unit object is the scalar multiple `c • 𝟙` of the identity exactly
when it multiplies by `c`. -/
theorem eq_smul_id_iff {a : 𝟙_ (FiniteHopfModuleCat k H) ⟶ 𝟙_ (FiniteHopfModuleCat k H)}
    {c : k} :
    a = c • 𝟙 _ ↔ ∀ r, trivialEquiv k H (a.hom.hom r) = c * trivialEquiv k H r := by
  refine ⟨fun h r => h ▸ trivialEquiv_smul_id_hom_hom c r, fun h => ?_⟩
  ext r
  apply (trivialEquiv k H).injective
  rw [h, trivialEquiv_smul_id_hom_hom]

end TauCeti.FiniteHopfModuleCat
