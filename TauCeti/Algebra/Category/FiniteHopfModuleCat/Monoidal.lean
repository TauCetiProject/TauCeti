/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Basic
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

For finite modules in independent carrier universes, `shrinkTensorEquiv` compares tensoring
small models with shrinking the coproduct tensor product. It is natural, satisfies the
associativity and unit laws, and becomes the native tensor congruence after forgetting the
`H`-action. This construction uses `BialgebraModule.tensorCongr`.

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

* `TauCeti.FiniteHopfModuleCat.shrinkTensorEquiv`: the tensor comparison for small models,
  with computation rules, naturality, coherence and scalar-linear compatibility.

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
instance isMonoidal : (HopfModuleCat.isFinite k H).IsMonoidal where
  prop_unit := (of (k := k) (H := H) (Trivial k H)).property
  prop_tensor M N hM hN :=
    have : Module.Finite k M := hM
    have : Module.Finite k N := hN
    (of (k := k) (H := H) (Tensor k H M N)).property

/-- Finite-dimensional modules over a bialgebra form a monoidal category under the tensor
product over the base field, with `H` acting through its coproduct: the full monoidal
subcategory of all modules. -/
instance instMonoidalCategory : MonoidalCategory (FiniteHopfModuleCat k H) :=
  ObjectProperty.fullMonoidalSubcategory (HopfModuleCat.isFinite k H)

instance : MonoidalPreadditive (FiniteHopfModuleCat k H) :=
  ObjectProperty.instMonoidalPreadditiveFullSubcategory (HopfModuleCat.isFinite k H)

instance : MonoidalLinear k (FiniteHopfModuleCat k H) :=
  ObjectProperty.instMonoidalLinearFullSubcategory (HopfModuleCat.isFinite k H) k

/-- The inclusion of finite-dimensional modules into all modules is monoidal. -/
instance : (toHopfModuleCat k H).Monoidal :=
  ObjectProperty.monoidalι (HopfModuleCat.isFinite k H)

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
  ObjectProperty.ι_μ _ M N

/-- The unit comparison of the inclusion into all modules is the identity
(`ObjectProperty.ι_ε`). -/
@[simp]
theorem toHopfModuleCat_ε : Functor.LaxMonoidal.ε (toHopfModuleCat k H) = 𝟙 _ :=
  ObjectProperty.ι_ε _

end Inclusion

section Struct

/-! Mathlib's `ObjectProperty.fullMonoidalSubcategory` defines the tensor product, associator and
unitors of a full monoidal subcategory as those of the ambient category on underlying objects
(`ObjectProperty.homMk (f.hom ⊗ₘ g.hom)`, `ObjectProperty.isoMk (α_ M.obj N.obj P.obj)`, and so
on). The underlying intertwiners below are therefore, by construction, those of
`HopfModuleCat k H`, and each lemma is the corresponding `HopfModuleCat` lemma. -/

variable {k H}
variable {M M' N N' P : FiniteHopfModuleCat k H}

/-- The tensor product of morphisms is the tensor product of the underlying intertwiners. -/
theorem tensorHom_hom_hom (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g).hom.hom = tensorMap k H f.hom.hom g.hom.hom :=
  HopfModuleCat.tensorHom_hom f.hom g.hom

/-- Left whiskering tensors the underlying intertwiner with the identity on the left. -/
theorem whiskerLeft_hom_hom (g : N ⟶ N') :
    (M ◁ g).hom.hom = tensorMap k H LinearMap.id g.hom.hom :=
  HopfModuleCat.whiskerLeft_hom g.hom

/-- Right whiskering tensors the underlying intertwiner with the identity on the right. -/
theorem whiskerRight_hom_hom (f : M ⟶ M') :
    (f ▷ N).hom.hom = tensorMap k H f.hom.hom LinearMap.id :=
  HopfModuleCat.whiskerRight_hom f.hom

/-- The associator is the reassociation equivalence `BialgebraModule.assoc`. -/
theorem associator_hom_hom :
    (α_ M N P).hom.hom.hom = (assoc k H M N P).toLinearMap :=
  HopfModuleCat.associator_hom_hom

/-- The inverse associator is the inverse reassociation equivalence. -/
theorem associator_inv_hom :
    (α_ M N P).inv.hom.hom = (assoc k H M N P).symm.toLinearMap :=
  HopfModuleCat.associator_inv_hom

/-- The left unitor is the left unit equivalence `BialgebraModule.lid`. -/
theorem leftUnitor_hom_hom : (λ_ M).hom.hom.hom = (lid k H M).toLinearMap :=
  HopfModuleCat.leftUnitor_hom_hom

/-- The inverse left unitor is the inverse left unit equivalence. -/
theorem leftUnitor_inv_hom : (λ_ M).inv.hom.hom = (lid k H M).symm.toLinearMap :=
  HopfModuleCat.leftUnitor_inv_hom

/-- The right unitor is the right unit equivalence `BialgebraModule.rid`. -/
theorem rightUnitor_hom_hom : (ρ_ M).hom.hom.hom = (rid k H M).toLinearMap :=
  HopfModuleCat.rightUnitor_hom_hom

/-- The inverse right unitor is the inverse right unit equivalence. -/
theorem rightUnitor_inv_hom : (ρ_ M).inv.hom.hom = (rid k H M).symm.toLinearMap :=
  HopfModuleCat.rightUnitor_inv_hom

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

section Shrink

variable (k H)

universe w w' w'' w'''
variable (V : Type w) [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]
variable (W : Type w') [AddCommGroup W] [Module k W] [Module H W]
  [IsScalarTower k H W] [Module.Finite k W]

/-- Tensoring the small models gives the small model of the coproduct tensor product.
The comparison sends `v ⊗ w` to the small representative of the corresponding original tensor. -/
def shrinkTensorEquiv :
    (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H) ≃ₗ[H]
      ofShrink k H (Tensor k H V W) :=
  (tensorCongr k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W)).trans
    (ofShrinkEquiv k H (Tensor k H V W)).symm

/-- The tensor comparison acts factorwise on pure tensors. -/
@[simp]
theorem shrinkTensorEquiv_tmul (x : ofShrink k H V) (y : ofShrink k H W) :
    shrinkTensorEquiv k H V W (tmul k H x y) =
      (ofShrinkEquiv k H (Tensor k H V W)).symm
        (tmul k H (ofShrinkEquiv k H V x) (ofShrinkEquiv k H W y)) := by
  exact congrArg (ofShrinkEquiv k H (Tensor k H V W)).symm
    (tensorCongr_tmul k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W) x y)

/-- On the original modules, tensor comparison is the coproduct tensor product of the
shrinking maps. -/
-- Simplify the composite before the primitive shrink map expands into carrier casts.
@[simp↓]
theorem ofShrinkEquiv_shrinkTensorEquiv
    (x : (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H)) :
    ofShrinkEquiv k H (Tensor k H V W) (shrinkTensorEquiv k H V W x) =
      tensorMap k H (ofShrinkEquiv k H V).toLinearMap (ofShrinkEquiv k H W).toLinearMap x := by
  calc
    _ = tensorCongr k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W) x :=
      (ofShrinkEquiv k H (Tensor k H V W)).apply_symm_apply _
    _ = _ := tensorCongr_apply k H _ _ x

/-- The inverse tensor comparison returns the tensor of the small representatives. -/
@[simp]
theorem shrinkTensorEquiv_symm_tmul (x : V) (y : W) :
    (shrinkTensorEquiv k H V W).symm
        ((ofShrinkEquiv k H (Tensor k H V W)).symm (tmul k H x y)) =
      tmul k H ((ofShrinkEquiv k H V).symm x) ((ofShrinkEquiv k H W).symm y) := by
  apply (shrinkTensorEquiv k H V W).injective
  simp only [LinearEquiv.apply_symm_apply, shrinkTensorEquiv_tmul]

/-- Forgetting the action identifies the tensor comparison with the tensor product of the
scalar-linear shrinking equivalences. -/
@[simp↓]
theorem tensorEquiv_ofShrinkLinearEquiv_shrinkTensorEquiv
    (x : (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H)) :
    tensorEquiv k H V W (ofShrinkLinearEquiv k H (Tensor k H V W)
      (shrinkTensorEquiv k H V W x)) =
      TensorProduct.congr (ofShrinkLinearEquiv k H V) (ofShrinkLinearEquiv k H W)
        (tensorEquiv k H (ofShrink k H V) (ofShrink k H W) x) := by
  rw [ofShrinkLinearEquiv_apply, ofShrinkEquiv_shrinkTensorEquiv, tensorEquiv_tensorMap]
  have hV : (ofShrinkEquiv k H V).toLinearMap.restrictScalars k =
      (ofShrinkLinearEquiv k H V).toLinearMap := by
    ext x
    exact (ofShrinkLinearEquiv_apply k H V x).symm
  have hW : (ofShrinkEquiv k H W).toLinearMap.restrictScalars k =
      (ofShrinkLinearEquiv k H W).toLinearMap := by
    ext x
    exact (ofShrinkLinearEquiv_apply k H W x).symm
  rw [hV, hW, ← TensorProduct.toLinearMap_congr]
  rfl

variable {V W}
variable {V' : Type w''} [AddCommGroup V'] [Module k V'] [Module H V']
  [IsScalarTower k H V'] [Module.Finite k V']
variable {W' : Type w'''} [AddCommGroup W'] [Module k W'] [Module H W']
  [IsScalarTower k H W'] [Module.Finite k W']

/-- Tensor comparison commutes with the transport of intertwiners to small models. -/
theorem shrinkTensorEquiv_naturality (f : V →ₗ[H] V') (g : W →ₗ[H] W') :
    (shrinkHom k H f ⊗ₘ shrinkHom k H g) ≫
        (shrinkTensorEquiv k H V' W').toFiniteHopfModuleCatIso.hom =
      (shrinkTensorEquiv k H V W).toFiniteHopfModuleCatIso.hom ≫
        shrinkHom k H (tensorMap k H f g) := by
  ext x y
  simp

variable (V)

/-- Tensor comparison commutes with the left unitor, including the unit comparison. -/
theorem shrinkTensorEquiv_left_unitality :
    (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom ▷ ofShrink k H V ≫
        (shrinkTensorEquiv k H (Trivial k H) V).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (lid k H V).toLinearMap =
      (λ_ (ofShrink k H V)).hom := by
  ext r x
  simp [-ofShrinkEquiv_apply, ← ofShrinkLinearEquiv_apply, ← ofShrinkLinearEquiv_symm_apply]

/-- Tensor comparison commutes with the right unitor, including the unit comparison. -/
theorem shrinkTensorEquiv_right_unitality :
    ofShrink k H V ◁ (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom ≫
        (shrinkTensorEquiv k H V (Trivial k H)).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (rid k H V).toLinearMap =
      (ρ_ (ofShrink k H V)).hom := by
  ext x r
  simp [-ofShrinkEquiv_apply, ← ofShrinkLinearEquiv_apply, ← ofShrinkLinearEquiv_symm_apply]

variable (W)
variable (P : Type w'') [AddCommGroup P] [Module k P] [Module H P]
  [IsScalarTower k H P] [Module.Finite k P]

/-- The two ways of comparing a triple tensor product agree through the actual associator. -/
theorem shrinkTensorEquiv_associativity :
    (shrinkTensorEquiv k H V W).toFiniteHopfModuleCatIso.hom ▷ ofShrink k H P ≫
        (shrinkTensorEquiv k H (Tensor k H V W) P).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (assoc k H V W P).toLinearMap =
      (α_ (ofShrink k H V) (ofShrink k H W) (ofShrink k H P)).hom ≫
        ofShrink k H V ◁ (shrinkTensorEquiv k H W P).toFiniteHopfModuleCatIso.hom ≫
          (shrinkTensorEquiv k H V (Tensor k H W P)).toFiniteHopfModuleCatIso.hom := by
  apply hom_ext
  simp only [hom_hom_comp, whiskerRight_hom_hom, whiskerLeft_hom_hom,
    LinearEquiv.toFiniteHopfModuleCatIso_hom_hom, associator_hom_hom, shrinkHom_hom_hom]
  have hVW : (ofShrinkEquiv k H (Tensor k H V W)).toLinearMap ∘ₗ
      (shrinkTensorEquiv k H V W).toLinearMap =
        tensorMap k H (ofShrinkEquiv k H V).toLinearMap
          (ofShrinkEquiv k H W).toLinearMap := by
    ext x
    exact ofShrinkEquiv_shrinkTensorEquiv k H V W x
  have hWP : (ofShrinkEquiv k H (Tensor k H W P)).toLinearMap ∘ₗ
      (shrinkTensorEquiv k H W P).toLinearMap =
        tensorMap k H (ofShrinkEquiv k H W).toLinearMap
          (ofShrinkEquiv k H P).toLinearMap := by
    ext x
    exact ofShrinkEquiv_shrinkTensorEquiv k H W P x
  -- Full-subcategory tensors inherit ambient instances; state the pointwise
  -- comparison on canonical module carriers so tensor-map naturality applies directly.
  suffices h : ∀ x : Tensor k H (Tensor k H (ofShrink k H V) (ofShrink k H W))
      (ofShrink k H P),
      (ofShrinkEquiv k H (Tensor k H V (Tensor k H W P))).symm
        (assoc k H V W P (ofShrinkEquiv k H (Tensor k H (Tensor k H V W) P)
          (shrinkTensorEquiv k H (Tensor k H V W) P
            (tensorMap k H (shrinkTensorEquiv k H V W).toLinearMap LinearMap.id x)))) =
      shrinkTensorEquiv k H V (Tensor k H W P)
        (tensorMap k H LinearMap.id (shrinkTensorEquiv k H W P).toLinearMap
          (assoc k H (ofShrink k H V) (ofShrink k H W) (ofShrink k H P) x)) by
    exact LinearMap.ext h
  intro x
  apply (ofShrinkEquiv k H (Tensor k H V (Tensor k H W P))).injective
  simp only [LinearEquiv.apply_symm_apply, ofShrinkEquiv_shrinkTensorEquiv]
  have hl := tensorMap_comp k H (shrinkTensorEquiv k H V W).toLinearMap
    (ofShrinkEquiv k H (Tensor k H V W)).toLinearMap LinearMap.id
    (ofShrinkEquiv k H P).toLinearMap
  have hr := tensorMap_comp k H LinearMap.id (ofShrinkEquiv k H V).toLinearMap
    (shrinkTensorEquiv k H W P).toLinearMap
    (ofShrinkEquiv k H (Tensor k H W P)).toLinearMap
  simp only [hVW, LinearMap.comp_id] at hl
  simp only [hWP, LinearMap.comp_id] at hr
  exact (congrArg (assoc k H V W P) (LinearMap.congr_fun hl x)).symm.trans
    ((tensorMap_tensorMap_assoc k H (ofShrinkEquiv k H V).toLinearMap
      (ofShrinkEquiv k H W).toLinearMap (ofShrinkEquiv k H P).toLinearMap x).symm.trans
        (LinearMap.congr_fun hr
          (assoc k H (ofShrink k H V) (ofShrink k H W) (ofShrink k H P) x)))

end Shrink

end TauCeti.FiniteHopfModuleCat
