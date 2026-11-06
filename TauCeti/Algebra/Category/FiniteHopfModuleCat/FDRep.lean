/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Monoidal
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.OfModule

/-!
# Finite-dimensional modules over a monoid algebra are finite-dimensional representations

For a field `k` and a monoid `G`, this file identifies the category
`FiniteHopfModuleCat k k[G]` of finite-dimensional modules over the monoid algebra with Mathlib's
category `FDRep k G` of finite-dimensional representations, as monoidal categories.

The equivalence `fdRepEquivalence k G` is the restriction to finite-dimensional objects of
Mathlib's `Rep.equivalenceModuleMonoidAlgebra`: its functor `ofFDRep k G` sends a representation
`V` to the `k[G]`-module `Representation.asModule V.ρ`, and after the inclusion into all
`k[G]`-modules it agrees with the native functor (`ofFDRepCompInclIso`). The inverse
`toFDRep k G` reads a module as the representation `Representation.ofModule'` on the same
carrier. Both functors are the identity on underlying vector spaces; `ofFDRepLinearEquiv` records
this identification as a `k`-linear equivalence, and `ofFDRepCompForgetIso` packages it as a
natural isomorphism of forgetful functors to `ModuleCat k`.

The monoidal structure of `FiniteHopfModuleCat k k[G]` is the tensor product over `k`, on which
`k[G]` acts through its coproduct `single g 1 ↦ single g 1 ⊗ single g 1`; this is the diagonal
action used by the tensor product of `FDRep k G`. Accordingly `ofFDRep k G` is a monoidal functor,
with tensor and unit comparisons given by the identity maps of underlying vector spaces
(`ofFDRepTensorEquiv` and `ofFDRepUnitEquiv`). The monoidal structure of the inverse is the one
induced by the equivalence, so that `fdRepEquivalence k G` is a monoidal equivalence. This is a
statement about the tensor product over `k`: when `G` is commutative, `ModuleCat k[G]` also has
a tensor product over `k[G]`, which is not the one used here.

For a finite monoid, `TauCeti.fdRepEquivalence` identifies `FDRep k G` with the finitely generated
`k[G]`-modules instead, for its exact structure. Here `G` is an arbitrary monoid, and finiteness
is measured over `k`, as the monoidal structure requires.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.ofFDRep`, `TauCeti.FiniteHopfModuleCat.toFDRep`: the two functors.
* `TauCeti.FiniteHopfModuleCat.fdRepEquivalence`: the equivalence
  `FDRep k G ≌ FiniteHopfModuleCat k k[G]`.
* `TauCeti.FiniteHopfModuleCat.ofFDRepCompInclIso`: the equivalence restricts Mathlib's
  `Rep.equivalenceModuleMonoidAlgebra`.
* `TauCeti.FiniteHopfModuleCat.ofFDRepCompForgetIso`: the equivalence commutes with the forgetful
  functors to `ModuleCat k`.
* `(TauCeti.FiniteHopfModuleCat.ofFDRep k G).Monoidal`: the functor is monoidal; with the induced
  structure on its inverse, instance search finds `(fdRepEquivalence k G).IsMonoidal`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped MonoidAlgebra

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable (k : Type u) [Field k] (G : Type v) [Monoid G]

/-- A finite-dimensional representation of `G`, regarded as a finite-dimensional module over the
monoid algebra `k[G]`. An equivariant map is the same map, now `k[G]`-linear. -/
-- The body is exposed so that the carrier of `(ofFDRep k G).obj V` is definitionally
-- `Representation.asModule V.ρ`, as for Mathlib's `Rep.toModuleMonoidAlgebra`.
@[expose] def ofFDRep : FDRep k G ⥤ FiniteHopfModuleCat k k[G] where
  obj V := of (Representation.asModule V.ρ)
  map {V W} f := ofHom <| Representation.IntertwiningMap.equivLinearMapAsModule V.ρ W.ρ
    ⟨f.hom.hom.hom, fun g => congrArg (fun φ => φ.hom.hom) (f.comm g)⟩

/-- A finite-dimensional `k[G]`-module, regarded as a finite-dimensional representation of `G`
on the same carrier, with `g` acting as `MonoidAlgebra.single g 1`. -/
-- The body is exposed so that the carrier of `(toFDRep k G).obj M` is definitionally `M`.
@[expose] def toFDRep : FiniteHopfModuleCat k k[G] ⥤ FDRep k G where
  obj M := FDRep.of (Representation.ofModule' (k := k) (G := G) M)
  map {M N} f := ⟨FGModuleCat.ofHom (f.hom.hom.restrictScalars k), fun g => by
    ext x
    exact f.hom.hom.map_smul _ x⟩

variable {k G}

/-- The group-algebra module attached to a representation has the same underlying vector space.
This is the identity map. -/
def ofFDRepLinearEquiv (V : FDRep k G) : (ofFDRep k G).obj V ≃ₗ[k] V :=
  { AddEquiv.refl V with
    map_smul' r x := by
      -- The scalar action of `k` on a module of `FiniteHopfModuleCat` is restriction of scalars
      -- along `algebraMap k k[G]`.
      change algebraMap k k[G] r • x = _
      exact (Representation.asModuleEquiv_symm_map_smul V.ρ r x).symm }

/-- The monoid algebra acts on the module attached to a representation through the extension of
the representation to `k[G]`. -/
@[simp]
theorem ofFDRepLinearEquiv_smul (V : FDRep k G) (r : k[G]) (x : (ofFDRep k G).obj V) :
    ofFDRepLinearEquiv V (r • x) =
      Representation.asAlgebraHom V.ρ r (ofFDRepLinearEquiv V x) := (rfl)

/-- The basis element `single g 1` of the monoid algebra acts on the module attached to a
representation as `g` does. -/
theorem ofFDRepLinearEquiv_single_smul (V : FDRep k G) (g : G) (x : (ofFDRep k G).obj V) :
    ofFDRepLinearEquiv V (MonoidAlgebra.single g (1 : k) • x) =
      V.ρ g (ofFDRepLinearEquiv V x) :=
  (Representation.single_smul V.ρ 1 g x).trans (one_smul k _)

/-- The `k[G]`-linear map attached to an equivariant map is the same map. -/
@[simp]
theorem ofFDRepLinearEquiv_ofFDRep_map_apply {V W : FDRep k G} (f : V ⟶ W)
    (x : (ofFDRep k G).obj V) :
    ofFDRepLinearEquiv W (((ofFDRep k G).map f).hom.hom x) =
      f.hom.hom.hom (ofFDRepLinearEquiv V x) := (rfl)

/-- An element `g` acts on the representation attached to a `k[G]`-module as `single g 1`. -/
@[simp]
theorem toFDRep_obj_ρ_apply (M : FiniteHopfModuleCat k k[G]) (g : G) (x : M) :
    ((toFDRep k G).obj M).ρ g x = MonoidAlgebra.single g (1 : k) • x := (rfl)

/-- The equivariant map attached to a `k[G]`-linear map is the same map. -/
@[simp]
theorem toFDRep_map_hom_hom_hom_apply {M N : FiniteHopfModuleCat k k[G]} (f : M ⟶ N)
    (x : (toFDRep k G).obj M) :
    ((toFDRep k G).map f).hom.hom.hom x = f.hom.hom x := (rfl)

/-- A representation is isomorphic to the representation attached to its `k[G]`-module, by the
identity map of the underlying vector space. -/
def fdRepUnitIso (V : FDRep k G) : V ≅ (toFDRep k G).obj ((ofFDRep k G).obj V) :=
  Action.mkIso (ofFDRepLinearEquiv V).symm.toFGModuleCatIso fun g => by
    ext x
    -- After `ext`, the action of `g` on the target is multiplication by `single g 1`.
    change (ofFDRepLinearEquiv V).symm (V.ρ g x) =
      MonoidAlgebra.single g (1 : k) • (ofFDRepLinearEquiv V).symm x
    rw [LinearEquiv.symm_apply_eq, ofFDRepLinearEquiv_single_smul, LinearEquiv.apply_symm_apply]

/-- The unit isomorphism is the identity of the underlying vector space. -/
@[simp]
theorem fdRepUnitIso_hom_hom_hom_hom_apply (V : FDRep k G) (x : V) :
    (fdRepUnitIso V).hom.hom.hom.hom x = (ofFDRepLinearEquiv V).symm x := (rfl)

/-- The inverse unit isomorphism is the identity of the underlying vector space. -/
@[simp]
theorem fdRepUnitIso_inv_hom_hom_hom_apply (V : FDRep k G)
    (x : (toFDRep k G).obj ((ofFDRep k G).obj V)) :
    (fdRepUnitIso V).inv.hom.hom.hom x = ofFDRepLinearEquiv V x := (rfl)

/-- A `k[G]`-module is isomorphic to the module attached to its representation, by the identity
map of the carrier. -/
def fdRepCounitIso (M : FiniteHopfModuleCat k k[G]) :
    (ofFDRep k G).obj ((toFDRep k G).obj M) ≅ M :=
  ObjectProperty.isoMk _ <| LinearEquiv.toModuleIso
    { ofFDRepLinearEquiv ((toFDRep k G).obj M) with
      map_smul' r x := TauCeti.Representation.asAlgebraHom_ofModule'_apply (G := G) M r x }

/-- The counit isomorphism is the identity of the carrier. -/
@[simp]
theorem fdRepCounitIso_hom_hom_hom_apply (M : FiniteHopfModuleCat k k[G])
    (x : (ofFDRep k G).obj ((toFDRep k G).obj M)) :
    (fdRepCounitIso M).hom.hom.hom x = ofFDRepLinearEquiv _ x := (rfl)

/-- The inverse counit isomorphism is the identity of the carrier. -/
@[simp]
theorem ofFDRepLinearEquiv_fdRepCounitIso_inv_hom_hom_apply (M : FiniteHopfModuleCat k k[G])
    (x : M) :
    ofFDRepLinearEquiv _ ((fdRepCounitIso M).inv.hom.hom x) = x := (rfl)

/-- Naturality of the unit isomorphisms. -/
theorem fdRepUnitIso_hom_naturality {V W : FDRep k G} (f : V ⟶ W) :
    f ≫ (fdRepUnitIso W).hom =
      (fdRepUnitIso V).hom ≫ (toFDRep k G).map ((ofFDRep k G).map f) := by
  ext; rfl

/-- Naturality of the counit isomorphisms. -/
theorem fdRepCounitIso_hom_naturality {M N : FiniteHopfModuleCat k k[G]} (f : M ⟶ N) :
    (ofFDRep k G).map ((toFDRep k G).map f) ≫ (fdRepCounitIso N).hom =
      (fdRepCounitIso M).hom ≫ f := by
  ext; rfl

/-- The triangle identity relating the unit and counit isomorphisms. -/
theorem ofFDRep_map_fdRepUnitIso_hom_comp_fdRepCounitIso_hom (V : FDRep k G) :
    (ofFDRep k G).map (fdRepUnitIso V).hom ≫ (fdRepCounitIso ((ofFDRep k G).obj V)).hom =
      𝟙 _ := by
  ext; rfl

variable (k G)

/-- **Finite-dimensional representations of `G` are finite-dimensional `k[G]`-modules.** The
functor is `ofFDRep k G` and the inverse is `toFDRep k G`. -/
-- The body is exposed so that the functor and inverse are definitionally `ofFDRep k G` and
-- `toFDRep k G`, which carry the monoidal structures below.
@[expose] def fdRepEquivalence : FDRep k G ≌ FiniteHopfModuleCat k k[G] where
  functor := ofFDRep k G
  inverse := toFDRep k G
  unitIso := NatIso.ofComponents fdRepUnitIso fdRepUnitIso_hom_naturality
  counitIso := NatIso.ofComponents fdRepCounitIso fdRepCounitIso_hom_naturality
  functor_unitIso_comp := ofFDRep_map_fdRepUnitIso_hom_comp_fdRepCounitIso_hom

/-- The equivalence restricts Mathlib's equivalence `Rep.equivalenceModuleMonoidAlgebra` between
all representations and all `k[G]`-modules: both send a representation `V` to
`Representation.asModule V.ρ`. -/
def ofFDRepCompInclIso :
    ofFDRep k G ⋙ incl k k[G] ≅ forget₂ (FDRep k G) (Rep k G) ⋙ Rep.toModuleMonoidAlgebra :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by ext; rfl

/-- The components of `ofFDRepCompInclIso` are identities. -/
@[simp]
theorem ofFDRepCompInclIso_hom_app (V : FDRep k G) :
    (ofFDRepCompInclIso k G).hom.app V = 𝟙 _ := (rfl)

/-- The components of the inverse of `ofFDRepCompInclIso` are identities. -/
@[simp]
theorem ofFDRepCompInclIso_inv_app (V : FDRep k G) :
    (ofFDRepCompInclIso k G).inv.app V = 𝟙 _ := (rfl)

/-- The underlying vector space of the `k[G]`-module attached to a representation is the
underlying vector space of the representation. -/
def ofFDRepCompForgetIso :
    ofFDRep k G ⋙ forgetToModule k k[G] ≅
      Action.forget (FGModuleCat k) G ⋙ forget₂ (FGModuleCat k) (ModuleCat k) :=
  NatIso.ofComponents (fun V => (ofFDRepLinearEquiv V).toModuleIso) fun _ => by ext; rfl

/-- The forward map of `ofFDRepCompForgetIso` is `ofFDRepLinearEquiv`. -/
@[simp]
theorem ofFDRepCompForgetIso_hom_app (V : FDRep k G) :
    (ofFDRepCompForgetIso k G).hom.app V = ModuleCat.ofHom (ofFDRepLinearEquiv V).toLinearMap :=
  (rfl)

/-- The inverse map of `ofFDRepCompForgetIso` is the inverse of `ofFDRepLinearEquiv`. -/
@[simp]
theorem ofFDRepCompForgetIso_inv_app (V : FDRep k G) :
    (ofFDRepCompForgetIso k G).inv.app V =
      ModuleCat.ofHom (ofFDRepLinearEquiv V).symm.toLinearMap :=
  (rfl)

variable {k G}

private theorem ofFDRepTensorEquiv_aux (V W : FDRep k G) (g : G)
    (x : ((ofFDRep k G).obj V ⊗ (ofFDRep k G).obj W : FiniteHopfModuleCat k k[G])) :
    (ofFDRepLinearEquiv (V ⊗ W)).symm (TensorProduct.congr (ofFDRepLinearEquiv V)
      (ofFDRepLinearEquiv W) (tensorEquiv k k[G] _ _ (MonoidAlgebra.single g (1 : k) • x))) =
    MonoidAlgebra.single g (1 : k) • (ofFDRepLinearEquiv (V ⊗ W)).symm (TensorProduct.congr
      (ofFDRepLinearEquiv V) (ofFDRepLinearEquiv W) (tensorEquiv k k[G] _ _ x)) := by
  rw [LinearEquiv.symm_apply_eq, ofFDRepLinearEquiv_single_smul, LinearEquiv.apply_symm_apply,
    FDRep.tensor_ρ, tensorEquiv_smul_of_comul_eq_tmul
      (MonoidAlgebra.isGroupLikeElem_single_one g).comul_eq_tmul_self]
  induction tensorEquiv k k[G] _ _ x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [TensorProduct.map_tmul, Algebra.lsmul_coe, TensorProduct.congr_tmul,
      ofFDRepLinearEquiv_single_smul]
    exact (TensorProduct.map_tmul _ _ _ _).symm
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The tensor comparison of `ofFDRep k G`: the coproduct tensor product of the modules attached
to two representations is the module attached to their tensor product. On underlying vector
spaces this is the identity of `V ⊗[k] W`. -/
def ofFDRepTensorEquiv (V W : FDRep k G) :
    ((ofFDRep k G).obj V ⊗ (ofFDRep k G).obj W : FiniteHopfModuleCat k k[G]) ≃ₗ[k[G]]
      (ofFDRep k G).obj (V ⊗ W) :=
  let e : ((ofFDRep k G).obj V ⊗ (ofFDRep k G).obj W : FiniteHopfModuleCat k k[G]) ≃ₗ[k]
      (ofFDRep k G).obj (V ⊗ W) :=
    (tensorEquiv k k[G] _ _).trans <|
      (TensorProduct.congr (ofFDRepLinearEquiv V) (ofFDRepLinearEquiv W)).trans
        (ofFDRepLinearEquiv (V ⊗ W)).symm
  { MonoidAlgebra.equivariantOfLinearOfComm e.toLinearMap (ofFDRepTensorEquiv_aux V W) with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- On underlying vector spaces, the tensor comparison is the identity of `V ⊗[k] W`. -/
theorem ofFDRepTensorEquiv_apply (V W : FDRep k G)
    (x : ((ofFDRep k G).obj V ⊗ (ofFDRep k G).obj W : FiniteHopfModuleCat k k[G])) :
    ofFDRepTensorEquiv V W x = (ofFDRepLinearEquiv (V ⊗ W)).symm
      (TensorProduct.congr (ofFDRepLinearEquiv V) (ofFDRepLinearEquiv W)
        (tensorEquiv k k[G] _ _ x)) := (rfl)

/-- The tensor comparison sends a pure tensor to the corresponding pure tensor. -/
-- Not a `simp` lemma: `simp` rewrites the carrier `(V ⊗ W).V` in the type of its left-hand side.
theorem ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul (V W : FDRep k G)
    (v : (ofFDRep k G).obj V) (w : (ofFDRep k G).obj W) :
    ofFDRepLinearEquiv (V ⊗ W) (ofFDRepTensorEquiv V W (tmul k k[G] v w)) =
      ofFDRepLinearEquiv V v ⊗ₜ[k] ofFDRepLinearEquiv W w := by
  simp [ofFDRepTensorEquiv_apply]

private theorem ofFDRepUnitEquiv_aux (g : G)
    (x : (𝟙_ (FiniteHopfModuleCat k k[G]) : FiniteHopfModuleCat k k[G])) :
    (ofFDRepLinearEquiv (𝟙_ (FDRep k G))).symm
        (trivialEquiv k k[G] (MonoidAlgebra.single g (1 : k) • x)) =
      MonoidAlgebra.single g (1 : k) •
        (ofFDRepLinearEquiv (𝟙_ (FDRep k G))).symm (trivialEquiv k k[G] x) := by
  rw [LinearEquiv.symm_apply_eq, ofFDRepLinearEquiv_single_smul, LinearEquiv.apply_symm_apply,
    FDRep.tensorUnit_ρ, LinearMap.id_apply, trivialEquiv_smul,
    (MonoidAlgebra.isGroupLikeElem_single_one g).counit_eq_one, one_mul]

/-- The unit comparison of `ofFDRep k G`: the trivial module, on which `k[G]` acts through its
counit, is the module attached to the trivial representation. On underlying vector spaces this
is the identity of `k`. -/
def ofFDRepUnitEquiv :
    (𝟙_ (FiniteHopfModuleCat k k[G]) : FiniteHopfModuleCat k k[G]) ≃ₗ[k[G]]
      (ofFDRep k G).obj (𝟙_ (FDRep k G)) :=
  let e : (𝟙_ (FiniteHopfModuleCat k k[G]) : FiniteHopfModuleCat k k[G]) ≃ₗ[k]
      (ofFDRep k G).obj (𝟙_ (FDRep k G)) :=
    (trivialEquiv k k[G]).trans (ofFDRepLinearEquiv (𝟙_ (FDRep k G))).symm
  { MonoidAlgebra.equivariantOfLinearOfComm e.toLinearMap (ofFDRepUnitEquiv_aux (k := k)) with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- On underlying vector spaces, the unit comparison is the identity of `k`. -/
theorem ofFDRepUnitEquiv_apply
    (r : (𝟙_ (FiniteHopfModuleCat k k[G]) : FiniteHopfModuleCat k k[G])) :
    ofFDRepUnitEquiv r = (ofFDRepLinearEquiv (𝟙_ (FDRep k G))).symm (trivialEquiv k k[G] r) :=
  (rfl)

/-- The unit comparison sends `r` to `r`. -/
-- Not a `simp` lemma: `simp` rewrites the carrier `(𝟙_ (FDRep k G)).V` in the type of its
-- left-hand side.
theorem ofFDRepLinearEquiv_ofFDRepUnitEquiv
    (r : (𝟙_ (FiniteHopfModuleCat k k[G]) : FiniteHopfModuleCat k k[G])) :
    ofFDRepLinearEquiv (𝟙_ (FDRep k G)) (ofFDRepUnitEquiv r) = trivialEquiv k k[G] r := by
  simp [ofFDRepUnitEquiv_apply]

/-- The functor from finite-dimensional representations to finite-dimensional `k[G]`-modules is
monoidal, with tensor comparison `ofFDRepTensorEquiv` and unit comparison `ofFDRepUnitEquiv`. -/
instance : (ofFDRep k G).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ofFDRepUnitEquiv.toFiniteHopfModuleCatIso
      μIso V W := (ofFDRepTensorEquiv V W).toFiniteHopfModuleCatIso
      μIso_hom_natural_left f Z := by
        ext x y
        apply (ofFDRepLinearEquiv _).injective
        simp only [hom_hom_comp, LinearMap.comp_apply, LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
          LinearEquiv.coe_coe, whiskerRight_tmul, ofFDRepLinearEquiv_ofFDRep_map_apply,
          ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]
        exact (ModuleCat.MonoidalCategory.whiskerRight_apply _ _ _ _).symm
      μIso_hom_natural_right Z f := by
        ext x y
        apply (ofFDRepLinearEquiv _).injective
        simp only [hom_hom_comp, LinearMap.comp_apply, LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
          LinearEquiv.coe_coe, whiskerLeft_tmul, ofFDRepLinearEquiv_ofFDRep_map_apply,
          ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]
        exact (ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ _ _).symm
      associativity X Y Z := by
        ext m z
        apply (ofFDRepLinearEquiv _).injective
        simp only [hom_hom_comp, LinearMap.comp_apply, LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
          LinearEquiv.coe_coe, whiskerRight_tmul, ofFDRepLinearEquiv_ofFDRep_map_apply,
          ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]
        induction m using Tensor.inductionOn with
        | htmul x y =>
          rw [associator_hom_tmul, ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]
          -- The associator returns a pure tensor typed by the coproduct tensor carrier, so the
          -- whiskering lemma is applied with the tensor object named explicitly.
          refine (ModuleCat.MonoidalCategory.associator_hom_apply _ _ _).trans
            ((congrArg (fun t => ofFDRepLinearEquiv _ (ofFDRepTensorEquiv X (Y ⊗ Z) t))
              (whiskerLeft_tmul (N := (ofFDRep k G).obj Y ⊗ (ofFDRep k G).obj Z)
                (ofFDRepTensorEquiv Y Z).toFiniteHopfModuleCatIso.hom x
                (tmul k k[G] y z))).trans ?_).symm
          simp only [LinearEquiv.toFiniteHopfModuleCatIso_hom_hom, LinearEquiv.coe_coe,
            ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]
          -- What remains is an identity map of `ModuleCat k` applied to the last factor.
          rfl
        | hadd a b ha hb => simp only [map_add, add_tmul, TensorProduct.add_tmul, ha, hb]
      left_unitality X := by
        ext r x
        apply (ofFDRepLinearEquiv _).injective
        simp only [hom_hom_comp, LinearMap.comp_apply, LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
          LinearEquiv.coe_coe, whiskerRight_tmul, ofFDRepLinearEquiv_ofFDRep_map_apply,
          ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul, leftUnitor_hom_tmul,
          ofFDRepLinearEquiv_ofFDRepUnitEquiv, LinearEquiv.map_smul]
        exact (ModuleCat.MonoidalCategory.leftUnitor_hom_apply _ _).symm
      right_unitality X := by
        ext x r
        apply (ofFDRepLinearEquiv _).injective
        simp only [hom_hom_comp, LinearMap.comp_apply, LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
          LinearEquiv.coe_coe, whiskerLeft_tmul, ofFDRepLinearEquiv_ofFDRep_map_apply,
          ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul, rightUnitor_hom_tmul,
          ofFDRepLinearEquiv_ofFDRepUnitEquiv, LinearEquiv.map_smul]
        exact (ModuleCat.MonoidalCategory.rightUnitor_hom_apply _ _).symm }

/-- The tensor comparison of `ofFDRep k G` is `ofFDRepTensorEquiv`. -/
@[simp]
theorem ofFDRep_μ_hom_hom (V W : FDRep k G) :
    (Functor.LaxMonoidal.μ (ofFDRep k G) V W).hom.hom = (ofFDRepTensorEquiv V W).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The unit comparison of `ofFDRep k G` is `ofFDRepUnitEquiv`. -/
@[simp]
theorem ofFDRep_ε_hom_hom :
    (Functor.LaxMonoidal.ε (ofFDRep k G)).hom.hom = (ofFDRepUnitEquiv (G := G)).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

instance : (fdRepEquivalence k G).functor.Monoidal := inferInstanceAs (ofFDRep k G).Monoidal

/-- The functor from finite-dimensional `k[G]`-modules to finite-dimensional representations is
monoidal, with the structure induced by the monoidal equivalence `fdRepEquivalence k G`. -/
instance : (toFDRep k G).Monoidal := (fdRepEquivalence k G).inverseMonoidal

instance : (fdRepEquivalence k G).inverse.Monoidal := inferInstanceAs (toFDRep k G).Monoidal

end TauCeti.FiniteHopfModuleCat
