/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.CategoryTheory.DG.CochainComplex.Basic
public import TauCeti.CategoryTheory.DG.NaturalTransformation
public import TauCeti.CategoryTheory.DG.Representable
public import TauCeti.CategoryTheory.DG.SingleObj
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Right DG modules over a DG algebra as DG modules over its one-object DG category

There are two notions of right DG module over a differential graded algebra `(A, d)`.  On the
algebra side, `TauCeti.DGRightModuleCat h` consists of internally graded right `A`-modules with a
differential satisfying the right Leibniz rule.  On the category side, a right DG module over a DG
category `C` is a DG functor `Cᵒᵖ ⥤ C(R)` to cochain complexes, as for the representable modules
`TauCeti.dgRepresentable`, and `A` is the one-object DG category `TauCeti.DGSingleObj h`.  This
file shows that the two conventions agree.

A right DG module `M` gives the DG functor `M.toDGFunctor`: it sends the unique object to the
underlying complex of `M`, and a morphism `a` of degree `n` acts on elements of degree `p` by the
**signed right action**

`x ↦ (-1) ^ (n * p) • x * a`.

The sign is forced.  Composition in the one-object DG category is multiplication in the reversed
order with the Koszul sign (`TauCeti.DGSingleObj.dgHomEquiv_dgComp`), and composition in the
opposite DG category and of cochains each carry a further Koszul sign.  With the sign
`(-1) ^ (n * p)`, the right Leibniz rule says exactly that the action of `d a` is the differential
`δ` of the action of `a` (`TauCeti.DGRightModuleCat.actionCochain_eq_δ`), and associativity of the
action says that it preserves composition (`TauCeti.DGRightModuleCat.actionCochain_eq_comp`).  On
the free rank-one module the signed right action is precomposition, so its DG module is the
representable module of the unique object
(`TauCeti.DGRightModuleCat.toDGFunctor_of_isDGRightModule_dgMap_v_apply`).

A morphism of right DG modules induces a chain map of underlying complexes
(`TauCeti.DGRightModuleCat.toCochainMap`) commuting with the signed actions, hence a DG natural
transformation.  This gives the functor
`TauCeti.DGRightModuleCat.singleObjFunctor` from right DG modules to DG functors, and it is fully
faithful: a DG natural transformation between the DG modules of `M` and `N` is a closed degree-zero
family of maps on the homogeneous pieces commuting with the action of every homogeneous element,
and these are exactly the morphisms of right DG modules `M ⟶ N`.

## Main definitions

* `TauCeti.DGRightModuleCat.actionCochain`: the signed right action of a homogeneous element, as a
  cochain on the underlying complex.
* `TauCeti.DGRightModuleCat.toDGFunctor`: the DG module over the one-object DG category of a right
  DG module.
* `TauCeti.DGRightModuleCat.toDGFunctorMap`: the DG natural transformation of a morphism of right
  DG modules.
* `TauCeti.DGRightModuleCat.singleObjFunctor`: right DG modules as DG modules over the one-object
  DG category, as a functor.

## Main results

* `TauCeti.DGRightModuleCat.actionCochain_eq_δ`,
  `TauCeti.DGRightModuleCat.actionCochain_eq_ofHom_id` and
  `TauCeti.DGRightModuleCat.actionCochain_eq_comp`: the signed action commutes with the
  differentials and preserves identities and composition.
* `TauCeti.DGRightModuleCat.toDGFunctor_dgMap_v_apply`: a morphism acts on the DG module by the
  signed right action.
* `TauCeti.DGRightModuleCat.toDGFunctor_of_isDGRightModule_dgMap_v_apply`: the DG module of the
  free rank-one module is the representable module.
* `TauCeti.DGRightModuleCat.dgApp_toDGFunctorMap` and
  `TauCeti.DGRightModuleCat.dgApp_toDGFunctorMap_v_apply`: the component of the DG natural
  transformation of a morphism is its chain map of underlying complexes, which is the morphism
  on homogeneous pieces.
* `TauCeti.DGRightModuleCat.singleObjFunctor` is `Functor.Full` and `Functor.Faithful`.

## Implementation notes

The target is the DG category of cochain complexes of `R`-modules in the universe of `R`, and the
one-object DG category needs `A` in that universe, so ground ring, algebra and modules share one
universe, as for the DG category structure on `TauCeti.DGRightModuleCat`.

`toDGFunctor` is an abbreviation with a literal object map, so that the objects of the DG module
are the underlying complex `TauCeti.DGRightModuleCat.toCochainComplex M` up to reducible
unfolding; the lemmas about that complex, stated through `TauCeti.gradedCochainComplexXEquiv`,
then apply to the DG module directly.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open CategoryTheory MulOpposite CochainComplex.HomComplex

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleCat

variable (M : DGRightModuleCat.{u, u, u} h)

/-- The signed right action `x ↦ (-1) ^ (n * p) • x * a` of a homogeneous element `a` of degree
`n` on the elements of degree `p`, bilinear in `a` and `x`. -/
private noncomputable def actionV (n p q : ℤ) (hpq : p + n = q) :
    𝒜 n →ₗ[R] M.grading p →ₗ[R] M.grading q :=
  LinearMap.mk₂ R
    (fun a x ↦ ⟨(n * p).negOnePow • op (a : A) • (x : M), by
      rw [Units.smul_def]
      exact zsmul_mem (hpq ▸ op_smul_mem_of_mem_graded a.2 x.2) _⟩)
    (fun a a' x ↦ Subtype.ext <| by
      simp only [Submodule.coe_add, MulOpposite.op_add, add_smul, smul_add])
    (fun r a x ↦ Subtype.ext <| by
      simp only [SetLike.val_smul, op_smul, smul_assoc]
      exact smul_comm _ _ _)
    (fun a x x' ↦ Subtype.ext <| by
      simp only [Submodule.coe_add, smul_add])
    (fun r a x ↦ Subtype.ext <| by
      simp only [SetLike.val_smul]
      rw [smul_comm (op (a : A)) r, smul_comm _ r])

/-- The **signed right action** of a homogeneous element `a` of degree `n` as a degree-`n`
cochain on the underlying complex of `M`: on elements of degree `p` it is
`x ↦ (-1) ^ (n * p) • x * a`. -/
noncomputable def actionCochain (n : ℤ) :
    𝒜 n →ₗ[R] Cochain M.toCochainComplex M.toCochainComplex n where
  toFun a := Cochain.mk fun p q hpq ↦ ModuleCat.ofHom <|
    (gradedCochainComplexXEquiv q).symm.toLinearMap ∘ₗ M.actionV n p q hpq a ∘ₗ
      (gradedCochainComplexXEquiv p).toLinearMap
  map_add' a a' := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    ext x
    simp
  map_smul' r a := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    ext x
    simp

/-- The signed right action on an element of degree `p`. -/
@[simp]
theorem actionCochain_v_apply (n : ℤ) (a : 𝒜 n) (p q : ℤ) (hpq : p + n = q)
    (x : M.toCochainComplex.X p) :
    (gradedCochainComplexXEquiv q (((M.actionCochain n a).v p q hpq).hom x) : M) =
      (n * p).negOnePow • (op (a : A) • (gradedCochainComplexXEquiv p x : M)) := by
  simp [actionCochain, actionV]

/-- **The signed action commutes with the differentials**: the action of `d a` is the
differential of the action of `a`.  This is the right Leibniz rule; the sign `(-1) ^ (n * p)` is
what turns it into the Leibniz rule `δ` of cochains. -/
theorem actionCochain_eq_δ {n : ℤ} (a : 𝒜 n) (a' : 𝒜 (n + 1)) (ha : (a' : A) = d a) :
    M.actionCochain (n + 1) a' = δ n (n + 1) (M.actionCochain n a) := by
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  obtain rfl : q = p + n + 1 := by omega
  rw [δ_v n (n + 1) rfl _ p (p + n + 1) hpq (p + n) (p + 1) (by omega) rfl]
  ext x
  apply (gradedCochainComplexXEquiv (p + n + 1)).injective
  apply Subtype.ext
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add, map_zsmul,
    Submodule.coe_add, Submodule.coe_smul_of_tower, gradedCochainComplexXEquiv_d,
    actionCochain_v_apply, ha]
  rw [M.isDGRightModule.leibniz (gradedCochainComplexXEquiv p x).2]
  have h₁ : ((n * p).negOnePow : ℤ) * p.negOnePow = ((n + 1) * p).negOnePow := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    ring
  have h₂ : ((n + 1).negOnePow : ℤ) * (n * (p + 1)).negOnePow = -(n * p).negOnePow := by
    rw [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨n, by ring⟩
  simp only [Units.smul_def, smul_add, smul_smul, h₁, h₂, neg_smul]
  abel

/-- The unit acts as the identity cochain. -/
theorem actionCochain_eq_ofHom_id (e : 𝒜 0) (he : (e : A) = 1) :
    M.actionCochain 0 e = Cochain.ofHom (𝟙 M.toCochainComplex) := by
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  obtain rfl : p = q := by omega
  ext x
  apply (gradedCochainComplexXEquiv p).injective
  apply Subtype.ext
  simp [actionCochain_v_apply, he]

/-- **The signed action of a product is the composite of the actions**, first the action of `a`
and then that of `b`, up to the Koszul sign `(-1) ^ (p * q)` of the two degrees. -/
theorem actionCochain_eq_comp {p q n : ℤ} (a : 𝒜 p) (b : 𝒜 q) (c : 𝒜 n) (hc : (c : A) = a * b)
    (hpq : p + q = n) :
    M.actionCochain n c =
      (p * q).negOnePow • (M.actionCochain p a).comp (M.actionCochain q b) hpq := by
  refine Cochain.ext _ _ fun r s hrs ↦ ?_
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ hpq r (r + p) s rfl (by omega)]
  ext x
  apply (gradedCochainComplexXEquiv s).injective
  apply Subtype.ext
  simp only [Units.smul_def, ModuleCat.hom_zsmul, ModuleCat.hom_comp, LinearMap.smul_apply,
    LinearMap.comp_apply, map_zsmul, Submodule.coe_smul_of_tower, actionCochain_v_apply, hc]
  subst hpq
  have hsign : (((p + q) * r).negOnePow : ℤ) =
      (p * q).negOnePow * ((q * (r + p)).negOnePow * (p * r).negOnePow) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p * q), by ring⟩
  rw [op_mul, mul_smul, smul_comm (op (b : A)) ((p * r).negOnePow : ℤ), hsign]
  simp only [smul_smul]

/-- The **DG module over the one-object DG category** of a right DG module `M`: the DG functor
from the opposite of `TauCeti.DGSingleObj h` to cochain complexes sending the unique object to the
underlying complex of `M`, on which a morphism `a` of degree `n` acts by the signed right action
`x ↦ (-1) ^ (n * p) • x * a` on elements of degree `p`. -/
-- This is an abbreviation whose object map is a literal function, so that the DG module sends
-- the unique object to the underlying complex of `M` up to reducible unfolding, and lemmas about
-- that complex apply to the objects of the DG module.
noncomputable abbrev toDGFunctor :
    DGFunctor R (DGSingleObj h)ᵒᵖ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  let F := EnrichedFunctor.ofDGMap (fun _ ↦ M.toCochainComplex)
      (fun {Y Z} n ↦ M.actionCochain n ∘ₗ (DGSingleObj.dgHomEquiv Z.unop Y.unop n).toLinearMap)
      (fun {Y Z} n f ↦ by
        rw [dgDifferential_linearHomComplex]
        exact M.actionCochain_eq_δ _ _ (DGSingleObj.dgHomEquiv_dgDifferential (X := Z.unop)
          (Y := Y.unop) n f))
      (fun Y ↦ by
        rw [dgId_linearHomComplex]
        exact M.actionCochain_eq_ofHom_id _ (by
          cases Y
          rw [dgId_op]
          exact DGSingleObj.dgHomEquiv_dgId _))
      (fun {Y Z W p q n} f g hpq ↦ by
        obtain ⟨Y⟩ := Y
        obtain ⟨Z⟩ := Z
        obtain ⟨W⟩ := W
        rw [dgComp_linearHomComplex]
        refine M.actionCochain_eq_comp _ _ _ ?_ hpq
        rw [LinearEquiv.coe_coe, dgComp_op (R := R) (X := Y) (Y := Z) (Z := W) f g hpq,
          map_zsmul_unit, Units.smul_def, Submodule.coe_smul_of_tower,
          DGSingleObj.dgHomEquiv_dgComp, mul_comm q p, ← Units.smul_def]
        simp)
  ⟨{ obj := fun _ ↦ M.toCochainComplex
     map := F.map
     map_id := F.map_id
     map_comp := F.map_comp }⟩

/-- The DG module of `M` sends the unique object to the underlying complex of `M`. -/
theorem toDGFunctor_obj (X : (DGSingleObj h)ᵒᵖ) :
    M.toDGFunctor.toEnrichedFunctor.obj X = M.toCochainComplex :=
  (rfl)

/-- A morphism of the one-object DG category acts on the DG module of `M` by the signed right
action of the corresponding element of the algebra. -/
@[simp]
theorem toDGFunctor_dgMap {X Y : DGSingleObj h} {n : ℤ} (f : DGHom R n Y X) :
    M.toDGFunctor.toEnrichedFunctor.dgMap n (X := Opposite.op X) (Y := Opposite.op Y) f =
      M.actionCochain n (DGSingleObj.dgHomEquiv Y X n f) := by
  rw [EnrichedFunctor.dgMap_apply]
  -- The map on Hom complexes is that of `EnrichedFunctor.ofDGMap`, whose degree-`n` component
  -- is the prescribed action.
  rfl

/-- A morphism `f` of degree `n` acts on an element `x` of degree `p` of the DG module of `M` by
`x ↦ (-1) ^ (n * p) • x * a`, for `a` the element of the algebra corresponding to `f`. -/
@[simp]
theorem toDGFunctor_dgMap_v_apply {X Y : DGSingleObj h} {n : ℤ} (f : DGHom R n Y X)
    (p q : ℤ) (hpq : p + n = q) (x : M.toCochainComplex.X p) :
    (gradedCochainComplexXEquiv q
        (((M.toDGFunctor.toEnrichedFunctor.dgMap n (X := Opposite.op X) (Y := Opposite.op Y)
          f).v p q hpq).hom x) : M) =
      (n * p).negOnePow •
        (op (DGSingleObj.dgHomEquiv Y X n f : A) • (gradedCochainComplexXEquiv p x : M)) := by
  rw [toDGFunctor_dgMap]
  exact M.actionCochain_v_apply n _ p q hpq x

/-- **The free rank-one module goes to the representable module.**  Identify the elements of
degree `p` of the free rank-one right module with the morphisms `X ⟶ Y` of degree `p` of the
one-object DG category.  Then a morphism `f : Y ⟶ X` acts on the DG module of the free module as
it acts on the representable module `Hom(-, Y)` of `TauCeti.dgRepresentable`, by precomposition
`g ↦ f ≫ g`. -/
theorem toDGFunctor_of_isDGRightModule_dgMap_v_apply {X Y : DGSingleObj h} {n p : ℤ}
    (f : DGHom R n Y X) (g : DGHom R p X Y) :
    (gradedCochainComplexXEquiv (p + n)
        ((((DGRightModuleCat.of h.isDGRightModule).toDGFunctor.toEnrichedFunctor.dgMap n
          (X := Opposite.op X) (Y := Opposite.op Y) f).v p (p + n) rfl).hom
            ((gradedCochainComplexXEquiv p).symm (DGSingleObj.dgHomEquiv X Y p g))) : A) =
      DGSingleObj.dgHomEquiv Y Y (p + n)
        ((((dgRepresentable R Y).dgMap n (X := Opposite.op X) (Y := Opposite.op Y) f).v p
          (p + n) rfl).hom g) := by
  rw [toDGFunctor_dgMap_v_apply, LinearEquiv.apply_symm_apply, dgRepresentable_dgMap]
  refine Eq.trans ?_ (congrArg (fun t ↦ (DGSingleObj.dgHomEquiv Y Y (p + n) t : A))
    (dgPrecomp_v R Y f p (p + n) rfl g)).symm
  rw [DGSingleObj.dgHomEquiv_dgComp, op_smul_eq_mul]

/-! ### Morphisms of right DG modules -/

variable {M} {N P : DGRightModuleCat.{u, u, u} h}

/-- The chain map of a morphism of right DG modules commutes with the signed actions. -/
private theorem naturality_toCochainMap (φ : M ⟶ N) {X Y : (DGSingleObj h)ᵒᵖ} (n : ℤ)
    (f : DGHom R n X Y) :
    dgComp R (M.toDGFunctor.toEnrichedFunctor.dgMap n f)
        (Cochain.ofHom (toCochainMap φ) : DGHom R 0 M.toCochainComplex N.toCochainComplex)
        (add_zero n) =
      dgComp R (Cochain.ofHom (toCochainMap φ) : DGHom R 0 M.toCochainComplex N.toCochainComplex)
        (N.toDGFunctor.toEnrichedFunctor.dgMap n f) (zero_add n) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  rw [dgComp_v R _ _ (add_zero n) p q q hpq (add_zero q),
    dgComp_v R _ _ (zero_add n) p p q (add_zero p) hpq, toDGFunctor_dgMap, toDGFunctor_dgMap]
  ext x
  apply (gradedCochainComplexXEquiv q).injective
  apply Subtype.ext
  simp

/-- The **DG natural transformation of a morphism** `φ` of right DG modules, between their DG
modules over the one-object DG category: its component is the chain map of underlying complexes
induced by `φ`, which commutes with the signed actions because `φ` is a map of right modules. -/
noncomputable def toDGFunctorMap (φ : M ⟶ N) : M.toDGFunctor ⟶ N.toDGFunctor :=
  DGNatTrans.ofDGApp (fun _ ↦ Cochain.ofHom (toCochainMap φ))
    (fun _ ↦ by
      rw [mem_dgCycles, dgDifferential_linearHomComplex]
      exact δ_ofHom _)
    (fun n f ↦ naturality_toCochainMap φ n f)

/-- The component of the DG natural transformation of a morphism `φ` of right DG modules is the
chain map of underlying complexes induced by `φ`. -/
@[simp]
theorem dgApp_toDGFunctorMap (φ : M ⟶ N) (X : (DGSingleObj h)ᵒᵖ) :
    DGNatTrans.dgApp (R := R) (toDGFunctorMap φ) X = Cochain.ofHom (toCochainMap φ) :=
  DGNatTrans.dgApp_ofDGApp _ _ _ X

/-- The DG natural transformation of the identity is the identity. -/
@[simp]
theorem toDGFunctorMap_id (M : DGRightModuleCat.{u, u, u} h) :
    toDGFunctorMap (𝟙 M) = 𝟙 M.toDGFunctor :=
  DGNatTrans.ext_dgApp (R := R) (F := M.toDGFunctor.toEnrichedFunctor)
    (G := M.toDGFunctor.toEnrichedFunctor) fun X ↦ by
    rw [dgApp_toDGFunctorMap, toCochainMap_id, ← dgId_linearHomComplex]
    exact (DGNatTrans.dgApp_id (R := R) M.toDGFunctor.toEnrichedFunctor X).symm

/-- The DG natural transformation of a composite is the composite. -/
@[simp]
theorem toDGFunctorMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    toDGFunctorMap (φ ≫ ψ) = toDGFunctorMap φ ≫ toDGFunctorMap ψ :=
  DGNatTrans.ext_dgApp (R := R) (F := M.toDGFunctor.toEnrichedFunctor)
    (G := P.toDGFunctor.toEnrichedFunctor) fun X ↦ by
    refine (dgApp_toDGFunctorMap _ X).trans ?_
    refine Eq.trans ?_
      (DGNatTrans.dgApp_comp (R := R) (toDGFunctorMap φ) (toDGFunctorMap ψ) X).symm
    rw [dgApp_toDGFunctorMap, dgApp_toDGFunctorMap, dgCompZero_def, dgComp_linearHomComplex,
      toCochainMap_comp, Cochain.ofHom_comp]
    simp

/-- **Right DG modules as DG modules over the one-object DG category.**  The functor sending a
right DG module `M` over `h` to its DG module `M.toDGFunctor` over `TauCeti.DGSingleObj h`, and a
morphism of right DG modules to its DG natural transformation `toDGFunctorMap`.  It is fully
faithful. -/
noncomputable def singleObjFunctor : DGRightModuleCat.{u, u, u} h ⥤
    DGFunctor R (DGSingleObj h)ᵒᵖ (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj M := M.toDGFunctor
  map φ := toDGFunctorMap φ
  map_id M := toDGFunctorMap_id M
  map_comp φ ψ := toDGFunctorMap_comp φ ψ

/-- `singleObjFunctor` sends a right DG module to its DG module. -/
@[simp]
theorem singleObjFunctor_obj (M : DGRightModuleCat.{u, u, u} h) :
    singleObjFunctor.obj M = M.toDGFunctor :=
  (rfl)

/-- `singleObjFunctor` sends a morphism of right DG modules to its DG natural transformation,
transported along `singleObjFunctor_obj`. -/
@[simp]
theorem singleObjFunctor_map (φ : M ⟶ N) :
    singleObjFunctor.map φ = eqToHom (singleObjFunctor_obj M) ≫ toDGFunctorMap φ ≫
      eqToHom (singleObjFunctor_obj N).symm := by
  -- Both transports are along definitional equalities, so they are identities.
  change toDGFunctorMap φ = 𝟙 _ ≫ toDGFunctorMap φ ≫ 𝟙 _
  simp

/-- The component of the DG natural transformation of a morphism `φ` of right DG modules is `φ`
on elements of every degree. -/
theorem dgApp_toDGFunctorMap_v_apply (φ : M ⟶ N) (X : (DGSingleObj h)ᵒᵖ) (p : ℤ)
    (x : M.toCochainComplex.X p) :
    (gradedCochainComplexXEquiv p
        (((DGNatTrans.dgApp (R := R) (toDGFunctorMap φ) X :
          Cochain M.toCochainComplex N.toCochainComplex 0).v p p (add_zero p)).hom x) : N) =
      φ (gradedCochainComplexXEquiv p x) := by
  rw [dgApp_toDGFunctorMap, Cochain.ofHom_v, toCochainMap_f_apply]

/-- `singleObjFunctor` is faithful: a morphism of right DG modules is determined by its
components on the homogeneous pieces. -/
instance : (singleObjFunctor (h := h)).Faithful where
  map_injective {M N} {φ ψ} e := by
    have hc : toCochainMap φ = toCochainMap ψ := Cochain.ofHom_injective <| by
      -- Within this file `singleObjFunctor.map` unfolds to `toDGFunctorMap`.
      have e' : toDGFunctorMap φ = toDGFunctorMap ψ := e
      rw [← dgApp_toDGFunctorMap φ (Opposite.op (DGSingleObj.star h)), e', dgApp_toDGFunctorMap]
    refine DGRightModuleCat.hom_ext fun x ↦ ?_
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => rw [map_zero, map_zero]
    | @homogeneous p x =>
      have := congrArg (fun g : M.toCochainComplex ⟶ N.toCochainComplex ↦
        (gradedCochainComplexXEquiv p ((g.f p).hom ((gradedCochainComplexXEquiv p).symm x)) : N))
        hc
      simpa only [toCochainMap_f_apply, LinearEquiv.apply_symm_apply] using this
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### Fullness -/

/-- The linear map on total modules assembled from the components of a degree-zero cochain
between underlying complexes. -/
private noncomputable def totalMap (z : Cochain M.toCochainComplex N.toCochainComplex 0) :
    M →ₗ[R] N :=
  DirectSum.toModule R ℤ N (fun p ↦ (N.grading p).subtype ∘ₗ
      (gradedCochainComplexXEquiv p).toLinearMap ∘ₗ (z.v p p (add_zero p)).hom ∘ₗ
        (gradedCochainComplexXEquiv p).symm.toLinearMap) ∘ₗ
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

private theorem totalMap_of_mem (z : Cochain M.toCochainComplex N.toCochainComplex 0) {p : ℤ}
    {x : M} (hx : x ∈ M.grading p) :
    totalMap z x = gradedCochainComplexXEquiv p
      ((z.v p p (add_zero p)).hom ((gradedCochainComplexXEquiv p).symm ⟨x, hx⟩)) := by
  simp only [totalMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem _ hx]
  rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  simp

/-- A closed degree-zero cochain commutes with the module differentials on total modules. -/
private theorem totalMap_differential {z : Cochain M.toCochainComplex N.toCochainComplex 0}
    (hz : δ 0 1 z = 0) (x : M) : N.differential (totalMap z x) = totalMap z (M.differential x) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | @homogeneous p x =>
    have hd : (gradedCochainComplexXEquiv (p + 1)).symm
        ⟨M.differential x, M.isDGRightModule.isHomogeneous.map_mem x.2⟩ =
          (M.toCochainComplex.d p (p + 1)).hom ((gradedCochainComplexXEquiv p).symm x) := by
      apply (gradedCochainComplexXEquiv (p + 1)).injective
      apply Subtype.ext
      rw [LinearEquiv.apply_symm_apply, gradedCochainComplexXEquiv_d,
        LinearEquiv.apply_symm_apply]
    have hzd := congrArg (fun g ↦ g.hom ((gradedCochainComplexXEquiv p).symm x))
      (Cochain.congr_v hz p (p + 1) rfl)
    simp only [δ_zero_cochain_v, Cochain.zero_v, ModuleCat.hom_sub, ModuleCat.hom_comp,
      LinearMap.sub_apply, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      sub_eq_zero] at hzd
    rw [totalMap_of_mem z x.2, totalMap_of_mem z (M.isDGRightModule.isHomogeneous.map_mem x.2),
      ← gradedCochainComplexXEquiv_d, hd, hzd]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- A degree-zero cochain commuting with the signed actions is a map of right modules on total
modules. -/
private theorem totalMap_op_smul {z : Cochain M.toCochainComplex N.toCochainComplex 0}
    (hnat : ∀ (n : ℤ) (a : 𝒜 n),
      (M.actionCochain n a).comp z (add_zero n) = z.comp (N.actionCochain n a) (zero_add n))
    (a : A) (x : M) : totalMap z (op a • x) = op a • totalMap z x := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 generalizing x with
  | zero => rw [op_zero, zero_smul, zero_smul, map_zero]
  | add a b ha hb => rw [MulOpposite.op_add, add_smul, add_smul, map_add, ha, hb]
  | @homogeneous n a =>
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | @homogeneous p x =>
      have hax := op_smul_mem_of_mem_graded a.2 x.2
      have key := congrArg (fun g ↦ (gradedCochainComplexXEquiv (p + n)
        (g.hom ((gradedCochainComplexXEquiv p).symm x)) : N))
        (Cochain.congr_v (hnat n a) p (p + n) rfl)
      simp only [Cochain.comp_v _ _ (add_zero n) p (p + n) (p + n) rfl (add_zero _),
        Cochain.comp_v _ _ (zero_add n) p p (p + n) (add_zero p) rfl, ModuleCat.hom_comp,
        LinearMap.comp_apply, actionCochain_v_apply] at key
      have hy : ((M.actionCochain n a).v p (p + n) rfl).hom
          ((gradedCochainComplexXEquiv p).symm x) =
            (n * p).negOnePow • (gradedCochainComplexXEquiv (p + n)).symm ⟨_, hax⟩ := by
        apply (gradedCochainComplexXEquiv (p + n)).injective
        apply Subtype.ext
        simp
      rw [hy] at key
      rw [totalMap_of_mem z hax, totalMap_of_mem z x.2]
      simpa using congrArg (fun y : N ↦ (n * p).negOnePow • y) key

/-- The morphism of right DG modules assembled from a closed degree-zero cochain commuting with
the signed actions. -/
private noncomputable def homOfCochain (z : Cochain M.toCochainComplex N.toCochainComplex 0)
    (hz : δ 0 1 z = 0)
    (hnat : ∀ (n : ℤ) (a : 𝒜 n),
      (M.actionCochain n a).comp z (add_zero n) = z.comp (N.actionCochain n a) (zero_add n)) :
    M ⟶ N where
  toFun := totalMap z
  map_add' := map_add _
  map_smul' c x := by
    rw [← op_unop c]
    exact totalMap_op_smul hnat c.unop x
  map_mem' hx := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, totalMap_of_mem z hx]
    exact Subtype.mem _
  map_d' x := totalMap_differential hz x

private theorem homOfCochain_apply (z : Cochain M.toCochainComplex N.toCochainComplex 0)
    (hz : δ 0 1 z = 0)
    (hnat : ∀ (n : ℤ) (a : 𝒜 n),
      (M.actionCochain n a).comp z (add_zero n) = z.comp (N.actionCochain n a) (zero_add n))
    (x : M) : homOfCochain z hz hnat x = totalMap z x :=
  (rfl)

/-- `singleObjFunctor` is full: every DG natural transformation between DG modules of right DG
modules comes from a morphism of right DG modules, whose value on an element of degree `p` is
the component of the transformation. -/
instance : (singleObjFunctor (h := h)).Full where
  map_surjective {M N} η := by
    -- Retype `η` through `singleObjFunctor_obj`, so that the lemmas about `toDGFunctor` apply.
    let η' : M.toDGFunctor ⟶ N.toDGFunctor := η
    let z : Cochain M.toCochainComplex N.toCochainComplex 0 := DGNatTrans.dgApp (R := R) η'
      (Opposite.op (DGSingleObj.star h))
    have hz : δ 0 1 z = 0 := by
      have := DGNatTrans.dgApp_mem_dgCycles (R := R) η' (Opposite.op (DGSingleObj.star h))
      rwa [mem_dgCycles, dgDifferential_linearHomComplex] at this
    have hnat (n : ℤ) (a : 𝒜 n) :
        (M.actionCochain n a).comp z (add_zero n) = z.comp (N.actionCochain n a) (zero_add n) := by
      have := DGNatTrans.dgComp_dgMap_dgApp (R := R) η'
        ((DGSingleObj.dgHomEquiv (DGSingleObj.star h) (DGSingleObj.star h) n).symm a)
      rw [dgComp_linearHomComplex, dgComp_linearHomComplex, toDGFunctor_dgMap,
        toDGFunctor_dgMap] at this
      simpa using this
    refine ⟨homOfCochain z hz hnat, show toDGFunctorMap (homOfCochain z hz hnat) = η' from ?_⟩
    refine DGNatTrans.ext_dgApp (R := R) (F := M.toDGFunctor.toEnrichedFunctor)
      (G := N.toDGFunctor.toEnrichedFunctor) fun X ↦ ?_
    obtain ⟨X⟩ := X
    obtain rfl : X = DGSingleObj.star h := Subsingleton.elim _ _
    rw [dgApp_toDGFunctorMap]
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    ext x
    apply (gradedCochainComplexXEquiv p).injective
    apply Subtype.ext
    rw [Cochain.ofHom_v, toCochainMap_f_apply, homOfCochain_apply,
      totalMap_of_mem z (gradedCochainComplexXEquiv p x).2]
    simp [z]

end DGRightModuleCat

end TauCeti
