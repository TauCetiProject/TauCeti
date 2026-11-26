/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Comparison

/-!
# External products of Ext groups of functors

For functors `M, N : C ⥤ AddCommGrpCat`, `CategoryTheory.objectwiseTensor` gives their objectwise
tensor product `M ⊗ N : c ↦ M(c) ⊗[ℤ] N(c)`, as a bifunctor. A functor *has flat values*
(`CategoryTheory.Functor.HasFlatValues`) if all its values are flat `ℤ`-modules, that is,
torsion-free abelian groups; tensoring with such a functor, on either side, is exact.

For `x ∈ Extᵃ(M, F)` and `y ∈ Extᵇ(N, G)`, with `M` and `G` of flat values, and a pairing
`μ : F ⊗ G ⟶ K`, the *external product*
`CategoryTheory.Abelian.Ext.externalProduct μ x y : Extᵃ⁺ᵇ(M ⊗ N, K)` is the push-forward by `μ`
of the Yoneda product of `M ⊗ y ∈ Extᵇ(M ⊗ N, M ⊗ G)` and `x ⊗ G ∈ Extᵃ(M ⊗ G, F ⊗ G)`. It is
natural in both arguments (`CategoryTheory.Abelian.Ext.mk₀_comp_externalProduct`) and in the
coefficients (`CategoryTheory.Abelian.Ext.externalProduct_comp_mk₀_comp_mk₀`), commutes with
restriction along a functor, and comparison maps (`CategoryTheory.Functor.extComparison`) carry
external products to external products when they carry the pairing to the pairing
(`CategoryTheory.Functor.extComparison_externalProduct`).

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (declarations `New.Variety.abTensor`,
  `New.Variety.HasFlatValues`, `New.Variety.cup`, `New.Variety.cup_map`,
  `New.Variety.Comparison.pull_cup`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  definitions and results are adapted from these declarations.
-/

public section

open CategoryTheory Limits Abelian TensorProduct

universe t t' w v u v' u' v'' u''

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Two homomorphisms out of a tensor product of abelian groups agree if they agree on pure
tensors. -/
lemma AddCommGrpCat.tensor_hom_ext {A B X : AddCommGrpCat.{w}}
    {f g : AddCommGrpCat.of (A ⊗[ℤ] B) ⟶ X} (h : ∀ (a : A) (b : B), f (a ⊗ₜ b) = g (a ⊗ₜ b)) :
    f = g :=
  AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective (TensorProduct.ext' h))

variable (C) in
/-- The objectwise tensor product over `ℤ` of functors to abelian groups, as a bifunctor:
`(M ⊗ N)(c) = M(c) ⊗[ℤ] N(c)`. -/
@[expose] noncomputable def objectwiseTensor :
    (C ⥤ AddCommGrpCat.{w}) ⥤ (C ⥤ AddCommGrpCat.{w}) ⥤ C ⥤ AddCommGrpCat.{w} :=
  Functor.curryObj
    { obj p :=
        { obj c := AddCommGrpCat.of (p.1.obj c ⊗[ℤ] p.2.obj c)
          map f := AddCommGrpCat.ofHom
            (TensorProduct.map (p.1.map f).hom.toIntLinearMap (p.2.map f).hom.toIntLinearMap)
          map_id _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp
          map_comp _ _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }
      map f :=
        { app c := AddCommGrpCat.ofHom
            (TensorProduct.map (f.1.app c).hom.toIntLinearMap (f.2.app c).hom.toIntLinearMap)
          naturality _ _ _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }
      map_id _ := NatTrans.ext <| funext fun _ ↦ AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp
      map_comp _ _ :=
        NatTrans.ext <| funext fun _ ↦ AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }

namespace objectwiseTensor

variable {M M' N N' K : C ⥤ AddCommGrpCat.{w}}

@[simp]
lemma obj_obj_obj (M N : C ⥤ AddCommGrpCat.{w}) (c : C) :
    (((objectwiseTensor C).obj M).obj N).obj c = AddCommGrpCat.of (M.obj c ⊗[ℤ] N.obj c) :=
  (rfl)

/-- Tensoring with a map on the right acts on pure tensors. -/
@[simp]
lemma obj_map_app_tmul (M : C ⥤ AddCommGrpCat.{w}) (β : N ⟶ N') (c : C) (m : M.obj c)
    (n : N.obj c) :
    ((((objectwiseTensor C).obj M).map β).app c)
      (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) = m ⊗ₜ β.app c n :=
  (rfl)

/-- Tensoring with a map on the left acts on pure tensors. -/
@[simp]
lemma map_app_app_tmul (α : M ⟶ M') (N : C ⥤ AddCommGrpCat.{w}) (c : C) (m : M.obj c)
    (n : N.obj c) :
    ((((objectwiseTensor C).map α).app N).app c)
      (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) = α.app c m ⊗ₜ n :=
  (rfl)

/-- Two maps out of an objectwise tensor product agree if they agree on pure tensors. -/
lemma hom_ext {f g : ((objectwiseTensor C).obj M).obj N ⟶ K}
    (h : ∀ (c : C) (m : M.obj c) (n : N.obj c),
      f.app c (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) =
        g.app c (m ⊗ₜ n)) :
    f = g :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.tensor_hom_ext (h c))

/-- The two ways of tensoring a pair of maps agree. -/
lemma map_app_comp_map (α : M ⟶ M') (β : N ⟶ N') :
    ((objectwiseTensor C).map α).app N ≫ ((objectwiseTensor C).obj M').map β =
      ((objectwiseTensor C).obj M).map β ≫ ((objectwiseTensor C).map α).app N' :=
  (((objectwiseTensor C).map α).naturality β).symm

instance (M : C ⥤ AddCommGrpCat.{w}) : ((objectwiseTensor C).obj M).Additive :=
  ⟨fun {_ _ f g} ↦ hom_ext fun c m n ↦ by
    change m ⊗ₜ[ℤ] (f + g).app c n = m ⊗ₜ[ℤ] f.app c n + m ⊗ₜ[ℤ] g.app c n
    simp [tmul_add]⟩

instance (N : C ⥤ AddCommGrpCat.{w}) : ((objectwiseTensor C).flip.obj N).Additive :=
  ⟨fun {_ _ f g} ↦ hom_ext fun c m n ↦ by
    change (f + g).app c m ⊗ₜ[ℤ] n = f.app c m ⊗ₜ[ℤ] n + g.app c m ⊗ₜ[ℤ] n
    simp [add_tmul]⟩

end objectwiseTensor

/-- A functor to abelian groups *has flat values* if each of its values is a flat `ℤ`-module. -/
class Functor.HasFlatValues (F : C ⥤ AddCommGrpCat.{w}) : Prop where
  /-- Each value of `F` is a flat `ℤ`-module. -/
  flat (c : C) : Module.Flat ℤ (F.obj c)

instance {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C) (F : C ⥤ AddCommGrpCat.{w})
    [F.HasFlatValues] : (φ ⋙ F).HasFlatValues :=
  ⟨fun c ↦ Functor.HasFlatValues.flat (F := F) (φ.obj c)⟩

instance {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C) (F : C ⥤ AddCommGrpCat.{w})
    [F.HasFlatValues] :
    (((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ).obj F).HasFlatValues :=
  inferInstanceAs (φ ⋙ F).HasFlatValues

/-- A functor `G` preserves finite limits and colimits if it is additive and sends short exact
sequences to exact sequences, objectwise as homomorphisms of abelian groups. -/
private lemma preservesFiniteLimitsColimits_of_exact
    (G : (C ⥤ AddCommGrpCat.{w}) ⥤ C ⥤ AddCommGrpCat.{w}) [G.Additive]
    (h : ∀ S : ShortComplex (C ⥤ AddCommGrpCat.{w}), S.Exact →
      ∀ c, Function.Exact ((G.map S.f).app c) ((G.map S.g).app c)) :
    PreservesFiniteLimits G ∧ PreservesFiniteColimits G :=
  (G.exact_tfae.out 2 4 :).mp fun S hS ↦ (ShortComplex.exact_iff_forall_function_exact _).2 (h S hS)

/-- Tensoring on the left with a functor of flat values is exact. -/
private lemma exact_tensorLeft (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).obj M) ∧
      PreservesFiniteColimits ((objectwiseTensor C).obj M) := by
  refine preservesFiniteLimitsColimits_of_exact _ fun S hS c ↦ ?_
  have := Functor.HasFlatValues.flat (F := M) c
  exact Module.Flat.lTensor_exact (M.obj c)
    ((ShortComplex.exact_iff_forall_function_exact S).1 hS c)

/-- Tensoring on the right with a functor of flat values is exact. -/
private lemma exact_tensorRight (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).flip.obj N) ∧
      PreservesFiniteColimits ((objectwiseTensor C).flip.obj N) := by
  refine preservesFiniteLimitsColimits_of_exact _ fun S hS c ↦ ?_
  have := Functor.HasFlatValues.flat (F := N) c
  exact Module.Flat.rTensor_exact (N.obj c)
    ((ShortComplex.exact_iff_forall_function_exact S).1 hS c)

instance (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).obj M) := (exact_tensorLeft M).1

instance (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteColimits ((objectwiseTensor C).obj M) := (exact_tensorLeft M).2

instance (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).flip.obj N) := (exact_tensorRight N).1

instance (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteColimits ((objectwiseTensor C).flip.obj N) := (exact_tensorRight N).2

/-! ### The external product -/

namespace Abelian.Ext

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] {M N F G K : C ⥤ AddCommGrpCat.{w}} {a b n : ℕ}

local notation "T" => objectwiseTensor C

/-- The *external product* of `x ∈ Extᵃ(M, F)` and `y ∈ Extᵇ(N, G)` along a pairing
`μ : F ⊗ G ⟶ K`, for `M` and `G` of flat values: the class in `Extᵃ⁺ᵇ(M ⊗ N, K)` obtained by
pushing forward along `μ` the Yoneda product of `M ⊗ y ∈ Extᵇ(M ⊗ N, M ⊗ G)` and
`x ⊗ G ∈ Extᵃ(M ⊗ G, F ⊗ G)`. -/
noncomputable def externalProduct [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    Ext.{t} (((T).obj M).obj N) K n :=
  ((y.mapExactFunctor ((T).obj M)).comp (x.mapExactFunctor ((T).flip.obj G))
    (by lia)).comp (mk₀ μ) (add_zero n)

/-- Naturality of the action of exact functors on Ext, in right-associated form: for
`τ : Φ ⟶ Ψ`, the class `Φ x` followed by `τ` and `z` is `τ` followed by `Ψ x` and `z`. -/
private lemma mapExactFunctor_comp_mk₀_comp {𝒜 𝒟 : Type*} [Category* 𝒜] [Abelian 𝒜]
    [HasExt.{t} 𝒜] [Category* 𝒟] [Abelian 𝒟] [HasExt.{t'} 𝒟] {Φ Ψ : 𝒜 ⥤ 𝒟}
    [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] [Ψ.Additive]
    [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (τ : Φ ⟶ Ψ) {X Y : 𝒜} {W : 𝒟} {c : ℕ}
    (x : Ext.{t} X Y a) (z : Ext.{t'} (Ψ.obj Y) W c) (h : a + c = n) :
    (x.mapExactFunctor Φ).comp ((mk₀ (τ.app Y)).comp z (zero_add c)) h =
      (mk₀ (τ.app X)).comp ((x.mapExactFunctor Ψ).comp z h) (zero_add n) := by
  rw [← comp_assoc_of_second_deg_zero, mapExactFunctor_comp_mk₀_natTransApp,
    comp_assoc _ _ _ (zero_add a) h (by lia)]

/-- Composition of Ext classes is associative when the first class has degree zero. -/
private lemma mk₀_comp_comp {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasExt.{t} 𝒜] {X Y Z W : 𝒜}
    {p q r : ℕ} (f : X ⟶ Y) (y : Ext.{t} Y Z p) (z : Ext.{t} Z W q) (h : p + q = r) :
    ((mk₀ f).comp y (zero_add p)).comp z h = (mk₀ f).comp (y.comp z h) (zero_add r) :=
  comp_assoc _ _ _ (zero_add p) h (by lia)

/-- Pushing an external product forward along `κ : K ⟶ K'` changes the pairing to `μ ≫ κ`. -/
lemma externalProduct_comp_mk₀ [M.HasFlatValues] [G.HasFlatValues] {K' : C ⥤ AddCommGrpCat.{w}}
    (μ : ((T).obj F).obj G ⟶ K) (κ : K ⟶ K') (x : Ext.{t} M F a) (y : Ext.{t} N G b)
    (h : a + b = n) :
    (externalProduct μ x y h).comp (mk₀ κ) (add_zero n) = externalProduct (μ ≫ κ) x y h := by
  unfold externalProduct
  rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]

/-- The external product is natural in the coefficients: pushing `x` forward along `β₁ : F ⟶ F'`
and `y` along `β₂ : G ⟶ G'` and pairing by `μ'` is pairing `x` and `y` by `(β₁ ⊗ β₂) ≫ μ'`. -/
lemma externalProduct_comp_mk₀_comp_mk₀ [M.HasFlatValues] [G.HasFlatValues]
    {F' G' : C ⥤ AddCommGrpCat.{w}} [G'.HasFlatValues] (β₁ : F ⟶ F') (β₂ : G ⟶ G')
    (μ' : ((T).obj F').obj G' ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    externalProduct μ' (x.comp (mk₀ β₁) (add_zero a)) (y.comp (mk₀ β₂) (add_zero b)) h =
      externalProduct (((T).map β₁).app G ≫ ((T).obj F').map β₂ ≫ μ') x y h := by
  have hτ := mapExactFunctor_comp_mk₀_comp ((T).flip.map β₂) x
    (mk₀ (((T).flip.obj G').map β₁ ≫ μ')) (add_zero a)
  unfold externalProduct
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀, comp_assoc_of_third_deg_zero,
    comp_assoc_of_second_deg_zero, mk₀_comp_mk₀]
  rw [show ((T).obj M).map β₂ = ((T).flip.map β₂).app M from rfl, ← hτ, mk₀_comp_mk₀,
    ← Category.assoc, ← Category.assoc]
  congr 4
  exact (objectwiseTensor.map_app_comp_map β₁ β₂).symm

/-- **Naturality of the external product in both arguments.** For `α : M' ⟶ M`, `β : N' ⟶ N`
and `γ : L ⟶ M ⊗ N` equal to `γ' : L ⟶ M' ⊗ N'` followed by `α ⊗ β`, pulling back the external
product of `x` and `y` along `γ` is pulling back the external product of `α* x` and `β* y` along
`γ'`. -/
lemma mk₀_comp_externalProduct [M.HasFlatValues] [G.HasFlatValues]
    {M' N' L : C ⥤ AddCommGrpCat.{w}} [M'.HasFlatValues] (μ : ((T).obj F).obj G ⟶ K)
    (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) (α : M' ⟶ M) (β : N' ⟶ N)
    {γ : L ⟶ ((T).obj M).obj N} {γ' : L ⟶ ((T).obj M').obj N'}
    (hγ : γ' ≫ ((T).map α).app N' ≫ ((T).obj M).map β = γ) :
    (mk₀ γ).comp (externalProduct μ x y h) (zero_add n) =
      (mk₀ γ').comp (externalProduct μ ((mk₀ α).comp x (zero_add a))
        ((mk₀ β).comp y (zero_add b)) h) (zero_add n) := by
  have hτ := mapExactFunctor_comp_mk₀_comp ((T).map α) y
    ((x.mapExactFunctor ((T).flip.obj G)).comp (mk₀ μ) (add_zero a)) (by lia : b + a = n)
  unfold externalProduct
  simp only [mapExactFunctor_comp, mapExactFunctor_mk₀, comp_assoc_of_third_deg_zero,
    mk₀_comp_mk₀_assoc, mk₀_comp_comp]
  rw [show ((T).flip.obj G).map α = ((T).map α).app G from rfl, hτ, mk₀_comp_mk₀_assoc,
    ← hγ, Category.assoc, objectwiseTensor.map_app_comp_map]

/-- Restriction along a functor `φ : C' ⥤ C` commutes with external products: the restriction of
the external product of `x` and `y` along `μ` is the external product of the restrictions along the
restricted pairing `φ.whiskerLeft μ`. -/
lemma mapExactFunctor_whiskeringLeft_externalProduct {C' : Type u'} [Category.{v'} C']
    [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})] (φ : C' ⥤ C) [M.HasFlatValues] [G.HasFlatValues]
    (μ : ((T).obj F).obj G ⟶ K) (x : Ext.{t} M F a) (y : Ext.{t} N G b) (h : a + b = n) :
    (externalProduct μ x y h).mapExactFunctor
        ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ) =
      externalProduct (Functor.whiskerLeft φ μ)
        (x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ))
        (y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)) h := by
  unfold externalProduct
  rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_mk₀, ← comp_mapExactFunctor,
    ← comp_mapExactFunctor, ← comp_mapExactFunctor, ← comp_mapExactFunctor]
  rfl

end Abelian.Ext

open Abelian.Ext in
/-- **Comparison maps respect external products.** Let `(φ, β)` be a comparison from `F` on `C` to
`F'` on `C'`, both of flat values, carrying the pairing `μ : F ⊗ F ⟶ F` to `μ' : F' ⊗ F' ⟶ F'`, in
the sense that `(β ⊗ β) ≫ μ' = φ.whiskerLeft μ ≫ β`. For `x ∈ Extᵃ(M, F)`, `y ∈ Extᵇ(M', F)` and
maps `α₁ : N₁ ⟶ φ ⋙ M`, `α₂ : N₂ ⟶ φ ⋙ M'`, the comparison map along `α₁ ⊗ α₂` sends the
external product of `x` and `y` to the external product of the comparison images of `x` and `y`.
The case of functors `M = Θ ⋙ N`, `M' = Θ ⋙ N'` restricted from a third category along
`Θ : C ⥤ A`, with `α₁` and `α₂` induced by a natural transformation `η : Θ' ⟶ φ ⋙ Θ`, is the
compatibility of comparisons with products of the cohomology of functors on `A`. -/
theorem Functor.extComparison_externalProduct {C' : Type u'} [Category.{v'} C']
    [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})]
    {F M M' : C ⥤ AddCommGrpCat.{w}} {F' N₁ N₂ : C' ⥤ AddCommGrpCat.{w}} [F.HasFlatValues]
    [F'.HasFlatValues] [M.HasFlatValues] [N₁.HasFlatValues] (φ : C' ⥤ C) (β : φ ⋙ F ⟶ F')
    {μ : ((objectwiseTensor C).obj F).obj F ⟶ F} {μ' : ((objectwiseTensor C').obj F').obj F' ⟶ F'}
    (hμ : ((objectwiseTensor C').map β).app (φ ⋙ F) ≫ ((objectwiseTensor C').obj F').map β ≫ μ' =
      φ.whiskerLeft μ ≫ β)
    {a b n : ℕ} (x : Ext.{t} M F a) (y : Ext.{t} M' F b) (α₁ : N₁ ⟶ φ ⋙ M) (α₂ : N₂ ⟶ φ ⋙ M')
    (h : a + b = n) :
    extComparison φ β (((objectwiseTensor C').map α₁).app N₂ ≫
        ((objectwiseTensor C').obj (φ ⋙ M)).map α₂ :
          _ ⟶ φ ⋙ ((objectwiseTensor C).obj M).obj M') n (externalProduct μ x y h) =
      externalProduct μ' (extComparison φ β α₁ a x) (extComparison φ β α₂ b y) h := by
  have h₁ := mapExactFunctor_whiskeringLeft_externalProduct φ μ x y h
  have h₂ := externalProduct_comp_mk₀ (φ.whiskerLeft μ) β
    (x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ))
    (y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)) h
  have h₄ := (congrArg (fun m ↦ externalProduct m
      (x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ))
      (y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)) h)
      hμ.symm).trans (externalProduct_comp_mk₀_comp_mk₀ β β μ' _ _ h).symm
  have h₃ := mk₀_comp_externalProduct μ'
    ((x.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)).comp (mk₀ β)
      (add_zero a))
    ((y.mapExactFunctor ((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)).comp (mk₀ β)
      (add_zero b)) h α₁ α₂ (γ' := 𝟙 _) (Category.id_comp _)
  rw [mk₀_id_comp] at h₃
  rw [extComparison_apply, h₁]
  erw [h₂, h₄]
  rw [extComparison_apply, extComparison_apply]
  exact h₃

end CategoryTheory
