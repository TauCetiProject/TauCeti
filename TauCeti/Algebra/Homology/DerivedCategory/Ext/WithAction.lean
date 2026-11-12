/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat base change of `Ext`-groups along actions on the target

Let `C` be an abelian category, `A ⟶ B` a flat map of commutative rings, `F` an object of `C`
with an action `ρ : A →+* End F` of `A`, and `G` an object with an action `σ : B →+* End G` of
`B`, together with a morphism `η : F ⟶ G` intertwining the two actions. For every object `P`
the groups `Ext P F n` and `Ext P G n` are modules over `A` and `B`
(`TauCeti.Abelian.ExtWithAction`), and there is a `B`-linear base change map
```
  B ⊗[A] Ext P F n ⟶ Ext P G n,   b ⊗ x ↦ b • η_* x
```
(`TauCeti.Abelian.ExtWithAction.baseChange`). We show that the class of objects `P` for
which these maps are bijective in all degrees is closed under isomorphisms, binary biproducts and
cokernels of monomorphisms between its members. The last point is the five lemma applied to the
long exact sequences of `Ext`-groups, the first of which stays exact after `B ⊗[A] -` since `B`
is flat over `A`.

This is the algebraic core of flat base change for the cohomology of quasi-coherent modules,
where `P` runs through the free abelian sheaves `ℤ_U` on opens `U` and a short exact sequence
`0 ⟶ ℤ_{U ∩ V} ⟶ ℤ_U ⊕ ℤ_V ⟶ ℤ_{U ∪ V} ⟶ 0` gives the Mayer–Vietoris sequence.

## Main statements

- `TauCeti.Abelian.ExtWithAction.bijective_baseChange_of_iso`,
  `TauCeti.Abelian.ExtWithAction.bijective_baseChange_biprod`,
  `TauCeti.Abelian.ExtWithAction.bijective_baseChange_of_shortExact`: the closure
  properties of the objects for which the base change maps are bijective.
-/

public section

universe w v u

open CategoryTheory Limits TensorProduct CategoryTheory.Abelian CategoryTheory.Abelian.Ext

namespace TauCeti.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Action

variable {A : Type*} [Semiring A] {F : C} (ρ : A →+* End F)

/-- `Ext P F n` with the action of `A` induced by an action `ρ : A →+* End F` of `A` on `F`,
`a • x = ρ(a)_* x`. -/
-- Expose the synonym so its inherited additive and scalar instances share the Ext carrier.
@[expose]
def ExtWithAction (_ρ : A →+* End F) (P : C) (n : ℕ) : Type w := Ext P F n

namespace ExtWithAction

noncomputable instance (P : C) (n : ℕ) : AddCommGroup (ExtWithAction ρ P n) :=
  inferInstanceAs (AddCommGroup (Ext P F n))

/-- The action of `A` on `Ext P F n` induced by `ρ`, as a ring homomorphism to the additive
endomorphisms. -/
noncomputable def smulEnd (P : C) (n : ℕ) : A →+* AddMonoid.End (Ext P F n) where
  toFun a := (mk₀ (ρ a).asHom).postcomp P (add_zero n)
  map_one' := by
    ext x
    -- AddMonoid.End.one evaluates to the identity, and postcomp evaluates to Ext.comp.
    change x.comp (mk₀ (ρ 1).asHom) (add_zero n) = x
    rw [map_one, End.one_asHom]
    exact comp_mk₀_id x
  map_mul' a b := by
    ext x
    -- Endomorphism multiplication is composition; postcomp exposes its two Ext factors.
    change x.comp (mk₀ (ρ (a * b)).asHom) (add_zero n) =
      (x.comp (mk₀ (ρ b).asHom) (add_zero n)).comp (mk₀ (ρ a).asHom) (add_zero n)
    rw [map_mul, End.mul_asHom, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
  map_zero' := by
    ext x
    -- The zero endomorphism evaluates to zero, while postcomp evaluates to Ext.comp.
    change x.comp (mk₀ (ρ 0).asHom) (add_zero n) = 0
    rw [map_zero, End.zero_asHom, mk₀_zero]
    exact comp_zero _ _ _ _ _
  map_add' a b := by
    ext x
    -- Addition of endomorphisms is pointwise, and each postcomp evaluates to Ext.comp.
    change x.comp (mk₀ (ρ (a + b)).asHom) (add_zero n) =
      x.comp (mk₀ (ρ a).asHom) (add_zero n) + x.comp (mk₀ (ρ b).asHom) (add_zero n)
    rw [map_add, End.add_asHom, mk₀_add]
    exact comp_add _ _ _ _

noncomputable instance (P : C) (n : ℕ) : Module A (ExtWithAction ρ P n) :=
  Module.compHom (Ext P F n) (smulEnd ρ P n)

/-- The identification of `ExtWithAction ρ P n` with `Ext P F n`. -/
noncomputable def toExt {P : C} {n : ℕ} : ExtWithAction ρ P n ≃+ Ext P F n := AddEquiv.refl _

@[simp]
lemma toExt_smul {P : C} {n : ℕ} (a : A) (x : ExtWithAction ρ P n) :
    toExt ρ (a • x) = (toExt ρ x).comp (mk₀ (ρ a).asHom) (add_zero n) :=
  (rfl)

/-- Precomposition with `α : Ext P P' m` is `A`-linear. -/
noncomputable def precompLinearMap {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ} (h : m + n = n') :
    ExtWithAction ρ P' n →ₗ[A] ExtWithAction ρ P n' where
  toFun x := (toExt ρ).symm (α.comp (toExt ρ x) h)
  map_add' x y := comp_add α (toExt ρ x) (toExt ρ y) h
  map_smul' a x := (comp_assoc_of_third_deg_zero α (toExt ρ x) (mk₀ (ρ a).asHom) h).symm

@[simp]
lemma toExt_precompLinearMap {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ} (h : m + n = n')
    (x : ExtWithAction ρ P' n) : toExt ρ (precompLinearMap ρ α h x) = α.comp (toExt ρ x) h :=
  (rfl)

/-- Precomposition with an isomorphism, as an `A`-linear equivalence. -/
noncomputable def precompLinearEquiv {P P' : C} (e : P ≅ P') (n : ℕ) :
    ExtWithAction ρ P' n ≃ₗ[A] ExtWithAction ρ P n :=
  LinearEquiv.ofLinearMap (precompLinearMap ρ (mk₀ e.hom) (zero_add n))
    (precompLinearMap ρ (mk₀ e.inv) (zero_add n))
    (LinearMap.ext fun x ↦ by
      -- Forget the transported module structure and compute composition in Ext.
      change (mk₀ e.hom).comp ((mk₀ e.inv).comp (toExt ρ x) (zero_add n)) (zero_add n) =
        toExt ρ x
      rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.hom_inv_id, mk₀_id_comp])
    (LinearMap.ext fun x ↦ by
      -- Forget the transported module structure and compute composition in Ext.
      change (mk₀ e.inv).comp ((mk₀ e.hom).comp (toExt ρ x) (zero_add n)) (zero_add n) =
        toExt ρ x
      rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.inv_hom_id, mk₀_id_comp])

@[simp]
lemma toExt_precompLinearEquiv {P P' : C} (e : P ≅ P') (n : ℕ) (x : ExtWithAction ρ P' n) :
    toExt ρ (precompLinearEquiv ρ e n x) = (mk₀ e.hom).comp (toExt ρ x) (zero_add n) :=
  (rfl)

@[simp]
lemma toExt_precompLinearEquiv_symm {P P' : C} (e : P ≅ P') (n : ℕ) (x : ExtWithAction ρ P n) :
    toExt ρ ((precompLinearEquiv ρ e n).symm x) =
      (mk₀ e.inv).comp (toExt ρ x) (zero_add n) :=
  (rfl)

/-- Exactness of the rows of the long exact sequence of `Ext`-groups, in the form needed for the
five lemma. -/
lemma exact_precompLinearMap_mk₀_g_f {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompLinearMap ρ (mk₀ S.g) (zero_add n))
      (precompLinearMap ρ (mk₀ S.f) (zero_add n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (contravariant_sequence_exact₂' hS F n)

lemma exact_precompLinearMap_mk₀_f_extClass {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompLinearMap ρ (mk₀ S.f) (zero_add n))
      (precompLinearMap ρ hS.extClass (add_comm 1 n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (contravariant_sequence_exact₁' hS F n (n + 1) (add_comm 1 n))

lemma exact_precompLinearMap_extClass_mk₀_g {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompLinearMap ρ hS.extClass (add_comm 1 n))
      (precompLinearMap ρ (mk₀ S.g) (zero_add (n + 1))) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (contravariant_sequence_exact₃' hS F n (n + 1) (add_comm 1 n))

end ExtWithAction

end Action

namespace ExtWithAction

section BaseChange

variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B] {F G : C}
  (ρ : A →+* End F) (σ : B →+* End G) (η : F ⟶ G)
  (hη : ∀ a, (ρ a).asHom ≫ η = η ≫ (σ (algebraMap A B a)).asHom)

/-- Base change of target actions on `Ext`: the linear extension of postcomposition with `η`.
On pure tensors it sends `b ⊗ x` to `b • η_* x`. -/
noncomputable def baseChange (P : C) (n : ℕ) :
    B ⊗[A] ExtWithAction ρ P n →ₗ[B] ExtWithAction σ P n := by
  letI : Module A (ExtWithAction σ P n) := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B (ExtWithAction σ P n) := .of_algebraMap_smul fun _ _ ↦ rfl
  exact LinearMap.liftBaseChange B
    { toFun := fun x ↦ (toExt σ).symm ((toExt ρ x).comp (mk₀ η) (add_zero n))
      map_add' := fun x y ↦ add_comp _ _ _ (add_zero n)
      map_smul' := fun a x ↦ by
        -- Both transported scalar actions are postcomposition by the target endomorphism.
        change ((toExt ρ x).comp (mk₀ (ρ a).asHom) (add_zero n)).comp (mk₀ η) (add_zero n) =
          ((toExt ρ x).comp (mk₀ η) (add_zero n)).comp
            (mk₀ (σ (algebraMap A B a)).asHom) (add_zero n)
        rw [comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero,
          mk₀_comp_mk₀, mk₀_comp_mk₀, hη] }

@[simp]
lemma baseChange_tmul (P : C) (n : ℕ) (b : B) (x : ExtWithAction ρ P n) :
    toExt σ (baseChange ρ σ η hη P n (b ⊗ₜ x)) =
      (toExt ρ x).comp (mk₀ (η ≫ (σ b).asHom)) (add_zero n) := by
  -- The tensor lift applies the target action after postcomposition with `η`.
  change ((toExt ρ x).comp (mk₀ η) (add_zero n)).comp (mk₀ (σ b).asHom) (add_zero n) = _
  rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]

/-- The base change maps commute with precomposition. -/
lemma baseChange_comp_lTensor_precompLinearMap {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ}
    (h : m + n = n') :
    (baseChange ρ σ η hη P n').toAddMonoidHom.comp
        ((precompLinearMap ρ α h).lTensor B).toAddMonoidHom =
      (precompLinearMap σ α h).toAddMonoidHom.comp (baseChange ρ σ η hη P' n).toAddMonoidHom := by
  ext z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul b x =>
    apply (toExt σ).injective
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.lTensor_tmul, toExt_precompLinearMap, baseChange_tmul]
    exact comp_assoc_of_third_deg_zero _ _ _ _

lemma baseChange_lTensor_precompLinearMap_apply {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ}
    (h : m + n = n') (z : B ⊗[A] ExtWithAction ρ P' n) :
    baseChange ρ σ η hη P n' ((precompLinearMap ρ α h).lTensor B z) =
      precompLinearMap σ α h (baseChange ρ σ η hη P' n z) :=
  DFunLike.congr_fun (baseChange_comp_lTensor_precompLinearMap ρ σ η hη α h) z

/-- The base change maps are bijective for an object isomorphic to one for which they are. -/
lemma bijective_baseChange_of_iso {P P' : C} (e : P ≅ P') {n : ℕ}
    (h : Function.Bijective (baseChange ρ σ η hη P n)) :
    Function.Bijective (baseChange ρ σ η hη P' n) := by
  have key : ⇑(precompLinearEquiv σ e n) ∘ ⇑(baseChange ρ σ η hη P' n) =
      ⇑(baseChange ρ σ η hη P n) ∘ ⇑((precompLinearEquiv ρ e n).lTensor B) :=
    funext fun z ↦
      (baseChange_lTensor_precompLinearMap_apply ρ σ η hη (mk₀ e.hom) (zero_add n) z).symm
  refine (Function.Bijective.of_comp_iff' (precompLinearEquiv σ e n).bijective _).mp ?_
  rw [key]
  exact h.comp (LinearEquiv.bijective _)

/-- The base change maps are bijective for a binary biproduct of objects for which they are. -/
lemma bijective_baseChange_biprod {P₁ P₂ : C} {n : ℕ}
    (h₁ : Function.Bijective (baseChange ρ σ η hη P₁ n))
    (h₂ : Function.Bijective (baseChange ρ σ η hη P₂ n)) :
    Function.Bijective (baseChange ρ σ η hη (P₁ ⊞ P₂) n) := by
  let πF : ExtWithAction ρ (P₁ ⊞ P₂) n →ₗ[A] ExtWithAction ρ P₁ n × ExtWithAction ρ P₂ n :=
    (precompLinearMap ρ (mk₀ biprod.inl) (zero_add n)).prod
      (precompLinearMap ρ (mk₀ biprod.inr) (zero_add n))
  have hπF : Function.Bijective πF := (biprodAddEquiv (Y := F) (n := n)).bijective
  let πG : ExtWithAction σ (P₁ ⊞ P₂) n → ExtWithAction σ P₁ n × ExtWithAction σ P₂ n :=
    fun x ↦ (precompLinearMap σ (mk₀ biprod.inl) (zero_add n) x,
      precompLinearMap σ (mk₀ biprod.inr) (zero_add n) x)
  have hπG : Function.Bijective πG := (biprodAddEquiv (Y := G) (n := n)).bijective
  have key : πG ∘ ⇑(baseChange ρ σ η hη (P₁ ⊞ P₂) n) =
      Prod.map (baseChange ρ σ η hη P₁ n) (baseChange ρ σ η hη P₂ n) ∘
        ⇑(TensorProduct.prodRight A A B _ _) ∘ ⇑(πF.lTensor B) := by
    have hprod (z : B ⊗[A] ExtWithAction ρ (P₁ ⊞ P₂) n) :
        TensorProduct.prodRight A A B _ _ (πF.lTensor B z) =
          ((precompLinearMap ρ (mk₀ biprod.inl) (zero_add n)).lTensor B z,
            (precompLinearMap ρ (mk₀ biprod.inr) (zero_add n)).lTensor B z) := by
      induction z using TensorProduct.inductionOn with
      | tmul b x => rfl
      | add z z' hz hz' =>
        simp only [map_add, hz, hz']
        rfl
    funext z
    -- The canonical product splitting identifies both components with precomposition.
    change _ = Prod.map (baseChange ρ σ η hη P₁ n) (baseChange ρ σ η hη P₂ n)
      (TensorProduct.prodRight A A B _ _ (πF.lTensor B z))
    rw [hprod]
    exact Prod.ext
      (baseChange_lTensor_precompLinearMap_apply ρ σ η hη (mk₀ biprod.inl) (zero_add n) z).symm
      (baseChange_lTensor_precompLinearMap_apply ρ σ η hη (mk₀ biprod.inr) (zero_add n) z).symm
  refine (Function.Bijective.of_comp_iff' hπG _).mp ?_
  rw [key]
  exact (h₁.prodMap h₂).comp ((LinearEquiv.bijective _).comp
    (LinearEquiv.lTensor B (LinearEquiv.ofBijective πF hπF)).bijective)


end BaseChange

section FlatBaseChange

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {F G : C}
  (ρ : A →+* End F) (σ : B →+* End G) (η : F ⟶ G)
  (hη : ∀ a, (ρ a).asHom ≫ η = η ≫ (σ (algebraMap A B a)).asHom)
  [Module.Flat A B]

/-- **Two out of three for base change.** Let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be short exact. If the
base change maps of `P₁` and `P₂` are bijective in all degrees, then so are those of `P₃`: this is
the five lemma for the long exact sequences of `Ext`-groups, the first one tensored with the flat
`A`-module `B`. -/
lemma bijective_baseChange_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ n, Function.Bijective (baseChange ρ σ η hη S.X₁ n))
    (h₂ : ∀ n, Function.Bijective (baseChange ρ σ η hη S.X₂ n)) (n : ℕ) :
    Function.Bijective (baseChange ρ σ η hη S.X₃ n) := by
  have := hS.epi_g
  have hc {P P' : C} {m : ℕ} (α : Ext P P' m) {k k' : ℕ} (h : m + k = k') :=
    (baseChange_comp_lTensor_precompLinearMap ρ σ η hη α h).symm
  cases n with
  | zero =>
    exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      (f₁ := ((precompLinearMap ρ (mk₀ S.g) (zero_add 0)).lTensor B).toAddMonoidHom)
      (f₂ := ((precompLinearMap ρ (mk₀ S.f) (zero_add 0)).lTensor B).toAddMonoidHom)
      (g₁ := (precompLinearMap σ (mk₀ S.g) (zero_add 0)).toAddMonoidHom)
      (g₂ := (precompLinearMap σ (mk₀ S.f) (zero_add 0)).toAddMonoidHom)
      (i₁ := (baseChange ρ σ η hη S.X₃ 0).toAddMonoidHom)
      (i₂ := (baseChange ρ σ η hη S.X₂ 0).toAddMonoidHom)
      (i₃ := (baseChange ρ σ η hη S.X₁ 0).toAddMonoidHom)
      (hc₁ := hc _ _) (hc₂ := hc _ _)
      (hf₁ := Module.Flat.lTensor_exact B (exact_precompLinearMap_mk₀_g_f ρ hS 0))
      (hg₁ := exact_precompLinearMap_mk₀_g_f σ hS 0) (hi₂ := h₂ 0) (hi₃ := (h₁ 0).1)
      (hf₀ := Module.Flat.lTensor_preserves_injective_linearMap _
        (precomp_mk₀_injective_of_epi F S.g))
      (hg₀ := precomp_mk₀_injective_of_epi G S.g)
  | succ n =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (f₁ := ((precompLinearMap ρ (mk₀ S.f) (zero_add n)).lTensor B).toAddMonoidHom)
      (f₂ := ((precompLinearMap ρ hS.extClass (add_comm 1 n)).lTensor B).toAddMonoidHom)
      (f₃ := ((precompLinearMap ρ (mk₀ S.g) (zero_add (n + 1))).lTensor B).toAddMonoidHom)
      (f₄ := ((precompLinearMap ρ (mk₀ S.f) (zero_add (n + 1))).lTensor B).toAddMonoidHom)
      (g₁ := (precompLinearMap σ (mk₀ S.f) (zero_add n)).toAddMonoidHom)
      (g₂ := (precompLinearMap σ hS.extClass (add_comm 1 n)).toAddMonoidHom)
      (g₃ := (precompLinearMap σ (mk₀ S.g) (zero_add (n + 1))).toAddMonoidHom)
      (g₄ := (precompLinearMap σ (mk₀ S.f) (zero_add (n + 1))).toAddMonoidHom)
      (i₁ := (baseChange ρ σ η hη S.X₂ n).toAddMonoidHom)
      (i₂ := (baseChange ρ σ η hη S.X₁ n).toAddMonoidHom)
      (i₃ := (baseChange ρ σ η hη S.X₃ (n + 1)).toAddMonoidHom)
      (i₄ := (baseChange ρ σ η hη S.X₂ (n + 1)).toAddMonoidHom)
      (i₅ := (baseChange ρ σ η hη S.X₁ (n + 1)).toAddMonoidHom)
      (hc₁ := hc _ _) (hc₂ := hc _ _) (hc₃ := hc _ _) (hc₄ := hc _ _)
      (hf₁ := Module.Flat.lTensor_exact B (exact_precompLinearMap_mk₀_f_extClass ρ hS n))
      (hf₂ := Module.Flat.lTensor_exact B (exact_precompLinearMap_extClass_mk₀_g ρ hS n))
      (hf₃ := Module.Flat.lTensor_exact B (exact_precompLinearMap_mk₀_g_f ρ hS (n + 1)))
      (hg₁ := exact_precompLinearMap_mk₀_f_extClass σ hS n)
      (hg₂ := exact_precompLinearMap_extClass_mk₀_g σ hS n)
      (hg₃ := exact_precompLinearMap_mk₀_g_f σ hS (n + 1))
      (hi₁ := (h₂ n).2) (hi₂ := h₁ n) (hi₄ := h₂ (n + 1)) (hi₅ := (h₁ (n + 1)).1)

end FlatBaseChange

end ExtWithAction

end TauCeti.Abelian
