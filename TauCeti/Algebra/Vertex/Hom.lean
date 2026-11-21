/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import Mathlib.Algebra.Group.IsApply

/-!
# Morphisms of formal vertex algebras

A morphism of formal vertex algebras `f : A.Hom B`, from a formal vertex algebra `A` on `V` to a
formal vertex algebra `B` on `W`, is an `R`-linear map `f : V → W` which preserves the vacuum and
every mode:

`f |0⟩ = |0⟩` and `f (a₍ₙ₎ b) = (f a)₍ₙ₎ (f b)` for all states `a`, `b` and all `n : ℤ`.

Equivalently `f ∘ Y(a,z) = Y(f a, z) ∘ f` coefficientwise. Compatibility with the translation
operators is then automatic, since `T a = a₍₋₂₎|0⟩`
(`TauCeti.FormalVertexAxioms.Hom.map_translation`). An equivalence `A.Equiv B` is a linear
equivalence with the same two properties; the inverse of a bijective morphism is again a morphism
(`TauCeti.FormalVertexAxioms.Equiv.ofBijective`), and the self-equivalences of `A` form its
automorphism group.

## Main definitions

* `TauCeti.FormalVertexAxioms.Hom`: morphisms of formal vertex algebras, with `Hom.id` and
  `Hom.comp`.
* `TauCeti.FormalVertexAxioms.Equiv`: equivalences of formal vertex algebras, with `Equiv.refl`,
  `Equiv.symm`, `Equiv.trans` and `Equiv.ofBijective`; `Equiv.aut` is the group structure on
  `A.Equiv A`.

## Main results

* `TauCeti.FormalVertexAxioms.Hom.map_translation`: morphisms intertwine the translation
  operators.
* `TauCeti.FormalVertexAxioms.Hom.comp_ncoeff_field`: `f ∘ a₍ₙ₎ = (f a)₍ₙ₎ ∘ f`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.3.
-/

public section

noncomputable section

open scoped VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V W U X : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X]

/-! ### Morphisms -/

/-- A morphism of formal vertex algebras from `A` to `B`: an `R`-linear map preserving the vacuum
and all modes, `f (a₍ₙ₎ b) = (f a)₍ₙ₎ (f b)`. -/
structure Hom (A : FormalVertexAxioms R V) (B : FormalVertexAxioms R W) extends V →ₗ[R] W where
  /-- A morphism preserves the vacuum. -/
  map_vacuum' : toFun A.vacuum = B.vacuum
  /-- A morphism preserves every mode: `f (a₍ₙ₎ b) = (f a)₍ₙ₎ (f b)`. -/
  map_ncoeff_field_apply' : ∀ (a b : V) (n : ℤ),
    toFun (((A.field a)[[n]]) b) = ((B.field (toFun a))[[n]]) (toFun b)

namespace Hom

variable {A : FormalVertexAxioms R V} {B : FormalVertexAxioms R W}
  {C : FormalVertexAxioms R U} {D : FormalVertexAxioms R X}

/-- Two morphisms are equal if their underlying linear maps are equal. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : A.Hom B → V →ₗ[R] W) := by
  rintro ⟨f, -, -⟩ ⟨g, -, -⟩ rfl
  rfl

instance : FunLike (A.Hom B) V W where
  coe f := f.toLinearMap
  coe_injective _ _ h := toLinearMap_injective (LinearMap.ext fun v ↦ congrFun h v)

instance : LinearMapClass (A.Hom B) R V W where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : CoeOut (A.Hom B) (V →ₗ[R] W) :=
  ⟨toLinearMap⟩

@[simp]
theorem coe_toLinearMap (f : A.Hom B) : ⇑f.toLinearMap = f := (rfl)

@[simp]
theorem coe_mk (f : V →ₗ[R] W) (h₁ h₂) : ⇑(Hom.mk f h₁ h₂ : A.Hom B) = f := (rfl)

/-- Two morphisms are equal if they agree on every state. -/
@[ext]
theorem ext {f g : A.Hom B} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

/-- A morphism preserves the vacuum. -/
@[simp]
theorem map_vacuum (f : A.Hom B) : f A.vacuum = B.vacuum :=
  f.map_vacuum'

/-- A morphism preserves every mode: `f (a₍ₙ₎ b) = (f a)₍ₙ₎ (f b)`. -/
@[simp]
theorem map_ncoeff_field_apply (f : A.Hom B) (a b : V) (n : ℤ) :
    f (((A.field a)[[n]]) b) = ((B.field (f a))[[n]]) (f b) :=
  f.map_ncoeff_field_apply' a b n

/-- A morphism intertwines the modes: `f ∘ a₍ₙ₎ = (f a)₍ₙ₎ ∘ f`. -/
theorem comp_ncoeff_field (f : A.Hom B) (a : V) (n : ℤ) :
    (f : V →ₗ[R] W) ∘ₗ (A.field a)[[n]] = (B.field (f a))[[n]] ∘ₗ (f : V →ₗ[R] W) :=
  LinearMap.ext fun b ↦ f.map_ncoeff_field_apply a b n

/-- A morphism intertwines the translation operators: `f (T a) = T (f a)`. -/
@[simp]
theorem map_translation (f : A.Hom B) (a : V) : f (A.translation a) = B.translation (f a) := by
  rw [A.translation_apply, B.translation_apply, map_ncoeff_field_apply, map_vacuum]

/-- A morphism intertwines the translation operators, as linear maps. -/
theorem comp_translation (f : A.Hom B) :
    (f : V →ₗ[R] W) ∘ₗ A.translation = B.translation ∘ₗ (f : V →ₗ[R] W) :=
  LinearMap.ext f.map_translation

/-- The identity morphism of a formal vertex algebra. -/
protected def id (A : FormalVertexAxioms R V) : A.Hom A where
  toLinearMap := LinearMap.id
  map_vacuum' := rfl
  map_ncoeff_field_apply' _ _ _ := rfl

@[simp]
theorem coe_id (A : FormalVertexAxioms R V) : ⇑(Hom.id A) = _root_.id := (rfl)

theorem id_apply (A : FormalVertexAxioms R V) (v : V) : Hom.id A v = v := (rfl)

/-- The composition of two morphisms of formal vertex algebras. -/
def comp (g : B.Hom C) (f : A.Hom B) : A.Hom C where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_vacuum' := by
    simp only [LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply, coe_toLinearMap,
      map_vacuum]
  map_ncoeff_field_apply' a b n := by
    simp only [LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply, coe_toLinearMap,
      map_ncoeff_field_apply]

@[simp]
theorem coe_comp (g : B.Hom C) (f : A.Hom B) : ⇑(g.comp f) = g ∘ f := (rfl)

theorem comp_apply (g : B.Hom C) (f : A.Hom B) (v : V) : g.comp f v = g (f v) := (rfl)

@[simp]
theorem comp_id (f : A.Hom B) : f.comp (Hom.id A) = f := (rfl)

@[simp]
theorem id_comp (f : A.Hom B) : (Hom.id B).comp f = f := (rfl)

theorem comp_assoc (h : C.Hom D) (g : B.Hom C) (f : A.Hom B) :
    (h.comp g).comp f = h.comp (g.comp f) := (rfl)

end Hom

/-! ### Equivalences -/

/-- An equivalence of formal vertex algebras from `A` to `B`: an `R`-linear equivalence preserving
the vacuum and all modes. -/
structure Equiv (A : FormalVertexAxioms R V) (B : FormalVertexAxioms R W) extends V ≃ₗ[R] W where
  /-- An equivalence preserves the vacuum. -/
  map_vacuum' : toFun A.vacuum = B.vacuum
  /-- An equivalence preserves every mode: `e (a₍ₙ₎ b) = (e a)₍ₙ₎ (e b)`. -/
  map_ncoeff_field_apply' : ∀ (a b : V) (n : ℤ),
    toFun (((A.field a)[[n]]) b) = ((B.field (toFun a))[[n]]) (toFun b)

namespace Equiv

variable {A : FormalVertexAxioms R V} {B : FormalVertexAxioms R W}
  {C : FormalVertexAxioms R U}

/-- Two equivalences are equal if their underlying linear equivalences are equal. -/
theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : A.Equiv B → V ≃ₗ[R] W) := by
  rintro ⟨e, -, -⟩ ⟨e', -, -⟩ rfl
  rfl

instance : EquivLike (A.Equiv B) V W where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' _ _ h _ := toLinearEquiv_injective (LinearEquiv.ext fun v ↦ congrFun h v)

instance : LinearEquivClass (A.Equiv B) R V W where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

instance : CoeOut (A.Equiv B) (V ≃ₗ[R] W) :=
  ⟨toLinearEquiv⟩

@[simp]
theorem coe_toLinearEquiv (e : A.Equiv B) : ⇑e.toLinearEquiv = e := (rfl)

@[simp]
theorem coe_mk (e : V ≃ₗ[R] W) (h₁ h₂) : ⇑(Equiv.mk e h₁ h₂ : A.Equiv B) = e := (rfl)

/-- Two equivalences are equal if they agree on every state. -/
@[ext]
theorem ext {e e' : A.Equiv B} (h : ∀ v, e v = e' v) : e = e' :=
  DFunLike.ext e e' h

/-- An equivalence preserves the vacuum. -/
@[simp]
theorem map_vacuum (e : A.Equiv B) : e A.vacuum = B.vacuum :=
  e.map_vacuum'

/-- An equivalence preserves every mode. -/
@[simp]
theorem map_ncoeff_field_apply (e : A.Equiv B) (a b : V) (n : ℤ) :
    e (((A.field a)[[n]]) b) = ((B.field (e a))[[n]]) (e b) :=
  e.map_ncoeff_field_apply' a b n

/-- The morphism underlying an equivalence. -/
def toHom (e : A.Equiv B) : A.Hom B where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_vacuum' := e.map_vacuum'
  map_ncoeff_field_apply' := e.map_ncoeff_field_apply'

@[simp]
theorem coe_toHom (e : A.Equiv B) : ⇑e.toHom = e := (rfl)

/-- An equivalence intertwines the translation operators. -/
@[simp]
theorem map_translation (e : A.Equiv B) (a : V) : e (A.translation a) = B.translation (e a) :=
  e.toHom.map_translation a

/-- The identity equivalence of a formal vertex algebra. -/
@[refl]
def refl (A : FormalVertexAxioms R V) : A.Equiv A where
  toLinearEquiv := LinearEquiv.refl R V
  map_vacuum' := rfl
  map_ncoeff_field_apply' _ _ _ := rfl

@[simp]
theorem coe_refl (A : FormalVertexAxioms R V) : ⇑(Equiv.refl A) = _root_.id := (rfl)

theorem refl_apply (A : FormalVertexAxioms R V) (v : V) : Equiv.refl A v = v := (rfl)

/-- The inverse of an equivalence of formal vertex algebras. -/
@[symm]
def symm (e : A.Equiv B) : B.Equiv A where
  toLinearEquiv := e.toLinearEquiv.symm
  map_vacuum' := by
    simp [LinearEquiv.symm_apply_eq]
  map_ncoeff_field_apply' a b n := by
    have h := e.map_ncoeff_field_apply (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b) n
    simp only [← coe_toLinearEquiv, LinearEquiv.apply_symm_apply] at h
    rw [← h]
    exact e.toLinearEquiv.symm_apply_apply _

@[simp]
theorem apply_symm_apply (e : A.Equiv B) (w : W) : e (e.symm w) = w :=
  e.toLinearEquiv.apply_symm_apply w

@[simp]
theorem symm_apply_apply (e : A.Equiv B) (v : V) : e.symm (e v) = v :=
  e.toLinearEquiv.symm_apply_apply v

@[simp]
theorem symm_symm (e : A.Equiv B) : e.symm.symm = e := (rfl)

/-- The composition of two equivalences of formal vertex algebras. -/
@[trans]
def trans (e : A.Equiv B) (e' : B.Equiv C) : A.Equiv C where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  map_vacuum' := (e'.toHom.comp e.toHom).map_vacuum'
  map_ncoeff_field_apply' := (e'.toHom.comp e.toHom).map_ncoeff_field_apply'

@[simp]
theorem coe_trans (e : A.Equiv B) (e' : B.Equiv C) : ⇑(e.trans e') = e' ∘ e := (rfl)

theorem trans_apply (e : A.Equiv B) (e' : B.Equiv C) (v : V) : e.trans e' v = e' (e v) := (rfl)

@[simp]
theorem toHom_trans (e : A.Equiv B) (e' : B.Equiv C) :
    (e.trans e').toHom = e'.toHom.comp e.toHom := (rfl)

@[simp]
theorem self_trans_symm (e : A.Equiv B) : e.trans e.symm = Equiv.refl A :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : A.Equiv B) : e.symm.trans e = Equiv.refl B :=
  ext e.apply_symm_apply

/-- A bijective morphism of formal vertex algebras is an equivalence: its inverse automatically
preserves the vacuum and all modes. -/
def ofBijective (f : A.Hom B) (hf : Function.Bijective f) : A.Equiv B where
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf
  map_vacuum' := f.map_vacuum'
  map_ncoeff_field_apply' := f.map_ncoeff_field_apply'

@[simp]
theorem coe_ofBijective (f : A.Hom B) (hf : Function.Bijective f) : ⇑(ofBijective f hf) = f :=
  (rfl)

@[simp]
theorem toHom_ofBijective (f : A.Hom B) (hf : Function.Bijective f) :
    (ofBijective f hf).toHom = f := (rfl)

@[simp]
theorem trans_refl (e : A.Equiv B) : e.trans (Equiv.refl B) = e := (rfl)

@[simp]
theorem refl_trans (e : A.Equiv B) : (Equiv.refl A).trans e = e := (rfl)

theorem trans_assoc {D : FormalVertexAxioms R X} (e : A.Equiv B) (e' : B.Equiv C)
    (e'' : C.Equiv D) : (e.trans e').trans e'' = e.trans (e'.trans e'') := (rfl)

instance : One (A.Equiv A) := ⟨Equiv.refl A⟩

instance : Mul (A.Equiv A) := ⟨fun e e' ↦ e'.trans e⟩

instance : Inv (A.Equiv A) := ⟨symm⟩

/-- The automorphisms of a formal vertex algebra form a group under composition, the right factor
acting first. -/
instance aut : Group (A.Equiv A) where
  mul_assoc e e' e'' := (trans_assoc e'' e' e).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

theorem mul_def (e e' : A.Equiv A) : e * e' = e'.trans e := (rfl)

theorem one_def : (1 : A.Equiv A) = Equiv.refl A := (rfl)

theorem inv_def (e : A.Equiv A) : e⁻¹ = e.symm := (rfl)

instance : IsOneApplyEqSelf (A.Equiv A) :=
  ⟨refl_apply A⟩

instance : IsMulApplyEqComp (A.Equiv A) :=
  ⟨fun e e' v ↦ trans_apply e' e v⟩

@[simp]
theorem inv_apply (e : A.Equiv A) (v : V) : e⁻¹ v = e.symm v := (rfl)

end Equiv

end FormalVertexAxioms

end TauCeti
