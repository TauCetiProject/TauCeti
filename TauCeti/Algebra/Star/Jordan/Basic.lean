/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Symmetrized
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Jordan star maps

Jordan star maps are complex linear maps preserving adjoints and self-adjoint squares.
`JordanStarEquiv` bundles the bijective maps. These maps unify star homomorphisms and
star anti-homomorphisms for projection and order reconstruction on star algebras.
For a complex star module (`StarModule ℂ A`), polarization identifies the square law
with multiplication in Mathlib's `SymAlg`. Unitality is separate and follows from
surjectivity even without `StarModule ℂ A`. Open `scoped TauCeti.ComplexAlgebra` to
obtain the scalar-induced inverse of two for `SymAlg` multiplication.
-/

public section

namespace TauCeti

variable (A B : Type*) [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  [Star A] [Star B] [Module ℂ A] [Module ℂ B]

/-- A complex linear, adjoint-preserving map preserving squares of self-adjoint elements. -/
structure JordanStarMap extends A →ₗ[ℂ] B where
  map_star' (x : A) : toLinearMap (star x) = star (toLinearMap x)
  map_mul_self_of_isSelfAdjoint' (x : A) :
    IsSelfAdjoint x → toLinearMap (x * x) = toLinearMap x * toLinearMap x

variable {A B}

namespace JordanStarMap

instance : FunLike (JordanStarMap A B) A B where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance : LinearMapClass (JordanStarMap A B) ℂ A B where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : StarHomClass (JordanStarMap A B) A B where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : JordanStarMap A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem toLinearMap_apply (f : JordanStarMap A B) (x : A) : f.toLinearMap x = f x := (rfl)

@[simp] theorem coe_mk (f : A →ₗ[ℂ] B) (hstar hmul) :
    ⇑(mk f hstar hmul : JordanStarMap A B) = f := (rfl)

@[simp] theorem coe_toLinearMap (f : JordanStarMap A B) : ⇑f.toLinearMap = f := (rfl)

@[simp] theorem toLinearMap_mk (f : A →ₗ[ℂ] B) (hstar hmul) :
    (mk f hstar hmul : JordanStarMap A B).toLinearMap = f := (rfl)

/-- A Jordan star map preserves squares on the self-adjoint part. -/
theorem map_mul_self_of_isSelfAdjoint (f : JordanStarMap A B) {x : A} (hx : IsSelfAdjoint x) :
    f (x * x) = f x * f x := f.map_mul_self_of_isSelfAdjoint' x hx

section Polarization

variable {A B : Type*} [NonUnitalNonAssocRing A] [StarAddMonoid A] [Module ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalNonAssocRing B] [Star B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]

/-- A Jordan star map on a complex star module preserves anticommutators. -/
theorem map_mul_add_mul (f : JordanStarMap A B) (x y : A) :
    f (x * y + y * x) = f x * f y + f y * f x :=
  f.toLinearMap.map_mul_add_mul_of_map_mul_self_of_isSelfAdjoint
    f.map_mul_self_of_isSelfAdjoint' x y

/-- A Jordan star map on a complex star module preserves squares of every element. -/
@[simp]
theorem map_mul_self (f : JordanStarMap A B) (x : A) : f (x * x) = f x * f x := by
  have h := f.map_mul_add_mul x x
  simp only [← two_smul ℂ, map_smul] at h
  exact (smul_right_injective B (two_ne_zero : (2 : ℂ) ≠ 0)) h

end Polarization

/-- A Jordan star map on a complex star module preserves multiplication in `SymAlg`. -/
theorem sym_map_unsym_sym_mul_sym
    {A B : Type*} [Ring A] [StarAddMonoid A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [Star B] [Algebra ℂ B] [Invertible (2 : A)] [Invertible (2 : B)]
    (f : JordanStarMap A B) (x y : A) :
    SymAlg.sym (f (SymAlg.unsym (SymAlg.sym x * SymAlg.sym y))) =
      SymAlg.sym (f x) * SymAlg.sym (f y) :=
  f.toLinearMap.map_mul_self_of_isSelfAdjoint_iff_sym_map_unsym_sym_mul_sym.mp
    f.map_mul_self_of_isSelfAdjoint' x y

/-- The identity Jordan star map. -/
def id : JordanStarMap A A where
  toLinearMap := LinearMap.id
  map_star' _ := rfl
  map_mul_self_of_isSelfAdjoint' _ _ := rfl

@[simp] theorem id_apply (x : A) : id x = x := (rfl)

@[simp] theorem coe_id : ⇑(id : JordanStarMap A A) = _root_.id := (rfl)

/-- Composition of Jordan star maps. -/
def comp {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (g : JordanStarMap B C) (f : JordanStarMap A B) : JordanStarMap A C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_star' x := by simp only [LinearMap.comp_apply, toLinearMap_apply, map_star]
  map_mul_self_of_isSelfAdjoint' x hx := by
    simp only [LinearMap.comp_apply, toLinearMap_apply, f.map_mul_self_of_isSelfAdjoint hx]
    exact g.map_mul_self_of_isSelfAdjoint (hx.map f)

@[simp] theorem comp_apply {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (g : JordanStarMap B C) (f : JordanStarMap A B) (x : A) : g.comp f x = g (f x) := (rfl)

@[simp] theorem coe_comp {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (g : JordanStarMap B C) (f : JordanStarMap A B) : ⇑(g.comp f) = ⇑g ∘ ⇑f := (rfl)

/-- The zero Jordan star map. -/
instance {A B : Type*} [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [StarAddMonoid B] [Module ℂ B] :
    Zero (JordanStarMap A B) where
  zero := {
    toLinearMap := 0
    map_star' _ := by simp
    map_mul_self_of_isSelfAdjoint' _ _ := by simp }

@[simp] theorem zero_apply {A B : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [StarAddMonoid B] [Module ℂ B] (x : A) :
    (0 : JordanStarMap A B) x = 0 := (rfl)

@[simp] theorem coe_zero {A B : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [StarAddMonoid B] [Module ℂ B] :
    ⇑(0 : JordanStarMap A B) = 0 := (rfl)

@[simp] theorem toLinearMap_id : (id : JordanStarMap A A).toLinearMap = LinearMap.id := (rfl)

variable {C D : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
  [NonUnitalNonAssocSemiring D] [Star D] [Module ℂ D]

@[simp] theorem toLinearMap_comp (g : JordanStarMap B C) (f : JordanStarMap A B) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := (rfl)

@[simp] theorem id_comp (f : JordanStarMap A B) : id.comp f = f := by ext; rfl

@[simp] theorem comp_id (f : JordanStarMap A B) : f.comp id = f := by ext; rfl

@[simp] theorem comp_assoc (h : JordanStarMap C D) (g : JordanStarMap B C)
    (f : JordanStarMap A B) : (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

@[simp] theorem toLinearMap_zero {A B : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [StarAddMonoid B] [Module ℂ B] :
    (0 : JordanStarMap A B).toLinearMap = 0 := (rfl)

@[simp] theorem zero_comp {A B C : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [Star B] [Module ℂ B]
    [NonUnitalNonAssocSemiring C] [StarAddMonoid C] [Module ℂ C]
    (f : JordanStarMap A B) :
    (0 : JordanStarMap B C).comp f = 0 := by ext; simp

@[simp] theorem comp_zero {A B C : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A]
    [NonUnitalNonAssocSemiring B] [StarAddMonoid B] [Module ℂ B]
    [NonUnitalNonAssocSemiring C] [StarAddMonoid C] [Module ℂ C]
    (g : JordanStarMap B C) :
    g.comp (0 : JordanStarMap A B) = 0 := by ext; simp

/-- A Jordan star map between unital star algebras whose range contains the unit preserves
the unit, without requiring a complex star-module structure. -/
theorem map_one_of_mem_range
    {A B : Type*} [NonAssocSemiring A] [StarRing A] [Module ℂ A]
    [NonAssocSemiring B] [StarMul B] [Module ℂ B]
    (f : JordanStarMap A B) (h1 : 1 ∈ Set.range f) : f 1 = 1 := by
  obtain ⟨x, hx⟩ := h1
  -- Addition in a complex module is cancellative.
  have : IsCancelAdd B := by
    let := Module.addCommMonoidToAddCommGroup ℂ (M := B)
    infer_instance
  have hy : f (x + star x) = (2 : ℂ) • (1 : B) := by
    simp [map_star, hx, two_smul]
  have h := f.toLinearMap.toAddMonoidHom.map_mul_add_mul_of_isSelfAdjoint
    f.map_mul_self_of_isSelfAdjoint' (IsSelfAdjoint.add_star_self x) (.one A)
  simp only [mul_one, one_mul, LinearMap.toAddMonoidHom_coe, toLinearMap_apply] at h
  rw [map_add, hy] at h
  have h' : (2 : ℂ) • (2 : ℂ) • (1 : B) = (2 : ℂ) • (2 : ℂ) • f 1 := by
    simpa [two_smul, add_mul, mul_add] using h
  -- Scaling by the inverse of four cancels the factor on both sides.
  have h'' := congrArg (fun z : B => ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • z) h'
  simp only [smul_smul] at h''
  norm_num at h''
  exact h''.symm

/-- A surjective Jordan star map between unital star algebras preserves the unit,
without requiring a complex star-module structure. -/
theorem map_one_of_surjective
    {A B : Type*} [NonAssocSemiring A] [StarRing A] [Module ℂ A]
    [NonAssocSemiring B] [StarMul B] [Module ℂ B]
    (f : JordanStarMap A B) (hf : Function.Surjective f) : f 1 = 1 :=
  f.map_one_of_mem_range (hf 1)

end JordanStarMap

variable (A B) in
/-- A bijective Jordan star map, carried by a native complex linear equivalence. -/
structure JordanStarEquiv extends A ≃ₗ[ℂ] B where
  map_star' (x : A) : toLinearEquiv (star x) = star (toLinearEquiv x)
  map_mul_self_of_isSelfAdjoint' (x : A) : IsSelfAdjoint x → toLinearEquiv (x * x) =
    toLinearEquiv x * toLinearEquiv x

namespace JordanStarEquiv

/-- Forget bijectivity of a Jordan star equivalence. -/
def toJordanStarMap (e : JordanStarEquiv A B) : JordanStarMap A B where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_star' := e.map_star'
  map_mul_self_of_isSelfAdjoint' := e.map_mul_self_of_isSelfAdjoint'

instance : EquivLike (JordanStarEquiv A B) A B where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' e f h _ := by cases e; cases f; congr; exact DFunLike.coe_injective h

instance : LinearEquivClass (JordanStarEquiv A B) ℂ A B where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

instance : StarHomClass (JordanStarEquiv A B) A B where
  map_star e := e.map_star'

@[ext]
theorem ext {e f : JordanStarEquiv A B} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.ext _ _ h

@[simp]
theorem toJordanStarMap_apply (e : JordanStarEquiv A B) (x : A) :
    e.toJordanStarMap x = e x := (rfl)

@[simp] theorem coe_mk (e : A ≃ₗ[ℂ] B) (hstar hmul) :
    ⇑(mk e hstar hmul : JordanStarEquiv A B) = e := (rfl)

@[simp] theorem coe_toLinearEquiv (e : JordanStarEquiv A B) : ⇑e.toLinearEquiv = e := (rfl)

@[simp] theorem toLinearEquiv_mk (e : A ≃ₗ[ℂ] B) (hstar hmul) :
    (mk e hstar hmul : JordanStarEquiv A B).toLinearEquiv = e := (rfl)

@[simp] theorem coe_toJordanStarMap (e : JordanStarEquiv A B) : ⇑e.toJordanStarMap = e := (rfl)

@[simp] theorem toLinearMap_toJordanStarMap (e : JordanStarEquiv A B) :
    e.toJordanStarMap.toLinearMap = e.toLinearEquiv.toLinearMap := (rfl)

/-- A bijective Jordan star map, as a Jordan star equivalence. -/
noncomputable def ofBijective (f : JordanStarMap A B) (hf : Function.Bijective f) :
    JordanStarEquiv A B where
  toLinearEquiv := LinearEquiv.ofBijective f.toLinearMap hf
  map_star' := f.map_star'
  map_mul_self_of_isSelfAdjoint' := f.map_mul_self_of_isSelfAdjoint'

@[simp] theorem coe_ofBijective (f : JordanStarMap A B) (hf : Function.Bijective f) :
    ⇑(ofBijective f hf) = f := (rfl)

@[simp] theorem ofBijective_apply (f : JordanStarMap A B) (hf : Function.Bijective f) (x : A) :
    ofBijective f hf x = f x := (rfl)

@[simp] theorem toJordanStarMap_ofBijective (f : JordanStarMap A B)
    (hf : Function.Bijective f) : (ofBijective f hf).toJordanStarMap = f := by
  ext; rfl

/-- A Jordan star equivalence preserves squares on the self-adjoint part. -/
theorem map_mul_self_of_isSelfAdjoint (e : JordanStarEquiv A B) {x : A}
    (hx : IsSelfAdjoint x) : e (x * x) = e x * e x :=
  e.toJordanStarMap.map_mul_self_of_isSelfAdjoint hx

section Polarization

variable {A B : Type*} [NonUnitalNonAssocRing A] [StarAddMonoid A] [Module ℂ A]
  [StarModule ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalNonAssocRing B] [Star B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]

/-- A Jordan star equivalence on a complex star module preserves anticommutators. -/
theorem map_mul_add_mul (e : JordanStarEquiv A B) (x y : A) :
    e (x * y + y * x) = e x * e y + e y * e x :=
  e.toJordanStarMap.map_mul_add_mul x y

/-- A Jordan star equivalence on a complex star module preserves every square. -/
@[simp] theorem map_mul_self (e : JordanStarEquiv A B) (x : A) :
    e (x * x) = e x * e x := e.toJordanStarMap.map_mul_self x

end Polarization

/-- A Jordan star equivalence on a complex star module preserves `SymAlg` multiplication. -/
theorem sym_map_unsym_sym_mul_sym
    {A B : Type*} [Ring A] [StarAddMonoid A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [Star B] [Algebra ℂ B] [Invertible (2 : A)] [Invertible (2 : B)]
    (e : JordanStarEquiv A B) (x y : A) :
    SymAlg.sym (e (SymAlg.unsym (SymAlg.sym x * SymAlg.sym y))) =
      SymAlg.sym (e x) * SymAlg.sym (e y) := e.toJordanStarMap.sym_map_unsym_sym_mul_sym x y

/-- The inverse of a Jordan star equivalence. -/
@[symm]
def symm (e : JordanStarEquiv A B) : JordanStarEquiv B A where
  toLinearEquiv := e.toLinearEquiv.symm
  map_star' x := by
    apply EquivLike.injective e
    have hinv (y : B) : e (e.toLinearEquiv.symm y) = y :=
      e.toLinearEquiv.apply_symm_apply y
    simp only [map_star, hinv]
  map_mul_self_of_isSelfAdjoint' x hx := by
    have hsa := IsSelfAdjoint.of_map e (EquivLike.injective e)
      ((e.toLinearEquiv.apply_symm_apply x).symm ▸ hx)
    apply EquivLike.injective e
    have hinv (y : B) : e (e.toLinearEquiv.symm y) = y :=
      e.toLinearEquiv.apply_symm_apply y
    rw [map_mul_self_of_isSelfAdjoint e hsa, hinv, hinv]

/-- The identity Jordan star equivalence. -/
@[refl]
def refl : JordanStarEquiv A A where
  toLinearEquiv := LinearEquiv.refl ℂ A
  map_star' _ := rfl
  map_mul_self_of_isSelfAdjoint' _ _ := rfl

/-- Compose Jordan star equivalences in application order. -/
@[trans]
def trans {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) : JordanStarEquiv A C where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_star' x := by simp [e.map_star', f.map_star']
  map_mul_self_of_isSelfAdjoint' x hx :=
    (f.toJordanStarMap.comp e.toJordanStarMap).map_mul_self_of_isSelfAdjoint hx

@[simp] theorem refl_apply (x : A) : refl x = x := (rfl)

@[simp] theorem coe_refl : ⇑(refl : JordanStarEquiv A A) = _root_.id := (rfl)

@[simp] theorem trans_apply {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) (x : A) :
    e.trans f x = f (e x) := (rfl)

@[simp] theorem coe_trans {C : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
    (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) : ⇑(e.trans f) = ⇑f ∘ ⇑e := (rfl)

@[simp] theorem symm_apply_apply (e : JordanStarEquiv A B) (x : A) :
    e.symm (e x) = x :=
  (e.toLinearEquiv.symm_apply_apply x)

@[simp] theorem apply_symm_apply (e : JordanStarEquiv A B) (x : B) :
    e (e.symm x) = x :=
  (e.toLinearEquiv.apply_symm_apply x)

@[simp] theorem symm_symm (e : JordanStarEquiv A B) : e.symm.symm = e := by ext; rfl

@[simp] theorem coe_symm_toLinearEquiv (e : JordanStarEquiv A B) :
    ⇑e.toLinearEquiv.symm = e.symm := (rfl)

@[simp] theorem toLinearEquiv_refl :
    (refl : JordanStarEquiv A A).toLinearEquiv = LinearEquiv.refl ℂ A := (rfl)

@[simp] theorem toLinearEquiv_symm (e : JordanStarEquiv A B) :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm := (rfl)

theorem symm_apply_eq (e : JordanStarEquiv A B) {x : B} {y : A} :
    e.symm x = y ↔ x = e y := e.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : JordanStarEquiv A B) {x : B} {y : A} :
    y = e.symm x ↔ e y = x := e.toLinearEquiv.eq_symm_apply

@[simp] theorem symm_refl : (refl : JordanStarEquiv A A).symm = refl := by ext; rfl

@[simp] theorem toJordanStarMap_refl :
    (refl : JordanStarEquiv A A).toJordanStarMap = JordanStarMap.id := by ext; rfl

variable {C D : Type*} [NonUnitalNonAssocSemiring C] [Star C] [Module ℂ C]
  [NonUnitalNonAssocSemiring D] [Star D] [Module ℂ D]

@[simp] theorem toLinearEquiv_trans (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) :
    (e.trans f).toLinearEquiv = e.toLinearEquiv.trans f.toLinearEquiv := (rfl)

@[simp] theorem toJordanStarMap_trans (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) :
    (e.trans f).toJordanStarMap = f.toJordanStarMap.comp e.toJordanStarMap := by ext; rfl

@[simp] theorem toJordanStarMap_comp_symm (e : JordanStarEquiv A B) :
    e.toJordanStarMap.comp e.symm.toJordanStarMap = JordanStarMap.id := by ext; simp

@[simp] theorem symm_toJordanStarMap_comp (e : JordanStarEquiv A B) :
    e.symm.toJordanStarMap.comp e.toJordanStarMap = JordanStarMap.id := by ext; simp

@[simp] theorem symm_trans (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) :
    (e.trans f).symm = f.symm.trans e.symm := by ext; rfl

@[simp] theorem self_trans_symm (e : JordanStarEquiv A B) : e.trans e.symm = refl := by
  ext; simp

@[simp] theorem symm_trans_self (e : JordanStarEquiv A B) : e.symm.trans e = refl := by
  ext; simp

@[simp] theorem refl_trans (e : JordanStarEquiv A B) : refl.trans e = e := by ext; rfl

@[simp] theorem trans_refl (e : JordanStarEquiv A B) : e.trans refl = e := by ext; rfl

@[simp] theorem trans_assoc (e : JordanStarEquiv A B) (f : JordanStarEquiv B C)
    (g : JordanStarEquiv C D) : (e.trans f).trans g = e.trans (f.trans g) := by ext; rfl

/-- A Jordan star equivalence between unital star algebras preserves the unit,
without requiring a complex star-module structure. -/
@[simp]
theorem map_one
    {A B : Type*} [NonAssocSemiring A] [StarRing A] [Module ℂ A]
    [NonAssocSemiring B] [StarMul B] [Module ℂ B] (e : JordanStarEquiv A B) : e 1 = 1 :=
  e.toJordanStarMap.map_one_of_surjective (EquivLike.surjective e)

end JordanStarEquiv
end TauCeti
