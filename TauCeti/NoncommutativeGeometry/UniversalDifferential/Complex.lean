/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.Map
public import TauCeti.LinearAlgebra.TensorPower.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The differential complex of universal form words

The degree-`n` module `UniversalForms k A n` is `A⁺ ⊗[k] A^⊗n`, with the forced
unitization retained even when `A` already has a unit. Its word `x da₁ … daₙ` has
differential `1_ext d(x.snd) da₁ … daₙ`. This differential squares to zero and defines
a native `CochainComplex (ModuleCat k) ℕ`. Degree zero identifies with `A⁺`, and degree
one identifies with the multiplication-kernel universal one-forms; the degree-zero
differential agrees with their universal derivation. Nonunital algebra homomorphisms induce
chain maps compatible with these identifications.

This constructs the underlying differential complex. Multiplication of general forms and
its graded Leibniz law require the further tensor-algebra construction.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Proposition 3, p. 190,
  for the tensor-word description of positive-degree universal forms.
-/

public section

open scoped TensorProduct
open CategoryTheory

namespace TauCeti

universe u v w z

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]

/-- The module of degree-`n` universal form words, including forced-unitized degree zero. -/
abbrev UniversalForms (n : ℕ) := Unitization k A ⊗[k] TensorPower k n A

namespace UniversalForms

noncomputable section

/-- The tensor word `x da₁ … daₙ`, with coefficient in the forced unitization. -/
def word {n : ℕ} (x : Unitization k A) (a : Fin n → A) : UniversalForms k A n :=
  x ⊗ₜ[k] PiTensorProduct.tprod k a

/-- Tensor coordinates of a universal form word. -/
theorem word_def {n : ℕ} (x : Unitization k A) (a : Fin n → A) :
    word k A x a = x ⊗ₜ[k] PiTensorProduct.tprod k a := (rfl)

/-- Every form is a sum of tensor words. Scalar factors are absorbed in the coefficient. -/
@[elab_as_elim]
theorem induction_on {n : ℕ} {P : UniversalForms k A n → Prop} (ω : UniversalForms k A n)
    (hword : ∀ x a, P (word k A x a))
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) : P ω := by
  induction ω using TensorProduct.inductionOn with
  | tmul x t =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      rw [TensorProduct.tmul_smul]
      exact hword (r • x) a
    | add t s ht hs => simpa only [TensorProduct.tmul_add] using hadd _ _ ht hs
  | add ω η hω hη => exact hadd _ _ hω hη

/-- The differential prepends the nonscalar part of the coefficient to the tensor word. -/
def d (n : ℕ) : UniversalForms k A n →ₗ[k] UniversalForms k A (n + 1) :=
  TensorProduct.mk k (Unitization k A) (TensorPower k (n + 1) A) 1 ∘ₗ
    (TensorPower.cast k A (Nat.add_comm 1 n)).toLinearMap ∘ₗ
      (TensorPower.mulEquiv (R := k) (M := A) (n := 1) (m := n)).toLinearMap ∘ₗ
        TensorProduct.map
          ((TensorPower.oneEquiv k A).symm.toLinearMap ∘ₗ Unitization.sndHom k k A)
          LinearMap.id

/-- The characteristic differential equation on an arbitrary pure word. -/
@[simp]
theorem d_word {n : ℕ} (x : Unitization k A) (a : Fin n → A) :
    d k A n (word k A x a) = word k A 1 (Fin.cons x.snd a) := by
  simp only [d, word, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, Unitization.sndHom_apply, LinearEquiv.coe_coe,
    TensorPower.oneEquiv_symm_apply, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod, TensorPower.cast_tprod, TensorProduct.mk_apply]
  congr 2
  funext i
  simp [Fin.append_left_eq_cons]

/-- A word with zero coefficient vanishes. -/
@[simp]
theorem word_zero {n : ℕ} (a : Fin n → A) : word k A 0 a = 0 :=
  TensorProduct.zero_tmul _ _

/-- A word with a zero differential letter vanishes. -/
theorem word_eq_zero_of_eq_zero {n : ℕ} (x : Unitization k A) (a : Fin n → A)
    (i : Fin n) (hi : a i = 0) : word k A x a = 0 := by
  rw [word, MultilinearMap.map_coord_zero (PiTensorProduct.tprod k) i hi,
    TensorProduct.tmul_zero]

/-- A leading zero differential letter makes a word vanish. -/
@[simp]
theorem word_cons_zero {n : ℕ} (x : Unitization k A) (a : Fin n → A) :
    word k A x (Fin.cons 0 a) = 0 :=
  word_eq_zero_of_eq_zero k A x _ 0 (Fin.cons_zero _ _)

/-- The universal differential squares to zero in every degree. -/
@[simp]
theorem d_d (n : ℕ) (ω : UniversalForms k A n) : d k A (n + 1) (d k A n ω) = 0 := by
  induction ω using induction_on k A with
  | hword x a => simp
  | hadd ω η hω hη => simp only [map_add, hω, hη, add_zero]

/-- Degree zero is the forced unitization, via the empty tensor-power identification. -/
def zeroEquiv : UniversalForms k A 0 ≃ₗ[k] Unitization k A :=
  (TensorProduct.congr (LinearEquiv.refl k (Unitization k A))
    (TensorPower.algebraMap₀ (R := k) (M := A)).symm).trans
      (TensorProduct.rid k (Unitization k A))

/-- An empty word is its coefficient in degree zero. -/
@[simp]
theorem zeroEquiv_word (x : Unitization k A) (a : Fin 0 → A) :
    zeroEquiv k A (word k A x a) = x := by
  simp [zeroEquiv, word, TensorPower.algebraMap₀, PiTensorProduct.isEmptyEquiv_apply_tprod]

/-- The inverse degree-zero identification inserts the empty word. -/
@[simp]
theorem zeroEquiv_symm_apply (x : Unitization k A) :
    (zeroEquiv k A).symm x = word k A x Fin.elim0 := by
  apply (zeroEquiv k A).injective
  simp

section One

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- Degree one identifies with the multiplication-kernel model of universal one-forms. -/
def oneEquiv : UniversalForms k A 1 ≃ₗ[k] UniversalOneForms k A :=
  (TensorProduct.congr (LinearEquiv.refl k (Unitization k A))
    (TensorPower.oneEquiv k A)).trans (UniversalOneForms.tensorEquiv k A).symm

/-- A degree-one word represents the corresponding coefficient times a universal differential. -/
@[simp]
theorem oneEquiv_word (x : Unitization k A) (a : Fin 1 → A) :
    oneEquiv k A (word k A x a) = x • UniversalOneForms.d k A (a 0) := by
  simp [oneEquiv, word]

/-- The inverse degree-one identification reconstructs a word from the universal derivation. -/
@[simp]
theorem oneEquiv_symm_smul_derivation (x y : Unitization k A) :
    (oneEquiv k A).symm (x • UniversalOneForms.derivation k A y) =
      word k A x (fun _ ↦ y.snd) := by
  apply (oneEquiv k A).injective
  rw [LinearEquiv.apply_symm_apply, oneEquiv_word, UniversalOneForms.d_snd]

/-- The degree-zero differential agrees with the existing universal derivation of `A⁺`. -/
@[simp↓]
theorem oneEquiv_d (ω : UniversalForms k A 0) :
    oneEquiv k A (d k A 0 ω) =
      UniversalOneForms.derivation k A (zeroEquiv k A ω) := by
  induction ω using induction_on k A with
  | hword x a =>
    rw [d_word, oneEquiv_word, zeroEquiv_word, Fin.cons_zero, one_smul,
      UniversalOneForms.d_snd]
  | hadd ω η hω hη => simp only [map_add, hω, hη]

end One

/-- The differential complex of universal form words, with degree-zero term `A⁺`. -/
def complex : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of k (UniversalForms k A n))
    (fun n ↦ ModuleCat.ofHom (d k A n)) (fun n ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext (d_d k A n))

/-- The degree-`n` carrier of the complex is the tensor-word module. -/
def complexXIso (n : ℕ) : (complex k A).X n ≅ ModuleCat.of k (UniversalForms k A n) :=
  CategoryTheory.Iso.refl _

/-- The complex differential is the word differential, under the public carrier identifications. -/
theorem complex_d (n : ℕ) :
    (complexXIso k A n).inv ≫ (complex k A).d n (n + 1) ≫
      (complexXIso k A (n + 1)).hom = ModuleCat.ofHom (d k A n) := by
  simp [complexXIso, complex]

/-- Evaluation of the complex differential after identifying its source and target carriers. -/
theorem complex_d_apply (n : ℕ) (ω : UniversalForms k A n) :
    (complexXIso k A (n + 1)).hom
      ((complex k A).d n (n + 1) ((complexXIso k A n).inv ω)) = d k A n ω := by
  exact congrArg (fun f ↦ f ω) (complex_d k A n)

section Map

variable {A} {B : Type w} {C : Type z}
  [IsScalarTower k A A] [SMulCommClass k A A]
  [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  [NonUnitalRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]

/-- The degreewise map of form words induced by a nonunital algebra homomorphism. -/
def map (f : A →ₙₐ[k] B) (n : ℕ) : UniversalForms k A n →ₗ[k] UniversalForms k B n :=
  TensorProduct.map (Unitization.map f).toLinearMap
    (PiTensorProduct.map fun _ : Fin n ↦ (LinearMap.ofClass f : A →ₗ[k] B))

/-- Functoriality on words applies the homomorphism to every letter and its unitization
to the coefficient. -/
@[simp]
theorem map_word (f : A →ₙₐ[k] B) {n : ℕ} (x : Unitization k A) (a : Fin n → A) :
    map k f n (word k A x a) = word k B (Unitization.map f x) (fun i ↦ f (a i)) := by
  simp [map, word]

/-- Algebra homomorphisms commute with the universal word differential. -/
@[simp]
theorem map_d (f : A →ₙₐ[k] B) (n : ℕ) (ω : UniversalForms k A n) :
    map k f (n + 1) (d k A n ω) = d k B n (map k f n ω) := by
  induction ω using induction_on k A with
  | hword x a =>
    simp only [d_word, map_word, map_one, Unitization.snd_map]
    congr 2
    exact Fin.comp_cons f x.snd a
  | hadd ω η hω hη => simp only [map_add, hω, hη]

/-- The identity algebra homomorphism induces the identity in every degree. -/
@[simp]
theorem map_id (n : ℕ) : map k (NonUnitalAlgHom.id k A) n = LinearMap.id := by
  have hid : (LinearMap.ofClass (NonUnitalAlgHom.id k A) : A →ₗ[k] A) = LinearMap.id :=
    LinearMap.ext (fun _ ↦ rfl)
  simp [map, hid, PiTensorProduct.map_id]

/-- Composition of algebra homomorphisms is preserved in every degree. -/
theorem map_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) (n : ℕ) :
    map k (g.comp f) n = (map k g n).comp (map k f n) := by
  simp only [map, Unitization.map_comp, AlgHom.comp_toLinearMap,
    ← TensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rfl

/-- Degree-zero functoriality agrees with the induced homomorphism of forced unitizations. -/
@[simp]
theorem zeroEquiv_map (f : A →ₙₐ[k] B) (ω : UniversalForms k A 0) :
    zeroEquiv k B (map k f 0 ω) = Unitization.map f (zeroEquiv k A ω) := by
  induction ω using induction_on k A with
  | hword x a => simp
  | hadd ω η hω hη => simp only [map_add, hω, hη]

/-- Degree-one functoriality agrees with the existing map of kernel-model one-forms. -/
@[simp]
theorem oneEquiv_map (f : A →ₙₐ[k] B) (ω : UniversalForms k A 1) :
    oneEquiv k B (map k f 1 ω) = UniversalOneForms.map k f (oneEquiv k A ω) := by
  induction ω using induction_on k A with
  | hword x a => simp
  | hadd ω η hω hη => simp only [map_add, hω, hη]

end Map

section ComplexMap

variable {A} {B C : Type v} [IsScalarTower k A A] [SMulCommClass k A A]
  [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  [NonUnitalRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]

/-- The chain map induced by a nonunital algebra homomorphism. -/
def complexMap (f : A →ₙₐ[k] B) : complex k A ⟶ complex k B :=
  CochainComplex.ofHom
    (fun n ↦ (complexXIso k A n).hom ≫ ModuleCat.ofHom (map k f n) ≫
      (complexXIso k B n).inv)
    (fun n ↦ by
      simp only [complex, CochainComplex.of_d, complexXIso, Iso.refl_hom,
        Iso.refl_inv, Category.id_comp, Category.comp_id]
      apply ModuleCat.hom_ext
      exact LinearMap.ext (fun ω ↦ (map_d k f n ω).symm))

/-- The component of the induced chain map in tensor-word coordinates. -/
theorem complexMap_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (complexXIso k A n).inv ≫ (complexMap k f).f n ≫ (complexXIso k B n).hom =
      ModuleCat.ofHom (map k f n) := by
  simp [complexMap]

/-- The identity algebra homomorphism induces the identity chain map. -/
@[simp]
theorem complexMap_id : complexMap k (NonUnitalAlgHom.id k A) = 𝟙 (complex k A) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [complexMap]

/-- The induced chain maps preserve composition. -/
theorem complexMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) :
    complexMap k (g.comp f) = complexMap k f ≫ complexMap k g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [complexMap, map_comp, ModuleCat.ofHom_comp]

end ComplexMap

end

end UniversalForms

end TauCeti
