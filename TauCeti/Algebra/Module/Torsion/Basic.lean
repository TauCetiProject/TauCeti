/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in a subgroup of finite order, and maps reflecting torsion

A subgroup of an additive commutative group consists of torsion points as soon as it is finite:
its cardinality annihilates each of its elements, so a subgroup `H` is contained in the
`Nat.card H`-torsion subgroup. For finite `H` this says that a subgroup with `n` elements is
`n`-torsion; for infinite `H` one has `Nat.card H = 0` and the statement is the trivial
`H ≤ A[0]`.

A linear map `f` with a left inverse up to multiplication by a nonzerodivisor `a`, that is
`g ∘ f = a • id`, reflects torsion: if `f x` is torsion then so is `x`.

## Main results

* `AddSubgroup.le_torsionBy_natCard`: a subgroup `H` is contained in the `Nat.card H`-torsion
  subgroup.
* `TauCeti.Submodule.comap_torsion_le_of_comp_eq_smul`: a linear map with a left inverse up to a
  nonzerodivisor reflects torsion.
-/

public section

namespace AddSubgroup

/-- A subgroup `H` consists of `Nat.card H`-torsion points; for finite `H` this is the statement
that a subgroup with `n` elements is `n`-torsion, and for infinite `H` it is the trivial
`H ≤ A[0]`. -/
theorem le_torsionBy_natCard {A : Type*} [AddCommGroup A] {H : AddSubgroup A} :
    H ≤ A[(Nat.card H : ℤ)] := fun x hx ↦
  torsionBy.nsmul_iff.mpr <| by
    have : Nat.card H • (⟨x, hx⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val this

end AddSubgroup

namespace TauCeti

namespace AddSubgroup

/-- Torsion in a product of additive commutative groups is additively equivalent to the product
of their torsion subgroups. -/
def torsionByPiEquiv {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)] (n : ℤ) :
    _root_.AddSubgroup.torsionBy (∀ i, A i) n ≃+
      (∀ i, _root_.AddSubgroup.torsionBy (A i) n) where
  toFun x i := ⟨x.1 i, by
    change n • x.1 i = 0
    have hx : n • (x.1 : ∀ i, A i) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp x.2
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun hx i⟩
  invFun x := ⟨fun i ↦ x i, by
    change n • (fun i ↦ (x i : A i)) = 0
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply]
    exact (Submodule.mem_torsionBy_iff _ _).mp (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `torsionByPiEquiv` sends a torsion element to its pointwise torsion elements. -/
@[simp]
theorem torsionByPiEquiv_apply_coe {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (n : ℤ) (x : _root_.AddSubgroup.torsionBy (∀ i, A i) n) (i : ι) :
    ((torsionByPiEquiv A n x i : _root_.AddSubgroup.torsionBy (A i) n) : A i) = x.1 i :=
  by simp [torsionByPiEquiv]

/-- The inverse of `torsionByPiEquiv` assembles torsion elements pointwise. -/
@[simp]
theorem torsionByPiEquiv_symm_apply_coe {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (n : ℤ) (x : ∀ i, _root_.AddSubgroup.torsionBy (A i) n) (i : ι) :
    (((torsionByPiEquiv A n).symm x : _root_.AddSubgroup.torsionBy (∀ i, A i) n) :
      ∀ i, A i) i = (x i).1 :=
  by simp [torsionByPiEquiv]

/-- Torsion by `a` inside the `b`-torsion subgroup is the ambient `a`-torsion when `a ∣ b`. -/
def torsionByTorsionByEquiv {A : Type*} [AddCommGroup A] {a b : ℕ} (hab : a ∣ b) :
    _root_.AddSubgroup.torsionBy (_root_.AddSubgroup.torsionBy A (b : ℤ)) (a : ℤ) ≃+
      _root_.AddSubgroup.torsionBy A (a : ℤ) := by
  have ha (x : _root_.AddSubgroup.torsionBy A (a : ℤ)) : a • (x.1 : A) = 0 := by
    have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rwa [natCast_zsmul] at hx
  exact
    { toFun := fun x ↦ ⟨x.1.1, _root_.AddSubgroup.torsionBy.nsmul_iff.2 <| by
          have hx := (Submodule.mem_torsionBy_iff _ _).mp x.2
          rw [natCast_zsmul] at hx
          exact congrArg Subtype.val hx⟩
      invFun := fun x ↦
        ⟨⟨x.1, _root_.AddSubgroup.torsionBy.nsmul_iff.2 <| by
            obtain ⟨c, rfl⟩ := hab
            calc
              (a * c) • (x.1 : A) = c • (a • (x.1 : A)) := by rw [mul_nsmul]
              _ = 0 := by simp only [ha x, nsmul_zero]⟩,
          _root_.AddSubgroup.torsionBy.nsmul_iff.2 <| Subtype.ext <| ha x⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

/-- `torsionByTorsionByEquiv` preserves the underlying ambient element. -/
@[simp]
theorem torsionByTorsionByEquiv_apply_coe {A : Type*} [AddCommGroup A] {a b : ℕ} (hab : a ∣ b)
    (x : _root_.AddSubgroup.torsionBy (_root_.AddSubgroup.torsionBy A (b : ℤ)) (a : ℤ)) :
    ((torsionByTorsionByEquiv hab x : _root_.AddSubgroup.torsionBy A (a : ℤ)) : A) = x.1.1 :=
  by simp [torsionByTorsionByEquiv]

/-- The inverse of `torsionByTorsionByEquiv` preserves the underlying ambient element. -/
@[simp]
theorem torsionByTorsionByEquiv_symm_apply_coe {A : Type*} [AddCommGroup A] {a b : ℕ}
    (hab : a ∣ b) (x : _root_.AddSubgroup.torsionBy A (a : ℤ)) :
    (((torsionByTorsionByEquiv hab).symm x :
      _root_.AddSubgroup.torsionBy (_root_.AddSubgroup.torsionBy A (b : ℤ)) (a : ℤ)) : A) = x.1 :=
  by simp [torsionByTorsionByEquiv]

end AddSubgroup

end TauCeti

namespace AddEquiv

/-- An additive equivalence carries the `n`-torsion subgroup to the `n`-torsion subgroup. -/
def torsionByCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℤ) :
    _root_.AddSubgroup.torsionBy A n ≃+ _root_.AddSubgroup.torsionBy B n where
  toFun x := ⟨e x, by
    change n • e x = 0
    have hx : n • (x.1 : A) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    calc
      n • e x = e (n • (x.1 : A)) := (map_zsmul e n x.1).symm
      _ = e 0 := congrArg e hx
      _ = 0 := map_zero e⟩
  invFun x := ⟨e.symm x, by
    change n • e.symm x = 0
    have hx : n • (x.1 : B) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    calc
      n • e.symm x = e.symm (n • (x.1 : B)) := (map_zsmul e.symm n x.1).symm
      _ = e.symm 0 := congrArg e.symm hx
      _ = 0 := map_zero e.symm⟩
  left_inv x := Subtype.ext (e.left_inv x)
  right_inv x := Subtype.ext (e.right_inv x)
  map_add' _ _ := Subtype.ext (e.map_add _ _)

/-- `torsionByCongr` applies its additive equivalence to the underlying element. -/
@[simp]
theorem torsionByCongr_apply_coe {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (n : ℤ) (x : _root_.AddSubgroup.torsionBy A n) :
    ((torsionByCongr e n x : _root_.AddSubgroup.torsionBy B n) : B) = e x.1 :=
  by simp [torsionByCongr]

/-- The inverse of `torsionByCongr` applies the inverse additive equivalence. -/
@[simp]
theorem torsionByCongr_symm_apply_coe {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℤ) (x : _root_.AddSubgroup.torsionBy B n) :
    (((torsionByCongr e n).symm x : _root_.AddSubgroup.torsionBy A n) : A) = e.symm x.1 :=
  by simp [torsionByCongr]

end AddEquiv

open scoped nonZeroDivisors

namespace TauCeti

namespace Submodule

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- A linear map `f` for which some `g` satisfies `g ∘ f = a • id` with `a` a nonzerodivisor
reflects torsion: an element whose image is torsion is itself torsion. -/
theorem comap_torsion_le_of_comp_eq_smul {f : M →ₗ[R] N} {g : N →ₗ[R] M} {a : R} (ha : a ∈ R⁰)
    (hgf : ∀ x, g (f x) = a • x) :
    (_root_.Submodule.torsion R N).comap f ≤ _root_.Submodule.torsion R M := by
  intro x hx
  obtain ⟨b, hb⟩ := (_root_.Submodule.mem_torsion_iff _).mp
    (_root_.Submodule.mem_comap.mp hx)
  refine (_root_.Submodule.mem_torsion_iff x).mpr ⟨b * ⟨a, ha⟩, ?_⟩
  rw [mul_smul, Submonoid.smul_def ⟨a, ha⟩, ← hgf, Submonoid.smul_def, ← map_smul,
    ← Submonoid.smul_def, hb, map_zero]

end Submodule

end TauCeti
