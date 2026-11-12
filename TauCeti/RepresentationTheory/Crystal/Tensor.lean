/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Tensor products of normal crystals

For normal crystals `B₁` and `B₂` over a root datum with a base, the tensor product `B₁ ⊗ B₂` is
the normal crystal on `B₁ × B₂` with weight `wt (x₁, x₂) = wt x₁ + wt x₂`, string lengths

* `ε i (x₁, x₂) = ε i x₁ + (ε i x₂ - φ i x₁)`,
* `φ i (x₁, x₂) = φ i x₂ + (φ i x₁ - ε i x₂)`

(truncated subtraction in `ℕ`), and root operators acting on one factor:

* `e i (x₁, x₂) = (e i x₁, x₂)` if `ε i x₂ ≤ φ i x₁`, and `(x₁, e i x₂)` otherwise;
* `f i (x₁, x₂) = (f i x₁, x₂)` if `ε i x₂ < φ i x₁`, and `(x₁, f i x₂)` otherwise.

If the operator on the factor it acts on returns `none` (standing for `0`), the operator on the
tensor product returns `none` as well.

**Tie convention.** This is Kashiwara's convention: on a tie `φ i x₁ = ε i x₂` the raising
operator acts on the left factor and the lowering operator on the right factor. It is the
convention under which Littelmann's concatenation `π₁ * π₂` of paths corresponds to `π₁ ⊗ π₂`:
on the concatenation, `e i` changes the path containing the first time at which the height
`⟨π(t), α_i^∨⟩` attains its minimum, and `f i` the path containing the last such time. Bump and
Schilling use the opposite convention, which is obtained from this one by exchanging the two
factors.

In Kashiwara's form the string lengths are `ε i (x₁, x₂) = max (ε i x₁) (ε i x₂ - ⟨wt x₁, α_i^∨⟩)`
and `φ i (x₁, x₂) = max (φ i x₂) (φ i x₁ + ⟨wt x₂, α_i^∨⟩)`; see
`TauCeti.NormalCrystal.tensor_ε_eq_max` and `TauCeti.NormalCrystal.tensor_φ_eq_max`.

## Main definitions

* `TauCeti.NormalCrystal.tensor`: the tensor product of two normal crystals.
* `TauCeti.NormalCrystal.StrictHom.tensor`: the tensor product of two strict morphisms.
* `TauCeti.NormalCrystal.tensorAssoc`, `TauCeti.NormalCrystal.tensorAssocInv`: the associator
  `(B₁ ⊗ B₂) ⊗ B₃ → B₁ ⊗ (B₂ ⊗ B₃)` and its inverse, as strict morphisms.
* `TauCeti.NormalCrystal.dualTensor`, `TauCeti.NormalCrystal.dualTensorInv`: the strict morphism
  `(B₁ ⊗ B₂)^∨ → B₂^∨ ⊗ B₁^∨` exchanging the factors, and its inverse.

## Main results

* `TauCeti.NormalCrystal.tensor_e_of_le`, `TauCeti.NormalCrystal.tensor_e_of_lt`,
  `TauCeti.NormalCrystal.tensor_f_of_lt`, `TauCeti.NormalCrystal.tensor_f_of_le`: the tensor
  product rule on each side of the tie.
* `TauCeti.NormalCrystal.StrictHom.tensor_id`, `TauCeti.NormalCrystal.StrictHom.tensor_comp`:
  functoriality of the tensor product in strict morphisms.
* `TauCeti.NormalCrystal.tensorAssocInv_comp_tensorAssoc`,
  `TauCeti.NormalCrystal.tensorAssoc_comp_tensorAssocInv`: associativity of the tensor product up
  to strict isomorphism.
* `TauCeti.NormalCrystal.dualTensorInv_comp_dualTensor`,
  `TauCeti.NormalCrystal.dualTensor_comp_dualTensorInv`: `(B₁ ⊗ B₂)^∨ ≅ B₂^∨ ⊗ B₁^∨`.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §2.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
-/

public section

namespace TauCeti

namespace NormalCrystal

universe u v w x₁ x₂ x₃ x₄ x₅ x₆

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}
  {B₁ : Type x₁} {B₂ : Type x₂} {B₃ : Type x₃}

section Tensor

variable (c : NormalCrystal P b B₁) (d : NormalCrystal P b B₂)

/-- The **tensor product** `B₁ ⊗ B₂` of two normal crystals, on the product type, with
Kashiwara's tie convention: on a tie `φ i x₁ = ε i x₂` the raising operator acts on the left
factor and the lowering operator on the right factor. -/
def tensor : NormalCrystal P b (B₁ × B₂) where
  wt x := c.wt x.1 + d.wt x.2
  e i x := if d.ε i x.2 ≤ c.φ i x.1 then (c.e i x.1).map (·, x.2) else (d.e i x.2).map (x.1, ·)
  f i x := if d.ε i x.2 < c.φ i x.1 then (c.f i x.1).map (·, x.2) else (d.f i x.2).map (x.1, ·)
  ε i x := c.ε i x.1 + (d.ε i x.2 - c.φ i x.1)
  φ i x := d.φ i x.2 + (c.φ i x.1 - d.ε i x.2)
  f_eq_some_iff {i x y} := by
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    dsimp only
    constructor
    · intro h
      split_ifs at h with hx
      · obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzy
        have := c.φ_of_f_eq_some hz
        rw [ite_eq_left (by omega), c.e_eq_some_iff.2 hz, Option.map_some]
      · obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzy
        have := d.ε_of_f_eq_some hz
        rw [ite_eq_right (by omega), d.e_eq_some_iff.2 hz, Option.map_some]
    · intro h
      split_ifs at h with hy
      · obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzx
        have := c.φ_of_e_eq_some hz
        rw [ite_eq_left (by omega), c.f_eq_some_iff.2 hz, Option.map_some]
      · obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzx
        have := d.ε_of_e_eq_some hz
        rw [ite_eq_right (by omega), d.f_eq_some_iff.2 hz, Option.map_some]
  wt_of_e_eq_some {i x y} h := by
    obtain ⟨x₁, x₂⟩ := x
    dsimp only at h ⊢
    split_ifs at h
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [c.wt_of_e_eq_some hz, add_right_comm]
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [d.wt_of_e_eq_some hz, add_assoc]
  ε_eq_zero_iff {i x} := by
    obtain ⟨x₁, x₂⟩ := x
    dsimp only
    split_ifs with h
    · rw [Option.map_eq_none_iff, ← c.ε_eq_zero_iff]
      omega
    · rw [Option.map_eq_none_iff, ← d.ε_eq_zero_iff]
      omega
  ε_of_e_eq_some {i x y} h := by
    obtain ⟨x₁, x₂⟩ := x
    dsimp only at h ⊢
    split_ifs at h with hx
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      have := c.ε_of_e_eq_some hz
      have := c.φ_of_e_eq_some hz
      dsimp only
      omega
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      have := d.ε_of_e_eq_some hz
      dsimp only
      omega
  φ_eq_zero_iff {i x} := by
    obtain ⟨x₁, x₂⟩ := x
    dsimp only
    split_ifs with h
    · rw [Option.map_eq_none_iff, ← c.φ_eq_zero_iff]
      omega
    · rw [Option.map_eq_none_iff, ← d.φ_eq_zero_iff]
      omega
  φ_sub_ε i x := by
    have h₁ := c.φ_sub_ε i x.1
    have h₂ := d.φ_sub_ε i x.2
    rw [map_add, LinearMap.add_apply]
    omega

variable {c d}

@[simp]
theorem tensor_wt (x : B₁ × B₂) : (c.tensor d).wt x = c.wt x.1 + d.wt x.2 := (rfl)

@[simp]
theorem tensor_ε (i : b.support) (x : B₁ × B₂) :
    (c.tensor d).ε i x = c.ε i x.1 + (d.ε i x.2 - c.φ i x.1) := (rfl)

@[simp]
theorem tensor_φ (i : b.support) (x : B₁ × B₂) :
    (c.tensor d).φ i x = d.φ i x.2 + (c.φ i x.1 - d.ε i x.2) := (rfl)

theorem tensor_e (i : b.support) (x : B₁ × B₂) :
    (c.tensor d).e i x = if d.ε i x.2 ≤ c.φ i x.1 then (c.e i x.1).map (·, x.2)
      else (d.e i x.2).map (x.1, ·) := (rfl)

theorem tensor_f (i : b.support) (x : B₁ × B₂) :
    (c.tensor d).f i x = if d.ε i x.2 < c.φ i x.1 then (c.f i x.1).map (·, x.2)
      else (d.f i x.2).map (x.1, ·) := (rfl)

variable {i : b.support} {x₁ : B₁} {x₂ : B₂}

/-- The tensor product rule for raising, when it acts on the left factor (including the tie). -/
@[simp]
theorem tensor_e_of_le (h : d.ε i x₂ ≤ c.φ i x₁) :
    (c.tensor d).e i (x₁, x₂) = (c.e i x₁).map (·, x₂) :=
  ite_eq_left h

/-- The tensor product rule for raising, when it acts on the right factor. -/
@[simp]
theorem tensor_e_of_lt (h : c.φ i x₁ < d.ε i x₂) :
    (c.tensor d).e i (x₁, x₂) = (d.e i x₂).map (x₁, ·) :=
  ite_eq_right h.not_ge

/-- The tensor product rule for lowering, when it acts on the left factor. -/
@[simp]
theorem tensor_f_of_lt (h : d.ε i x₂ < c.φ i x₁) :
    (c.tensor d).f i (x₁, x₂) = (c.f i x₁).map (·, x₂) :=
  ite_eq_left h

/-- The tensor product rule for lowering, when it acts on the right factor (including the
tie). -/
@[simp]
theorem tensor_f_of_le (h : c.φ i x₁ ≤ d.ε i x₂) :
    (c.tensor d).f i (x₁, x₂) = (d.f i x₂).map (x₁, ·) :=
  ite_eq_right h.not_gt

/-- Kashiwara's form of the raising string length of a tensor product:
`ε i (x₁ ⊗ x₂) = max (ε i x₁) (ε i x₂ - ⟨wt x₁, α_i^∨⟩)`. -/
theorem tensor_ε_eq_max (i : b.support) (x : B₁ × B₂) :
    ((c.tensor d).ε i x : ℤ) =
      max (c.ε i x.1 : ℤ) (d.ε i x.2 - P.toLinearMap (c.wt x.1) (P.coroot i)) := by
  have := c.φ_sub_ε i x.1
  rw [tensor_ε]
  omega

/-- Kashiwara's form of the lowering string length of a tensor product:
`φ i (x₁ ⊗ x₂) = max (φ i x₂) (φ i x₁ + ⟨wt x₂, α_i^∨⟩)`. -/
theorem tensor_φ_eq_max (i : b.support) (x : B₁ × B₂) :
    ((c.tensor d).φ i x : ℤ) =
      max (d.φ i x.2 : ℤ) (c.φ i x.1 + P.toLinearMap (d.wt x.2) (P.coroot i)) := by
  have := d.φ_sub_ε i x.2
  rw [tensor_φ]
  omega

end Tensor

/-! ### Functoriality -/

namespace StrictHom

variable {B₄ : Type x₄} {B₅ : Type x₅} {B₆ : Type x₆}
  {c : NormalCrystal P b B₁} {c' : NormalCrystal P b B₂} {c'' : NormalCrystal P b B₃}
  {d : NormalCrystal P b B₄} {d' : NormalCrystal P b B₅} {d'' : NormalCrystal P b B₆}

/-- The tensor product `ψ ⊗ χ` of two strict morphisms, acting factorwise. -/
def tensor (ψ : StrictHom c c') (χ : StrictHom d d') : StrictHom (c.tensor d) (c'.tensor d') where
  toFun := Prod.map ψ χ
  wt_toFun x := by simp
  e_toFun i x := by
    obtain ⟨x₁, x₂⟩ := x
    simp only [tensor_e, Prod.map_fst, Prod.map_snd, ε_apply, φ_apply]
    split_ifs <;> simp [Option.map_map, Function.comp_def]

@[simp]
theorem tensor_apply (ψ : StrictHom c c') (χ : StrictHom d d') (x : B₁ × B₄) :
    ψ.tensor χ x = (ψ x.1, χ x.2) := (rfl)

@[simp]
theorem tensor_id : (StrictHom.id c).tensor (StrictHom.id d) = StrictHom.id (c.tensor d) :=
  StrictHom.ext fun _ => by simp

theorem tensor_comp (ψ : StrictHom c c') (ψ' : StrictHom c' c'') (χ : StrictHom d d')
    (χ' : StrictHom d' d'') : (ψ'.comp ψ).tensor (χ'.comp χ) = (ψ'.tensor χ').comp (ψ.tensor χ) :=
  StrictHom.ext fun _ => by simp

end StrictHom

/-! ### Associativity -/

section Assoc

variable (c : NormalCrystal P b B₁) (d : NormalCrystal P b B₂) (g : NormalCrystal P b B₃)

/-- The **associator** `(B₁ ⊗ B₂) ⊗ B₃ → B₁ ⊗ (B₂ ⊗ B₃)` of the tensor product, a strict morphism
with inverse `TauCeti.NormalCrystal.tensorAssocInv`. -/
def tensorAssoc : StrictHom ((c.tensor d).tensor g) (c.tensor (d.tensor g)) where
  toFun := Equiv.prodAssoc B₁ B₂ B₃
  wt_toFun x := by simp [add_assoc]
  e_toFun i x := by
    obtain ⟨⟨x₁, x₂⟩, x₃⟩ := x
    simp only [Equiv.prodAssoc_apply, tensor_e, tensor_ε, tensor_φ]
    split_ifs <;> first | omega | simp [Option.map_map, Function.comp_def]

/-- The inverse `B₁ ⊗ (B₂ ⊗ B₃) → (B₁ ⊗ B₂) ⊗ B₃` of the associator
`TauCeti.NormalCrystal.tensorAssoc`. -/
def tensorAssocInv : StrictHom (c.tensor (d.tensor g)) ((c.tensor d).tensor g) where
  toFun := (Equiv.prodAssoc B₁ B₂ B₃).symm
  wt_toFun x := by simp [add_assoc]
  e_toFun i x := by
    obtain ⟨x₁, x₂, x₃⟩ := x
    simp only [Equiv.prodAssoc_symm_apply, tensor_e, tensor_ε, tensor_φ]
    split_ifs <;> first | omega | simp [Option.map_map, Function.comp_def]

@[simp]
theorem tensorAssoc_apply (x : (B₁ × B₂) × B₃) :
    c.tensorAssoc d g x = (x.1.1, x.1.2, x.2) := (rfl)

@[simp]
theorem tensorAssocInv_apply (x : B₁ × B₂ × B₃) :
    c.tensorAssocInv d g x = ((x.1, x.2.1), x.2.2) := (rfl)

@[simp]
theorem tensorAssocInv_comp_tensorAssoc :
    (c.tensorAssocInv d g).comp (c.tensorAssoc d g) = StrictHom.id _ :=
  StrictHom.ext fun _ => by simp

@[simp]
theorem tensorAssoc_comp_tensorAssocInv :
    (c.tensorAssoc d g).comp (c.tensorAssocInv d g) = StrictHom.id _ :=
  StrictHom.ext fun _ => by simp

end Assoc

/-! ### Duality -/

section Dual

variable (c : NormalCrystal P b B₁) (d : NormalCrystal P b B₂)

/-- The strict morphism `(B₁ ⊗ B₂)^∨ → B₂^∨ ⊗ B₁^∨` exchanging the two factors, with inverse
`TauCeti.NormalCrystal.dualTensorInv`. Duality exchanges the two halves of the tie convention:
on a tie the lowering operator of `B₁ ⊗ B₂` acts on its right factor, which is the left factor of
`B₂^∨ ⊗ B₁^∨`, where raising acts on ties. -/
def dualTensor : StrictHom (c.tensor d).dual (d.dual.tensor c.dual) where
  toFun := Prod.swap
  wt_toFun x := by simp [add_comm]
  e_toFun i x := by
    obtain ⟨x₁, x₂⟩ := x
    simp only [Prod.swap_prod_mk, tensor_e, dual_e, dual_ε, dual_φ, tensor_f]
    split_ifs <;> first | omega | simp [Option.map_map, Function.comp_def]

/-- The inverse `B₂^∨ ⊗ B₁^∨ → (B₁ ⊗ B₂)^∨` of `TauCeti.NormalCrystal.dualTensor`. -/
def dualTensorInv : StrictHom (d.dual.tensor c.dual) (c.tensor d).dual where
  toFun := Prod.swap
  wt_toFun x := by simp [add_comm]
  e_toFun i x := by
    obtain ⟨x₂, x₁⟩ := x
    simp only [Prod.swap_prod_mk, tensor_e, dual_e, dual_ε, dual_φ, tensor_f]
    split_ifs <;> first | omega | simp [Option.map_map, Function.comp_def]

@[simp]
theorem dualTensor_apply (x : B₁ × B₂) : c.dualTensor d x = x.swap := (rfl)

@[simp]
theorem dualTensorInv_apply (x : B₂ × B₁) : c.dualTensorInv d x = x.swap := (rfl)

@[simp]
theorem dualTensorInv_comp_dualTensor :
    (c.dualTensorInv d).comp (c.dualTensor d) = StrictHom.id _ :=
  StrictHom.ext fun _ => by simp

@[simp]
theorem dualTensor_comp_dualTensorInv :
    (c.dualTensor d).comp (c.dualTensorInv d) = StrictHom.id _ :=
  StrictHom.ext fun _ => by simp

end Dual

end NormalCrystal

end TauCeti
