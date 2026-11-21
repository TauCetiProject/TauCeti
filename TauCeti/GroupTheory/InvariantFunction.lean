/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Invariant functions and right translation

Left invariance by a subgroup and right level invariance are the algebraic transformation
laws of functions on a double quotient. They are independent of topology and smoothness.
Right translation preserves the left subgroup, but conjugates the right subgroup by the
translating element, not its inverse. These facts allow translation between different
levels before imposing analytic conditions on the functions.

The convention is `rightTranslate y f g = f (g * y)`, so the operators satisfy
`R(y) R(z) = R(y * z)`. Coefficients may be arbitrary types; closure under pointwise
addition, multiplication and scalar multiplication requires only the corresponding
operations on the coefficients.
-/

public section

namespace TauCeti

section Translation

variable {G A : Type*}

/-- Right translation of a function, with no inverse on the translating element. -/
def rightTranslate [Mul G] (y : G) (f : G → A) : G → A :=
  fun g ↦ f (g * y)

/-- Evaluation of a right translate. -/
@[simp]
theorem rightTranslate_apply [Mul G] (y : G) (f : G → A) (g : G) :
    rightTranslate y f g = f (g * y) := (rfl)

/-- Translation by the identity fixes every function. -/
@[simp]
theorem rightTranslate_one [MulOneClass G] (f : G → A) : rightTranslate 1 f = f := by
  ext g
  simp

/-- Right translations compose in the same order as the group elements. -/
theorem rightTranslate_mul [Semigroup G] (y z : G) (f : G → A) :
    rightTranslate (y * z) f = rightTranslate y (rightTranslate z f) := by
  ext g
  simp [mul_assoc]

/-- Every right translation fixes constant functions. -/
@[simp]
theorem rightTranslate_const [Mul G] (y : G) (a : A) :
    rightTranslate y (fun _ : G ↦ a) = fun _ ↦ a := (rfl)

end Translation

section Invariance

variable {G A : Type*} [Group G] {Γ Γ' J J' : Subgroup G} {f h : G → A}

/-- A function is left invariant by `Γ` if multiplication on the left by `Γ` fixes it. -/
def IsLeftInvariant (Γ : Subgroup G) (f : G → A) : Prop :=
  ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g

/-- A function has level `J` if multiplication on the right by `J` fixes it. -/
def IsLevelInvariant (J : Subgroup G) (f : G → A) : Prop :=
  ∀ u ∈ J, ∀ g, f (g * u) = f g

/-- The pointwise characterization of left invariance. -/
theorem isLeftInvariant_iff :
    IsLeftInvariant Γ f ↔ ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g := (Iff.rfl)

/-- The pointwise characterization of level invariance. -/
theorem isLevelInvariant_iff :
    IsLevelInvariant J f ↔ ∀ u ∈ J, ∀ g, f (g * u) = f g := (Iff.rfl)

/-- Left invariance restricts to smaller subgroups. -/
theorem IsLeftInvariant.subgroup_mono (hf : IsLeftInvariant Γ f) (hΓ : Γ' ≤ Γ) :
    IsLeftInvariant Γ' f :=
  fun γ hγ g ↦ hf γ (hΓ hγ) g

/-- Level invariance restricts to smaller subgroups. -/
theorem IsLevelInvariant.subgroup_mono (hf : IsLevelInvariant J f) (hJ : J' ≤ J) :
    IsLevelInvariant J' f :=
  fun u hu g ↦ hf u (hJ hu) g

/-- Constants are left invariant by every subgroup. -/
@[simp]
theorem isLeftInvariant_const (Γ : Subgroup G) (a : A) :
    IsLeftInvariant Γ (fun _ ↦ a) := by
  intro γ _ g
  rfl

/-- Constants have every level. -/
@[simp]
theorem isLevelInvariant_const (J : Subgroup G) (a : A) :
    IsLevelInvariant J (fun _ ↦ a) := by
  intro u _ g
  rfl

/-- The trivial left subgroup imposes no condition on a function. -/
@[simp]
theorem isLeftInvariant_bot (f : G → A) : IsLeftInvariant ⊥ f := by
  intro γ hγ g
  simpa using congrArg (fun x ↦ f (x * g)) (Subgroup.mem_bot.mp hγ)

/-- The trivial level imposes no condition on a function. -/
@[simp]
theorem isLevelInvariant_bot (f : G → A) : IsLevelInvariant ⊥ f := by
  intro u hu g
  simpa using congrArg (fun x ↦ f (g * x)) (Subgroup.mem_bot.mp hu)

/-- Full left invariance is precisely constancy, with value at the identity. -/
@[simp]
theorem isLeftInvariant_top_iff : IsLeftInvariant ⊤ f ↔ f = fun _ ↦ f 1 := by
  constructor
  · intro hf
    funext g
    simpa using hf g (Subgroup.mem_top g) 1
  · intro hf
    rw [hf]
    exact isLeftInvariant_const _ _

/-- Full right invariance is precisely constancy, with value at the identity. -/
@[simp]
theorem isLevelInvariant_top_iff : IsLevelInvariant ⊤ f ↔ f = fun _ ↦ f 1 := by
  constructor
  · intro hf
    funext g
    simpa using hf g (Subgroup.mem_top g) 1
  · intro hf
    rw [hf]
    exact isLevelInvariant_const _ _

/-- Right translation preserves the left-invariance law for the same subgroup. -/
theorem IsLeftInvariant.rightTranslate (hf : IsLeftInvariant Γ f) (y : G) :
    IsLeftInvariant Γ (rightTranslate y f) := by
  intro γ hγ g
  simpa [mul_assoc] using hf γ hγ (g * y)

/-- Right translation by `y` sends level `J` to level `y J y⁻¹`. -/
theorem IsLevelInvariant.rightTranslate (hf : IsLevelInvariant J f) (y : G) :
    IsLevelInvariant (J.map (MulAut.conj y)) (rightTranslate y f) := by
  rintro u ⟨j, hj, rfl⟩ g
  simpa [MulAut.conj_apply, mul_assoc] using hf j hj (g * y)

/-- Translation does not change whether the left-invariance condition holds. -/
@[simp]
theorem isLeftInvariant_rightTranslate_iff (y : G) :
    IsLeftInvariant Γ (rightTranslate y f) ↔ IsLeftInvariant Γ f := by
  constructor
  · intro hf
    have := hf.rightTranslate y⁻¹
    simpa [← rightTranslate_mul] using this
  · exact fun hf ↦ hf.rightTranslate y

/-- The conjugated level is exactly the transformation law transported by translation. -/
@[simp]
theorem isLevelInvariant_rightTranslate_iff (y : G) :
    IsLevelInvariant (J.map (MulAut.conj y)) (rightTranslate y f) ↔
      IsLevelInvariant J f := by
  constructor
  · intro hf j hj g
    have hj' : (MulAut.conj y) j ∈ J.map (MulAut.conj y) :=
      Subgroup.mem_map_of_mem _ hj
    simpa [MulAut.conj_apply, mul_assoc] using hf _ hj' (g * y⁻¹)
  · exact fun hf ↦ hf.rightTranslate y

section Pointwise

/-- Left invariance is closed under pointwise addition. -/
theorem IsLeftInvariant.add [Add A] (hf : IsLeftInvariant Γ f) (hh : IsLeftInvariant Γ h) :
    IsLeftInvariant Γ (f + h) := by
  intro γ hγ g
  simp only [Pi.add_apply, hf γ hγ, hh γ hγ]

/-- Level invariance is closed under pointwise addition. -/
theorem IsLevelInvariant.add [Add A] (hf : IsLevelInvariant J f) (hh : IsLevelInvariant J h) :
    IsLevelInvariant J (f + h) := by
  intro u hu g
  simp only [Pi.add_apply, hf u hu, hh u hu]

/-- Left invariance is closed under pointwise multiplication. -/
theorem IsLeftInvariant.mul [Mul A] (hf : IsLeftInvariant Γ f) (hh : IsLeftInvariant Γ h) :
    IsLeftInvariant Γ (f * h) := by
  intro γ hγ g
  simp only [Pi.mul_apply, hf γ hγ, hh γ hγ]

/-- Level invariance is closed under pointwise multiplication. -/
theorem IsLevelInvariant.mul [Mul A] (hf : IsLevelInvariant J f) (hh : IsLevelInvariant J h) :
    IsLevelInvariant J (f * h) := by
  intro u hu g
  simp only [Pi.mul_apply, hf u hu, hh u hu]

/-- Left invariance is preserved by pointwise scalar multiplication. -/
theorem IsLeftInvariant.smul {R : Type*} [SMul R A] (hf : IsLeftInvariant Γ f) (c : R) :
    IsLeftInvariant Γ (c • f) := by
  intro γ hγ g
  simp only [Pi.smul_apply, hf γ hγ]

/-- Level invariance is preserved by pointwise scalar multiplication. -/
theorem IsLevelInvariant.smul {R : Type*} [SMul R A] (hf : IsLevelInvariant J f) (c : R) :
    IsLevelInvariant J (c • f) := by
  intro u hu g
  simp only [Pi.smul_apply, hf u hu]

end Pointwise
end Invariance

end TauCeti
