/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CrossedCocycle.Basic
public import TauCeti.GroupTheory.GroupExtension.Splitting
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Crossed cocycles and sections of semidirect products

Let a monoid `Γ` map to a group `Q` by `η : Γ →* Q`, and let `Q` act on a group `H` by
`β : Q →* MulAut H`. A crossed cocycle `c` for the pulled-back action `β ∘ η` gives the
homomorphism `γ ↦ (c γ, η γ)` from `Γ` to `H ⋊[β] Q`, which lifts `η`; conversely the first
coordinate of a homomorphism lifting `η` is a crossed cocycle. Gauge by `h : H` becomes conjugation
of the lift by `SemidirectProduct.inl h`.

When `Γ` is a group and `η` is its identity, the lifts are the splittings of the semidirect
product extension `H → H ⋊[α] Γ → Γ`, so crossed cocycles are the same as splittings, and gauge
orbits are the `H`-conjugacy classes of splittings. This is the underlying algebraic correspondence
by which a Langlands parameter `Γ →* H^∨ ⋊ Γ` projecting to the identity of `Γ` is a crossed
cocycle with values in the dual group `H^∨`.

## Main definitions

* `TauCeti.CrossedCocycle.toSemidirectHom`: the lift `γ ↦ (c γ, η γ)` of `η` to `H ⋊[β] Q`, and
  `TauCeti.CrossedCocycle.semidirectHomEquiv`, the equivalence it defines with the lifts of `η`.
* `TauCeti.CrossedCocycle.toSplitting`: the splitting `γ ↦ (c γ, γ)` of `H ⋊[α] Γ`, with inverse
  `GroupExtension.Splitting.toCrossedCocycle`, and `TauCeti.CrossedCocycle.splittingEquiv`, the
  equivalence they define.

## Main results

* `TauCeti.CrossedCocycle.toSemidirectHom_smul` and `TauCeti.CrossedCocycle.toSplitting_smul`:
  gauge by `h` conjugates the lift by `SemidirectProduct.inl h`.
* `TauCeti.CrossedCocycle.isConj_toSplitting_iff`: two splittings are conjugate exactly when the
  crossed cocycles are gauge equivalent.

## References

* J.-F. Dat, D. Helm, R. Kurinczuk, G. Moss, *Moduli of Langlands parameters*, §1.2.
* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VIII.1.1.
-/

public section

namespace TauCeti

open SemidirectProduct

namespace CrossedCocycle

variable {H : Type*} [Group H]

/-! ### Lifts of a prescribed projection -/

section SemidirectHom

variable {Γ Q : Type*} [Monoid Γ] [Group Q] {β : Q →* MulAut H} {η : Γ →* Q}

/-- The homomorphism `γ ↦ (c γ, η γ)` from `Γ` to `H ⋊[β] Q` attached to a crossed cocycle `c`
for `β ∘ η`; it lifts `η` (`TauCeti.CrossedCocycle.rightHom_comp_toSemidirectHom`). -/
def toSemidirectHom (c : CrossedCocycle (β.comp η)) : Γ →* H ⋊[β] Q where
  toFun γ := ⟨c γ, η γ⟩
  map_one' := by ext <;> simp
  map_mul' γ δ := by ext <;> simp [c.apply_mul]

@[simp]
theorem left_toSemidirectHom (c : CrossedCocycle (β.comp η)) (γ : Γ) :
    (c.toSemidirectHom γ).left = c γ :=
  (rfl)

@[simp]
theorem right_toSemidirectHom (c : CrossedCocycle (β.comp η)) (γ : Γ) :
    (c.toSemidirectHom γ).right = η γ :=
  (rfl)

/-- The homomorphism attached to a crossed cocycle lifts `η`. -/
@[simp]
theorem rightHom_comp_toSemidirectHom (c : CrossedCocycle (β.comp η)) :
    rightHom.comp c.toSemidirectHom = η :=
  MonoidHom.ext fun _ ↦ by simp

/-- Restricting a lift of `η` along `f` gives a lift of `η.comp f`. -/
@[simp]
theorem toSemidirectHom_comap (c : CrossedCocycle (β.comp η)) {Δ : Type*} [Monoid Δ]
    (f : Δ →* Γ) :
    toSemidirectHom (η := η.comp f) (c.comap f) = c.toSemidirectHom.comp f :=
  MonoidHom.ext fun δ ↦ by ext <;> simp

/-- The unit crossed cocycle lifts the projection by the canonical right inclusion. -/
@[simp]
theorem toSemidirectHom_one :
    (1 : CrossedCocycle (β.comp η)).toSemidirectHom = inr.comp η :=
  MonoidHom.ext fun γ ↦ by ext <;> simp

/-- The crossed cocycle for `β ∘ η` given by the first coordinate of a homomorphism
`s : Γ →* H ⋊[β] Q` lifting `η`. -/
def ofSemidirectHom (s : Γ →* H ⋊[β] Q) (hs : rightHom.comp s = η) :
    CrossedCocycle (β.comp η) where
  toFun γ := (s γ).left
  map_mul' γ δ := by
    rw [map_mul, mul_left, ← hs]
    simp

@[simp]
theorem ofSemidirectHom_apply (s : Γ →* H ⋊[β] Q) (hs : rightHom.comp s = η) (γ : Γ) :
    ofSemidirectHom s hs γ = (s γ).left :=
  (rfl)

/-- Crossed cocycles for `β ∘ η` are equivalent to the homomorphisms `Γ →* H ⋊[β] Q` lifting
`η`, by `c ↦ (γ ↦ (c γ, η γ))` with inverse the first coordinate. -/
def semidirectHomEquiv :
    CrossedCocycle (β.comp η) ≃ {s : Γ →* H ⋊[β] Q // rightHom.comp s = η} where
  toFun c := ⟨c.toSemidirectHom, c.rightHom_comp_toSemidirectHom⟩
  invFun s := ofSemidirectHom s.val s.property
  left_inv c := ext fun _ ↦ by simp
  right_inv s := Subtype.ext <| MonoidHom.ext fun γ ↦ by
    ext
    · simp
    · simpa using (DFunLike.congr_fun s.property γ).symm

@[simp]
theorem coe_semidirectHomEquiv_apply (c : CrossedCocycle (β.comp η)) :
    (semidirectHomEquiv c : Γ →* H ⋊[β] Q) = c.toSemidirectHom :=
  (rfl)

@[simp]
theorem semidirectHomEquiv_symm_apply (s : {s : Γ →* H ⋊[β] Q // rightHom.comp s = η}) :
    semidirectHomEquiv.symm s = ofSemidirectHom s.val s.property :=
  (rfl)

theorem toSemidirectHom_injective :
    Function.Injective (toSemidirectHom (β := β) (η := η)) :=
  fun _ _ h ↦ semidirectHomEquiv.injective (Subtype.ext h)

@[simp]
theorem toSemidirectHom_inj {c c' : CrossedCocycle (β.comp η)} :
    c.toSemidirectHom = c'.toSemidirectHom ↔ c = c' :=
  toSemidirectHom_injective.eq_iff

/-- Gauge by `h` conjugates the lift by `SemidirectProduct.inl h`. -/
theorem toSemidirectHom_smul (h : H) (c : CrossedCocycle (β.comp η)) (γ : Γ) :
    (h • c).toSemidirectHom γ = inl h * c.toSemidirectHom γ * (inl h)⁻¹ := by
  ext <;> simp [mul_assoc]

end SemidirectHom

/-! ### Splittings of the semidirect product -/

section Splitting

variable {Γ : Type*} [Group Γ] {α : Γ →* MulAut H}

/-- The splitting `γ ↦ (c γ, γ)` of the semidirect product extension `H → H ⋊[α] Γ → Γ`
attached to a crossed cocycle `c`: the lift `TauCeti.CrossedCocycle.toSemidirectHom` of the
identity of `Γ`. -/
def toSplitting (c : CrossedCocycle α) : (toGroupExtension α).Splitting where
  toMonoidHom := toSemidirectHom (β := α) (η := MonoidHom.id Γ) c
  rightInverse_rightHom _ := rfl

theorem toSplitting_apply (c : CrossedCocycle α) (γ : Γ) : c.toSplitting γ = ⟨c γ, γ⟩ :=
  (rfl)

@[simp]
theorem left_toSplitting (c : CrossedCocycle α) (γ : Γ) : (c.toSplitting γ).left = c γ :=
  (rfl)

/-- The unit crossed cocycle gives the canonical splitting `SemidirectProduct.inr`. -/
@[simp]
theorem toSplitting_one : (1 : CrossedCocycle α).toSplitting = inr_splitting α :=
  DFunLike.ext _ _ fun γ ↦ by ext <;> simp

/-- Gauge by `h` conjugates the splitting by `SemidirectProduct.inl h`. -/
theorem toSplitting_smul (h : H) (c : CrossedCocycle α) (γ : Γ) :
    (h • c).toSplitting γ = inl h * c.toSplitting γ * (inl h)⁻¹ :=
  toSemidirectHom_smul (β := α) (η := MonoidHom.id Γ) h c γ

end Splitting

end CrossedCocycle

end TauCeti

namespace GroupExtension.Splitting

open TauCeti SemidirectProduct

variable {H Γ : Type*} [Group H] [Group Γ] {α : Γ →* MulAut H}

/-- The crossed cocycle given by the first coordinate of a splitting of `H ⋊[α] Γ`, inverse to
`TauCeti.CrossedCocycle.toSplitting`. -/
def toCrossedCocycle (s : (toGroupExtension α).Splitting) : CrossedCocycle α :=
  CrossedCocycle.ofSemidirectHom (β := α) (η := MonoidHom.id Γ) s.toMonoidHom
    (MonoidHom.ext s.rightHom_splitting)

@[simp]
theorem toCrossedCocycle_apply (s : (toGroupExtension α).Splitting) (γ : Γ) :
    s.toCrossedCocycle γ = (s γ).left :=
  (rfl)

end GroupExtension.Splitting

namespace TauCeti.CrossedCocycle

open SemidirectProduct

variable {H Γ : Type*} [Group H] [Group Γ] {α : Γ →* MulAut H}

@[simp]
theorem toCrossedCocycle_toSplitting (c : CrossedCocycle α) :
    c.toSplitting.toCrossedCocycle = c :=
  ext fun _ ↦ by simp

@[simp]
theorem toSplitting_toCrossedCocycle (s : (toGroupExtension α).Splitting) :
    s.toCrossedCocycle.toSplitting = s :=
  DFunLike.ext _ _ fun γ ↦ by ext <;> simp

/-- Crossed cocycles are equivalent to splittings of the semidirect product extension, by
`c ↦ (γ ↦ (c γ, γ))` with inverse the first coordinate. -/
def splittingEquiv : CrossedCocycle α ≃ (toGroupExtension α).Splitting where
  toFun := toSplitting
  invFun := GroupExtension.Splitting.toCrossedCocycle
  left_inv := toCrossedCocycle_toSplitting
  right_inv := toSplitting_toCrossedCocycle

@[simp]
theorem splittingEquiv_apply (c : CrossedCocycle α) : splittingEquiv c = c.toSplitting :=
  (rfl)

@[simp]
theorem splittingEquiv_symm_apply (s : (toGroupExtension α).Splitting) :
    splittingEquiv.symm s = s.toCrossedCocycle :=
  (rfl)

theorem toSplitting_injective : Function.Injective (toSplitting (α := α)) :=
  splittingEquiv.injective

@[simp]
theorem toSplitting_inj {c c' : CrossedCocycle α} : c.toSplitting = c'.toSplitting ↔ c = c' :=
  toSplitting_injective.eq_iff

/-- The splittings of two crossed cocycles are `H`-conjugate exactly when the crossed cocycles
are gauge equivalent. -/
theorem isConj_toSplitting_iff {c c' : CrossedCocycle α} :
    (toGroupExtension α).IsConj c.toSplitting c'.toSplitting ↔ ∃ h : H, h • c' = c := by
  simp only [GroupExtension.IsConj, toGroupExtension_inl, ← toSplitting_smul]
  refine exists_congr fun h ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · exact (toSplitting_injective (DFunLike.ext' hc)).symm
  · rw [← hc]

end TauCeti.CrossedCocycle
