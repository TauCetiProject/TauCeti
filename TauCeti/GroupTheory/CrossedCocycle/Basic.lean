/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Crossed cocycles and their gauge action

Let a monoid `Γ` act on a group `H` through a homomorphism `α : Γ →* MulAut H`; `H` need not be
commutative. A **crossed cocycle** is a map `c : Γ → H` with

`c (γ * δ) = c γ * α γ (c δ)`,

and **gauge** by `h : H` is the map `(h • c) γ = h * c γ * (α γ h)⁻¹`. Gauge is an action of `H`
on crossed cocycles, and an `α`-equivariant homomorphism of coefficient groups sends crossed
cocycles to crossed cocycles compatibly with gauge. For trivial `α` crossed cocycles are exactly
the homomorphisms `Γ →* H`.

When `Γ` is a group, a crossed cocycle is the same thing as a splitting `γ ↦ (c γ, γ)` of the
semidirect product extension `H → H ⋊[α] Γ → Γ`, with inverse the first coordinate; gauge by `h`
becomes conjugation of the splitting by `SemidirectProduct.inl h`, so gauge orbits are the
`H`-conjugacy classes of splittings. This is the form in which a Langlands parameter with values
in an L-group `H^∨ ⋊ Γ` is a crossed cocycle with values in the dual group `H^∨`.

No topology is involved: the coefficient groups that occur are the groups of points `H^∨(B)` of a
group scheme on arbitrary coefficient algebras `B`, and the action is part of the data of the
semidirect product, so it is given as a homomorphism to `MulAut H`. For topological `Γ` and `H`,
continuous crossed cocycles with gauge are compared with `TauCeti.NonabelianH1` in
`TauCeti/GroupTheory/CrossedCocycle/NonabelianH1.lean`.

## Main definitions

* `TauCeti.CrossedCocycle α`: the crossed cocycles for the action `α : Γ →* MulAut H`.
* `TauCeti.CrossedCocycle.instMulAction`: the gauge action of `H`.
* `TauCeti.CrossedCocycle.map`: change of coefficients along an equivariant homomorphism.
* `TauCeti.CrossedCocycle.equivMonoidHom`: for the trivial action, crossed cocycles are
  homomorphisms.
* `TauCeti.CrossedCocycle.toSplitting`: the splitting `γ ↦ (c γ, γ)` of `H ⋊[α] Γ`, and
  `TauCeti.CrossedCocycle.splittingEquiv`, the equivalence it defines.

## Main results

* `TauCeti.CrossedCocycle.map_smul`: change of coefficients commutes with gauge.
* `TauCeti.CrossedCocycle.toSplitting_smul`: gauge by `h` conjugates the splitting by
  `SemidirectProduct.inl h`.
* `TauCeti.CrossedCocycle.isConj_toSplitting_iff`: two splittings are conjugate exactly when the
  crossed cocycles are gauge equivalent.

## References

* J.-F. Dat, D. Helm, R. Kurinczuk, G. Moss, *Moduli of Langlands parameters*, §1.2 and §2.1.
* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VIII.1.1.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.1.
-/

public section

namespace TauCeti

open SemidirectProduct

variable {Γ H : Type*} [Monoid Γ] [Group H]

/-- A **crossed cocycle** of `Γ` with values in `H` for the action `α : Γ →* MulAut H`: a map
`c : Γ → H` with `c (γ * δ) = c γ * α γ (c δ)`. For trivial `α` these are the homomorphisms
`Γ →* H` (`TauCeti.CrossedCocycle.equivMonoidHom`). -/
structure CrossedCocycle (α : Γ →* MulAut H) where
  /-- The underlying map of a crossed cocycle. -/
  toFun : Γ → H
  /-- The crossed cocycle identity `c (γ * δ) = c γ * α γ (c δ)`. -/
  map_mul' : ∀ γ δ : Γ, toFun (γ * δ) = toFun γ * α γ (toFun δ)

namespace CrossedCocycle

variable {α : Γ →* MulAut H}

instance : FunLike (CrossedCocycle α) Γ H where
  coe := toFun
  coe_injective c c' h := by
    cases c
    cases c'
    congr

@[ext]
theorem ext {c c' : CrossedCocycle α} (h : ∀ γ, c γ = c' γ) : c = c' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : Γ → H) (hf : ∀ γ δ : Γ, f (γ * δ) = f γ * α γ (f δ)) :
    ⇑(⟨f, hf⟩ : CrossedCocycle α) = f :=
  (rfl)

/-- The crossed cocycle identity. -/
theorem apply_mul (c : CrossedCocycle α) (γ δ : Γ) : c (γ * δ) = c γ * α γ (c δ) :=
  c.map_mul' γ δ

/-- A crossed cocycle takes the value `1` at `1`. -/
@[simp]
theorem apply_one (c : CrossedCocycle α) : c 1 = 1 := by
  simpa using c.apply_mul 1 1

/-- The value of a crossed cocycle at an inverse. -/
@[simp]
theorem apply_inv {Γ : Type*} [Group Γ] {α : Γ →* MulAut H} (c : CrossedCocycle α) (γ : Γ) :
    c γ⁻¹ = α γ⁻¹ (c γ)⁻¹ := by
  have h := c.apply_mul γ⁻¹ γ
  rw [inv_mul_cancel, apply_one, eq_comm, mul_eq_one_iff_eq_inv] at h
  rw [h]
  exact (map_inv (α γ⁻¹) (c γ)).symm

/-- The unit crossed cocycle `γ ↦ 1`. -/
instance : One (CrossedCocycle α) :=
  ⟨⟨fun _ ↦ 1, fun γ _ ↦ by simp⟩⟩

@[simp]
theorem one_apply (γ : Γ) : (1 : CrossedCocycle α) γ = 1 :=
  (rfl)

instance : Inhabited (CrossedCocycle α) :=
  ⟨1⟩

/-- With trivial coefficients, the unit crossed cocycle is the only one. -/
instance [Subsingleton H] : Subsingleton (CrossedCocycle α) :=
  ⟨fun _ _ ↦ ext fun _ ↦ Subsingleton.elim _ _⟩

/-! ### The gauge action -/

/-- **Gauge** by `h : H` sends a crossed cocycle `c` to `γ ↦ h * c γ * (α γ h)⁻¹`. -/
instance : SMul H (CrossedCocycle α) where
  smul h c :=
    { toFun γ := h * c γ * (α γ h)⁻¹
      map_mul' γ δ := by
        simp [c.apply_mul, mul_assoc] }

@[simp]
theorem smul_apply (h : H) (c : CrossedCocycle α) (γ : Γ) :
    (h • c) γ = h * c γ * (α γ h)⁻¹ :=
  (rfl)

/-- Gauge is an action of `H` on crossed cocycles. -/
instance instMulAction : MulAction H (CrossedCocycle α) where
  one_smul c := ext fun γ ↦ by simp
  mul_smul h k c := ext fun γ ↦ by simp [mul_assoc]

/-! ### Change of coefficients -/

section Map

variable {H' H'' : Type*} [Group H'] [Group H''] {α' : Γ →* MulAut H'} {α'' : Γ →* MulAut H''}

/-- An `α`-equivariant homomorphism `f : H →* H'` sends crossed cocycles to crossed cocycles,
by `c ↦ f ∘ c`. -/
def map (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) (c : CrossedCocycle α) :
    CrossedCocycle α' where
  toFun γ := f (c γ)
  map_mul' γ δ := by rw [c.apply_mul, map_mul, hf]

@[simp]
theorem map_apply (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) (c : CrossedCocycle α)
    (γ : Γ) : c.map f hf γ = f (c γ) :=
  (rfl)

@[simp]
theorem map_id (c : CrossedCocycle α) : c.map (MonoidHom.id H) (fun _ _ ↦ rfl) = c :=
  (rfl)

theorem map_map (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) (g : H' →* H'')
    (hg : ∀ γ x, g (α' γ x) = α'' γ (g x)) (c : CrossedCocycle α) :
    (c.map f hf).map g hg = c.map (g.comp f) (fun γ x ↦ by simp [hf, hg]) :=
  (rfl)

@[simp]
theorem map_one (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) :
    (1 : CrossedCocycle α).map f hf = 1 :=
  ext fun _ ↦ by simp

/-- Change of coefficients commutes with gauge. -/
@[simp]
theorem map_smul (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) (h : H)
    (c : CrossedCocycle α) : (h • c).map f hf = f h • c.map f hf :=
  ext fun _ ↦ by simp [hf]

end Map

/-! ### Trivial action -/

/-- For the trivial action, crossed cocycles are exactly the homomorphisms `Γ →* H`. -/
def equivMonoidHom : CrossedCocycle (1 : Γ →* MulAut H) ≃ (Γ →* H) where
  toFun c :=
    { toFun := c
      map_one' := c.apply_one
      map_mul' γ δ := by simpa using c.apply_mul γ δ }
  invFun f := ⟨f, fun γ δ ↦ by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivMonoidHom_apply (c : CrossedCocycle (1 : Γ →* MulAut H)) (γ : Γ) :
    equivMonoidHom c γ = c γ :=
  (rfl)

@[simp]
theorem equivMonoidHom_symm_apply (f : Γ →* H) (γ : Γ) : equivMonoidHom.symm f γ = f γ :=
  (rfl)

/-! ### Splittings of the semidirect product -/

section Splitting

variable {Γ : Type*} [Group Γ] {α : Γ →* MulAut H}

/-- The splitting `γ ↦ (c γ, γ)` of the semidirect product extension `H → H ⋊[α] Γ → Γ`
attached to a crossed cocycle `c`. -/
def toSplitting (c : CrossedCocycle α) : (toGroupExtension α).Splitting where
  toFun γ := ⟨c γ, γ⟩
  map_one' := by ext <;> simp
  map_mul' γ δ := by ext <;> simp [c.apply_mul]
  rightInverse_rightHom _ := rfl

theorem toSplitting_apply (c : CrossedCocycle α) (γ : Γ) : c.toSplitting γ = ⟨c γ, γ⟩ :=
  (rfl)

@[simp]
theorem left_toSplitting (c : CrossedCocycle α) (γ : Γ) : (c.toSplitting γ).left = c γ :=
  (rfl)

@[simp]
theorem right_toSplitting (c : CrossedCocycle α) (γ : Γ) : (c.toSplitting γ).right = γ :=
  (rfl)

/-- The unit crossed cocycle gives the canonical splitting `SemidirectProduct.inr`. -/
@[simp]
theorem toSplitting_one : (1 : CrossedCocycle α).toSplitting = inr_splitting α :=
  -- Mathlib states no evaluation lemma for `inr_splitting`, whose values are `inr γ = (1, γ)`.
  DFunLike.ext _ _ fun _ ↦ rfl

/-- Gauge by `h` conjugates the splitting by `SemidirectProduct.inl h`. -/
theorem toSplitting_smul (h : H) (c : CrossedCocycle α) (γ : Γ) :
    (h • c).toSplitting γ = inl h * c.toSplitting γ * (inl h)⁻¹ := by
  ext <;> simp [mul_assoc]

/-- The crossed cocycle given by the first coordinate of a splitting of `H ⋊[α] Γ`. -/
def ofSplitting (s : (toGroupExtension α).Splitting) : CrossedCocycle α where
  toFun γ := (s γ).left
  map_mul' γ δ := by
    rw [map_mul, mul_left, right_splitting]

@[simp]
theorem ofSplitting_apply (s : (toGroupExtension α).Splitting) (γ : Γ) :
    ofSplitting s γ = (s γ).left :=
  (rfl)

/-- Crossed cocycles are equivalent to splittings of the semidirect product extension, by
`c ↦ (γ ↦ (c γ, γ))` with inverse the first coordinate. -/
def splittingEquiv : CrossedCocycle α ≃ (toGroupExtension α).Splitting where
  toFun := toSplitting
  invFun := ofSplitting
  left_inv _ := rfl
  right_inv s := DFunLike.ext _ _ fun γ ↦ by
    ext
    · rfl
    · exact (right_splitting s γ).symm

@[simp]
theorem splittingEquiv_apply (c : CrossedCocycle α) : splittingEquiv c = c.toSplitting :=
  (rfl)

@[simp]
theorem splittingEquiv_symm_apply (s : (toGroupExtension α).Splitting) :
    splittingEquiv.symm s = ofSplitting s :=
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

end Splitting

end CrossedCocycle

end TauCeti
