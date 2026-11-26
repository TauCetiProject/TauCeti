/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End

/-!
# Crossed cocycles and their gauge action

Let a monoid `Γ` act on a group `H` through a homomorphism `α : Γ →* MulAut H`; `H` need not be
commutative. A **crossed cocycle** is a map `c : Γ → H` with

`c (γ * δ) = c γ * α γ (c δ)`,

and **gauge** by `h : H` is the map `(h • c) γ = h * c γ * (α γ h)⁻¹`. Gauge is an action of `H`
on crossed cocycles, and an `α`-equivariant homomorphism of coefficient groups sends crossed
cocycles to crossed cocycles compatibly with gauge. For trivial `α` crossed cocycles are exactly
the homomorphisms `Γ →* H`.

No topology is involved: the coefficient groups that occur are the groups of points `H^∨(B)` of a
group scheme on arbitrary coefficient algebras `B`, and the action is part of the data of the
semidirect product, so it is given as a homomorphism to `MulAut H`.

Related files:

* `TauCeti/GroupTheory/CrossedCocycle/Splitting.lean` identifies crossed cocycles for `β ∘ η`,
  where `η : Γ →* Q` and `β : Q →* MulAut H`, with the homomorphisms `Γ →* H ⋊[β] Q` lifting `η`,
  and, for `η` the identity of a group, with the splittings of the semidirect product. This is the
  underlying algebraic correspondence by which a Langlands parameter `Γ →* H^∨ ⋊ Γ` projecting to
  the identity of `Γ` is a crossed cocycle with values in the dual group `H^∨`.
* `TauCeti/GroupTheory/CrossedCocycle/NonabelianH1.lean` identifies the continuous crossed
  cocycles, for topological groups and an action `α` agreeing with a `MulDistribMulAction`, with
  the cocycles of `TauCeti.NonabelianH1`. When `Γ` is discrete every crossed cocycle is
  continuous, so all crossed cocycles are cocycles of `TauCeti.NonabelianH1`.

## Main definitions

* `TauCeti.CrossedCocycle α`: the crossed cocycles for the action `α : Γ →* MulAut H`.
* `TauCeti.CrossedCocycle.instMulAction`: the gauge action of `H`.
* `TauCeti.CrossedCocycle.map`: change of coefficients along an equivariant homomorphism.
* `TauCeti.CrossedCocycle.equivMonoidHom`: for the trivial action, crossed cocycles are
  homomorphisms.
* `TauCeti.CrossedCocycle.conjInv`: the crossed cocycle `γ ↦ γ⁻¹` for conjugation.

## Main results

* `TauCeti.CrossedCocycle.map_smul`: change of coefficients commutes with gauge.
* `TauCeti.CrossedCocycle.map_id` and `TauCeti.CrossedCocycle.map_map`: change of coefficients
  is functorial.

## References

* J.-F. Dat, D. Helm, R. Kurinczuk, G. Moss, *Moduli of Langlands parameters*, §1.2 and §2.1.
* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VIII.1.1.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.1.
-/

public section

namespace TauCeti

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
  refine (mul_eq_one_iff_eq_inv.mp ?_).trans (map_inv (α γ⁻¹) (c γ)).symm
  simpa using (c.apply_mul γ⁻¹ γ).symm

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

/-- Change of coefficients along the identity does nothing. -/
@[simp]
theorem map_id (c : CrossedCocycle α) : c.map (MonoidHom.id H) (fun _ _ ↦ rfl) = c :=
  ext fun _ ↦ by simp

/-- Successive changes of coefficients agree with the change along the composite. -/
@[simp]
theorem map_map (f : H →* H') (hf : ∀ γ x, f (α γ x) = α' γ (f x)) (g : H' →* H'')
    (hg : ∀ γ x, g (α' γ x) = α'' γ (g x)) (c : CrossedCocycle α) :
    (c.map f hf).map g hg = c.map (g.comp f) (fun γ x ↦ by simp [hf, hg]) :=
  ext fun _ ↦ by simp

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
      map_mul' γ δ := by rw [c.apply_mul, MonoidHom.one_apply, MulAut.one_apply] }
  invFun f := ⟨f, fun γ δ ↦ by rw [map_mul, MonoidHom.one_apply, MulAut.one_apply]⟩
  left_inv c := ext fun _ ↦ by simp only [coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  right_inv f := MonoidHom.ext fun _ ↦ by simp only [coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

@[simp]
theorem equivMonoidHom_apply (c : CrossedCocycle (1 : Γ →* MulAut H)) (γ : Γ) :
    equivMonoidHom c γ = c γ :=
  (rfl)

@[simp]
theorem equivMonoidHom_symm_apply (f : Γ →* H) (γ : Γ) : equivMonoidHom.symm f γ = f γ :=
  (rfl)

/-! ### The conjugation action -/

/-- A group acting on itself by conjugation has the crossed cocycle `γ ↦ γ⁻¹`. -/
def conjInv (G : Type*) [Group G] : CrossedCocycle (MulAut.conj : G →* MulAut G) where
  toFun γ := γ⁻¹
  map_mul' γ δ := by simp [mul_assoc]

@[simp]
theorem conjInv_apply {G : Type*} [Group G] (γ : G) : conjInv G γ = γ⁻¹ :=
  (rfl)

end CrossedCocycle

end TauCeti
