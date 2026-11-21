/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Sigma
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Sigma

/-!
# Linear independence in dependent products

This file records the `LinearIndepOn` companion of `Pi.linearIndependent_single`: a family of
one-point vectors `Pi.single p.1 (v p.1 p.2)` is linearly independent on a sigma set `t.sigma s`
if and only if each coordinate family `v c` is linearly independent on `s c` for `c ∈ t`.
-/

public section

namespace Pi

/-- A family of one-point vectors `Pi.single p.1 (v p.1 p.2)` is linearly independent on
`t.sigma s` if and only if each coordinate family `v c` is linearly independent on `s c` for
`c ∈ t`. This is the `LinearIndepOn` companion of `Pi.linearIndependent_single`. -/
theorem linearIndepOn_single_iff {R κ : Type*} [Semiring R] [DecidableEq κ]
    {ι M : κ → Type*} [∀ c, AddCommMonoid (M c)] [∀ c, Module R (M c)]
    (v : ∀ c, ι c → M c) {t : Set κ} {s : ∀ c, Set (ι c)} :
    LinearIndepOn R (fun p : Σ c, ι c ↦ Pi.single p.1 (v p.1 p.2)) (t.sigma s) ↔
      ∀ c ∈ t, LinearIndepOn R (v c) (s c) := by
  constructor
  · intro h c hc
    let g : s c → t.sigma s := fun i ↦ (Equiv.Set.sigma t s).symm ⟨⟨c, hc⟩, i⟩
    have hg : Function.Injective g :=
      (Equiv.Set.sigma t s).symm.injective.comp fun _ _ h' ↦ by simpa using h'
    exact (h.comp g hg).of_comp (LinearMap.single R M c)
  · intro hli
    let res : (∀ c : κ, M c) →ₗ[R] (∀ c : t, M c) :=
      { toFun := fun x c ↦ x c.val
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine LinearIndependent.of_comp res ?_
    convert (Pi.linearIndependent_single (fun (c : t) (i : s c) ↦ v c.val i.val)
      fun c ↦ hli c.val c.property).comp (Equiv.Set.sigma t s) (Equiv.Set.sigma t s).injective
    ext ⟨⟨c, i⟩, h⟩ d
    dsimp only [Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, res]
    have heq : (Equiv.Set.sigma t s) ⟨⟨c, i⟩, h⟩ = ⟨⟨c, h.1⟩, ⟨i, h.2⟩⟩ := rfl
    rw [heq]
    by_cases hdc : d = ⟨c, h.1⟩
    · subst hdc
      simp
    · simp [Pi.single_eq_of_ne (mt Subtype.ext hdc), Pi.single_eq_of_ne hdc]

end Pi
