/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.PiTensorProduct.Map
public import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Tensor powers of representations

This file equips the tensor power of a representation with its diagonal action. The action on a
pure tensor applies the original action in every factor. Concatenation of tensor factors is an
equivalence of representations, so the character of a tensor power is the corresponding power of
the character.

## Main definitions

* `Representation.tensorPower` is the diagonal action on `⨂[R]^d M`.
* `Representation.tensorPowerAddEquiv` identifies the tensor product of the `d`-th and `e`-th
  tensor-power representations with the `(d + e)`-th one.

## Main results

* `Representation.char_tensorPower`: the character of the `d`-th tensor power is the `d`-th
  power of the character.
-/

public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun _ : Fin d => ρ)

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g := by
  rfl

/-- The action on the zero-fold tensor power is the identity.

This is intentionally not a simp lemma: `tensorPower_apply` followed by
`TauCeti.PiTensorProduct.map_of_isEmpty` already performs this simplification. -/
theorem tensorPower_zero_apply (ρ : Representation R G M) (g : G) :
    ρ.tensorPower 0 g = LinearMap.id := by
  simp

/-- Splitting the factors gives an equivalence from the tensor product of two tensor-power
representations to the tensor power indexed by their sum. -/
noncomputable def tensorPowerAddEquiv (ρ : Representation R G M) (d e : ℕ) :
    ((ρ.tensorPower d).tprod (ρ.tensorPower e)).Equiv (ρ.tensorPower (d + e)) :=
  .mk TensorPower.mulEquiv fun g => by
    have h : Fin.append (fun _ : Fin d => ρ g) (fun _ : Fin e => ρ g) = fun _ => ρ g :=
      Fin.append_castAdd_natAdd (f := fun _ : Fin (d + e) => ρ g)
    simpa only [tprod_apply, tensorPower_apply, h] using
      TauCeti.TensorPower.mulEquiv_comp_map (fun _ : Fin d => ρ g) (fun _ : Fin e => ρ g)

end CommSemiring

section Field

variable [Field R] [Monoid G] [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The character of a tensor-power representation is the corresponding power of the character. -/
@[simp]
theorem char_tensorPower (ρ : Representation R G M) (d : ℕ) (g : G) :
    (ρ.tensorPower d).character g = (ρ.character g) ^ d := by
  induction d with
  | zero =>
    rw [character, tensorPower_zero_apply, LinearMap.trace_id,
      (PiTensorProduct.isEmptyEquiv (Fin 0)).finrank_eq, Module.finrank_self, Nat.cast_one,
      pow_zero]
  | succ d ih =>
    have h_one : (ρ.tensorPower 1).character g = ρ.character g := by
      rw [character, character, ← LinearMap.trace_conj' _ (TauCeti.TensorPower.oneEquiv R M)]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply]
    rw [← char_iso (ρ.tensorPowerAddEquiv d 1), char_tensor, Pi.mul_apply, ih, h_one, pow_succ]

end Field

end Representation
