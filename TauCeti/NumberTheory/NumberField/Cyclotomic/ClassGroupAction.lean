/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv

/-!
# The Galois action on the ideal class group of a cyclotomic field

Let `K` be the `m`-th cyclotomic field over `ℚ`. Mathlib identifies `Gal(K/ℚ)` with `(ZMod m)ˣ`
through `IsCyclotomicExtension.Rat.galEquivZMod`, under which a residue `a` corresponds to the
automorphism `σ_a` with `σ_a ζ = ζ ^ a` on every `m`-th root of unity `ζ`. Transporting `σ_a` to the
ring of integers and then to ideal classes gives the covariant action `σ_a [𝔞] = [σ_a 𝔞]` of
`(ZMod m)ˣ` on `ClassGroup (𝓞 K)`. Its scalar extension to `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`,
for a ring `R` such as `ℤ_[p]`, is the Galois module in which the tame character eigenspaces of the
cyclotomic class group are cut out and on which Stickelberger elements act.

The action is covariant: no inverse is inserted, so `a` acts through `σ_a` itself and not through
`σ_a⁻¹`. Both actions are bundled as monoid homomorphisms, so the identity residue acts trivially
and products of residues act by composition (`map_one`, `map_mul`).

## Main definitions

* `TauCeti.cyclotomicClassGroupAction m K`: the action `(ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K))`.
* `TauCeti.cyclotomicClassAction R m K`: its scalar extension
  `(ZMod m)ˣ →* Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K)))`.

## Main results

* `TauCeti.cyclotomicClassGroupAction_mk0`: `σ_a` sends the class of a nonzero ideal `𝔞` to the
  class of its image `σ_a 𝔞`.
* `TauCeti.cyclotomicClassAction_tmul`: on a pure tensor, `r ⊗ c ↦ r ⊗ σ_a c`.

## References

* R. Sharifi, *Iwasawa theory*, §1.3, Propositions 1.3.1–1.3.2.
-/

public section

open NumberField IsCyclotomicExtension.Rat
open scoped TensorProduct nonZeroDivisors

namespace TauCeti

variable (R : Type*) [Ring R] (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

/-- The covariant action of `(ZMod m)ˣ ≃* Gal(K/ℚ)` on the ideal class group of the `m`-th
cyclotomic field `K`: the residue `a` acts by the class-group automorphism induced by the
automorphism `σ_a` of `𝓞 K`, where `σ_a ζ = ζ ^ a` for every `m`-th root of unity `ζ`. It is the
Galois action `classGroupAction` transported along `galEquivZMod m K`. -/
noncomputable def cyclotomicClassGroupAction : (ZMod m)ˣ →* MulAut (ClassGroup (𝓞 K)) :=
  (classGroupAction (K ≃ₐ[ℚ] K) K).comp (galEquivZMod m K).symm.toMonoidHom

variable {m K} in
/-- The residue `a` acts on ideal classes through the class-group isomorphism
`RingEquiv.classGroupEquiv` of the automorphism `σ_a = (galEquivZMod m K).symm a` of `K`. -/
theorem cyclotomicClassGroupAction_apply (a : (ZMod m)ˣ) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassGroupAction m K a c =
      ((galEquivZMod m K).symm a).toRingEquiv.classGroupEquiv c :=
  DFunLike.congr_fun (classGroupAction_apply _) c

variable {m K} in
/-- **The action on ideal classes.** The residue `a` sends the class of a nonzero ideal `𝔞` of
`𝓞 K` to the class of its image `σ_a 𝔞`. -/
@[simp]
theorem cyclotomicClassGroupAction_mk0 (a : (ZMod m)ˣ) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicClassGroupAction m K a (ClassGroup.mk0 I) = ClassGroup.mk0
      ⟨I.val.map (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingEquiv.injective _)).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ :=
  (cyclotomicClassGroupAction_apply a _).trans (RingEquiv.classGroupEquiv_mk0 _ I)

/-- **The cyclotomic class action.** The scalar extension, to `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`,
of the covariant action `cyclotomicClassGroupAction m K` of `(ZMod m)ˣ` on the ideal class group of
the `m`-th cyclotomic field `K`. The residue `a` acts by `r ⊗ c ↦ r ⊗ σ_a c`. -/
noncomputable def cyclotomicClassAction :
    (ZMod m)ˣ →* Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) where
  toFun a := LinearMap.baseChange R
    (cyclotomicClassGroupAction m K a).toAdditive.toAddMonoidHom.toIntLinearMap
  map_one' := by
    ext c
    simp
  map_mul' a b := by
    ext c
    simp

variable {R m K} in
/-- The cyclotomic class action is the scalar extension of the action on ideal classes. -/
theorem cyclotomicClassAction_apply (a : (ZMod m)ˣ) :
    cyclotomicClassAction R m K a = LinearMap.baseChange R
      (cyclotomicClassGroupAction m K a).toAdditive.toAddMonoidHom.toIntLinearMap :=
  (rfl)

variable {R m K} in
/-- **The action on pure tensors.** The residue `a` sends `r ⊗ c` to `r ⊗ σ_a c`. -/
@[simp]
theorem cyclotomicClassAction_tmul (a : (ZMod m)ˣ) (r : R) (c : ClassGroup (𝓞 K)) :
    cyclotomicClassAction R m K a (r ⊗ₜ Additive.ofMul c) =
      r ⊗ₜ Additive.ofMul (cyclotomicClassGroupAction m K a c) := by
  simp [cyclotomicClassAction_apply]

end TauCeti
