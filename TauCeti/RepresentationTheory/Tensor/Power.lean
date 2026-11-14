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
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Tensor.Pi.Basic

/-!
# Tensor powers of representations

This file equips the tensor power of a representation with its diagonal action. The action on a
pure tensor applies the original action in every factor. Concatenation of tensor factors is an
equivalence of representations, so the character of a tensor power is the corresponding power of
the character.

## Main definitions

* `Representation.tensorPower` is the diagonal action on `⨂[R]^d M`.
* `FDRep.tensorPower` is its bundled finite-dimensional form.
* `Representation.oneEquivTensorPower`, `Representation.tensorPowerAddEquiv`, and
  `Representation.tensorPowerSuccEquiv` identify the `1`-st, `(d + e)`-th, and `(n + 1)`-th
  tensor-power representations.
* `FDRep.tensorPowerZeroIsoTensorUnit` and `FDRep.tensorPowerSuccIso` are the bundled `FDRep`
  isomorphisms `V.tensorPower 0 ≅ 𝟙_ (FDRep k G)` and
  `V.tensorPower (n + 1) ≅ V ⊗ V.tensorPower n`.

## Main results

* `Representation.char_tensorPower` and `FDRep.char_tensorPower`: the character of the `d`-th
  tensor power is the `d`-th power of the character.
-/

public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation: the tensor
product `Representation.piTensorProduct` of `d` copies of `ρ`. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) :=
  piTensorProduct fun _ : Fin d => ρ

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g :=
  piTensorProduct_apply _ g

/-- The action on the zero-fold tensor power is the identity.

This is intentionally not a simp lemma: `tensorPower_apply` followed by
`TauCeti.PiTensorProduct.map_of_isEmpty` already performs this simplification. -/
theorem tensorPower_zero_apply (ρ : Representation R G M) (g : G) :
    ρ.tensorPower 0 g = LinearMap.id := by
  simp

/-- A representation is equivalent to its `1`-fold tensor power via
`(TauCeti.TensorPower.oneEquiv R M).symm`. -/
noncomputable def oneEquivTensorPower (ρ : Representation R G M) :
    ρ.Equiv (ρ.tensorPower 1) :=
  .mk (TauCeti.TensorPower.oneEquiv R M).symm fun g => by
    simpa only [tensorPower_apply] using TauCeti.TensorPower.oneEquiv_symm_comp (ρ g)

@[simp]
theorem toLinearEquiv_oneEquivTensorPower (ρ : Representation R G M) :
    ρ.oneEquivTensorPower.toLinearEquiv = (TauCeti.TensorPower.oneEquiv R M).symm :=
  (rfl)

/-- Splitting the factors gives an equivalence from the tensor product of two tensor-power
representations to the tensor power indexed by their sum. -/
noncomputable def tensorPowerAddEquiv (ρ : Representation R G M) (d e : ℕ) :
    ((ρ.tensorPower d).tprod (ρ.tensorPower e)).Equiv (ρ.tensorPower (d + e)) :=
  .mk TensorPower.mulEquiv fun g => by
    simpa only [tprod_apply, tensorPower_apply] using
      TauCeti.TensorPower.mulEquiv_comp_map_const d e (ρ g)

@[simp]
theorem toLinearEquiv_tensorPowerAddEquiv (ρ : Representation R G M) (d e : ℕ) :
    (ρ.tensorPowerAddEquiv d e).toLinearEquiv = TensorPower.mulEquiv :=
  (rfl)

/-- Reindexing the exponent along `h : d = e` gives an equivalence of tensor-power
representations via `TensorPower.cast`. -/
noncomputable def tensorPowerCastEquiv (ρ : Representation R G M) {d e : ℕ} (h : d = e) :
    (ρ.tensorPower d).Equiv (ρ.tensorPower e) :=
  .mk (TensorPower.cast R M h) fun g => by
    subst h
    ext x
    simp

@[simp]
theorem toLinearEquiv_tensorPowerCastEquiv (ρ : Representation R G M) {d e : ℕ} (h : d = e) :
    (ρ.tensorPowerCastEquiv h).toLinearEquiv = TensorPower.cast R M h :=
  (rfl)

/-- Splitting off the first factor identifies the `(n + 1)`-fold tensor-power representation with
`ρ.tprod (ρ.tensorPower n)`. -/
noncomputable def tensorPowerSuccEquiv (ρ : Representation R G M) (n : ℕ) :
    (ρ.tensorPower (n + 1)).Equiv (ρ.tprod (ρ.tensorPower n)) :=
  (ρ.tensorPowerCastEquiv (Nat.add_comm n 1)).trans
    ((ρ.tensorPowerAddEquiv 1 n).symm.trans
      (ρ.oneEquivTensorPower.symm.tprod (Equiv.refl (ρ.tensorPower n))))

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
    rw [← char_iso (ρ.tensorPowerAddEquiv d 1), char_tensor, Pi.mul_apply, ih,
      ← char_iso ρ.oneEquivTensorPower, pow_succ]

end Field

end Representation

namespace FDRep

open CategoryTheory MonoidalCategory

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The diagonal action on the `n`-fold tensor power of a finite-dimensional representation.
The zero-fold power is one-dimensional, including when the original representation is zero. -/
noncomputable def tensorPower (V : FDRep k G) (n : ℕ) : FDRep k G :=
  FDRep.of (Representation.tensorPower V.ρ n)

/-- The bundled tensor power is the unbundled tensor-power action, bundled.
Together with `FDRep.of_ρ'`, this recovers the action without unfolding `tensorPower`. -/
theorem tensorPower_def (V : FDRep k G) (n : ℕ) :
    V.tensorPower n = FDRep.of (Representation.tensorPower V.ρ n) :=
  (rfl)

/-- `V.tensorPower 0` is isomorphic in `FDRep k G` to the monoidal unit `𝟙_ (FDRep k G)`. -/
noncomputable def tensorPowerZeroIsoTensorUnit (V : FDRep k G) :
    V.tensorPower 0 ≅ 𝟙_ (FDRep k G) :=
  eqToIso (tensorPower_def V 0) ≪≫
    (PiTensorProduct.isEmptyEquiv (Fin 0)).toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ', FDRep.tensorUnit_ρ, Representation.tensorPower_zero_apply,
        LinearMap.id_apply, LinearMap.id_apply]

@[simp]
theorem isoToLinearEquiv_tensorPowerZeroIsoTensorUnit (V : FDRep k G) :
    isoToLinearEquiv V.tensorPowerZeroIsoTensorUnit =
      (isoToLinearEquiv (eqToIso (tensorPower_def V 0))).trans
        (PiTensorProduct.isEmptyEquiv (Fin 0)) := by
  simp [tensorPowerZeroIsoTensorUnit]

/-- `V.tensorPower (n + 1)` is isomorphic in `FDRep k G` to `V ⊗ V.tensorPower n`. -/
noncomputable def tensorPowerSuccIso (V : FDRep k G) (n : ℕ) :
    V.tensorPower (n + 1) ≅ (V ⊗ V.tensorPower n : FDRep k G) :=
  let e : _root_.Representation.Equiv (Representation.tensorPower V.ρ (n + 1))
      ((V ⊗ FDRep.of (Representation.tensorPower V.ρ n) : FDRep k G)).ρ :=
    (Representation.tensorPowerSuccEquiv V.ρ n).trans
      (FDRep.tensorEquivTprod V (FDRep.of (Representation.tensorPower V.ρ n))).symm
  eqToIso (tensorPower_def V (n + 1)) ≪≫
    (e.toLinearEquiv.toFDRepIso fun g x ↦ by
      rw [FDRep.of_ρ']
      exact LinearMap.congr_fun (e.isIntertwining' g) x) ≪≫
    whiskerLeftIso V (eqToIso (tensorPower_def V n)).symm

@[simp]
theorem isoToLinearEquiv_tensorPowerSuccIso (V : FDRep k G) (n : ℕ) :
    isoToLinearEquiv (V.tensorPowerSuccIso n) =
      (isoToLinearEquiv (eqToIso (tensorPower_def V (n + 1)))).trans
        ((Representation.tensorPowerSuccEquiv V.ρ n).toLinearEquiv.trans
          (isoToLinearEquiv (whiskerLeftIso V (eqToIso (tensorPower_def V n)).symm))) := by
  ext x
  simp only [tensorPowerSuccIso, isoToLinearEquiv_trans, isoToLinearEquiv_toFDRepIso,
    LinearEquiv.trans_apply, _root_.Representation.Equiv.toLinearEquiv_apply,
    _root_.Representation.Equiv.coe_toIntertwiningMap]
  refine congrArg (isoToLinearEquiv (whiskerLeftIso V (eqToIso (tensorPower_def V n)).symm)) ?_
  exact (_root_.Representation.Equiv.trans_apply (Representation.tensorPowerSuccEquiv V.ρ n)
    (V.tensorEquivTprod (FDRep.of (Representation.tensorPower V.ρ n))).symm _).trans
    (FDRep.tensorEquivTprod_symm_apply V (FDRep.of (Representation.tensorPower V.ρ n)) _)

/-- The character of the bundled tensor power is the corresponding power of the character. -/
@[simp]
theorem char_tensorPower (V : FDRep k G) (n : ℕ) (g : G) :
    (V.tensorPower n).character g = V.character g ^ n := by
  rw [tensorPower_def, character_of, Representation.char_tensorPower, character_ρ]

end FDRep
