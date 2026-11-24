/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Basic
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat base change of regular class functions

For a commutative Hopf algebra `H` over a commutative ring `R` and a flat `R`-algebra `S`, the
regular class functions of the base change `S ⊗[R] H` over `S` are the scalar extension of the
class functions of `H`: the natural map `S ⊗[R] C(H) → C(S ⊗[R] H)` is an isomorphism
(`TauCeti.HopfAlgebra.classFunctionsBaseChangeEquiv`). Geometrically, formation of the conjugacy
quotient commutes with flat base change. This is what lets statements about class functions be
checked after extending the ground field.

The coordinate map of conjugation of `S ⊗[R] H` is the scalar extension of that of `H`
(`TauCeti.HopfAlgebra.baseChangeTensorAlgEquiv_symm_comp_conjugationAlgHom`). The class
functions of `S ⊗[R] H` are then the equalizer of two scalar-extended algebra maps, and an
equalizer of `R`-linear maps commutes with flat scalar extension (`AlgHom.tensorEqualizerEquiv`).

## Main declarations

* `TauCeti.HopfAlgebra.classFunctions_baseChange_eq_equalizer`: the class functions of the base
  change as an equalizer of scalar-extended maps.
* `TauCeti.HopfAlgebra.classFunctionsBaseChangeEquiv`: the isomorphism
  `S ⊗[R] C(H) ≃ C(S ⊗[R] H)` for flat `S`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3 (invariants and flat base
  change).
-/

public section

open TensorProduct
open TauCeti.Algebra.TensorProduct (baseChangeTensorAlgEquiv
  baseChangeTensorAlgEquiv_symm_comp_includeRight)

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {S : Type w} {H : Type v}

section Semiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring H] [_root_.HopfAlgebra R H]

/-- The class functions of the base change `S ⊗[R] H` are the equalizer of the scalar extensions
of the coordinate map of conjugation of `H` and of the second-factor inclusion. -/
theorem classFunctions_baseChange_eq_equalizer :
    classFunctions S (S ⊗[R] H) =
      AlgHom.equalizer
        (Algebra.TensorProduct.map (AlgHom.id S S) (conjugationAlgHom (R := R) (H := H)))
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))) := by
  ext z
  rw [mem_classFunctions_iff, AlgHom.mem_equalizer,
    ← baseChangeTensorAlgEquiv_symm_comp_conjugationAlgHom,
    ← baseChangeTensorAlgEquiv_symm_comp_includeRight]
  simp

/-- A class function of `H`, extended by scalars, is a class function of `S ⊗[R] H`. -/
theorem tmul_mem_classFunctions_baseChange (s : S) {f : H} (hf : f ∈ classFunctions R H) :
    s ⊗ₜ[R] f ∈ classFunctions S (S ⊗[R] H) := by
  rw [classFunctions_baseChange_eq_equalizer]
  simp [mem_classFunctions_iff.mp hf]

end Semiring

section Ring

variable [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [_root_.HopfAlgebra R H]
variable [Module.Flat R S]

variable (R S H) in
/-- **Class functions commute with flat base change.** For a flat `R`-algebra `S`, the natural
map `S ⊗[R] C(H) → C(S ⊗[R] H)` from the scalar extension of the class functions of `H` to the
class functions of `S ⊗[R] H` over `S` is an isomorphism. -/
noncomputable def classFunctionsBaseChangeEquiv :
    S ⊗[R] classFunctions R H ≃ₐ[S] classFunctions S (S ⊗[R] H) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
      (Subalgebra.equivOfEq _ _ (classFunctions_eq_equalizer R H))).trans <|
    (AlgHom.tensorEqualizerEquiv S S (conjugationAlgHom (R := R) (H := H))
      Algebra.TensorProduct.includeRight).trans
      (Subalgebra.equivOfEq _ _ classFunctions_baseChange_eq_equalizer.symm)

/-- The comparison isomorphism sends a tensor `s ⊗ f` to `s ⊗ f` in `S ⊗[R] H`. -/
@[simp]
theorem coe_classFunctionsBaseChangeEquiv_tmul (s : S) (f : classFunctions R H) :
    (classFunctionsBaseChangeEquiv R S H (s ⊗ₜ[R] f) : S ⊗[R] H) = s ⊗ₜ[R] (f : H) := by
  simp [classFunctionsBaseChangeEquiv, Subalgebra.equivOfEq_apply,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]

/-- The comparison isomorphism is the scalar extension of the inclusion `C(H) ⊆ H`. -/
theorem coe_classFunctionsBaseChangeEquiv (z : S ⊗[R] classFunctions R H) :
    (classFunctionsBaseChangeEquiv R S H z : S ⊗[R] H) =
      Algebra.TensorProduct.map (AlgHom.id S S) (classFunctions R H).val z := by
  induction z with
  | tmul s f => exact coe_classFunctionsBaseChangeEquiv_tmul s f
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]

end Ring

end HopfAlgebra

end TauCeti
