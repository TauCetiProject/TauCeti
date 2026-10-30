/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The local rings of the fibre ring

For a prime `p` of `R` and a prime `Q` of the fibre ring `κ(p) ⊗[R] B` lying over the prime `q`
of `B`, Mathlib's `Ideal.Fiber.algEquivAux₂` identifies the local ring `(κ(p) ⊗[R] B)_Q` with
`B_q ⧸ p B_q`. This file records that this identification is compatible with the maps from `B`.

## Main results

* `Ideal.Fiber.algEquivAux₂_algebraMap_one_tmul`: `Ideal.Fiber.algEquivAux₂` sends `1 ⊗ b` to the
  class of `b`.
-/

public section

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

namespace Ideal.Fiber

open Algebra.TensorProduct

variable (p : Ideal R) [p.IsPrime]

/-- The isomorphism `(κ(p) ⊗[R] B)_Q ≃ B_q ⧸ p B_q` of `Ideal.Fiber.algEquivAux₂`, where `q` is
the prime of `B` under `Q`, is compatible with the maps from `B`: it sends `1 ⊗ b` to the class
of `b`. -/
@[simp]
theorem algEquivAux₂_algebraMap_one_tmul (Q : Ideal (p.Fiber B)) [Q.IsPrime] (b : B) :
    algEquivAux₂ p Q (algebraMap _ (Localization.AtPrime Q) ((1 : p.ResidueField) ⊗ₜ[R] b)) =
      Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime (Q.comap includeRight)) b) := by
  -- `algEquivAux₂` is the restriction of scalars to `R` of a composite of `B`-algebra
  -- isomorphisms; rebuild that composite, with the local instances of its definition, and use
  -- that it commutes with the maps from `B`.
  let : Algebra B (p.Fiber B) := rightAlgebra
  let Bp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  let pB := p.map (algebraMap R B)
  let r := Q.comap includeRight
  let e₁ : p.Fiber B ≃ₐ[B] Bp ⧸ pB.map (algebraMap B Bp) := algEquivAux₁ p
  let Q' : Ideal (Bp ⧸ pB.map (algebraMap B Bp)) := Q.comap e₁.symm
  have : (Q'.under (B ⧸ pB)).LiesOver r := Ideal.under_liesOver_of_liesOver _ Q' (Q.under B)
  have : Algebra.algebraMapSubmonoid (B ⧸ pB) r.primeCompl = (Q'.under (B ⧸ pB)).primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective _ r Ideal.Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ pB) r.primeCompl)
      (Localization.AtPrime Q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (B ⧸ pB) (Algebra.algebraMapSubmonoid B p.primeCompl))
      (Localization.AtPrime Q') Q'
  have := IsScalarTower.to₁₃₄ B (B ⧸ pB) (Bp ⧸ pB.map (algebraMap B Bp)) (Localization.AtPrime Q')
  exact ((Localization.localAlgEquiv Q' Q e₁.symm rfl).symm.trans
    ((IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (B ⧸ pB) r.primeCompl)
      (Localization.AtPrime Q') (Localization.AtPrime r ⧸ pB.map (algebraMap B _))).restrictScalars
        B)).commutes b

end Ideal.Fiber
