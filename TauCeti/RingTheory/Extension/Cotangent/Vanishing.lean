/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Vanishing of the cotangent module of an extension

For an extension `P` of `S` over `R`, the cotangent module `P.Cotangent` is `I / I²` for the kernel
`I` of `P.Ring → S`.

* `Algebra.Extension.lTensor_cotangentComplex_eq_zero`: the base change to `κ` of the cotangent
  complex of `P` vanishes when the kernel of `P` lies in the square of the kernel of
  `P.Ring → κ`.
* `Algebra.Extension.isIdempotentElem_ker_of_subsingleton_cotangent`: the kernel of `P` is
  idempotent when the cotangent module of `P` vanishes.
-/

public section

open TensorProduct

namespace Algebra.Extension

/-- The base change to `κ` of the cotangent complex of an extension vanishes when the kernel of the
extension lies in the square of the kernel of `P.Ring → κ`. -/
theorem lTensor_cotangentComplex_eq_zero {R S κ : Type*} [CommRing R] [CommRing S]
    [CommRing κ] [Algebra R S] [Algebra S κ]
    (P : Algebra.Extension R S) [Algebra P.Ring κ] [IsScalarTower P.Ring S κ]
    (h : ∀ x ∈ P.ker, x ∈ RingHom.ker (algebraMap P.Ring κ) ^ 2) :
    P.cotangentComplex.lTensor κ = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a m =>
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P) m
    have hxsq : (x : P.Ring) ∈ RingHom.ker (algebraMap P.Ring κ) ^ 2 := h x x.property
    let xg : RingHom.ker (algebraMap P.Ring κ) :=
      ⟨x, Ideal.pow_le_self two_ne_zero hxsq⟩
    have hxzero : (RingHom.ker (algebraMap P.Ring κ)).toCotangent xg = 0 :=
      (Ideal.toCotangent_eq_zero _ xg).2 hxsq
    have hdx : (1 : κ) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (x : P.Ring) = 0 := by
      simpa only [xg, map_zero, KaehlerDifferential.kerCotangentToTensor_toCotangent] using
        congrArg (KaehlerDifferential.kerCotangentToTensor R P.Ring κ) hxzero
    rw [LinearMap.lTensor_tmul, P.cotangentComplex_mk]
    -- `Extension.CotangentSpace` is an abbreviation for this nested tensor product; exposing
    -- it is necessary to apply the associativity equivalence `cancelBaseChange` below.
    change a ⊗ₜ[S] (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (x : P.Ring)) = 0
    apply (AlgebraTensorModule.cancelBaseChange P.Ring S κ κ
      (KaehlerDifferential R P.Ring)).injective
    simpa only [map_zero, AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_zero] using
      congrArg (a • ·) hdx

/-- The kernel of an extension is idempotent when the cotangent module of the extension vanishes. -/
theorem isIdempotentElem_ker_of_subsingleton_cotangent {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (P : Algebra.Extension R S) (h : Subsingleton P.Cotangent) :
    IsIdempotentElem P.ker := by
  have hcotangentKer : Subsingleton P.ker.Cotangent := by
    constructor
    intro x y
    apply P.cotangentEquivCotangentKer.symm.injective
    exact Subsingleton.elim _ _
  exact (Ideal.cotangent_subsingleton_iff (I := P.ker)).mp hcotangentKer

end Algebra.Extension
