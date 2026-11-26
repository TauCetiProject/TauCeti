/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Morphism
public import TauCeti.LinearAlgebra.SymmetricAlgebra.RankOne
import TauCeti.Algebra.Bialgebra.Primitive

/-!
# The Frobenius kernel `αₚ` is unipotent

Over a base ring `R` of prime characteristic `p`, the coordinate Hopf algebra of `αₚ` is
`R[x] / (xᵖ)` (`TauCeti.AlphaP.CoordinateRing`). Write `[x]` for the class of `x`. This file shows
that the coordinate ring is free with basis `1, [x], …, [x]ᵖ⁻¹` (`TauCeti.AlphaP.powerBasis`,
transported from `AdjoinRoot (Xᵖ)`), and that the `R`-linear map `R[x] / (xᵖ) → R[x]` sending
`[x]ⁱ` to `xⁱ` for `i < p` (`TauCeti.AlphaP.truncation`) is an injective coalgebra map sending `1`
to `1` (`TauCeti.AlphaP.truncationCoalgHom`). It is not multiplicative, but it preserves the
comultiplication because `Δ(xⁿ) = ∑ (n choose i) xⁱ ⊗ xⁿ⁻ⁱ` only involves exponents at most `n`.

So the coalgebra of `αₚ` is the subcoalgebra `span {1, x, …, xᵖ⁻¹}` of the coalgebra of `𝔾ₐ`.
Over a field `k` of characteristic `p`, every `αₚ`-comodule is then a `𝔾ₐ`-comodule with the
same fixed vectors, and since `𝔾ₐ` is unipotent
(`TauCeti.AdditiveGroup.unipotentCommHopfAlgProperty_coordinateHopfAlgebra`), so is `αₚ`
(`TauCeti.AlphaP.unipotentCommHopfAlgProperty_coordinateRing`). Together with
`TauCeti.AlphaP.coordinateRing_not_isReduced` this is the roadmap Check that `αₚ` is unipotent
and not smooth.

## Main definitions

* `TauCeti.AlphaP.powerBasis`: the power basis `1, [x], …, [x]ᵖ⁻¹` of `R[x] / (xᵖ)`.
* `TauCeti.AlphaP.truncationCoalgHom`: the coalgebra map `R[x] / (xᵖ) → R[x]`, `[x]ⁱ ↦ xⁱ`.

## Main results

* `TauCeti.AlphaP.truncationCoalgHom_injective`: the coalgebra map is injective.
* `TauCeti.AlphaP.unipotentCommHopfAlgProperty_coordinateRing`: `αₚ` is unipotent.
-/

public section

open Polynomial SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti

namespace AlphaP

universe u

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The coordinate ring of `αₚ` is `AdjoinRoot (Xᵖ)`, through the identification of the
coordinate ring of `𝔾ₐ` with the polynomial ring. -/
noncomputable def coordinateRingEquivAdjoinRoot :
    CoordinateRing (R := R) p ≃ₐ[R] AdjoinRoot (X ^ p : R[X]) :=
  Ideal.quotientEquivAlg _ _ SymmetricAlgebra.equivPolynomial <| by
    rw [hopfIdeal_toIdeal, Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {X ^ p} = _
    rw [← equivPolynomial_ι_one (R := R)]
    rfl

/-- **The power basis `1, [x], …, [x]ᵖ⁻¹` of the coordinate ring of `αₚ`.** -/
noncomputable def powerBasis : PowerBasis R (CoordinateRing (R := R) p) :=
  (AdjoinRoot.powerBasis' (monic_X_pow p)).map (coordinateRingEquivAdjoinRoot p).symm

/-- The generator of `TauCeti.AlphaP.powerBasis` is the class of `x`. -/
theorem powerBasis_gen :
    (powerBasis (R := R) p).gen =
      Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal (ι R R 1 : SymmetricAlgebra R R) := by
  rw [powerBasis, PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen, AlgEquiv.symm_apply_eq]
  change AdjoinRoot.root _ = AdjoinRoot.mk _ (equivPolynomial (ι R R 1))
  rw [equivPolynomial_ι_one, AdjoinRoot.mk_X]

/-- The power basis of the coordinate ring of `αₚ` has `p` elements. -/
theorem powerBasis_dim : (powerBasis (R := R) p).dim = p := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out (p := p.Prime)).ne_one
  rw [powerBasis, PowerBasis.map_dim, AdjoinRoot.powerBasis'_dim, natDegree_X_pow]

/-- The class of `xⁿ`, for `n < p`, is a vector of the power basis. -/
private theorem mk_pow_eq_basis {n : ℕ} (hn : n < p) :
    Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal ((ι R R 1 : SymmetricAlgebra R R) ^ n) =
      (powerBasis (R := R) p).basis ⟨n, (powerBasis_dim (R := R) p).symm ▸ hn⟩ := by
  rw [PowerBasis.coe_basis, map_pow, powerBasis_gen]

/-- The `R`-linear map `R[x] / (xᵖ) → R[x]` sending `[x]ⁱ` to `xⁱ` for `i < p`. -/
noncomputable def truncation : CoordinateRing (R := R) p →ₗ[R] SymmetricAlgebra R R :=
  (powerBasis (R := R) p).basis.constr R fun i ↦ (ι R R 1 : SymmetricAlgebra R R) ^ (i : ℕ)

/-- The truncation map sends the class of `xⁿ`, for `n < p`, to `xⁿ`. -/
theorem truncation_mk_pow {n : ℕ} (hn : n < p) :
    truncation p (Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal
      ((ι R R 1 : SymmetricAlgebra R R) ^ n)) = (ι R R 1 : SymmetricAlgebra R R) ^ n := by
  rw [mk_pow_eq_basis p hn, truncation, Module.Basis.constr_basis]

/-- The truncation map is a section of the quotient map `R[x] → R[x] / (xᵖ)`. -/
theorem mk_truncation (a : CoordinateRing (R := R) p) :
    Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal (truncation p a) = a := by
  refine LinearMap.congr_fun ((powerBasis (R := R) p).basis.ext
    (f₁ := (Ideal.Quotient.mkₐ R (hopfIdeal (R := R) p).toIdeal).toLinearMap ∘ₗ truncation p)
    (f₂ := LinearMap.id) fun i ↦ ?_) a
  have hi : (i : ℕ) < p := i.isLt.trans_eq (powerBasis_dim (R := R) p)
  rw [LinearMap.comp_apply, LinearMap.id_apply, ← mk_pow_eq_basis p hi, AlgHom.toLinearMap_apply,
    truncation_mk_pow p hi, Ideal.Quotient.mkₐ_eq_mk]

/-- The truncation map is injective. -/
theorem truncation_injective : Function.Injective (truncation (R := R) p) :=
  Function.LeftInverse.injective (g := Ideal.Quotient.mk _) (mk_truncation p)

/-- The truncation map sends `1` to `1`. -/
theorem truncation_one : truncation (R := R) p 1 = 1 := by
  have h := truncation_mk_pow (R := R) p (n := 0) (Fact.out (p := p.Prime)).pos
  rwa [pow_zero, map_one] at h

/-- **The coalgebra of `αₚ` is a subcoalgebra of the coalgebra of `𝔾ₐ`**: the truncation map
`R[x] / (xᵖ) → R[x]`, `[x]ⁱ ↦ xⁱ` for `i < p`, preserves the counit and the comultiplication. -/
@[expose] noncomputable def truncationCoalgHom :
    CoordinateRing (R := R) p →ₗc[R] SymmetricAlgebra R R where
  toLinearMap := truncation p
  counit_comp := (powerBasis (R := R) p).basis.ext fun i ↦ by
    have hi : (i : ℕ) < p := i.isLt.trans_eq (powerBasis_dim (R := R) p)
    rw [LinearMap.comp_apply, ← mk_pow_eq_basis p hi, truncation_mk_pow p hi,
      Bialgebra.Quotient.counit_mk]
  map_comp_comul := (powerBasis (R := R) p).basis.ext fun i ↦ by
    have hi : (i : ℕ) < p := i.isLt.trans_eq (powerBasis_dim (R := R) p)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← mk_pow_eq_basis p hi,
      truncation_mk_pow p hi, Bialgebra.Quotient.comul_mk, ← LinearMap.comp_apply
        (TensorProduct.map _ _), ← TensorProduct.map_comp,
      TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R R 1)]
    simp only [map_sum, map_nsmul, TensorProduct.map_tmul, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    refine Finset.sum_congr rfl fun mn hmn ↦ ?_
    have hmn' := Finset.mem_antidiagonal.mp hmn
    rw [truncation_mk_pow p (by omega), truncation_mk_pow p (by omega)]

@[simp]
theorem truncationCoalgHom_apply (a : CoordinateRing (R := R) p) :
    truncationCoalgHom p a = truncation p a :=
  rfl

/-- The coalgebra map `R[x] / (xᵖ) → R[x]` is injective. -/
theorem truncationCoalgHom_injective : Function.Injective (truncationCoalgHom (R := R) p) :=
  truncation_injective p

/-- **`αₚ` is unipotent**: over a field `k` of characteristic `p`, every nonzero representation of
`αₚ` has a nonzero fixed vector. Its coalgebra embeds in that of the unipotent group `𝔾ₐ` by a
map sending `1` to `1`. -/
theorem unipotentCommHopfAlgProperty_coordinateRing (k : Type u) [Field k] [CharP k p] :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k (CoordinateRing (R := k) p)) :=
  (AdditiveGroup.unipotentCommHopfAlgProperty_coordinateHopfAlgebra k).of_coalgHom_injective
    (truncationCoalgHom p) (truncationCoalgHom_injective p) (truncation_one p)

end AlphaP

end TauCeti
