/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.PowerBasis
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Morphism
import TauCeti.Algebra.Bialgebra.Primitive

/-!
# The Frobenius kernel `αₚ` is unipotent

Over a base ring `R` of prime characteristic `p`, the coordinate Hopf algebra of `αₚ` is
`R[x] / (xᵖ)` (`TauCeti.AlphaP.CoordinateRing`), free with basis `1, [x], …, [x]ᵖ⁻¹`
(`TauCeti.AlphaP.powerBasis`), where `[x]` is the class of `x`. This file shows that the
`R`-linear map `R[x] / (xᵖ) → R[x]` sending `[x]ⁱ` to `xⁱ` for `i < p`
(`TauCeti.AlphaP.truncation`, reduction modulo `xᵖ`) is an injective coalgebra map sending `1`
to `1` (`TauCeti.AlphaP.truncationCoalgHom`). It is not multiplicative, but it preserves the
comultiplication because `Δ(xⁿ) = ∑ (n choose i) xⁱ ⊗ xⁿ⁻ⁱ` only involves exponents at most `n`.

So the coalgebra of `αₚ` is the subcoalgebra `span {1, x, …, xᵖ⁻¹}` of the coalgebra of `𝔾ₐ`.
Over a field `k` of characteristic `p`, every `αₚ`-comodule is then a `𝔾ₐ`-comodule with the
same fixed vectors, and since `𝔾ₐ` is unipotent
(`TauCeti.AdditiveGroup.unipotentCommHopfAlgProperty_coordinateHopfAlgebra`), so is `αₚ`
(`TauCeti.AlphaP.unipotentCommHopfAlgProperty_coordinateRing`). Together with
`TauCeti.AlphaP.coordinateRing_not_isReduced`, this shows that `αₚ` is unipotent but not smooth.

## Main definitions

* `TauCeti.AlphaP.truncation`: the linear map `R[x] / (xᵖ) → R[x]`, `[x]ⁱ ↦ xⁱ`.
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

/-- The `R`-linear map `R[x] / (xᵖ) → R[x]` sending `[x]ⁱ` to `xⁱ` for `i < p`: the class of `f`
goes to the remainder of `f` modulo `xᵖ` (`AdjoinRoot.modByMonicHom`). -/
noncomputable def truncation : CoordinateRing (R := R) p →ₗ[R] SymmetricAlgebra R R :=
  equivPolynomial.symm.toLinearMap ∘ₗ AdjoinRoot.modByMonicHom (monic_X_pow p) ∘ₗ
    (coordinateRingEquivAdjoinRoot (R := R) p).toLinearMap

/-- The truncation map sends `[x]ⁿ`, for `n < p`, to `xⁿ`.

The class is taken modulo `Ideal.span {x ^ p}`, the `simp` normal form of
`(hopfIdeal p).toIdeal`, as in `TauCeti.AlphaP.mk_ι_pow_eq_zero`. -/
@[simp]
theorem truncation_mk_pow {n : ℕ} (hn : n < p) :
    truncation p (Ideal.Quotient.mk (Ideal.span {(ι R R 1 : SymmetricAlgebra R R) ^ p})
      (ι R R 1 : SymmetricAlgebra R R) ^ n) = (ι R R 1 : SymmetricAlgebra R R) ^ n := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out (p := p.Prime)).ne_one
  -- Unfold `truncation`. The argument is stated over `Ideal.span {x ^ p}`, which is only
  -- definitionally the ideal of `CoordinateRing p`, so `rw` cannot unfold the composition.
  change equivPolynomial.symm (AdjoinRoot.modByMonicHom (monic_X_pow p)
    (coordinateRingEquivAdjoinRoot p
      (Ideal.Quotient.mk (Ideal.span {(ι R R 1 : SymmetricAlgebra R R) ^ p}) (ι R R 1 ^ n)))) = _
  rw [coordinateRingEquivAdjoinRoot_mk, map_pow, equivPolynomial_ι_one,
    AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (monic_X_pow p)).mpr (by
      rw [degree_X_pow, degree_X_pow]; exact_mod_cast hn), map_pow, equivPolynomial_symm_X]

/-- The truncation map sends the `i`-th vector `[x]ⁱ` of the power basis to `xⁱ`. -/
theorem truncation_powerBasis_basis (i : Fin (powerBasis (R := R) p).dim) :
    truncation p ((powerBasis (R := R) p).basis i) =
      (ι R R 1 : SymmetricAlgebra R R) ^ (i : ℕ) := by
  rw [PowerBasis.coe_basis, powerBasis_gen]
  -- The goal is over `(hopfIdeal p).toIdeal` and `truncation_mk_pow` over `Ideal.span {x ^ p}`.
  -- These are definitionally equal (`hopfIdeal_toIdeal` is `rfl`) but cannot be rewritten into each
  -- other, since the quotient type depends on the ideal.
  exact truncation_mk_pow p (i.isLt.trans_eq (powerBasis_dim p))

/-- The truncation map is a section of the quotient map `R[x] → R[x] / (xᵖ)`. -/
theorem mk_truncation (a : CoordinateRing (R := R) p) :
    Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal (truncation p a) = a := by
  apply (coordinateRingEquivAdjoinRoot (R := R) p).injective
  -- `coordinateRingEquivAdjoinRoot_mk` is stated over `Ideal.span {x ^ p}`, definitionally the
  -- ideal `(hopfIdeal p).toIdeal` of the goal (`hopfIdeal_toIdeal` is `rfl`).
  refine (coordinateRingEquivAdjoinRoot_mk p _).trans ?_
  rw [truncation, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    AdjoinRoot.mk_leftInverse]

/-- The truncation map is injective. -/
theorem truncation_injective : Function.Injective (truncation (R := R) p) :=
  Function.LeftInverse.injective (g := Ideal.Quotient.mk _) (mk_truncation p)

/-- The truncation map sends `1` to `1`. -/
@[simp]
theorem truncation_one : truncation (R := R) p 1 = 1 := by
  -- The middle step applies `truncation_mk_pow`, stated over `Ideal.span {x ^ p}`, to a class
  -- modulo `(hopfIdeal p).toIdeal`: the two ideals are definitionally equal (`hopfIdeal_toIdeal`).
  calc truncation p 1
      = truncation p (Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal (ι R R 1) ^ 0) :=
        congrArg (truncation p) (pow_zero _).symm
    _ = (ι R R 1 : SymmetricAlgebra R R) ^ 0 :=
        truncation_mk_pow p (Fact.out (p := p.Prime)).pos
    _ = 1 := pow_zero _

/-- **The coalgebra of `αₚ` is a subcoalgebra of the coalgebra of `𝔾ₐ`**: the truncation map
`R[x] / (xᵖ) → R[x]`, `[x]ⁱ ↦ xⁱ` for `i < p`, preserves the counit and the comultiplication. -/
noncomputable def truncationCoalgHom :
    CoordinateRing (R := R) p →ₗc[R] SymmetricAlgebra R R where
  toLinearMap := truncation p
  counit_comp := (powerBasis (R := R) p).basis.ext fun i ↦ by
    rw [LinearMap.comp_apply, truncation_powerBasis_basis, powerBasis_basis_apply,
      Bialgebra.Quotient.counit_mk]
  map_comp_comul := (powerBasis (R := R) p).basis.ext fun i ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, truncation_powerBasis_basis,
      powerBasis_basis_apply, Bialgebra.Quotient.comul_mk, ← LinearMap.comp_apply
        (TensorProduct.map _ _), ← TensorProduct.map_comp,
      TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R R 1)]
    simp only [map_sum, map_nsmul, TensorProduct.map_tmul, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, map_pow]
    refine Finset.sum_congr rfl fun mn hmn ↦ ?_
    have hmn' := Finset.mem_antidiagonal.mp hmn
    have hi : (i : ℕ) < p := i.isLt.trans_eq (powerBasis_dim (R := R) p)
    -- The classes are modulo `(hopfIdeal p).toIdeal`, and `truncation_mk_pow` is stated over the
    -- definitionally equal `Ideal.span {x ^ p}` (`hopfIdeal_toIdeal` is `rfl`).
    exact congrArg₂ (fun a b ↦ (i : ℕ).choose mn.1 • a ⊗ₜ[R] b) (truncation_mk_pow p (by omega))
      (truncation_mk_pow p (by omega))

@[simp]
theorem truncationCoalgHom_apply (a : CoordinateRing (R := R) p) :
    truncationCoalgHom p a = truncation p a :=
  (rfl)

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
