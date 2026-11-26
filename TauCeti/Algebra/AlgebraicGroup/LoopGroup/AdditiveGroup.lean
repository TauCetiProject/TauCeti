/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Jet

/-!
# The positive loop group of the additive group

For the additive group `𝔾ₐ = Spec (SymmetricAlgebra k k)` over a commutative ring `k`, the
positive loop group is `L⁺𝔾ₐ(R) = 𝔾ₐ(R⟦X⟧) = (R⟦X⟧, +)`, and an arc `a = Σ aₙ Xⁿ` is the
sequence of its coefficients `aₙ ∈ R`. So `L⁺𝔾ₐ` is the infinite-dimensional affine space with
coordinates the coefficients of the arc: its coordinate Hopf algebra
`positiveLoopHopfAlgebra k (SymmetricAlgebra k k)` is the polynomial algebra `MvPolynomial ℕ k`,
the variable `Xₙ` being the function `arcCoeff k n` taking an arc to its `n`-th coefficient.

## Main definitions

* `TauCeti.AdditiveGroup.arcCoeff k n`: the `n`-th coefficient of the arc, a function on `L⁺𝔾ₐ`.
* `TauCeti.AdditiveGroup.positiveLoopHopfAlgebraAlgEquiv`: the coordinate Hopf algebra of
  `L⁺𝔾ₐ` is `MvPolynomial ℕ k`, with `arcCoeff k n ↦ Xₙ`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Studies in Advanced
  Mathematics 103 (2007), §1.3.1.
-/

public section

open WithConv SymmetricAlgebra TauCeti.HopfAlgebra

namespace TauCeti.AdditiveGroup

variable (k : Type*) [CommRing k]

/-- **The `n`-th coefficient of the arc**, the function on the positive loop group `L⁺𝔾ₐ` taking
an arc `a ∈ R⟦X⟧` of `𝔾ₐ` to its `n`-th coefficient (`ofConv_apply_arcCoeff`): the `n`-th
coefficient of the universal arc. -/
noncomputable def arcCoeff (n : ℕ) : positiveLoopHopfAlgebra k (SymmetricAlgebra k k) :=
  PowerSeries.coeff n
    ((positiveLoopPointsMulEquiv k _ _ (toConv (AlgHom.id k _))).ofConv (ι k k 1))

variable {k}

/-- A point of `L⁺𝔾ₐ` takes the value `aₙ` on `arcCoeff k n`, where `a ∈ R⟦X⟧` is its arc. -/
@[simp]
theorem ofConv_apply_arcCoeff {R : Type*} [CommRing R] [Algebra k R]
    (x : WithConv (positiveLoopHopfAlgebra k (SymmetricAlgebra k k) →ₐ[k] R)) (n : ℕ) :
    x.ofConv (arcCoeff k n) =
      PowerSeries.coeff n ((positiveLoopPointsMulEquiv k _ R x).ofConv (ι k k 1)) := by
  have hx : x = AlgHom.mapValue x.ofConv (toConv (AlgHom.id k _)) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]
  conv_rhs => rw [hx, positiveLoopPointsMulEquiv_naturality]
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, PowerSeries.mapAlgHom_apply,
    PowerSeries.coeff_map, AlgHom.coe_toRingHom, arcCoeff]

variable (k)

-- The point of `L⁺𝔾ₐ` with values in `MvPolynomial ℕ k` whose arc is `Σ Xₙ Xⁿ`.
private noncomputable def universalArcPoint :
    positiveLoopHopfAlgebra k (SymmetricAlgebra k k) →ₐ[k] MvPolynomial ℕ k :=
  ((positiveLoopPointsMulEquiv k (SymmetricAlgebra k k) (MvPolynomial ℕ k)).symm
    ((AdditiveGroup.gaPointsMulEquiv (R := k)).symm
      (Multiplicative.ofAdd (PowerSeries.mk MvPolynomial.X)))).ofConv

private theorem universalArcPoint_arcCoeff (n : ℕ) :
    universalArcPoint k (arcCoeff k n) = MvPolynomial.X n := by
  rw [← ofConv_toConv (universalArcPoint k), ofConv_apply_arcCoeff, universalArcPoint,
    toConv_ofConv, MulEquiv.apply_symm_apply, gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd,
    PowerSeries.coeff_mk]

/-- **The coordinate Hopf algebra of `L⁺𝔾ₐ` is a polynomial algebra in the coefficients of the
arc.** The positive loop group of `𝔾ₐ` is the affine space with coordinates the coefficients of
the arc: `positiveLoopHopfAlgebra k (SymmetricAlgebra k k) ≃ₐ[k] MvPolynomial ℕ k`, taking the
`n`-th coefficient `arcCoeff k n` to `Xₙ`. -/
noncomputable def positiveLoopHopfAlgebraAlgEquiv :
    positiveLoopHopfAlgebra k (SymmetricAlgebra k k) ≃ₐ[k] MvPolynomial ℕ k :=
  AlgEquiv.ofAlgHom (universalArcPoint k) (MvPolynomial.aeval (arcCoeff k))
    (MvPolynomial.algHom_ext fun n ↦ by
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, universalArcPoint_arcCoeff, AlgHom.id_apply])
    (by
      -- both maps are points of `L⁺𝔾ₐ`; their arcs have the same coefficients
      refine WithConv.toConv_injective <|
        (positiveLoopPointsMulEquiv k (SymmetricAlgebra k k) _).injective <|
        (AdditiveGroup.gaPointsMulEquiv (R := k)).injective <|
          Multiplicative.toAdd.injective <| PowerSeries.ext fun n ↦ ?_
      rw [toAdd_gaPointsMulEquiv, toAdd_gaPointsMulEquiv, ← ofConv_apply_arcCoeff,
        ← ofConv_apply_arcCoeff, ofConv_toConv, ofConv_toConv, AlgHom.comp_apply,
        universalArcPoint_arcCoeff, MvPolynomial.aeval_X, AlgHom.id_apply])

variable {k}

@[simp]
theorem positiveLoopHopfAlgebraAlgEquiv_arcCoeff (n : ℕ) :
    positiveLoopHopfAlgebraAlgEquiv k (arcCoeff k n) = MvPolynomial.X n :=
  universalArcPoint_arcCoeff k n

@[simp]
theorem positiveLoopHopfAlgebraAlgEquiv_symm_X (n : ℕ) :
    (positiveLoopHopfAlgebraAlgEquiv k).symm (MvPolynomial.X n) = arcCoeff k n :=
  MvPolynomial.aeval_X _ n

end TauCeti.AdditiveGroup
