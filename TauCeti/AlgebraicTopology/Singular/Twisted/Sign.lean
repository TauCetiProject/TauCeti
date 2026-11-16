/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Coinvariants

/-!
# Zeroth homology with sign coefficients

A local coefficient system `L` on a path-connected space whose fibre at `x` is a copy of `R`, and
whose loops at `x` act by `1` or by `-1`, has zeroth homology either `R` or `R ⧸ 2R`. Twisted zeroth
homology is the coinvariants of the monodromy representation
(`TauCeti.LocalCoefficientSystem.twistedHomology₀IsoCoinvariants`). If every loop acts by `1`,
these coinvariants are the fibre itself
(`TauCeti.LocalCoefficientSystem.twistedHomology₀EquivOfIsTrivial`). If some loop acts by `-1`,
the class of a coefficient `a` agrees with that of `-a`, and the coinvariants are the fibre modulo
`2` (`TauCeti.LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo`).

The sign local system of a double cover (`IsCoveringMap.signLocalSystem`) is of this kind
(`IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one`). For the
orientation local system `o(E)` of a real vector bundle `E` with integer coefficients, this is the
familiar dichotomy: over a connected base, `H₀(B; o(E))` is `ℤ` when `E` is orientable and `ℤ/2`
otherwise. The bundle form is in `TauCeti.Topology.VectorBundle.Orientation.TwistedHomology`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo`: zeroth homology of a local
  system with fibre `R` on which some loop acts by `-1` and every loop by `±1` is `R ⧸ 2R`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (zeroth homology with local coefficients as
  coinvariants, and the orientation system of a manifold).
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [CommRing R] {X : TopCat.{v}} [PathConnectedSpace X]
  (L : LocalCoefficientSystem.{u, v, max v w} R X) (x : X)

/-- **Zeroth homology modulo two.** Let the fibre of `L` at `x` be identified with `R` by `e`. If
every loop at `x` acts on it by `1` or by `-1`, and some loop acts by `-1`, twisted zeroth homology
is `R ⧸ 2R`. -/
def twistedHomology₀EquivQuotientTwo (e : L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] R)
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1) :
    twistedHomology L 0 ≃ₗ[R] R ⧸ Ideal.span {(2 : R)} :=
  (twistedHomology₀IsoCoinvariants L x).toLinearEquiv ≪≫ₗ
    Representation.coinvariantsEquivQuotientTwo h hg₀ ≪≫ₗ
    Submodule.Quotient.equiv _ _ e (by simp [Submodule.map_smul''])

/-- The identification of zeroth homology with `R ⧸ 2R` sends the class of a coefficient `a` at `x`
to the residue of `e a`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀
    (e : L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] R)
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    twistedHomology₀EquivQuotientTwo L x e h hg₀ (ιTwistedHomology₀ L x a) =
      Ideal.Quotient.mk _ (e a) := by
  rw [twistedHomology₀EquivQuotientTwo, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply]
  simp

/-- The inverse identification sends the residue of `r` to the class of `e.symm r`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_symm_mk
    (e : L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] R)
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1) (r : R) :
    (twistedHomology₀EquivQuotientTwo L x e h hg₀).symm (Ideal.Quotient.mk _ r) =
      ιTwistedHomology₀ L x (e.symm r) :=
  (LinearEquiv.symm_apply_eq _).2 (by simp)

end TauCeti.LocalCoefficientSystem
