/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Coinvariants

/-!
# Zeroth homology with sign coefficients

A local coefficient system `L` on a path-connected space whose loops at `x` act on the fibre `V`
at `x` by `1` or by `-1` has zeroth homology either `V` or `V ⧸ 2V`. Twisted zeroth
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
  system whose loops at `x` act on the fibre `V` at `x` by `±1`, some by `-1`, is `V ⧸ 2V`.

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

/-- **Zeroth homology modulo two.** If every loop at `x` acts on the fibre of `L` at `x` by `1` or
by `-1`, and some loop acts by `-1`, twisted zeroth homology is that fibre modulo `2`. -/
def twistedHomology₀EquivQuotientTwo
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1) :
    twistedHomology L 0 ≃ₗ[R]
      L.obj (FundamentalGroupoid.mk x) ⧸
        (Ideal.span {(2 : R)} • ⊤ : Submodule R (L.obj (FundamentalGroupoid.mk x))) :=
  (twistedHomology₀IsoCoinvariants L x).toLinearEquiv ≪≫ₗ
    Representation.coinvariantsEquivQuotientTwo h hg₀

/-- The identification of zeroth homology with the fibre modulo `2` sends the class of a
coefficient `a` at `x` to the residue of `a`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    twistedHomology₀EquivQuotientTwo L x h hg₀ (ιTwistedHomology₀ L x a) =
      Submodule.Quotient.mk a := by
  rw [twistedHomology₀EquivQuotientTwo, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply]
  simp

/-- The inverse identification sends the residue of a coefficient `a` at `x` to its class. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_symm_mk
    (h : ∀ g, monodromyRepresentation L x g = 1 ∨ monodromyRepresentation L x g = -1)
    {g₀ : FundamentalGroup X x} (hg₀ : monodromyRepresentation L x g₀ = -1)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    (twistedHomology₀EquivQuotientTwo L x h hg₀).symm (Submodule.Quotient.mk a) =
      ιTwistedHomology₀ L x a :=
  (LinearEquiv.symm_apply_eq _).2
    (twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀ L x h hg₀ a).symm

end TauCeti.LocalCoefficientSystem
