/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power classes of a commutative group under equivalences and products

The group of `n`-th power classes of a commutative group `G` is the quotient
`G ⧸ (powMonoidHom n).range`, the spelling `Mathlib.RingTheory.DedekindDomain.SelmerGroup` uses.
This file transports that quotient along a multiplicative equivalence, and identifies the power
classes of the units of a product with the product of the power classes of the units of the
factors. Composed with the Chinese Remainder decomposition of `K[X] ⧸ (f)` for a squarefree `f`,
the latter computes the power classes of units of that algebra one field factor at a time
(`TauCeti.RingTheory.AdjoinRoot.Factors`).

## Main definitions

* `QuotientGroup.congrRangePowMonoidHom`: an equivalence `G ≃* H` induces
  `G ⧸ (powMonoidHom n).range ≃* H ⧸ (powMonoidHom n).range`.
* `Units.modPowPiEquiv`: taking `n`-th power classes of units commutes with products.

## Main results

* `QuotientGroup.pow_eq_one_quotient_range_powMonoidHom`: every `n`-th power class is killed by
  `n`.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `modPow`, where the two are stated for the source's
`Units.modPow` abbreviation. Mathlib's `QuotientGroup.mulEquivPiModRangePowMonoidHom` and
`MulEquiv.piUnits` do the work of the source's `Units.modPow.piEquiv`; what is left here is the
transport along an equivalence and the composition of those two.
`QuotientGroup.pow_eq_one_quotient_range_powMonoidHom` is not from the source.
-/

public section

namespace QuotientGroup

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def congrRangePowMonoidHom (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e (e.map_range_powMonoidHom n)

@[simp]
lemma congrRangePowMonoidHom_mk (e : G ≃* H) (n : ℕ) (g : G) :
    congrRangePowMonoidHom e n (QuotientGroup.mk g) = QuotientGroup.mk (e g) :=
  (rfl)

/-- The inverse of `congrRangePowMonoidHom e n` is induced by the inverse of `e`. -/
@[simp]
lemma congrRangePowMonoidHom_symm (e : G ≃* H) (n : ℕ) :
    (congrRangePowMonoidHom e n).symm = congrRangePowMonoidHom e.symm n := by
  rw [congrRangePowMonoidHom, QuotientGroup.congr_symm, congrRangePowMonoidHom]

/-- Every class modulo the subgroup of `n`-th powers is killed by `n`. -/
@[simp]
theorem pow_eq_one_quotient_range_powMonoidHom (n : ℕ)
    (x : G ⧸ (powMonoidHom n : G →* G).range) :
    x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact ⟨g, rfl⟩

end QuotientGroup

namespace Units

variable {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ)

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def modPowPiEquiv :
    ((i : ι) → α i)ˣ ⧸ (powMonoidHom n : ((i : ι) → α i)ˣ →* _).range ≃*
      ((i : ι) → (α i)ˣ ⧸ (powMonoidHom n : (α i)ˣ →* _).range) :=
  (QuotientGroup.congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    QuotientGroup.mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

/-- On the class of a unit, `Units.modPowPiEquiv` is componentwise projection to the factors. -/
@[simp]
lemma modPowPiEquiv_mk (u : ((i : ι) → α i)ˣ) (i : ι) :
    modPowPiEquiv α n (QuotientGroup.mk u) i = QuotientGroup.mk (MulEquiv.piUnits u i) := by
  simp [modPowPiEquiv]

end Units

end
