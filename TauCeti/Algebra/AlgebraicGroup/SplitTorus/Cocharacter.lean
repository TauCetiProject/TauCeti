/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic

/-!
# The character–cocharacter perfect pairing of a split torus

`TauCeti.Algebra.AlgebraicGroup.Cocharacter` builds, for the diagonalizable group `D(M)`, the
character–cocharacter pairing `DiagonalizableGroup.pairing m ψ = (ψ m).toAdd`, valued in the
power endomorphisms of `𝔾ₘ` (`charPoints_comp_cocharPoints`), and computes it in the rank-`1`
case `𝔾ₘ = D(Multiplicative ℤ)` as multiplication of integers (`pairing_ofAdd`). This file does
the arbitrary-rank case, the **split torus** `T = D(Multiplicative (σ →₀ ℤ))` of
`TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic`, whose character lattice is
`X*(T) = σ →₀ ℤ` (the free `ℤ`-module on `σ`).

* The **cocharacter lattice** `X_*(T)` is identified with `σ → ℤ` by `SplitTorus.cocharEquiv`,
  reading a cocharacter `ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ` off on the standard
  generators; this is `TauCeti.freeAbelianCharEquiv` composed with `Multiplicative.toAdd`.
* The **pairing is the dot product**: `SplitTorus.pairing_ofAdd_eq` computes
  `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i`, so that `X*(T) × X_*(T) → ℤ` is the canonical
  evaluation pairing between `σ →₀ ℤ` and `σ → ℤ`. It is realized on the group as the
  corresponding power endomorphism of `𝔾ₘ` (`SplitTorus.charPoints_comp_cocharPoints_ofAdd`).
* The pairing is **perfect**: `SplitTorus.pairing_eq_zero_left` and
  `SplitTorus.pairing_eq_zero_right` are its non-degeneracy in each slot — a character pairing
  to `0` against every cocharacter is trivial, and vice versa.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap),
Layer 4: "Tori: split ... the **character lattice `X*(T)`** and **cocharacter lattice
`X_*(T)`** with their **perfect pairing**: the input to root data", extending the rank-`1`
pairing of `DiagonalizableGroup.pairing_ofAdd` to the split torus of arbitrary rank.

## Main declarations

* `TauCeti.SplitTorus.cocharEquiv`: the identification of the cocharacter lattice `X_*(T)` of
  the rank-`σ` split torus with `σ → ℤ`.
* `TauCeti.SplitTorus.pairing_ofAdd_eq`: the character–cocharacter pairing is the dot product
  `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i`.
* `TauCeti.SplitTorus.charPoints_comp_cocharPoints_ofAdd`: the dot-product pairing is realized
  on points as the corresponding power endomorphism of `𝔾ₘ`.
* `TauCeti.SplitTorus.pairing_eq_zero_left`, `TauCeti.SplitTorus.pairing_eq_zero_right`: the
  pairing is perfect (non-degenerate in each slot).

## References

The abstract diagonalizable-group character–cocharacter pairing is Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`, and the free-abelian-group character
identification `TauCeti.freeAbelianCharEquiv` is `TauCeti.Algebra.Group.FreeAbelianCharacter`.
The dot-product form reuses Mathlib's `Finsupp.linearCombination` and the additive/multiplicative
type-tag adjunction `AddMonoidHom.toMultiplicative`. This realizes the split-torus perfect
pairing of the Tau Ceti reductive-groups roadmap (Layer 4).
-/

public section

namespace TauCeti

namespace SplitTorus

universe u v w

variable {σ : Type w}

/-- The **cocharacter lattice `X_*(T)`** of the rank-`σ` split torus
`T = D(Multiplicative (σ →₀ ℤ))`, identified with `σ → ℤ`. A cocharacter
`ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ` is read off on the standard generators
`ofAdd (single i 1)`, its coordinate at `i` being `(ψ (ofAdd (single i 1))).toAdd`. This is
`TauCeti.freeAbelianCharEquiv` (with target `Multiplicative ℤ`) followed by `Multiplicative.toAdd`
in each coordinate. -/
noncomputable def cocharEquiv :
    (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) ≃ (σ → ℤ) :=
  freeAbelianCharEquiv.toEquiv.trans (Equiv.piCongrRight fun _ => Multiplicative.toAdd)

/-- The `i`-th coordinate of a cocharacter is its value on the standard generator
`ofAdd (single i 1)`, read as an integer through `Multiplicative.toAdd`. -/
@[simp]
theorem cocharEquiv_apply (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (i : σ) :
    cocharEquiv ψ i = (ψ (Multiplicative.ofAdd (Finsupp.single i 1))).toAdd := by
  simp [cocharEquiv, Equiv.piCongrRight_apply]

/-- **The split-torus character–cocharacter pairing is the dot product.** For a character
`ofAdd m` of `T` (`m : σ →₀ ℤ = X*(T)`) and a cocharacter `ψ` (with coordinates
`cocharEquiv ψ : σ → ℤ = X_*(T)`), the pairing `⟨ofAdd m, ψ⟩` of
`TauCeti.Algebra.AlgebraicGroup.Cocharacter` is `∑ᵢ mᵢ · cocharEquiv ψ i`. This is the
canonical evaluation pairing between the free `ℤ`-module `σ →₀ ℤ` and its dual `σ → ℤ`,
extending the rank-`1` `DiagonalizableGroup.pairing_ofAdd` to arbitrary rank. -/
theorem pairing_ofAdd_eq (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (m : σ →₀ ℤ) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ =
      m.sum fun i c => c * cocharEquiv ψ i := by
  -- Both sides are additive in `m` and agree on the standard generators `single i 1`.
  let L : (σ →₀ ℤ) →+ ℤ :=
    AddMonoidHom.mk' (fun x => (ψ (Multiplicative.ofAdd x)).toAdd) fun x y => by
      rw [ofAdd_add, map_mul, toAdd_mul]
  have hL : L = (Finsupp.linearCombination ℤ (cocharEquiv ψ)).toAddMonoidHom := by
    refine Finsupp.addHom_ext' fun i => ?_
    refine AddMonoidHom.ext_int ?_
    change (ψ (Multiplicative.ofAdd (Finsupp.single i 1))).toAdd =
      Finsupp.linearCombination ℤ (cocharEquiv ψ) (Finsupp.single i 1)
    rw [Finsupp.linearCombination_single, one_smul, cocharEquiv_apply]
  have hm : DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = L m := by
    rw [DiagonalizableGroup.pairing_def]
    rfl
  rw [hm, hL]
  simp [Finsupp.linearCombination_apply]

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The dot-product pairing is realized on points as a power endomorphism of `𝔾ₘ`.**
Composing the character `ofAdd m` after the cocharacter `ψ` is the power endomorphism of `𝔾ₘ`
with exponent the dot product `∑ᵢ mᵢ · cocharEquiv ψ i`, so on points it raises a unit to that
power. This is the split-torus instance of `DiagonalizableGroup.charPoints_comp_cocharPoints`. -/
theorem charPoints_comp_cocharPoints_ofAdd
    (m : σ →₀ ℤ) (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :
    (DiagonalizableGroup.charPoints (R := R) (A := A) (Multiplicative.ofAdd m)).comp
        (DiagonalizableGroup.cocharPoints ψ) =
      DiagonalizableGroup.powEnd (m.sum fun i c => c * cocharEquiv ψ i) := by
  rw [DiagonalizableGroup.charPoints_comp_cocharPoints, pairing_ofAdd_eq]

/-- **Left non-degeneracy of the split-torus pairing.** A character `ofAdd m` pairing to `0`
against every cocharacter is trivial: `m = 0`. Together with `pairing_eq_zero_right` this is
the perfectness of the character–cocharacter pairing. -/
theorem pairing_eq_zero_left {m : σ →₀ ℤ}
    (h : ∀ ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ,
      DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = 0) :
    m = 0 := by
  ext j
  -- Pair against the coordinate cocharacter `m ↦ ofAdd (m j)`.
  have hj := h (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom j))
  rw [DiagonalizableGroup.pairing_def] at hj
  simpa [AddMonoidHom.coe_toMultiplicative] using hj

/-- **Right non-degeneracy of the split-torus pairing.** A cocharacter `ψ` pairing to `0`
against every character is trivial: `ψ = 1`. Together with `pairing_eq_zero_left` this is the
perfectness of the character–cocharacter pairing. -/
theorem pairing_eq_zero_right {ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ}
    (h : ∀ m : σ →₀ ℤ, DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = 0) :
    ψ = 1 := by
  refine freeAbelianCharEquiv.injective ?_
  ext j
  rw [freeAbelianCharEquiv_apply, map_one, Pi.one_apply]
  have hj := h (Finsupp.single j 1)
  rw [DiagonalizableGroup.pairing_def] at hj
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_one]
  exact hj

end SplitTorus

end TauCeti
