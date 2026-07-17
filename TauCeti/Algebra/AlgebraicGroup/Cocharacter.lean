/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroupFunctoriality

/-!
# Characters, cocharacters, and their pairing for the diagonalizable group

`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup` computes the functor of points of the
diagonalizable group `D(M) = Spec R[M]`, and
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroupFunctoriality` records its contravariant
functoriality `DiagonalizableGroup.pointsMap`. This file uses that functoriality to build the
**character lattice `X*(D(M))`, the cocharacter lattice `X_*(D(M))`, and their pairing**
into the endomorphism lattice of the multiplicative group, all realized on the functor of points.

Throughout, the multiplicative group is `𝔾ₘ = D(Multiplicative ℤ)` in its group-algebra
presentation, so its `A`-points are the units `Aˣ` (its character group `Multiplicative ℤ →* Aˣ`
being determined by the value on the generator, `Mathlib`'s `MonoidHom.apply_mint`). Its
canonical Laurent-polynomial API is `TauCeti.MultiplicativeGroup`, matched to this presentation by
`TauCeti.DiagonalizableGroup.multiplicativeGroup_pointEquiv_apply`.

* A **character** of `D(M)` is an element `m : M`, giving the homomorphism of group functors
  `D(M) → 𝔾ₘ` whose action on points is evaluation of a character `χ : M →* Aˣ` at `m`.
* A **cocharacter** of `D(M)` is a homomorphism `ψ : M →* Multiplicative ℤ`, giving the
  homomorphism of group functors `𝔾ₘ → D(M)`; on points it sends a unit `u` to the character
  `m ↦ u ^ (ψ m).toAdd`.
* The **`n`-th power endomorphism** `powEnd n` of `𝔾ₘ` acts as `u ↦ u ^ n` on points; power
  endomorphisms compose by multiplication of exponents (`powEnd_comp`, `powEnd_one`), which
  is the ring `End(𝔾ₘ) ≅ ℤ` on the level of power maps.
* The **pairing** `⟨m, ψ⟩ = (ψ m).toAdd : ℤ` is realized as the composite endomorphism
  `character m ∘ cocharacter ψ = powEnd ⟨m, ψ⟩` of `𝔾ₘ` (`charPoints_comp_cocharPoints`). For
  `M = Multiplicative ℤ`, so `X*(𝔾ₘ) = X_*(𝔾ₘ) = ℤ`, the pairing is multiplication
  (`pairing_ofAdd`): the rank-`1` root datum input.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 4: "Tori ... the character lattice `X*(T)` and cocharacter lattice `X_*(T)` with their
perfect pairing: the input to root data").

## Main declarations

* `TauCeti.DiagonalizableGroup.charPoints`: the character of `D(M)` at `m : M`, on points.
* `TauCeti.DiagonalizableGroup.cocharPoints`: the cocharacter of `D(M)` at `ψ`, on points.
* `TauCeti.DiagonalizableGroup.powEnd`: the `n`-th power endomorphism of `𝔾ₘ`, on points.
* `TauCeti.DiagonalizableGroup.pairing`: the character–cocharacter pairing `⟨m, ψ⟩ : ℤ`.
* `TauCeti.DiagonalizableGroup.charPoints_comp_cocharPoints`: the pairing is realized as the
  composite endomorphism `character m ∘ cocharacter ψ = powEnd ⟨m, ψ⟩`.

## References

The contravariant points functoriality `DiagonalizableGroup.pointsMap` is Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroupFunctoriality`. The one-generator universal
property `zpowersHom : α ≃ (Multiplicative ℤ →* α)` and the induced `MonoidHom.apply_mint` are
Mathlib's (`Mathlib.Data.Int.Cast.Lemmas`). This realizes the character/cocharacter pairing of
the Tau Ceti reductive-groups roadmap (Layer 4).
-/

public section

open WithConv

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [CommGroup M]

/-- Composing the generator-`Multiplicative.ofAdd a` power homomorphism after the
generator-`Multiplicative.ofAdd b` one multiplies exponents. -/
private theorem zpowersHom_ofAdd_comp (a b : ℤ) :
    (zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd b)).comp
        (zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd a)) =
      zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd (a * b)) := by
  apply MonoidHom.ext_mint
  simp only [MonoidHom.comp_apply, zpowersHom_apply, toAdd_ofAdd, zpow_one]
  rw [← ofAdd_zsmul, smul_eq_mul]

/-! ### Characters -/

/-- **The character of `D(M)` attached to an element `m : M`, on points.** As a homomorphism of
group functors `D(M) → 𝔾ₘ`, it is induced (contravariantly) by the generator homomorphism
`zpowersHom M m : Multiplicative ℤ →* M`, `Multiplicative.ofAdd 1 ↦ m`. -/
noncomputable def charPoints (m : M) :
    WithConv (MonoidAlgebra R M →ₐ[R] A) →*
      WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :=
  pointsMap (zpowersHom M m)

/-- **A character acts on points by evaluation.** Reading the resulting `𝔾ₘ`-point on the
generator gives the value of the original character `χ : M →* Aˣ` at `m`. -/
theorem pointsMulEquiv_charPoints (m : M) (f : WithConv (MonoidAlgebra R M →ₐ[R] A)) :
    pointsMulEquiv (charPoints (R := R) (A := A) m f) (Multiplicative.ofAdd 1) =
      pointsMulEquiv f m := by
  rw [charPoints, pointsMulEquiv_pointsMap, MonoidHom.comp_apply, zpowersHom_apply,
    toAdd_ofAdd, zpow_one]

/-! ### Cocharacters -/

/-- **The cocharacter of `D(M)` attached to a homomorphism `ψ : M →* Multiplicative ℤ`, on
points.** As a homomorphism of group functors `𝔾ₘ → D(M)`, it is induced (contravariantly) by
`ψ`. -/
noncomputable def cocharPoints (ψ : M →* Multiplicative ℤ) :
    WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) →*
      WithConv (MonoidAlgebra R M →ₐ[R] A) :=
  pointsMap ψ

/-- **A cocharacter acts on points by a power character.** The `𝔾ₘ`-point with generator value
`u` is sent to the character `m ↦ u ^ (ψ m).toAdd`. -/
theorem pointsMulEquiv_cocharPoints (ψ : M →* Multiplicative ℤ)
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) (m : M) :
    pointsMulEquiv (cocharPoints (R := R) (A := A) ψ f) m =
      pointsMulEquiv f (Multiplicative.ofAdd 1) ^ (ψ m).toAdd := by
  rw [cocharPoints, pointsMulEquiv_pointsMap, MonoidHom.comp_apply, MonoidHom.apply_mint]

/-! ### Power endomorphisms of `𝔾ₘ` -/

/-- **The `n`-th power endomorphism of `𝔾ₘ`, on points.** It is induced (contravariantly) by the
`n`-th power homomorphism `zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd n)` of
`Multiplicative ℤ`. -/
noncomputable def powEnd (n : ℤ) :
    WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) →*
      WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :=
  pointsMap (zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd n))

/-- **The power endomorphism acts as `u ↦ u ^ n` on points.** -/
theorem pointsMulEquiv_powEnd (n : ℤ)
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    pointsMulEquiv (powEnd (R := R) (A := A) n f) (Multiplicative.ofAdd 1) =
      pointsMulEquiv f (Multiplicative.ofAdd 1) ^ n := by
  rw [powEnd, pointsMulEquiv_pointsMap, MonoidHom.comp_apply, zpowersHom_apply,
    toAdd_ofAdd, zpow_one, MonoidHom.apply_mint, toAdd_ofAdd]

/-- The first power endomorphism is the identity. -/
@[simp]
theorem powEnd_one : powEnd (R := R) (A := A) 1 = MonoidHom.id _ := by
  unfold powEnd
  rw [show zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd (1 : ℤ)) = MonoidHom.id _ from
    MonoidHom.ext_mint (by simp), pointsMap_id]

/-- **Power endomorphisms compose by multiplying exponents:** `powEnd a ∘ powEnd b = powEnd (a*b)`.
This is the multiplication of the endomorphism ring `End(𝔾ₘ) ≅ ℤ` on power maps. -/
theorem powEnd_comp (a b : ℤ) :
    (powEnd (R := R) (A := A) a).comp (powEnd b) = powEnd (a * b) := by
  unfold powEnd
  rw [← pointsMap_comp, zpowersHom_ofAdd_comp]

/-! ### The character–cocharacter pairing -/

/-- **The character–cocharacter pairing `⟨m, ψ⟩ : ℤ`** of a character `m : M` of `D(M)` with a
cocharacter `ψ : M →* Multiplicative ℤ`. -/
def pairing (m : M) (ψ : M →* Multiplicative ℤ) : ℤ :=
  (ψ m).toAdd

/-- The pairing `⟨m, ψ⟩` is the integer `(ψ m).toAdd`. -/
theorem pairing_def (m : M) (ψ : M →* Multiplicative ℤ) : pairing m ψ = (ψ m).toAdd := by
  rw [pairing]

/-- The pairing is additive in the character: `⟨m * m', ψ⟩ = ⟨m, ψ⟩ + ⟨m', ψ⟩`. -/
theorem pairing_mul_left (m m' : M) (ψ : M →* Multiplicative ℤ) :
    pairing (m * m') ψ = pairing m ψ + pairing m' ψ := by
  simp only [pairing_def, map_mul, toAdd_mul]

/-- The pairing vanishes on the identity character: `⟨1, ψ⟩ = 0`. -/
theorem pairing_one_left (ψ : M →* Multiplicative ℤ) : pairing (1 : M) ψ = 0 := by
  simp only [pairing_def, map_one, toAdd_one]

/-- The pairing is additive in the cocharacter: `⟨m, ψ * ψ'⟩ = ⟨m, ψ⟩ + ⟨m, ψ'⟩`. -/
theorem pairing_mul_right (m : M) (ψ ψ' : M →* Multiplicative ℤ) :
    pairing m (ψ * ψ') = pairing m ψ + pairing m ψ' := by
  simp only [pairing_def, MonoidHom.mul_apply, toAdd_mul]

/-- **The pairing is realized as a power endomorphism of `𝔾ₘ`.** Composing the character `m`
after the cocharacter `ψ` is the `⟨m, ψ⟩`-power endomorphism of `𝔾ₘ`, so on points it is
`u ↦ u ^ ⟨m, ψ⟩`. This realizes the character–cocharacter pairing
`X*(D(M)) × X_*(D(M)) → End(𝔾ₘ)`, valued in the power endomorphisms (the ring `End(𝔾ₘ) ≅ ℤ`
on the level of power maps). -/
theorem charPoints_comp_cocharPoints (m : M) (ψ : M →* Multiplicative ℤ) :
    (charPoints (R := R) (A := A) m).comp (cocharPoints ψ) = powEnd (pairing m ψ) := by
  unfold charPoints cocharPoints powEnd pairing
  rw [← pointsMap_comp]
  congr 1
  apply MonoidHom.ext_mint
  simp

/-- The pairing evaluated through `charPoints_comp_cocharPoints`: on points, the composite of
the cocharacter `ψ` and the character `m` raises a unit to the `⟨m, ψ⟩` power. -/
theorem pointsMulEquiv_charPoints_cocharPoints (m : M) (ψ : M →* Multiplicative ℤ)
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    pointsMulEquiv (charPoints (R := R) (A := A) m (cocharPoints ψ f))
        (Multiplicative.ofAdd 1) =
      pointsMulEquiv f (Multiplicative.ofAdd 1) ^ pairing m ψ := by
  have := DFunLike.congr_fun (charPoints_comp_cocharPoints (R := R) (A := A) m ψ) f
  rw [MonoidHom.comp_apply] at this
  rw [this, pointsMulEquiv_powEnd]

/-- **The rank-`1` pairing is multiplication.** For `𝔾ₘ = D(Multiplicative ℤ)`, with character
lattice `X*(𝔾ₘ) = ℤ` (via `Multiplicative.ofAdd`) and cocharacter lattice `X_*(𝔾ₘ) = ℤ` (via
`ψ ↦ (ψ (Multiplicative.ofAdd 1)).toAdd`), the pairing is the product of the two integers. -/
theorem pairing_ofAdd (a : ℤ) (ψ : Multiplicative ℤ →* Multiplicative ℤ) :
    pairing (Multiplicative.ofAdd a) ψ = a * (ψ (Multiplicative.ofAdd 1)).toAdd := by
  rw [pairing, MonoidHom.apply_mint, toAdd_ofAdd, toAdd_zpow, smul_eq_mul]

end DiagonalizableGroup

end TauCeti
