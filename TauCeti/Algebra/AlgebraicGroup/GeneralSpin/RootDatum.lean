/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Base
public import TauCeti.LinearAlgebra.RootSystem.CentralExtension
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD.RootDatum

/-!
# The based root data of the general spin and similitude groups

This file constructs the based root data of the split groups `GSpin_{2n+1}`, `GSpin_{2n}`,
`GSp₂ₙ` and `GSO₂ₙ` on the lattices `X = ℤε₀ ⊕ ℤε₁ ⊕ ⋯ ⊕ ℤεₙ` and its dual, written as `M × ℤ`
and `N × ℤ` with `ε₀ = (0, 1)`. `GSpin_{2n+1}` and `GSpin_{2n}` extend the root data of `SO_{2n+1}`
and `SO_{2n}` by the central cocharacter `ε₀∨` (`RootPairing.extendCoroot`), and `GSp₂ₙ` and
`GSO₂ₙ` extend those of `Sp₂ₙ` and `SO_{2n}` by the multiplier `ε₀` (`RootPairing.extendRoot`):

* `GSpin_{2n+1}` (`TauCeti.gspinOddRootDatum`): roots `εᵢ - εⱼ`, `±(εᵢ + εⱼ)`, `±εᵢ`, those of
  `SO_{2n+1}`, and coroots `εᵢ∨ - εⱼ∨`, `±(εᵢ∨ + εⱼ∨ - ε₀∨)`, `±(2εᵢ∨ - ε₀∨)`. The simple roots
  are `εᵢ - εᵢ₊₁` and `εₙ`, with simple coroots `εᵢ∨ - εᵢ₊₁∨` and `2εₙ∨ - ε₀∨`.
* `GSp₂ₙ` (`TauCeti.gspRootDatum`): roots `εᵢ - εⱼ`, `±(εᵢ + εⱼ - ε₀)`, `±(2εᵢ - ε₀)`, and coroots
  `εᵢ∨ - εⱼ∨`, `±(εᵢ∨ + εⱼ∨)`, `±εᵢ∨`, those of `Sp₂ₙ`.
* `GSpin_{2n}` (`TauCeti.gspinEvenRootDatum`): roots `±εᵢ ± εⱼ`, those of `SO_{2n}`, and coroots
  `εᵢ∨ - εⱼ∨`, `±(εᵢ∨ + εⱼ∨ - ε₀∨)`; the simple roots are `εᵢ - εᵢ₊₁` and `εₙ₋₁ + εₙ`, with
  simple coroots `εᵢ∨ - εᵢ₊₁∨` and `εₙ₋₁∨ + εₙ∨ - ε₀∨`.
* `GSO₂ₙ` (`TauCeti.gsoRootDatum`): roots `εᵢ - εⱼ`, `±(εᵢ + εⱼ - ε₀)`, and coroots `±εᵢ∨ ± εⱼ∨`.

The general spin data are those of Asgari and of Cai–Friedberg–Kaplan §1. An index `i : Fin n`
stands for the coordinate `ε_{i+1}`, so `ε₀` always denotes the multiplier. In both, `ε₀∨` is
central, it pairs to zero with every root, and the character `Υ = 2ε₀ + ε₁ + ⋯ + εₙ` (the Clifford
norm `ν`) pairs to zero with every coroot and to `2` with `ε₀∨`. Dividing out `ε₀∨`, that is,
restricting to the characters orthogonal to `ε₀∨` and projecting the coroots to `N`, returns the
root datum of `SO_{2n+1}`, respectively `SO_{2n}`.

The dualities of root data hold as follows:

* `GSpin_{2n+1}^∨ = GSp₂ₙ` (`TauCeti.flip_gspinOddRootDatum`), by construction;
* `GSpin_{2n}^∨ = GSO₂ₙ` (`TauCeti.flip_gspinEvenRootDatum`), with `ε₀∨` dual to the multiplier
  `ε₀`, because `SO_{2n}` is self-dual (`TauCeti.DynkinType.flip_typeDClassicalRootDatum`);
* `Sp₂ₙ^∨ = SO_{2n+1}` (`TauCeti.Symplectic.flip_diagonalRootDatum`): the root datum of
  `SO_{2n+1}` (`TauCeti.soOddRootDatum`) is the dual of `TauCeti.Symplectic.diagonalRootDatum`.

The bases of `GSpin_{2n+1}` and `GSp₂ₙ` come from the base `TauCeti.soOddBase` of `SO_{2n+1}`,
the dual of `TauCeti.Symplectic.diagonalRootBase`, those of `GSpin_{2n}` and `GSO₂ₙ` from
`TauCeti.DynkinType.typeDClassicalBase`, for `2 ≤ n`.

## Main declarations

* `TauCeti.gspinOddRootDatum`, `TauCeti.gspRootDatum`, `TauCeti.gspinEvenRootDatum` and
  `TauCeti.gsoRootDatum`: the root data.
* `TauCeti.gspinOddBase`, `TauCeti.gspBase`, `TauCeti.gspinEvenBase` and `TauCeti.gsoBase`: their
  bases.
* `TauCeti.gspinOddUpsilon` and `TauCeti.gspinEvenUpsilon`: the character `Υ`.
* `TauCeti.gspinOddRootDatum_toLinearMap_root_inr` and
  `TauCeti.gspinOddRootDatum_toLinearMap_gspinOddUpsilon_coroot`: `ε₀∨` is central and `Υ` is
  orthogonal to the coroots, with their counterparts for `GSpin_{2n}`.

## References

* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2.
* M. Asgari, F. Shahidi, *Generic transfer for general spin groups*, Duke Math. J. 132 (2006),
  Definition 2.1.
* Y. Cai, S. Friedberg, E. Kaplan, *Doubling constructions: local and global theory, with an
  application to global functoriality for non-generic cuspidal representations*, Ann. of Math.,
  §1.
-/

public section

open Function Matrix

namespace TauCeti

universe u

/-! ### The odd general spin group and the general symplectic group -/

section Odd

variable (n : ℕ)

namespace GeneralSpin

/-- The linear form `x ↦ -(x₁ + ⋯ + xₙ)` on the characters of the diagonal torus of `Sp₂ₙ`. -/
noncomputable def negCharacterSum : (ULift.{u} (Fin n) →₀ ℤ) →ₗ[ℤ] ℤ :=
  -SplitTorus.dotPairing.flip fun _ => 1

@[simp]
theorem negCharacterSum_apply (x : ULift.{u} (Fin n) →₀ ℤ) :
    negCharacterSum n x = -SplitTorus.dotPairing x fun _ => 1 :=
  (rfl)

/-- The `ε₀`-coordinate of the roots of `GSp₂ₙ`, and the `ε₀∨`-coordinate of the coroots of
`GSpin_{2n+1}`: minus half the coordinate sum of the corresponding root of `Sp₂ₙ`. -/
@[simp]
def multiplierCoordinate {n : ℕ} : GLSymplecticFin.RootSubgroupIndex n → ℤ
  | .positiveLong _ => -1
  | .negativeLong _ => 1
  | .difference _ _ _ => 0
  | .positiveSum _ _ _ => -1
  | .negativeSum _ _ _ => 1

theorem two_mul_multiplierCoordinate (i : GLSymplecticFin.RootSubgroupIndex n) :
    2 * multiplierCoordinate i =
      negCharacterSum.{u} n ((Symplectic.diagonalRootDatum.{u} n).root i) := by
  cases i <;>
  simp [Symplectic.diagonalRootDatum_root_positiveLong,
    Symplectic.diagonalRootDatum_root_negativeLong, Symplectic.diagonalRootDatum_root_difference,
    Symplectic.diagonalRootDatum_root_positiveSum, Symplectic.diagonalRootDatum_root_negativeSum]

end GeneralSpin

open GeneralSpin

/-- The character `Υ = 2ε₀ + ε₁ + ⋯ + εₙ` of `GSpin_{2n+1}`, the Clifford norm `ν`. -/
def gspinOddUpsilon : (ULift.{u} (Fin n) → ℤ) × ℤ :=
  (fun _ => 1, 2)

@[simp]
theorem gspinOddUpsilon_fst : (gspinOddUpsilon.{u} n).1 = fun _ => 1 :=
  (rfl)

@[simp]
theorem gspinOddUpsilon_snd : (gspinOddUpsilon.{u} n).2 = 2 :=
  (rfl)

/-- **The root datum of `GSpin_{2n+1}`** on `X = (ULift (Fin n) → ℤ) × ℤ`, the second factor
being `ℤε₀`: the root datum of `SO_{2n+1}` extended by the central cocharacter `ε₀∨`. Its roots
are those of `SO_{2n+1}` and its coroots are `εᵢ∨ - εⱼ∨`, `±(εᵢ∨ + εⱼ∨ - ε₀∨)`,
`±(2εᵢ∨ - ε₀∨)`. -/
noncomputable def gspinOddRootDatum :
    RootDatum (GLSymplecticFin.RootSubgroupIndex n) ((ULift.{u} (Fin n) → ℤ) × ℤ)
      ((ULift.{u} (Fin n) →₀ ℤ) × ℤ) :=
  (soOddRootDatum.{u} n).extendCoroot (negCharacterSum n) multiplierCoordinate fun i => by
    rw [soOddRootDatum_coroot]
    exact two_mul_multiplierCoordinate n i

/-- **The root datum of `GSp₂ₙ`** on `X = (ULift (Fin n) →₀ ℤ) × ℤ`: the root datum of `Sp₂ₙ`
extended by the multiplier `ε₀`. Its roots are `εᵢ - εⱼ`, `±(εᵢ + εⱼ - ε₀)`, `±(2εᵢ - ε₀)` and its
coroots are those of `Sp₂ₙ`. It is the extension `RootPairing.extendRoot` of the root datum of
`Sp₂ₙ` (`gspRootDatum_eq_extendRoot`), defined as the dual of the root datum of `GSpin_{2n+1}`. -/
noncomputable def gspRootDatum :
    RootDatum (GLSymplecticFin.RootSubgroupIndex n) ((ULift.{u} (Fin n) →₀ ℤ) × ℤ)
      ((ULift.{u} (Fin n) → ℤ) × ℤ) :=
  (gspinOddRootDatum n).flip

/-- **`GSpin_{2n+1}^∨ = GSp₂ₙ`**: the dual of the root datum of `GSpin_{2n+1}` is the root datum
of `GSp₂ₙ`, with `ε₀∨` dual to the multiplier `ε₀`. -/
theorem flip_gspinOddRootDatum : (gspinOddRootDatum.{u} n).flip = gspRootDatum.{u} n :=
  (rfl)

/-- **`GSp₂ₙ^∨ = GSpin_{2n+1}`.** -/
theorem flip_gspRootDatum : (gspRootDatum.{u} n).flip = gspinOddRootDatum.{u} n :=
  (gspinOddRootDatum.{u} n).flip_flip

/-- The root datum of `GSp₂ₙ` is the extension of the root datum of `Sp₂ₙ` by the multiplier
`ε₀`, with roots `(αᵢ, multiplierCoordinate i)` and the coroots of `Sp₂ₙ`. -/
theorem gspRootDatum_eq_extendRoot :
    gspRootDatum.{u} n = (Symplectic.diagonalRootDatum.{u} n).extendRoot (negCharacterSum n)
      multiplierCoordinate (two_mul_multiplierCoordinate n) := by
  rw [gspRootDatum, gspinOddRootDatum, RootPairing.flip_extendCoroot]
  congr 1
  exact flip_soOddRootDatum n

/-- The pairing of `GSpin_{2n+1}`: the dot product on the first factors plus the product of the
`ε₀`-coordinates. -/
@[simp]
theorem gspinOddRootDatum_toLinearMap_apply (x : (ULift.{u} (Fin n) → ℤ) × ℤ)
    (y : (ULift.{u} (Fin n) →₀ ℤ) × ℤ) :
    (gspinOddRootDatum.{u} n).toLinearMap x y = SplitTorus.dotPairing y.1 x.1 + x.2 * y.2 := by
  rw [gspinOddRootDatum, RootPairing.extendCoroot_toLinearMap, RootPairing.extendPairing_apply,
    soOddRootDatum_toLinearMap_apply]

/-- The pairing of `GSp₂ₙ`: the dot product on the first factors plus the product of the
`ε₀`-coordinates. -/
@[simp]
theorem gspRootDatum_toLinearMap_apply (x : (ULift.{u} (Fin n) →₀ ℤ) × ℤ)
    (y : (ULift.{u} (Fin n) → ℤ) × ℤ) :
    (gspRootDatum.{u} n).toLinearMap x y = SplitTorus.dotPairing x.1 y.1 + x.2 * y.2 := by
  rw [gspRootDatum_eq_extendRoot, RootPairing.extendRoot_toLinearMap_apply,
    Symplectic.diagonalRootDatum_toLinearMap]

/-- The roots of `GSpin_{2n+1}` are the roots of `SO_{2n+1}`, with `ε₀`-coordinate zero. -/
@[simp]
theorem gspinOddRootDatum_root (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspinOddRootDatum.{u} n).root i = ((soOddRootDatum.{u} n).root i, 0) := by
  rw [gspinOddRootDatum, RootPairing.extendCoroot_root]

/-- The coroots of `GSpin_{2n+1}` project to the coroots of `SO_{2n+1}`; their `ε₀∨`-coordinate
is `multiplierCoordinate`. -/
@[simp]
theorem gspinOddRootDatum_coroot (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspinOddRootDatum.{u} n).coroot i =
      ((soOddRootDatum.{u} n).coroot i, multiplierCoordinate i) := by
  rw [gspinOddRootDatum, RootPairing.extendCoroot_coroot]

/-- The roots of `GSp₂ₙ` project to the roots of `Sp₂ₙ`; their `ε₀`-coordinate is
`multiplierCoordinate`. -/
@[simp]
theorem gspRootDatum_root (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspRootDatum.{u} n).root i =
      ((Symplectic.diagonalRootDatum.{u} n).root i, multiplierCoordinate i) := by
  rw [gspRootDatum_eq_extendRoot, RootPairing.extendRoot_root]

/-- The coroots of `GSp₂ₙ` are the coroots of `Sp₂ₙ`, with `ε₀∨`-coordinate zero. -/
@[simp]
theorem gspRootDatum_coroot (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspRootDatum.{u} n).coroot i = ((Symplectic.diagonalRootDatum.{u} n).coroot i, 0) := by
  rw [gspRootDatum_eq_extendRoot, RootPairing.extendRoot_coroot]

/-- The coroot of the short root `ε_{i+1}` of `GSpin_{2n+1}` is `2ε_{i+1}∨ - ε₀∨`. -/
theorem gspinOddRootDatum_coroot_positiveLong (i : Fin n) :
    (gspinOddRootDatum.{u} n).coroot (.positiveLong i) = (Finsupp.single (ULift.up i) 2, -1) := by
  rw [gspinOddRootDatum_coroot, soOddRootDatum_coroot,
    Symplectic.diagonalRootDatum_root_positiveLong]
  rfl

/-- For `i < j`, the coroot of `ε_{i+1} + ε_{j+1}` in `GSpin_{2n+1}` is
`ε_{i+1}∨ + ε_{j+1}∨ - ε₀∨`. -/
theorem gspinOddRootDatum_coroot_positiveSum {i j : Fin n} (hij : i < j) :
    (gspinOddRootDatum.{u} n).coroot (.positiveSum i j hij) =
      (Finsupp.single (ULift.up i) 1 + Finsupp.single (ULift.up j) 1, -1) := by
  rw [gspinOddRootDatum_coroot, soOddRootDatum_coroot,
    Symplectic.diagonalRootDatum_root_positiveSum]
  rfl

/-- The short root `ε_{i+1}` of `GSpin_{2n+1}`. -/
theorem gspinOddRootDatum_root_positiveLong (i : Fin n) :
    (gspinOddRootDatum.{u} n).root (.positiveLong i) = (Pi.single (ULift.up i) 1, 0) := by
  rw [gspinOddRootDatum_root, soOddRootDatum_root,
    Symplectic.diagonalRootDatum_coroot_positiveLong]

/-- The long root `2ε_{i+1} - ε₀` of `GSp₂ₙ`. -/
theorem gspRootDatum_root_positiveLong (i : Fin n) :
    (gspRootDatum.{u} n).root (.positiveLong i) = (Finsupp.single (ULift.up i) 2, -1) := by
  rw [← flip_gspinOddRootDatum, RootPairing.flip_root, gspinOddRootDatum_coroot_positiveLong]

/-- For `i < j`, the root `ε_{i+1} + ε_{j+1} - ε₀` of `GSp₂ₙ`. -/
theorem gspRootDatum_root_positiveSum {i j : Fin n} (hij : i < j) :
    (gspRootDatum.{u} n).root (.positiveSum i j hij) =
      (Finsupp.single (ULift.up i) 1 + Finsupp.single (ULift.up j) 1, -1) := by
  rw [← flip_gspinOddRootDatum, RootPairing.flip_root, gspinOddRootDatum_coroot_positiveSum]

/-- The coroot `ε_{i+1}∨` of the long root `2ε_{i+1} - ε₀` of `GSp₂ₙ`. -/
theorem gspRootDatum_coroot_positiveLong (i : Fin n) :
    (gspRootDatum.{u} n).coroot (.positiveLong i) = (Pi.single (ULift.up i) 1, 0) := by
  rw [← flip_gspinOddRootDatum, RootPairing.flip_coroot, gspinOddRootDatum_root_positiveLong]

/-- **`ε₀∨` is central in `GSpin_{2n+1}`**: it pairs to zero with every root. -/
theorem gspinOddRootDatum_toLinearMap_root_inr (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspinOddRootDatum.{u} n).toLinearMap ((gspinOddRootDatum.{u} n).root i) (0, 1) = 0 :=
  RootPairing.extendCoroot_toLinearMap_root_inr _ _ _ _ i

/-- **The Clifford norm `Υ = 2ε₀ + ε₁ + ⋯ + εₙ` of `GSpin_{2n+1}`** pairs to zero with every
coroot. -/
theorem gspinOddRootDatum_toLinearMap_gspinOddUpsilon_coroot
    (i : GLSymplecticFin.RootSubgroupIndex n) :
    (gspinOddRootDatum.{u} n).toLinearMap (gspinOddUpsilon n)
      ((gspinOddRootDatum.{u} n).coroot i) = 0 :=
  RootPairing.extendCoroot_toLinearMap_coroot_of_eq_neg _ _ _ _ (fun y => by
    rw [soOddRootDatum_toLinearMap_apply, negCharacterSum_apply, neg_neg]) i

/-- `Υ` pairs with `ε₀∨` to `2`. -/
theorem gspinOddRootDatum_toLinearMap_gspinOddUpsilon_inr :
    (gspinOddRootDatum.{u} n).toLinearMap (gspinOddUpsilon n) (0, 1) = 2 :=
  RootPairing.extendCoroot_toLinearMap_inr _ _ _ _ _

/-- **The base of `GSpin_{2n+1}`**: simple roots `εᵢ - εᵢ₊₁` and `εₙ`, with simple coroots
`εᵢ∨ - εᵢ₊₁∨` and `2εₙ∨ - ε₀∨`: the extension of the base `TauCeti.soOddBase` of `SO_{2n+1}`. -/
noncomputable def gspinOddBase : (gspinOddRootDatum.{u} n).Base :=
  (soOddBase.{u} n).extendCoroot _ _ _

/-- **The base of `GSp₂ₙ`**: simple roots `εᵢ - εᵢ₊₁` and `2εₙ - ε₀`. -/
noncomputable def gspBase : (gspRootDatum.{u} n).Base :=
  (gspinOddBase n).flip

/-- The simple roots of `GSpin_{2n+1}` are indexed by `TauCeti.Symplectic.diagonalSimpleRootIndex`.
-/
theorem mem_gspinOddBase_support (p : GLSymplecticFin.RootSubgroupIndex n) :
    p ∈ (gspinOddBase.{u} n).support ↔ ∃ i, Symplectic.diagonalSimpleRootIndex n i = p := by
  rw [gspinOddBase, RootPairing.Base.extendCoroot_support, mem_soOddBase_support]

/-- The simple roots of `GSp₂ₙ` are indexed by `TauCeti.Symplectic.diagonalSimpleRootIndex`. -/
theorem mem_gspBase_support (p : GLSymplecticFin.RootSubgroupIndex n) :
    p ∈ (gspBase.{u} n).support ↔ ∃ i, Symplectic.diagonalSimpleRootIndex n i = p := by
  rw [gspBase, RootPairing.Base.flip_support]
  exact mem_gspinOddBase_support n p

end Odd

/-! ### The even general spin group and the general special orthogonal group -/

section Even

open DynkinType

variable (n : ℕ)

namespace GeneralSpin

/-- The linear form `y ↦ -(y₁ + ⋯ + yₙ)` on `ℤⁿ`. -/
noncomputable def negCoordinateSum : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  -dotProductEquiv ℤ (Fin n) 1

@[simp]
theorem negCoordinateSum_apply (y : Fin n → ℤ) : negCoordinateSum n y = -(1 ⬝ᵥ y) :=
  (rfl)

/-- The `ε₀∨`-coordinate of the coroots of `GSpin_{2n}`, and the `ε₀`-coordinate of the roots of
`GSO₂ₙ`: minus half the coordinate sum of the root `±εᵢ ± εⱼ`. -/
def halfNegCoordinateSum {n : ℕ} (x : TypeDRoot n) : ℤ :=
  -(∑ i, x.val i) / 2

theorem two_mul_halfNegCoordinateSum (x : TypeDRoot n) :
    2 * halfNegCoordinateSum x = negCoordinateSum n x.val := by
  obtain ⟨k, hk⟩ := even_sum_typeDRoot x
  rw [halfNegCoordinateSum, negCoordinateSum_apply, one_dotProduct, hk, ← two_mul, ← mul_neg,
    Int.mul_ediv_cancel_left _ two_ne_zero]

end GeneralSpin

open GeneralSpin

/-- The character `Υ = 2ε₀ + ε₁ + ⋯ + εₙ` of `GSpin_{2n}`, the Clifford norm `ν`. -/
def gspinEvenUpsilon : (Fin n → ℤ) × ℤ :=
  (1, 2)

@[simp]
theorem gspinEvenUpsilon_fst : (gspinEvenUpsilon n).1 = 1 :=
  (rfl)

@[simp]
theorem gspinEvenUpsilon_snd : (gspinEvenUpsilon n).2 = 2 :=
  (rfl)

/-- **The root datum of `GSpin_{2n}`** on `X = (Fin n → ℤ) × ℤ`: the root datum of `SO_{2n}`
extended by the central cocharacter `ε₀∨`. Its roots are `±εᵢ ± εⱼ` and its coroots are
`εᵢ∨ - εⱼ∨` and `±(εᵢ∨ + εⱼ∨ - ε₀∨)`. -/
noncomputable def gspinEvenRootDatum :
    RootDatum (TypeDRoot n) ((Fin n → ℤ) × ℤ) ((Fin n → ℤ) × ℤ) :=
  (typeDClassicalRootDatum n).extendCoroot (negCoordinateSum n) halfNegCoordinateSum fun x => by
    rw [typeDClassicalRootDatum_coroot]
    exact two_mul_halfNegCoordinateSum n x

/-- **The root datum of `GSO₂ₙ`** on `X = (Fin n → ℤ) × ℤ`: the root datum of `SO_{2n}` extended
by the multiplier `ε₀`. Its roots are `εᵢ - εⱼ` and `±(εᵢ + εⱼ - ε₀)` and its coroots are
`±εᵢ∨ ± εⱼ∨`. -/
noncomputable def gsoRootDatum : RootDatum (TypeDRoot n) ((Fin n → ℤ) × ℤ) ((Fin n → ℤ) × ℤ) :=
  (typeDClassicalRootDatum n).extendRoot (negCoordinateSum n) halfNegCoordinateSum fun x => by
    rw [typeDClassicalRootDatum_root]
    exact two_mul_halfNegCoordinateSum n x

/-- The roots of `GSpin_{2n}` are the roots `±εᵢ ± εⱼ` of `SO_{2n}`, with `ε₀`-coordinate zero. -/
@[simp]
theorem gspinEvenRootDatum_root (x : TypeDRoot n) :
    (gspinEvenRootDatum n).root x = (x.val, 0) := by
  rw [gspinEvenRootDatum, RootPairing.extendCoroot_root, typeDClassicalRootDatum_root]

/-- The coroots of `GSpin_{2n}` project to the coroots of `SO_{2n}`. -/
@[simp]
theorem gspinEvenRootDatum_coroot (x : TypeDRoot n) :
    (gspinEvenRootDatum n).coroot x = (x.val, halfNegCoordinateSum x) := by
  rw [gspinEvenRootDatum, RootPairing.extendCoroot_coroot, typeDClassicalRootDatum_coroot]

@[simp]
theorem gsoRootDatum_root (x : TypeDRoot n) :
    (gsoRootDatum n).root x = (x.val, halfNegCoordinateSum x) := by
  rw [gsoRootDatum, RootPairing.extendRoot_root, typeDClassicalRootDatum_root]

@[simp]
theorem gsoRootDatum_coroot (x : TypeDRoot n) : (gsoRootDatum n).coroot x = (x.val, 0) := by
  rw [gsoRootDatum, RootPairing.extendRoot_coroot, typeDClassicalRootDatum_coroot]

/-- The pairing of `GSpin_{2n}`: the dot product on the first factors plus the product of the
`ε₀`-coordinates. -/
@[simp]
theorem gspinEvenRootDatum_toLinearMap_apply (x y : (Fin n → ℤ) × ℤ) :
    (gspinEvenRootDatum n).toLinearMap x y = x.1 ⬝ᵥ y.1 + x.2 * y.2 := by
  rw [gspinEvenRootDatum, RootPairing.extendCoroot_toLinearMap, RootPairing.extendPairing_apply,
    typeDClassicalRootDatum_toLinearMap_apply]

/-- The pairing of `GSO₂ₙ`: the dot product on the first factors plus the product of the
`ε₀`-coordinates. -/
@[simp]
theorem gsoRootDatum_toLinearMap_apply (x y : (Fin n → ℤ) × ℤ) :
    (gsoRootDatum n).toLinearMap x y = x.1 ⬝ᵥ y.1 + x.2 * y.2 := by
  rw [gsoRootDatum, RootPairing.extendRoot_toLinearMap_apply,
    typeDClassicalRootDatum_toLinearMap_apply]

/-- **`GSpin_{2n}^∨ = GSO₂ₙ`**: the dual of the root datum of `GSpin_{2n}` is the root datum of
`GSO₂ₙ`, with `ε₀∨` dual to the multiplier `ε₀`. -/
theorem flip_gspinEvenRootDatum : (gspinEvenRootDatum n).flip = gsoRootDatum n :=
  (RootPairing.flip_extendCoroot _ _ _ _).trans <| by
    rw [gsoRootDatum]
    congr 1
    exact flip_typeDClassicalRootDatum

/-- **`ε₀∨` is central in `GSpin_{2n}`**: it pairs to zero with every root. -/
theorem gspinEvenRootDatum_toLinearMap_root_inr (x : TypeDRoot n) :
    (gspinEvenRootDatum n).toLinearMap ((gspinEvenRootDatum n).root x) (0, 1) = 0 :=
  RootPairing.extendCoroot_toLinearMap_root_inr _ _ _ _ x

/-- **The Clifford norm `Υ = 2ε₀ + ε₁ + ⋯ + εₙ` of `GSpin_{2n}`** pairs to zero with every
coroot. -/
theorem gspinEvenRootDatum_toLinearMap_gspinEvenUpsilon_coroot (x : TypeDRoot n) :
    (gspinEvenRootDatum n).toLinearMap (gspinEvenUpsilon n) ((gspinEvenRootDatum n).coroot x) =
      0 :=
  RootPairing.extendCoroot_toLinearMap_coroot_of_eq_neg _ _ _ _ (fun y => by
    rw [typeDClassicalRootDatum_toLinearMap_apply, negCoordinateSum_apply, neg_neg]) x

/-- `Υ` pairs with `ε₀∨` to `2`. -/
theorem gspinEvenRootDatum_toLinearMap_gspinEvenUpsilon_inr :
    (gspinEvenRootDatum n).toLinearMap (gspinEvenUpsilon n) (0, 1) = 2 :=
  RootPairing.extendCoroot_toLinearMap_inr _ _ _ _ _

variable {n} (hn : 2 ≤ n)

/-- **The base of `GSpin_{2n}`**, for `2 ≤ n`: simple roots `εᵢ - εᵢ₊₁` and `εₙ₋₁ + εₙ`, with
simple coroots `εᵢ∨ - εᵢ₊₁∨` and `εₙ₋₁∨ + εₙ∨ - ε₀∨`. -/
noncomputable def gspinEvenBase : (gspinEvenRootDatum n).Base :=
  (typeDClassicalBase hn).extendCoroot _ _ _

/-- **The base of `GSO₂ₙ`**, for `2 ≤ n`: simple roots `εᵢ - εᵢ₊₁` and `εₙ₋₁ + εₙ - ε₀`. -/
noncomputable def gsoBase : (gsoRootDatum n).Base :=
  (typeDClassicalBase hn).extendRoot _ _ _

/-- The simple roots of `GSpin_{2n}` are the Bourbaki simple roots of type `Dₙ`. -/
theorem mem_gspinEvenBase_support {x : TypeDRoot n} :
    x ∈ (gspinEvenBase hn).support ↔ ∃ i, typeDClassicalSimpleIndex hn i = x := by
  rw [gspinEvenBase, RootPairing.Base.extendCoroot_support]
  exact mem_typeDClassicalBase_support hn

/-- The simple roots of `GSO₂ₙ` are the Bourbaki simple roots of type `Dₙ`. -/
theorem mem_gsoBase_support {x : TypeDRoot n} :
    x ∈ (gsoBase hn).support ↔ ∃ i, typeDClassicalSimpleIndex hn i = x := by
  rw [gsoBase, RootPairing.Base.extendRoot_support]
  exact mem_typeDClassicalBase_support hn

/-- The coroot of the last simple root `εₙ₋₁ + εₙ` of `GSpin_{2n}` is `εₙ₋₁∨ + εₙ∨ - ε₀∨`. -/
theorem gspinEvenRootDatum_coroot_typeDClassicalSimpleIndex_last :
    (gspinEvenRootDatum n).coroot (typeDClassicalSimpleIndex hn ⟨n - 1, by omega⟩) =
      (Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1, -1) := by
  rw [gspinEvenRootDatum_coroot, typeDClassicalSimpleIndex_val,
    typeDClassicalSimpleRoot_of_not_add_one_lt hn (by simp; omega)]
  congr 1
  rw [halfNegCoordinateSum, typeDClassicalSimpleIndex_val,
    typeDClassicalSimpleRoot_of_not_add_one_lt hn (by simp; omega)]
  simp [Finset.sum_add_distrib]

end Even

/-! ### Checks -/

/-- `GSpin₁` and `GSp₀` have no roots. -/
example : IsEmpty (GLSymplecticFin.RootSubgroupIndex 0) := inferInstance

/-- `GSpin₂` has no roots: there are no roots of type `D₁`. -/
example : IsEmpty (DynkinType.TypeDRoot 1) := inferInstance

/-- `GSpin₄` and `GSpin₆` have bases, of types `A₁ × A₁` and `A₃`, with two and three simple
roots. -/
example : (gspinEvenBase (n := 2) le_rfl).support.card = 2 ∧
    (gspinEvenBase (n := 3) (by norm_num)).support.card = 3 := by
  simp only [gspinEvenBase, RootPairing.Base.extendCoroot_support,
    DynkinType.card_typeDClassicalBase_support, and_self]

/-- In `GSp₄`, the coroot of the long root `2ε₁ - ε₀` is `ε₁∨`: it pairs to `0` with `ε₀` and to
`2` with `2ε₁ - ε₀`. -/
example :
    (gspRootDatum.{0} 2).toLinearMap (0, 1) ((gspRootDatum.{0} 2).coroot (.positiveLong 0)) = 0 ∧
      (gspRootDatum.{0} 2).toLinearMap ((gspRootDatum.{0} 2).root (.positiveLong 0))
        ((gspRootDatum.{0} 2).coroot (.positiveLong 0)) = 2 := by
  refine ⟨?_, (gspRootDatum.{0} 2).root_coroot_two _⟩
  simp [Symplectic.diagonalRootDatum_coroot_positiveLong]

end TauCeti
