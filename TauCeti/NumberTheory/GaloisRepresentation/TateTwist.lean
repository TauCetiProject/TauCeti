/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.RepresentationTheory.Continuous.Determinant.Operations
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.BaseChange
public import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Topology.Algebra.ContinuousMonoidHom.CompactOpen
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Tate twists of continuous Galois representations

Let `F` be a field, `ℓ` a prime and `χ_ℓ = TauCeti.continuousLocalCyclotomicCharacter ℓ F` the
`ℓ`-adic cyclotomic character of `G_F`. For a topological `ℤ_ℓ`-algebra `A`, the character
`TauCeti.cyclotomicPow ℓ F A n = χ_ℓ ^ n : G_F →ₜ* Aˣ` is `χ_ℓ` composed with `ℤ_ℓ → A` and
raised to the power `n ∈ ℤ`. The **Tate twist** `M(n)` of a continuous representation `ρ` of
`G_F` over `A` is the twist `ρ(χ_ℓ ^ n)` (`TauCeti.ContinuousRep.tateTwist`), and
`TauCeti.ContinuousRep.cyclotomicLine ℓ F = ofCharacter χ_ℓ` is the line `ℤ_ℓ(1)`.

The twists satisfy `M(0) = M`, `M(m)(n) = M(m + n)`, `det M(n) = det M · χ_ℓ ^ (n · rank M)` for
`M` of constant rank, and commute with restriction to `G_{F'}` for a field extension `F'/F`, along
which `ℤ_ℓ(1)` restricts to `ℤ_ℓ(1)`. For `M` finite projective with the module topology the
contragredient of `M(n)` is `M^∨(−n)`. Over `ℤ_ℓ`, `ℤ_ℓ(−1)` is the line of `χ_ℓ⁻¹`
(`TauCeti.ContinuousRep.tateTwist_trivial_neg_one`), so `TauCeti.ContinuousRep.dualOfCharacterIso`
gives `ℤ_ℓ(1)^∨ ≅ ℤ_ℓ(−1)`.
Extending coefficients from `A` to an `A`-algebra `B` sends `χ_ℓ ^ n` with values in `Aˣ` to
`χ_ℓ ^ n` with values in `Bˣ`, so it commutes with Tate twists.

## Main definitions

* `TauCeti.cyclotomicPow ℓ F A n`: the character `χ_ℓ ^ n` of `G_F` with values in `Aˣ`.
* `TauCeti.ContinuousRep.cyclotomicLine ℓ F`: the line `ℤ_ℓ(1)`, `ofCharacter χ_ℓ`.
* `TauCeti.ContinuousRep.tateTwist ρ ℓ n`: the Tate twist `M(n) = M(χ_ℓ ^ n)`.

## Main results

* `TauCeti.ContinuousRep.tateTwist_zero`, `TauCeti.ContinuousRep.tateTwist_tateTwist`:
  `M(0) = M` and `M(m)(n) = M(m + n)`.
* `TauCeti.ContinuousRep.det_tateTwist`: `det M(n) = det M · χ_ℓ ^ (n · d)` for `M` of constant
  rank `d`.
* `TauCeti.ContinuousRep.res_tateTwist`, `TauCeti.ContinuousRep.res_cyclotomicLine`: restriction to
  `G_{F'}` commutes with Tate twists and sends `ℤ_ℓ(1)` to `ℤ_ℓ(1)`.
* `TauCeti.ContinuousRep.dual_tateTwist`: `M(n)^∨ = M^∨(−n)`.
* `TauCeti.unitsMapCharacter_cyclotomicPow`, `TauCeti.ContinuousRep.baseChange_tateTwist`:
  extending coefficients from `A` to `B` sends `χ_ℓ ^ n` to `χ_ℓ ^ n`, so it commutes with Tate
  twists.

## References

* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, revised version (2007) of Current
  Developments in Mathematics 1995, §2.1, p. 50.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type*) [Field F]

section Character

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
  [ContinuousSMul ℤ_[ℓ] A]

/-- **The `n`-th power of the cyclotomic character** `χ_ℓ ^ n : G_F → Aˣ`, for `n ∈ ℤ`, with values
in a topological `ℤ_ℓ`-algebra `A`. -/
def cyclotomicPow (n : ℤ) : Field.absoluteGaloisGroup F →ₜ* Aˣ :=
  ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F) ^ n

theorem cyclotomicPow_def (n : ℤ) :
    cyclotomicPow ℓ F A n =
      ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F) ^ n :=
  (rfl)

@[simp]
theorem cyclotomicPow_apply (n : ℤ) (σ : Field.absoluteGaloisGroup F) :
    cyclotomicPow ℓ F A n σ =
      ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F) σ ^ n :=
  ContinuousMonoidHom.zpow_apply _ n σ

@[simp]
theorem cyclotomicPow_zero : cyclotomicPow ℓ F A 0 = 1 :=
  zpow_zero _

theorem cyclotomicPow_add (m n : ℤ) :
    cyclotomicPow ℓ F A (m + n) = cyclotomicPow ℓ F A m * cyclotomicPow ℓ F A n :=
  zpow_add _ m n

theorem cyclotomicPow_neg (n : ℤ) : cyclotomicPow ℓ F A (-n) = (cyclotomicPow ℓ F A n)⁻¹ :=
  zpow_neg (ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F)) n

theorem cyclotomicPow_one :
    cyclotomicPow ℓ F A 1 =
      ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F) :=
  zpow_one _

theorem cyclotomicPow_pow (n : ℤ) (d : ℕ) :
    cyclotomicPow ℓ F A n ^ d = cyclotomicPow ℓ F A (n * d) :=
  ((zpow_mul (ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter ℓ F)) n d).trans
    (zpow_natCast _ d)).symm

theorem coe_cyclotomicPow_pow (n : ℤ) (d : ℕ) :
    (cyclotomicPow ℓ F A n : Field.absoluteGaloisGroup F →* Aˣ) ^ d =
      (cyclotomicPow ℓ F A (n * d) : Field.absoluteGaloisGroup F →* Aˣ) := by
  ext σ
  simp [zpow_mul]

/-- Over `ℤ_ℓ` itself, the first power is the cyclotomic character. -/
@[simp]
theorem cyclotomicPow_one_padicInt :
    cyclotomicPow ℓ F ℤ_[ℓ] 1 = continuousLocalCyclotomicCharacter ℓ F := by
  ext σ
  simp

/-- Over `ℤ_ℓ` itself, the `(-1)`-st power is the inverse of the cyclotomic character. -/
@[simp]
theorem cyclotomicPow_neg_one_padicInt :
    cyclotomicPow ℓ F ℤ_[ℓ] (-1) = (continuousLocalCyclotomicCharacter ℓ F)⁻¹ := by
  rw [cyclotomicPow_neg, cyclotomicPow_one_padicInt]

/-- **Extending coefficients** from `A` to an `A`-algebra `B` sends `χ_ℓ ^ n` with values in `Aˣ`
to `χ_ℓ ^ n` with values in `Bˣ`. -/
@[simp]
theorem unitsMapCharacter_cyclotomicPow (B : Type*) [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra ℤ_[ℓ] B] [ContinuousSMul ℤ_[ℓ] B] [Algebra A B]
    [ContinuousSMul A B] [IsScalarTower ℤ_[ℓ] A B] (n : ℤ) :
    ContinuousRep.unitsMapCharacter B (cyclotomicPow ℓ F A n) = cyclotomicPow ℓ F B n := by
  rw [cyclotomicPow_def, cyclotomicPow_def, ContinuousRep.unitsMapCharacter_zpow,
    ContinuousRep.unitsMapCharacter_unitsMapCharacter]

section Restriction

variable (F' : Type*) [Field F'] [Algebra F F'] [Algebra (AlgebraicClosure F) (AlgebraicClosure F')]
  [IsScalarTower F (AlgebraicClosure F) (AlgebraicClosure F')]

/-- **`χ_ℓ ^ n` restricts to `χ_ℓ ^ n`**: precomposed with `G_{F'} → G_F`, the `Aˣ`-valued
character `χ_ℓ ^ n` of `G_F` is that of `G_{F'}`. -/
@[simp]
theorem cyclotomicPow_comp_mapOfAlgebra (n : ℤ) :
    (cyclotomicPow ℓ F A n).comp (Field.absoluteGaloisGroup.mapOfAlgebra F F') =
      cyclotomicPow ℓ F' A n := by
  rw [cyclotomicPow_def, cyclotomicPow_def,
    ← continuousLocalCyclotomicCharacter_comp_mapOfAlgebra ℓ F F',
    ContinuousRep.unitsMapCharacter_comp, ← ContinuousMonoidHom.compLeft_apply, map_zpow,
    ContinuousMonoidHom.compLeft_apply]

end Restriction

end Character

namespace ContinuousRep

/-- **The line `ℤ_ℓ(1)`**: `ℤ_ℓ` with `G_F` acting through the cyclotomic character `χ_ℓ`. -/
def cyclotomicLine : ContinuousRep (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ] :=
  ofCharacter (continuousLocalCyclotomicCharacter ℓ F)

theorem cyclotomicLine_def :
    cyclotomicLine ℓ F = ofCharacter (continuousLocalCyclotomicCharacter ℓ F) :=
  (rfl)

@[simp]
theorem cyclotomicLine_apply (σ : Field.absoluteGaloisGroup F) (a : ℤ_[ℓ]) :
    cyclotomicLine ℓ F σ a = (localCyclotomicCharacter ℓ F σ : ℤ_[ℓ]) * a := by
  rw [cyclotomicLine_def, ofCharacter_apply, continuousLocalCyclotomicCharacter_apply]

/-- The line of the cyclotomic character `χ_ℓ` is `ℤ_ℓ(1)`. -/
@[simp]
theorem ofCharacter_continuousLocalCyclotomicCharacter :
    ofCharacter (continuousLocalCyclotomicCharacter ℓ F) = cyclotomicLine ℓ F :=
  (cyclotomicLine_def ℓ F).symm

/-- **The determinant of `ℤ_ℓ(1)`** is the cyclotomic character `χ_ℓ`. -/
@[simp]
theorem det_cyclotomicLine :
    (cyclotomicLine ℓ F).det =
      (continuousLocalCyclotomicCharacter ℓ F : Field.absoluteGaloisGroup F →* ℤ_[ℓ]ˣ) := by
  rw [cyclotomicLine_def, det_ofCharacter]

/-- **`ℤ_ℓ(1)` restricts to `ℤ_ℓ(1)`** along `G_{F'} → G_F`. -/
@[simp]
theorem res_cyclotomicLine (F' : Type*) [Field F'] [Algebra F F']
    [Algebra (AlgebraicClosure F) (AlgebraicClosure F')]
    [IsScalarTower F (AlgebraicClosure F) (AlgebraicClosure F')] :
    (cyclotomicLine ℓ F).res (Field.absoluteGaloisGroup.mapOfAlgebra F F') =
      cyclotomicLine ℓ F' := by
  rw [cyclotomicLine_def, cyclotomicLine_def, res_ofCharacter,
    continuousLocalCyclotomicCharacter_comp_mapOfAlgebra]

variable {ℓ F} {A M : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra ℤ_[ℓ] A] [ContinuousSMul ℤ_[ℓ] A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [ContinuousSMul A M]

variable (ℓ) in
/-- **The Tate twist** `M(n) = M(χ_ℓ ^ n)` of a continuous representation of `G_F` over a
topological `ℤ_ℓ`-algebra `A`. -/
def tateTwist (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (n : ℤ) :
    ContinuousRep (Field.absoluteGaloisGroup F) A M :=
  ρ.twist (cyclotomicPow ℓ F A n)

theorem tateTwist_def (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (n : ℤ) :
    ρ.tateTwist ℓ n = ρ.twist (cyclotomicPow ℓ F A n) :=
  (rfl)

@[simp]
theorem tateTwist_apply (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (n : ℤ)
    (σ : Field.absoluteGaloisGroup F) (x : M) :
    ρ.tateTwist ℓ n σ x = (cyclotomicPow ℓ F A n σ : A) • ρ σ x :=
  twist_apply _ _ σ x

/-- **The zeroth Tate twist** is the representation itself: `M(0) = M`. -/
@[simp]
theorem tateTwist_zero (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    ρ.tateTwist ℓ 0 = ρ := by
  simp [tateTwist_def]

/-- **Tate twists add**: `M(m)(n) = M(m + n)`. -/
@[simp]
theorem tateTwist_tateTwist (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (m n : ℤ) :
    (ρ.tateTwist ℓ m).tateTwist ℓ n = ρ.tateTwist ℓ (m + n) := by
  simp [tateTwist_def, add_comm m n, cyclotomicPow_add]

/-- The Tate twist of the trivial line is the line of `χ_ℓ ^ n`. -/
@[simp]
theorem tateTwist_trivial (n : ℤ) :
    (trivial (Field.absoluteGaloisGroup F) A A).tateTwist ℓ n =
      ofCharacter (cyclotomicPow ℓ F A n) :=
  twist_trivial _

/-- The line `ℤ_ℓ(1)` is the first Tate twist of the trivial line `ℤ_ℓ`. -/
theorem tateTwist_trivial_one :
    (trivial (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ 1 = cyclotomicLine ℓ F := by
  rw [tateTwist_trivial, cyclotomicPow_one_padicInt, cyclotomicLine_def]

/-- **The Tate twists of `ℤ_ℓ(1)`**: `ℤ_ℓ(1)(n)` is the line of `χ_ℓ ^ (1 + n)`. -/
@[simp]
theorem tateTwist_cyclotomicLine (n : ℤ) :
    (cyclotomicLine ℓ F).tateTwist ℓ n = ofCharacter (cyclotomicPow ℓ F ℤ_[ℓ] (1 + n)) := by
  rw [← tateTwist_trivial_one, tateTwist_tateTwist, tateTwist_trivial]

/-- **The line `ℤ_ℓ(−1)`**: the `(−1)`-st Tate twist of the trivial line is the line of
`χ_ℓ⁻¹`. -/
theorem tateTwist_trivial_neg_one :
    (trivial (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ (-1) =
      ofCharacter (continuousLocalCyclotomicCharacter ℓ F)⁻¹ := by
  rw [tateTwist_trivial, cyclotomicPow_neg_one_padicInt]

/-- **Restriction to `G_{F'}` commutes with Tate twists** along `G_{F'} → G_F`. -/
@[simp]
theorem res_tateTwist (F' : Type*) [Field F'] [Algebra F F']
    [Algebra (AlgebraicClosure F) (AlgebraicClosure F')]
    [IsScalarTower F (AlgebraicClosure F) (AlgebraicClosure F')]
    (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (n : ℤ) :
    (ρ.tateTwist ℓ n).res (Field.absoluteGaloisGroup.mapOfAlgebra F F') =
      (ρ.res (Field.absoluteGaloisGroup.mapOfAlgebra F F')).tateTwist ℓ n := by
  simp [tateTwist_def]

/-- **Extension of scalars commutes with Tate twists**: `B ⊗ M(n) = (B ⊗ M)(n)` for an
`A`-algebra `B`. -/
theorem baseChange_tateTwist [IsModuleTopology A M] [Module.Finite A M] (B : Type*) [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [Algebra ℤ_[ℓ] B] [ContinuousSMul ℤ_[ℓ] B]
    [Algebra A B] [ContinuousSMul A B] [IsScalarTower ℤ_[ℓ] A B] [TopologicalSpace (B ⊗[A] M)]
    [IsModuleTopology B (B ⊗[A] M)] (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (n : ℤ) :
    haveI := IsModuleTopology.toContinuousSMul B (B ⊗[A] M)
    (ρ.tateTwist ℓ n).baseChange B = (ρ.baseChange B).tateTwist ℓ n := by
  rw [tateTwist_def, tateTwist_def, baseChange_twist, unitsMapCharacter_cyclotomicPow]

/-- **The determinant of a Tate twist**: for `M` finite projective of constant rank `d`,
`det M(n) = det M · χ_ℓ ^ (n · d)`. -/
theorem det_tateTwist {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [ContinuousSMul A N] [Module.Finite A N] [Module.Projective A N] {d : ℕ}
    (hd : ∀ p, Module.rankAtStalk (R := A) N p = d)
    (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A N) (n : ℤ) :
    (ρ.tateTwist ℓ n).det =
      ρ.det * (cyclotomicPow ℓ F A (n * d) : Field.absoluteGaloisGroup F →* Aˣ) := by
  rw [tateTwist_def, det_twist hd, coe_cyclotomicPow_pow]

section Dual

variable {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [Module.Finite A N] [Module.Projective A N] [TopologicalSpace (Module.Dual A N)]
  [IsModuleTopology A (Module.Dual A N)]

/-- **Duality of Tate twists**: for `M` finite projective, `M(n)^∨ = M^∨(−n)`. -/
@[simp]
theorem dual_tateTwist (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A N) (n : ℤ) :
    haveI := IsModuleTopology.toContinuousSMul A N
    haveI := IsModuleTopology.toContinuousSMul A (Module.Dual A N)
    (ρ.tateTwist ℓ n).dual = ρ.dual.tateTwist ℓ (-n) := by
  have := IsModuleTopology.toContinuousSMul A N
  have := IsModuleTopology.toContinuousSMul A (Module.Dual A N)
  rw [tateTwist_def, tateTwist_def, dual_twist, cyclotomicPow_neg]

end Dual

end ContinuousRep

end TauCeti
