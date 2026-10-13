/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Twist
public import TauCeti.Algebra.Homology.DG.Twisted.Map
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Twisting by a rank-one local system

A **rank-one local system** `L` on a pointed space `(B, b)`, with coefficients in a commutative
ring `R`, is the free module `R` in degree `0` on which a loop acts by a unit: here a monoid
homomorphism `ρ : Ω_b B →* Rˣ` on the Moore loops which is constant along paths, that is, a
character of `π₀(Ω_b B) = π₁(B, b)`.

Following the source's §2.3, `L` defines the map `Φ^L : C_*(Ω_b B) → C_*(Ω_b B)`,
`σ ↦ ρ(σ 0) • σ` on cubes, which is a morphism of DG algebras
(`TauCeti.RankOneLocalSystem.twist`, an instance of `TauCeti.cubicalChainTwist`).  It is an
automorphism, with inverse the twist by the inverse character.  The tensor product `𝓕 ⊗ L` of a
DG local system with `L`, on which a cube `σ` acts by `(α ⊗ ℓ) · σ = (α · ρ(σ 0) σ) ⊗ ℓ`, is the
pullback of `𝓕` along `Φ^L` (`TauCeti.RankOneLocalSystem.tensor`; its action is
`TauCeti.RankOneLocalSystem.tensor_smul_lof_ofCube`).

For a twisting cocycle `m` with values in `C_*(Ω_b B)`, the twisted cocycle `m^L = Φ^L ∘ m` is a
twisting cocycle, and the twisted complex of `𝓕 ⊗ L` with the cocycle `m` is isomorphic to the
twisted complex of `𝓕` with the cocycle `m^L`
(`TauCeti.RankOneLocalSystem.twistedCochainComplexIso`, the source's Proposition
`prop:FotimesL-mL`), so the two have isomorphic homology.

## Main definitions

* `TauCeti.RankOneLocalSystem B b R`: rank-one local systems on `(B, b)`.
* `TauCeti.RankOneLocalSystem.twist L`: the DG algebra automorphism `Φ^L` of `C_*(Ω_b B)`.
* `TauCeti.RankOneLocalSystem.tensor L`: the functor `𝓕 ↦ 𝓕 ⊗ L` on DG local systems.
* `TauCeti.RankOneLocalSystem.twistCocycle L m`: the twisted cocycle `m^L`.

## Main results

* `TauCeti.RankOneLocalSystem.twist_comp_twist_inv`: `Φ^L` is invertible.
* `TauCeti.RankOneLocalSystem.twistedCochainComplexIso`: the twisted complex of `𝓕 ⊗ L` is the
  twisted complex of `𝓕` with the cocycle `m^L`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §12 and Remark 4.6.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe uM

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- A **rank-one local system** on the pointed space `(B, b)`: a character of the Moore loops at
`b` with values in the units of `R`, constant along paths of loops. -/
structure RankOneLocalSystem where
  /-- The action of a loop on the free module `R` of rank one. -/
  ρ : MooreLoopSpace B b →* Rˣ
  /-- The action depends only on the path component of the loop. -/
  eq_of_joined : ∀ ⦃γ δ : MooreLoopSpace B b⦄, Joined γ δ → ρ γ = ρ δ

namespace RankOneLocalSystem

variable {B b R} (L : RankOneLocalSystem B b R)

/-- The character `Ω_b B → R` of a rank-one local system, with values in `R`. -/
def character : MooreLoopSpace B b →* R :=
  (Units.coeHom R).comp L.ρ

@[simp]
theorem character_apply (γ : MooreLoopSpace B b) : L.character γ = (L.ρ γ : R) := by
  rw [character, MonoidHom.comp_apply, Units.coeHom_apply]

theorem character_eq_of_joined ⦃γ δ : MooreLoopSpace B b⦄ (h : Joined γ δ) :
    L.character γ = L.character δ := by
  rw [character_apply, character_apply, L.eq_of_joined h]

/-- The **twist `Φ^L`** of a rank-one local system: the DG algebra endomorphism of
`C_*(Ω_b B; R)` scaling a cube `σ` by `ρ (σ 0)`. -/
def twist : DGAlgHom (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b R) :=
  cubicalChainTwist R L.character L.character_eq_of_joined

/-- `Φ^L` on a cube: `Φ^L σ = ρ (σ 0) • σ`. -/
@[simp]
theorem twist_lof_ofCube {n : ℕ} (σ : SingularCube (MooreLoopSpace B b) n) :
    L.twist (cubicalChainLof (MooreLoopSpace B b) R n
        (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ)) =
      (L.ρ (σ 0) : R) • cubicalChainLof (MooreLoopSpace B b) R n
        (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ) := by
  rw [twist, cubicalChainTwist_lof, NormalizedCubicalChain.twist_ofCube, map_smul,
    character_apply]

/-- The inverse rank-one local system, acting through the inverse units. -/
instance : Inv (RankOneLocalSystem B b R) where
  inv L :=
    { ρ := L.ρ⁻¹
      eq_of_joined := fun _ _ h ↦ by rw [MonoidHom.inv_apply, MonoidHom.inv_apply,
        L.eq_of_joined h] }

@[simp]
theorem inv_ρ : L⁻¹.ρ = L.ρ⁻¹ :=
  rfl

/-- The trivial rank-one local system. -/
instance : One (RankOneLocalSystem B b R) where
  one :=
    { ρ := 1
      eq_of_joined := fun _ _ _ ↦ rfl }

@[simp]
theorem one_ρ : (1 : RankOneLocalSystem B b R).ρ = 1 :=
  rfl

/-- The twist of the trivial local system is the identity. -/
@[simp]
theorem twist_one :
    (1 : RankOneLocalSystem B b R).twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  have h : (1 : RankOneLocalSystem B b R).character = 1 := by
    ext γ
    simp
  rw [twist, ← cubicalChainTwist_one (G := MooreLoopSpace B b) (R := R)]
  congr

/-- **`Φ^L` is an automorphism**: its inverse is the twist of the inverse local system. -/
theorem twist_comp_twist_inv :
    L.twist.comp L⁻¹.twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  have h : L.character * L⁻¹.character = 1 := by
    ext γ
    simp
  rw [twist, twist, cubicalChainTwist_mul, ← cubicalChainTwist_one (G := MooreLoopSpace B b)]
  congr

/-- `Φ^L` is an automorphism: the twist of the inverse local system is a left inverse. -/
theorem twist_inv_comp_twist :
    L⁻¹.twist.comp L.twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  have h : L⁻¹.character * L.character = 1 := by
    ext γ
    simp
  rw [twist, twist, cubicalChainTwist_mul, ← cubicalChainTwist_one (G := MooreLoopSpace B b)]
  congr

/-- The **tensor product `𝓕 ⊗ L`** of a DG local system with a rank-one local system: the
pullback of `𝓕` along `Φ^L`. -/
abbrev tensor : DGLocalSystem.{uM} B b R ⥤ DGLocalSystem.{uM} B b R :=
  DGRightModuleCat.restrictScalars L.twist

/-- **The action on `𝓕 ⊗ L`**: a cube `σ` acts on `α ⊗ ℓ` by `ρ (σ 0)` times its action on `α`. -/
theorem tensor_smul_lof_ofCube (𝓕 : DGLocalSystem.{uM} B b R) {n : ℕ}
    (σ : SingularCube (MooreLoopSpace B b) n) (x : (L.tensor.obj 𝓕 : Type uM)) :
    DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕
        (op (cubicalChainLof (MooreLoopSpace B b) R n
          (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ)) • x) =
      (L.ρ (σ 0) : R) • (op (cubicalChainLof (MooreLoopSpace B b) R n
          (NormalizedCubicalChain.ofCube (MooreLoopSpace B b) R σ)) •
        DGRightModuleCat.restrictScalarsEquiv L.twist 𝓕 x) := by
  rw [DGRightModuleCat.restrictScalarsEquiv_smul, unop_op, twist_lof_ofCube, op_smul, smul_assoc]

end RankOneLocalSystem

/-- A **twisting cocycle with values in `C_*(Ω_b B; R)`**, on the generators `P` graded by `ind`. -/
abbrev LoopTwistingCocycle (P : Type*) [Fintype P] (ind : P → ℤ) : Type _ :=
  TwistingCocycle (R := R) (A := loopChainAlgebra B b R)
    (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
    P ind

namespace RankOneLocalSystem

variable {B b R} (L : RankOneLocalSystem B b R) {P : Type*} [Fintype P] {ind : P → ℤ}

/-- The **twisted cocycle `m^L = Φ^L ∘ m`** of a twisting cocycle with values in `C_*(Ω_b B)`. -/
abbrev twistCocycle
    (m : LoopTwistingCocycle B b R P ind) : LoopTwistingCocycle B b R P ind :=
  m.map L.twist

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece ℳ]
  {dM : M →ₗ[R] M}

/- The generic instance for a restricted grading needs the `Algebra` structure of the chain algebra
of the loop space while unifying, one pending-synthesis level deeper than instance search reaches,
so it is supplied from `gradedSMul_restrictScalarsGrading`. -/
/-- The action of `C_*(Ω_b B)` on a module restricted along `Φ^L` respects degrees. -/
instance (f : DGAlgHom (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b R)) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece
      (IsDGRightModule.restrictScalarsGrading (ℳ := ℳ) f) :=
  gradedSMul_restrictScalarsGrading f

/-- **The twisted complex of `𝓕 ⊗ L`** with a twisting cocycle `m` is isomorphic to the twisted
complex of `𝓕` with the twisted cocycle `m^L` (the source's Proposition `prop:FotimesL-mL`).
Here `𝓕 = (ℳ, dM)` and `𝓕 ⊗ L` is its restriction of scalars along `Φ^L`. -/
def twistedCochainComplexIso (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)
    (m : LoopTwistingCocycle B b R P ind) :
    m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) L.twist)
        (hM.restrictScalars L.twist) ≅
      (L.twistCocycle m).twistedCochainComplex dM hM :=
  m.twistedCochainComplexRestrictScalarsIso L.twist hM

/-- The homology of the twisted complex of `𝓕 ⊗ L` with the cocycle `m` is the homology of the
twisted complex of `𝓕` with the cocycle `m^L`. -/
def twistedHomologyIso (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)
    (m : LoopTwistingCocycle B b R P ind) (q : ℤ) :
    (m.twistedCochainComplex (IsDGRightModule.restrictScalarsDifferential (dM := dM) L.twist)
        (hM.restrictScalars L.twist)).homology q ≅
      ((L.twistCocycle m).twistedCochainComplex dM hM).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (L.twistedCochainComplexIso hM m)

end RankOneLocalSystem

end TauCeti

end
