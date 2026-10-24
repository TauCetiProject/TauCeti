/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Homology
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Cohomology
public import TauCeti.RepresentationTheory.CharacterTwist
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

As a classical local system, `L` is the representation of `π₁(B, b)` on `R` through its monodromy
`TauCeti.RankOneLocalSystem.monodromy`, the character sending the inverse of the class of a Moore
loop `γ` to `ρ γ`. On homology, twisting by `L` tensors with this representation:
`H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L` as representations of the fundamental group
(`TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod`), through the identification of
the homology of the restriction of `𝓕` along `Φ^L` with that of `𝓕`. Equivalently, the
representation on `H(𝓕 ⊗ L)` is the one on `H(𝓕)` rescaled by the monodromy
(`TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivCharTwist`). The point is that the class
of the point chain of `γ` in `H(C_*(Ω_b B))` is scaled by `ρ γ` under `Φ^L`. These statements
concern the total homology `H(𝓕)`, the direct sum of the `H_q(𝓕)`.

## Main definitions

* `TauCeti.RankOneLocalSystem B b R`: rank-one local systems on `(B, b)`.
* `TauCeti.RankOneLocalSystem.twist L`: the DG algebra automorphism `Φ^L` of `C_*(Ω_b B)`.
* `TauCeti.RankOneLocalSystem.tensor L`: the functor `𝓕 ↦ 𝓕 ⊗ L` on DG local systems.
* `TauCeti.RankOneLocalSystem.twistCocycle L m`: the twisted cocycle `m^L`.
* `TauCeti.RankOneLocalSystem.monodromy L`: the monodromy character `π₁(B, b) →* Rˣ`.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod`: `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L`.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivCharTwist`: the same, with `L` absorbed
  into the twist of the representation on `H(𝓕)` by the monodromy.

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

/-- Moore loops with the same class in the fundamental group act by the same unit. -/
theorem ρ_eq_of_fundamentalGroupHom_eq {γ δ : MooreLoopSpace B b}
    (h : MooreLoopSpace.fundamentalGroupHom b γ = MooreLoopSpace.fundamentalGroupHom b δ) :
    L.ρ γ = L.ρ δ := by
  rw [← MooreLoopSpace.zerothHomotopyEquivFundamentalGroup_mk,
    ← MooreLoopSpace.zerothHomotopyEquivFundamentalGroup_mk] at h
  exact L.eq_of_joined
    (Quotient.exact ((MooreLoopSpace.zerothHomotopyEquivFundamentalGroup b).injective h))

/-- **The monodromy of a rank-one local system**: the character of the fundamental group by
which it is a classical local system, sending the inverse of the class
`MooreLoopSpace.fundamentalGroupHom b γ` of a Moore loop to the unit `ρ γ` by which `γ` acts
(`TauCeti.RankOneLocalSystem.monodromy_fundamentalGroupHom_inv`). This is the convention of
`TauCeti.DGRightModuleCat.IsConcentratedInDegreeZero.representation`. -/
def monodromy : FundamentalGroup B b →* Rˣ where
  toFun g := L.ρ (Function.surjInv (MooreLoopSpace.fundamentalGroupHom_surjective b) g⁻¹)
  map_one' := by
    rw [inv_one, ← map_one L.ρ]
    exact L.ρ_eq_of_fundamentalGroupHom_eq (by
      rw [Function.surjInv_eq (MooreLoopSpace.fundamentalGroupHom_surjective b), map_one])
  map_mul' g g' := by
    rw [mul_comm, ← map_mul L.ρ]
    exact L.ρ_eq_of_fundamentalGroupHom_eq (by
      rw [map_mul, Function.surjInv_eq (MooreLoopSpace.fundamentalGroupHom_surjective b),
        Function.surjInv_eq (MooreLoopSpace.fundamentalGroupHom_surjective b),
        Function.surjInv_eq (MooreLoopSpace.fundamentalGroupHom_surjective b), mul_inv_rev])

/-- The monodromy of the inverse of the class of a Moore loop `γ` is the unit by which `γ`
acts. -/
theorem monodromy_fundamentalGroupHom_inv (γ : MooreLoopSpace B b) :
    L.monodromy (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ = L.ρ γ :=
  L.ρ_eq_of_fundamentalGroupHom_eq (by
    rw [Function.surjInv_eq (MooreLoopSpace.fundamentalGroupHom_surjective b), inv_inv])

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

section Homology

universe u

namespace RankOneLocalSystem

variable {B : Type u} [TopologicalSpace B] {b : B} {R : Type u} [CommRing R]
  (L : RankOneLocalSystem B b R)
  {M : Type uM} [AddCommGroup M] [Module R M] [Module (loopChainAlgebra B b R)ᵐᵒᵖ M]
  [IsScalarTower R (loopChainAlgebra B b R)ᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece ℳ]
  {dM : M →ₗ[R] M}

/-- On cohomology, `Φ^L` scales the class of the point chain of a Moore loop `γ` by `ρ γ`. -/
private theorem cohomologyMap_twist_groupAlgebraToLoopChainCohomology (γ : MooreLoopSpace B b) :
    L.twist.cohomologyMap (groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ))) =
      (L.ρ γ : R) • groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)) := by
  rw [groupAlgebraToLoopChainCohomology_of_fundamentalGroupHom, DGAlgHom.cohomologyMap_mk,
    ← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [DGAlgHom.cyclesMap_apply_coe, twist_lof_ofCube, SingularCube.point_apply]
  -- Scalar multiplication of cycles is computed on their underlying chains.
  rfl

/-- The class of `Φ^L` applied to the point chain of `γ` acts as `ρ γ` times the point chain. -/
private theorem cohomologyAction_cohomologyMap_twist
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (γ : MooreLoopSpace B b)
    (y : hM.Cohomology) :
    (hM.cohomologyAction (L.twist.cohomologyMap (groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ))))).unop y =
      (L.ρ γ : R) • (hM.cohomologyAction (groupAlgebraToLoopChainCohomology B b R
        (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)))).unop y := by
  rw [cohomologyMap_twist_groupAlgebraToLoopChainCohomology]
  exact congrArg (fun f : (Module.End R hM.Cohomology)ᵐᵒᵖ ↦ f.unop y) (map_smul _ _ _)

/- The steps below are explicit equations rather than one chain of rewrites: rewriting inside these
terms makes the unifier compare instance arguments of `H(𝓕 ⊗ L)` and `H(𝓕)` elaborated in
different contexts, which exhausts the heartbeat budget. -/
/-- On homology, the inverse of the class of a Moore loop `γ` acts on `H(𝓕 ⊗ L)` as `ρ γ` times
its action on `H(𝓕)`. -/
private theorem restrictScalarsCohomologyEquiv_cohomologyRepresentation
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (γ : MooreLoopSpace B b)
    (x : (hM.restrictScalars L.twist).Cohomology) :
    hM.restrictScalarsCohomologyEquiv L.twist
        ((hM.restrictScalars L.twist).cohomologyRepresentation
          (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ x) =
      (L.ρ γ : R) • hM.cohomologyRepresentation (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹
        (hM.restrictScalarsCohomologyEquiv L.twist x) :=
  calc hM.restrictScalarsCohomologyEquiv L.twist
        ((hM.restrictScalars L.twist).cohomologyRepresentation
          (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ x)
      = hM.restrictScalarsCohomologyEquiv L.twist
          (((hM.restrictScalars L.twist).cohomologyAction (groupAlgebraToLoopChainCohomology B b R
            (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)))).unop x) :=
        congrArg (fun φ ↦ hM.restrictScalarsCohomologyEquiv L.twist (φ x))
          ((hM.restrictScalars L.twist).cohomologyRepresentation_fundamentalGroupHom_inv γ)
    _ = (hM.cohomologyAction (L.twist.cohomologyMap (groupAlgebraToLoopChainCohomology B b R
            (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ))))).unop
          (hM.restrictScalarsCohomologyEquiv L.twist x) :=
        hM.restrictScalarsCohomologyEquiv_cohomologyAction L.twist _ x
    _ = (L.ρ γ : R) • (hM.cohomologyAction (groupAlgebraToLoopChainCohomology B b R
            (MonoidAlgebra.of R _ (MooreLoopSpace.fundamentalGroupHom b γ)))).unop
          (hM.restrictScalarsCohomologyEquiv L.twist x) :=
        L.cohomologyAction_cohomologyMap_twist hM γ _
    _ = _ := congrArg (fun φ : Module.End R hM.Cohomology ↦
          (L.ρ γ : R) • φ (hM.restrictScalarsCohomologyEquiv L.twist x))
        (hM.cohomologyRepresentation_fundamentalGroupHom_inv γ).symm

/-- **The homology of `𝓕 ⊗ L` is the homology of `𝓕` twisted by the monodromy of `L`**: the
identification of the homology of the restriction of `𝓕` along `Φ^L` with that of `𝓕` is an
equivalence from the representation of the fundamental group on `H(𝓕 ⊗ L)` to the representation
on `H(𝓕)` rescaled by the monodromy of `L`. Here `𝓕 = (ℳ, dM)`. -/
noncomputable def cohomologyRepresentationEquivCharTwist
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) :
    (hM.restrictScalars L.twist).cohomologyRepresentation.Equiv
      (hM.cohomologyRepresentation.charTwist L.monodromy) :=
  .mk (hM.restrictScalarsCohomologyEquiv L.twist) fun g ↦ LinearMap.ext fun x ↦ by
    obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective b g⁻¹
    obtain rfl : g = (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ := by rw [hγ, inv_inv]
    have hr : (L.ρ γ : R) = (L.monodromy (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ : R) := by
      rw [monodromy_fundamentalGroupHom_inv]
    exact (L.restrictScalarsCohomologyEquiv_cohomologyRepresentation hM γ x).trans
      ((congrArg (fun r : R ↦ r • hM.cohomologyRepresentation
        (MooreLoopSpace.fundamentalGroupHom b γ)⁻¹ (hM.restrictScalarsCohomologyEquiv L.twist x))
        hr).trans (Representation.charTwist_apply_apply _ _ _ _).symm)

/-- The equivalence `H(𝓕 ⊗ L) ≅ H(𝓕)` sends a class to the class of the same cycle. -/
@[simp]
theorem cohomologyRepresentationEquivCharTwist_apply
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)
    (x : (hM.restrictScalars L.twist).Cohomology) :
    L.cohomologyRepresentationEquivCharTwist hM x = hM.restrictScalarsCohomologyEquiv L.twist x :=
  (rfl)

/-- **The homology of `𝓕 ⊗ L` is the homology of `𝓕` tensored with `L`**, `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L`
as representations of the fundamental group (the source's §2.3), where `L` is the free module `R`
on which the fundamental group acts through the monodromy of `L`. A class is sent to the class of
the same cycle, tensored with `1`
(`TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod_apply`). -/
noncomputable def cohomologyRepresentationEquivTprod
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) :
    (hM.restrictScalars L.twist).cohomologyRepresentation.Equiv
      (hM.cohomologyRepresentation.tprod (Representation.ofLinearCharacter L.monodromy)) :=
  (L.cohomologyRepresentationEquivCharTwist hM).trans
    (Representation.tprodOfLinearCharacterEquivCharTwist _ _).symm

/-- The equivalence `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L` sends a class to the class of the same cycle, tensored
with `1`. -/
@[simp]
theorem cohomologyRepresentationEquivTprod_apply
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM)
    (x : (hM.restrictScalars L.twist).Cohomology) :
    L.cohomologyRepresentationEquivTprod hM x =
      hM.restrictScalarsCohomologyEquiv L.twist x ⊗ₜ[R] (1 : R) := by
  have h := (Representation.tprodOfLinearCharacterEquivCharTwist L.monodromy
    hM.cohomologyRepresentation).symm_apply_apply (hM.restrictScalarsCohomologyEquiv L.twist x ⊗ₜ 1)
  rw [Representation.tprodOfLinearCharacterEquivCharTwist_tmul, one_smul] at h
  exact h

end RankOneLocalSystem

end Homology

end TauCeti

end
