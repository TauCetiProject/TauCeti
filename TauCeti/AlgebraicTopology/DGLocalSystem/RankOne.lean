/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Homology
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Cohomology
public import TauCeti.RepresentationTheory.Character.Twist
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
concern the total homology `H(𝓕)`, the direct sum of the `H_q(𝓕)`. The identification preserves
degrees, so they restrict to each degree: `H_q(𝓕 ⊗ L) ≅ H_q(𝓕) ⊗ L`
(`TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivTprod`), stated in the
cohomological degree `p = -q`.

Rank-one local systems form a commutative group under the tensor product, on which loops act by
the product of the units. Twisting turns products into composites, `Φ^{L L'} = Φ^L ∘ Φ^{L'}`
(`TauCeti.RankOneLocalSystem.twist_mul`), so `𝓕 ⊗ (L L') ≅ (𝓕 ⊗ L) ⊗ L'`
(`TauCeti.RankOneLocalSystem.tensorMulIso`) and `m^{L L'} = (m^{L'})^L`. The monodromy is an
isomorphism of groups onto the characters `π₁(B, b) →* Rˣ`
(`TauCeti.RankOneLocalSystem.monodromyEquiv`), with inverse
`TauCeti.RankOneLocalSystem.ofMonodromy`, so a rank-one local system is a classical local system of
rank one.

Along a based map `f : (B, b) → (B', b')`, rank-one local systems pull back by letting a loop act
through its image (`TauCeti.RankOneLocalSystem.pullback`), a group homomorphism, functorial in `f`,
whose monodromy is the monodromy composed with `π₁(f)`. Twisting is natural in the space,
`C_*(Ωf) ∘ Φ^{f^* L} = Φ^L ∘ C_*(Ωf)`
(`TauCeti.RankOneLocalSystem.loopChainMap_comp_twist_pullback`), so pulling back DG local
systems commutes with tensoring, `f^*(𝓕 ⊗ L) ≅ f^* 𝓕 ⊗ f^* L`
(`TauCeti.RankOneLocalSystem.tensorPullbackIso`), and pushing a twisting cocycle forward along
`C_*(Ωf)` commutes with twisting. These are the operations by which twisting local systems such as
the orientation local system of a manifold, pulled back along the evaluation of free loops, are
combined.

## Main definitions

* `TauCeti.RankOneLocalSystem B b R`: rank-one local systems on `(B, b)`.
* `TauCeti.RankOneLocalSystem.twist L`: the DG algebra automorphism `Φ^L` of `C_*(Ω_b B)`.
* `TauCeti.RankOneLocalSystem.tensor L`: the functor `𝓕 ↦ 𝓕 ⊗ L` on DG local systems.
* `TauCeti.RankOneLocalSystem.twistCocycle L m`: the twisted cocycle `m^L`.
* `TauCeti.RankOneLocalSystem.monodromy L`: the monodromy character `π₁(B, b) →* Rˣ`.
* `TauCeti.RankOneLocalSystem.monodromyEquiv`: rank-one local systems are the characters of
  `π₁(B, b)`, with inverse `TauCeti.RankOneLocalSystem.ofMonodromy`.
* `TauCeti.RankOneLocalSystem.pullback f hf`: the pullback along a based map.
* `TauCeti.RankOneLocalSystem.tensorOneIso`, `TauCeti.RankOneLocalSystem.tensorMulIso`:
  `𝓕 ⊗ 1 ≅ 𝓕` and `𝓕 ⊗ (L L') ≅ (𝓕 ⊗ L) ⊗ L'`.
* `TauCeti.RankOneLocalSystem.tensorPullbackIso`: `f^*(𝓕 ⊗ L) ≅ f^* 𝓕 ⊗ f^* L`.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod`: `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L`.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivCharTwist`: the same, with `L` absorbed
  into the twist of the representation on `H(𝓕)` by the monodromy.
* `TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivTprod`: `H_q(𝓕 ⊗ L) ≅ H_q(𝓕) ⊗ L`
  in each degree.
* `TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivCharTwist`: the same, with `L`
  absorbed into the twist.

## Main results

* `TauCeti.RankOneLocalSystem.twist_comp_twist_inv`: `Φ^L` is invertible.
* `TauCeti.RankOneLocalSystem.twist_mul`: `Φ^{L L'} = Φ^L ∘ Φ^{L'}`.
* `TauCeti.RankOneLocalSystem.loopChainMap_comp_twist_pullback`: twisting is natural in the space.
* `TauCeti.RankOneLocalSystem.twistCocycle_mul`,
  `TauCeti.RankOneLocalSystem.twistCocycle_map_loopChainMap`: `m^{L L'} = (m^{L'})^L`, and
  twisting commutes with pushing cocycles forward.
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
@[ext]
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

/-- The **product** of rank-one local systems, their tensor product over `R`: a loop acts on
`R ⊗ R = R` by the product of the units by which it acts on the factors. -/
instance : Mul (RankOneLocalSystem B b R) where
  mul L L' :=
    { ρ := L.ρ * L'.ρ
      eq_of_joined := fun _ _ h ↦ by
        rw [MonoidHom.mul_apply, MonoidHom.mul_apply, L.eq_of_joined h, L'.eq_of_joined h] }

/-- The quotient of rank-one local systems, `L ⊗ L'⁻¹`. -/
instance : Div (RankOneLocalSystem B b R) where
  div L L' :=
    { ρ := L.ρ / L'.ρ
      eq_of_joined := fun _ _ h ↦ by
        rw [MonoidHom.div_apply, MonoidHom.div_apply, L.eq_of_joined h, L'.eq_of_joined h] }

/-- The tensor powers of a rank-one local system. -/
instance : Pow (RankOneLocalSystem B b R) ℕ where
  pow L n :=
    { ρ := L.ρ ^ n
      eq_of_joined := fun _ _ h ↦ by
        rw [MonoidHom.pow_apply, MonoidHom.pow_apply, L.eq_of_joined h] }

/-- The integer tensor powers of a rank-one local system. -/
instance : Pow (RankOneLocalSystem B b R) ℤ where
  pow L n :=
    { ρ := L.ρ ^ n
      eq_of_joined := fun _ _ h ↦ by
        rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, L.eq_of_joined h] }

@[simp]
theorem mul_ρ (L L' : RankOneLocalSystem B b R) : (L * L').ρ = L.ρ * L'.ρ :=
  rfl

@[simp]
theorem div_ρ (L L' : RankOneLocalSystem B b R) : (L / L').ρ = L.ρ / L'.ρ :=
  rfl

@[simp]
theorem pow_ρ (n : ℕ) : (L ^ n).ρ = L.ρ ^ n :=
  rfl

@[simp]
theorem zpow_ρ (n : ℤ) : (L ^ n).ρ = L.ρ ^ n :=
  rfl

/-- Rank-one local systems form a commutative group under the tensor product. -/
instance : CommGroup (RankOneLocalSystem B b R) :=
  Function.Injective.commGroup ρ (fun _ _ ↦ RankOneLocalSystem.ext) rfl (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The twist of the trivial local system is the identity. -/
@[simp]
theorem twist_one :
    (1 : RankOneLocalSystem B b R).twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  have h : (1 : RankOneLocalSystem B b R).character = 1 := by
    ext γ
    simp
  rw [twist, ← cubicalChainTwist_one (G := MooreLoopSpace B b) (R := R)]
  congr

/-- **The twist of a product is the composite of the twists**, `Φ^{L L'} = Φ^L ∘ Φ^{L'}`. -/
theorem twist_mul (L L' : RankOneLocalSystem B b R) : (L * L').twist = L.twist.comp L'.twist := by
  have h : (L * L').character = L.character * L'.character := by
    ext γ
    simp
  rw [twist, twist, twist, cubicalChainTwist_mul]
  congr

/-- **`Φ^L` is an automorphism**: its inverse is the twist of the inverse local system. -/
theorem twist_comp_twist_inv :
    L.twist.comp L⁻¹.twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  rw [← twist_mul, mul_inv_cancel, twist_one]

/-- `Φ^L` is an automorphism: the twist of the inverse local system is a left inverse. -/
theorem twist_inv_comp_twist :
    L⁻¹.twist.comp L.twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  rw [← twist_mul, inv_mul_cancel, twist_one]

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

/-- **Tensoring with the trivial local system** is isomorphic to the identity, `𝓕 ⊗ 1 ≅ 𝓕`. -/
def tensorOneIso : tensor.{uM} (1 : RankOneLocalSystem B b R) ≅ 𝟭 _ :=
  eqToIso (by rw [tensor, twist_one]) ≪≫ DGRightModuleCat.restrictScalarsId

/-- The component of `tensorOneIso` at `𝓕`. -/
@[simp]
theorem tensorOneIso_hom_app (𝓕 : DGLocalSystem.{uM} B b R) :
    tensorOneIso.hom.app 𝓕 =
      eqToHom (by rw [tensor, twist_one]) ≫ (DGRightModuleCat.restrictScalarsIdApp 𝓕).hom := by
  simp [tensorOneIso, ← Iso.app_hom, DGRightModuleCat.restrictScalarsId_app]

/-- The component of the inverse of `tensorOneIso` at `𝓕`. -/
@[simp]
theorem tensorOneIso_inv_app (𝓕 : DGLocalSystem.{uM} B b R) :
    tensorOneIso.inv.app 𝓕 =
      (DGRightModuleCat.restrictScalarsIdApp 𝓕).inv ≫ eqToHom (by rw [tensor, twist_one]) := by
  simp [tensorOneIso, ← Iso.app_inv, DGRightModuleCat.restrictScalarsId_app]

/-- **Tensoring with a product is tensoring twice**, `𝓕 ⊗ (L L') ≅ (𝓕 ⊗ L) ⊗ L'`. -/
def tensorMulIso (L L' : RankOneLocalSystem B b R) :
    tensor.{uM} (L * L') ≅ L.tensor ⋙ L'.tensor :=
  eqToIso (by rw [tensor, twist_mul]) ≪≫ DGRightModuleCat.restrictScalarsComp _ _

/-- The component of `tensorMulIso` at `𝓕`. -/
@[simp]
theorem tensorMulIso_hom_app (L L' : RankOneLocalSystem B b R) (𝓕 : DGLocalSystem.{uM} B b R) :
    (tensorMulIso L L').hom.app 𝓕 =
      eqToHom (by rw [tensor, twist_mul]) ≫
        (DGRightModuleCat.restrictScalarsCompApp L'.twist L.twist 𝓕).hom := by
  simp [tensorMulIso, ← Iso.app_hom, DGRightModuleCat.restrictScalarsComp_app]

/-- The component of the inverse of `tensorMulIso` at `𝓕`. -/
@[simp]
theorem tensorMulIso_inv_app (L L' : RankOneLocalSystem B b R) (𝓕 : DGLocalSystem.{uM} B b R) :
    (tensorMulIso L L').inv.app 𝓕 =
      (DGRightModuleCat.restrictScalarsCompApp L'.twist L.twist 𝓕).inv ≫
        eqToHom (by rw [tensor, twist_mul]) := by
  simp [tensorMulIso, ← Iso.app_inv, DGRightModuleCat.restrictScalarsComp_app]

/-- Moore loops with the same class in the fundamental group act by the same unit. -/
theorem ρ_eq_of_fundamentalGroupHom_eq {γ δ : MooreLoopSpace B b}
    (h : MooreLoopSpace.fundamentalGroupHom b γ = MooreLoopSpace.fundamentalGroupHom b δ) :
    L.ρ γ = L.ρ δ :=
  L.eq_of_joined (MooreLoopSpace.fundamentalGroupHom_eq_iff_joined.1 h)

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

/-- The monodromy of the class of a Moore loop `γ` is the inverse of the unit by which `γ` acts. -/
theorem monodromy_fundamentalGroupHom (γ : MooreLoopSpace B b) :
    L.monodromy (MooreLoopSpace.fundamentalGroupHom b γ) = (L.ρ γ)⁻¹ := by
  rw [← monodromy_fundamentalGroupHom_inv, map_inv, inv_inv]

/-- The monodromy of the fundamental-group class of the path underlying a Moore loop `γ` is the
unit by which `γ` acts. This is `monodromy_fundamentalGroupHom_inv` in simp normal form. -/
@[simp]
theorem monodromy_fromPath_mk_toPath (γ : MooreLoopSpace B b) :
    L.monodromy (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ.toPath)) = L.ρ γ := by
  simpa using L.monodromy_fundamentalGroupHom_inv γ

/-- The monodromy of a product is the product of the monodromies. -/
@[simp]
theorem monodromy_mul (L L' : RankOneLocalSystem B b R) :
    (L * L').monodromy = L.monodromy * L'.monodromy :=
  MooreLoopSpace.fundamentalGroup_hom_ext fun γ ↦ by
    simp only [monodromy_fundamentalGroupHom, MonoidHom.mul_apply, mul_ρ, mul_inv]

/-- The trivial local system has trivial monodromy. -/
@[simp]
theorem monodromy_one : (1 : RankOneLocalSystem B b R).monodromy = 1 :=
  MooreLoopSpace.fundamentalGroup_hom_ext fun γ ↦ by
    simp only [monodromy_fundamentalGroupHom, one_ρ, MonoidHom.one_apply, inv_one]

/-- The rank-one local system with a given monodromy `χ`: the Moore loop `γ` acts by the value of
`χ` on the inverse of its class. -/
def ofMonodromy (χ : FundamentalGroup B b →* Rˣ) : RankOneLocalSystem B b R where
  ρ := (χ.comp (MooreLoopSpace.fundamentalGroupHom b))⁻¹
  eq_of_joined _ _ h := by
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MooreLoopSpace.fundamentalGroupHom_eq_iff_joined.2 h]

@[simp]
theorem ofMonodromy_ρ_apply (χ : FundamentalGroup B b →* Rˣ) (γ : MooreLoopSpace B b) :
    (ofMonodromy χ).ρ γ = (χ (MooreLoopSpace.fundamentalGroupHom b γ))⁻¹ :=
  (rfl)

@[simp]
theorem monodromy_ofMonodromy (χ : FundamentalGroup B b →* Rˣ) : (ofMonodromy χ).monodromy = χ :=
  MooreLoopSpace.fundamentalGroup_hom_ext fun γ ↦ by
    simp only [monodromy_fundamentalGroupHom, ofMonodromy_ρ_apply, inv_inv]

@[simp]
theorem ofMonodromy_monodromy : ofMonodromy L.monodromy = L :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by
    rw [ofMonodromy_ρ_apply, monodromy_fundamentalGroupHom, inv_inv]

/-- **Rank-one local systems are the characters of the fundamental group**: the monodromy is an
isomorphism of groups onto `FundamentalGroup B b →* Rˣ`, with inverse `ofMonodromy`. -/
def monodromyEquiv : RankOneLocalSystem B b R ≃* (FundamentalGroup B b →* Rˣ) where
  toFun L := L.monodromy
  invFun := ofMonodromy
  left_inv := ofMonodromy_monodromy
  right_inv := monodromy_ofMonodromy
  map_mul' := monodromy_mul

@[simp]
theorem monodromyEquiv_apply : monodromyEquiv L = L.monodromy :=
  (rfl)

@[simp]
theorem monodromyEquiv_symm_apply (χ : FundamentalGroup B b →* Rˣ) :
    monodromyEquiv.symm χ = ofMonodromy χ :=
  (rfl)

/-- The monodromy of the inverse local system is the inverse character. -/
@[simp]
theorem monodromy_inv : L⁻¹.monodromy = L.monodromy⁻¹ :=
  map_inv monodromyEquiv L

/-- A rank-one local system is determined by its monodromy. -/
theorem monodromy_injective : Function.Injective (monodromy : RankOneLocalSystem B b R → _) :=
  monodromyEquiv.injective

/-! ### Pullback along based maps -/

section Pullback

variable {B' B'' : Type*} [TopologicalSpace B'] [TopologicalSpace B''] {b' : B'} {b'' : B''}

/-- The **pullback** of rank-one local systems along a based map `f : (B, b) → (B', b')`, as a
group homomorphism: a loop acts through its image under `f`. -/
def pullback (f : C(B, B')) (hf : f b = b') :
    RankOneLocalSystem B' b' R →* RankOneLocalSystem B b R where
  toFun L :=
    { ρ := L.ρ.comp (MooreLoopSpace.map f hf).toMonoidHom
      eq_of_joined := fun _ _ h ↦ L.eq_of_joined (h.map (MooreLoopSpace.map f hf).continuous) }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem pullback_ρ_apply (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R)
    (γ : MooreLoopSpace B b) : (pullback f hf L).ρ γ = L.ρ (MooreLoopSpace.map f hf γ) :=
  (rfl)

/-- The character of a pullback is the character composed with the induced map on Moore loops. -/
theorem pullback_character (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R) :
    (pullback f hf L).character = L.character.comp (MooreLoopSpace.map f hf).toMonoidHom :=
  (rfl)

/-- The pullback along the identity is the identity. -/
@[simp]
theorem pullback_id :
    pullback (R := R) (.id B) (ContinuousMap.id_apply b) = MonoidHom.id _ :=
  MonoidHom.ext fun L ↦ RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp

/-- The pullback along a composite is the composite of the pullbacks. -/
theorem pullback_comp (g : C(B', B'')) (f : C(B, B')) (hg : g b' = b'') (hf : f b = b') :
    pullback (R := R) (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (pullback f hf).comp (pullback g hg) :=
  MonoidHom.ext fun L ↦ RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by
    simp [MooreLoopSpace.map_comp g f hg hf]

/-- The monodromy of a pullback is the monodromy composed with the induced map on fundamental
groups. -/
@[simp]
theorem monodromy_pullback (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R) :
    (pullback f hf L).monodromy = L.monodromy.comp (FundamentalGroup.mapOfEq f hf) :=
  MooreLoopSpace.fundamentalGroup_hom_ext fun γ ↦ by
    simp only [monodromy_fundamentalGroupHom, pullback_ρ_apply, MonoidHom.comp_apply,
      ← MooreLoopSpace.fundamentalGroupHom_map]

/-- **The twist is natural in the space**: `C_*(Ωf) ∘ Φ^{f^* L} = Φ^L ∘ C_*(Ωf)`. -/
theorem loopChainMap_comp_twist_pullback (f : C(B, B')) (hf : f b = b')
    (L : RankOneLocalSystem B' b' R) :
    (loopChainMap R f hf).comp (pullback f hf L).twist = L.twist.comp (loopChainMap R f hf) := by
  rw [loopChainMap_def]
  exact cubicalChainDGAlgHom_comp_cubicalChainTwist (MooreLoopSpace.map f hf)
    L.character_eq_of_joined

/-- **Pulling back commutes with tensoring**: `f^*(𝓕 ⊗ L) ≅ f^* 𝓕 ⊗ f^* L`. -/
def tensorPullbackIso (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R) :
    tensor.{uM} L ⋙ DGLocalSystem.pullback R f hf ≅
      DGLocalSystem.pullback R f hf ⋙ (pullback f hf L).tensor :=
  (DGRightModuleCat.restrictScalarsComp _ _).symm ≪≫
    eqToIso (by rw [loopChainMap_comp_twist_pullback]) ≪≫
      DGRightModuleCat.restrictScalarsComp _ _

/-- The component of `tensorPullbackIso` at `𝓕`. -/
@[simp]
theorem tensorPullbackIso_hom_app (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R)
    (𝓕 : DGLocalSystem.{uM} B' b' R) :
    (tensorPullbackIso f hf L).hom.app 𝓕 =
      (DGRightModuleCat.restrictScalarsCompApp (loopChainMap R f hf) L.twist 𝓕).inv ≫
        eqToHom (by rw [loopChainMap_comp_twist_pullback]) ≫
          (DGRightModuleCat.restrictScalarsCompApp (pullback f hf L).twist
            (loopChainMap R f hf) 𝓕).hom := by
  simp [tensorPullbackIso, ← Iso.app_hom, ← Iso.app_inv, DGRightModuleCat.restrictScalarsComp_app]

/-- The component of the inverse of `tensorPullbackIso` at `𝓕`. -/
@[simp]
theorem tensorPullbackIso_inv_app (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R)
    (𝓕 : DGLocalSystem.{uM} B' b' R) :
    (tensorPullbackIso f hf L).inv.app 𝓕 =
      (DGRightModuleCat.restrictScalarsCompApp (pullback f hf L).twist
          (loopChainMap R f hf) 𝓕).inv ≫
        eqToHom (by rw [loopChainMap_comp_twist_pullback]) ≫
          (DGRightModuleCat.restrictScalarsCompApp (loopChainMap R f hf) L.twist 𝓕).hom := by
  simp [tensorPullbackIso, ← Iso.app_hom, ← Iso.app_inv, DGRightModuleCat.restrictScalarsComp_app]

end Pullback

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

/-- Twisting a cocycle by a product twists it successively, `m^{L L'} = (m^{L'})^L`. -/
theorem twistCocycle_mul (L L' : RankOneLocalSystem B b R) (m : LoopTwistingCocycle B b R P ind) :
    (L * L').twistCocycle m = L.twistCocycle (L'.twistCocycle m) := by
  rw [twistCocycle, twistCocycle, twistCocycle, TwistingCocycle.map_map, twist_mul]

/-- Twisting by the trivial local system leaves a cocycle unchanged. -/
@[simp]
theorem twistCocycle_one (m : LoopTwistingCocycle B b R P ind) :
    (1 : RankOneLocalSystem B b R).twistCocycle m = m := by
  rw [twistCocycle, twist_one, TwistingCocycle.map_id]

/-- Twisting commutes with pushing cocycles forward along a based map `f`: the image of `m^{f^* L}`
under `C_*(Ωf)` is the twist by `L` of the image of `m`. -/
theorem twistCocycle_map_loopChainMap {B' : Type*} [TopologicalSpace B'] {b' : B'}
    (f : C(B, B')) (hf : f b = b') (L : RankOneLocalSystem B' b' R)
    (m : LoopTwistingCocycle B b R P ind) :
    L.twistCocycle (m.map (loopChainMap R f hf)) =
      ((pullback f hf L).twistCocycle m).map (loopChainMap R f hf) := by
  rw [twistCocycle, twistCocycle, TwistingCocycle.map_map, TwistingCocycle.map_map,
    loopChainMap_comp_twist_pullback]

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
  rw [DGAlgHom.cyclesMap_apply_coe, twist_lof_ofCube, SingularCube.point_apply, SetLike.val_smul]

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
      hM.restrictScalarsCohomologyEquiv L.twist x ⊗ₜ[R] (1 : R) :=
  Representation.tprodOfLinearCharacterEquivCharTwist_symm_apply L.monodromy
    hM.cohomologyRepresentation _

/-- On a class of degree `p`, a class `g` of the fundamental group acts on `H^p(𝓕 ⊗ L)` as
`L.monodromy g` times its action on `H^p(𝓕)`. -/
private theorem coe_restrictScalarsCohomologyGradingEquiv_cohomologyGradingRepresentation
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (p : ℤ) (g : FundamentalGroup B b)
    (x : (hM.restrictScalars L.twist).cohomologyGrading p) :
    (hM.restrictScalarsCohomologyGradingEquiv L.twist p
        ((hM.restrictScalars L.twist).cohomologyGradingRepresentation p g x) : hM.Cohomology) =
      (L.monodromy g : R) • (hM.cohomologyGradingRepresentation p g
        (hM.restrictScalarsCohomologyGradingEquiv L.twist p x) : hM.Cohomology) :=
  calc (hM.restrictScalarsCohomologyGradingEquiv L.twist p
        ((hM.restrictScalars L.twist).cohomologyGradingRepresentation p g x) : hM.Cohomology)
      = hM.restrictScalarsCohomologyEquiv L.twist
          ((hM.restrictScalars L.twist).cohomologyRepresentation g x) :=
        (hM.coe_restrictScalarsCohomologyGradingEquiv_apply L.twist p _).trans
          (congrArg (hM.restrictScalarsCohomologyEquiv L.twist)
            ((hM.restrictScalars L.twist).coe_cohomologyGradingRepresentation_apply p g x))
    _ = (L.monodromy g : R) • hM.cohomologyRepresentation g
          (hM.restrictScalarsCohomologyEquiv L.twist x) :=
        (Representation.IntertwiningMap.isIntertwining _ _
          (L.cohomologyRepresentationEquivCharTwist hM).toIntertwiningMap g x).trans
          (Representation.charTwist_apply_apply _ _ _ _)
    _ = _ := congrArg ((L.monodromy g : R) • ·)
          ((congrArg (hM.cohomologyRepresentation g)
            (hM.coe_restrictScalarsCohomologyGradingEquiv_apply L.twist p x).symm).trans
          (hM.coe_cohomologyGradingRepresentation_apply p g _).symm)

/-- **The homology of `𝓕 ⊗ L` in a single degree is that of `𝓕` twisted by the monodromy of `L`**:
`cohomologyRepresentationEquivCharTwist` restricts to an equivalence from the representation on
the classes of `H(𝓕 ⊗ L)` of cohomological degree `p` to the representation on those of `H(𝓕)`,
rescaled by the monodromy of `L`. -/
noncomputable def cohomologyGradingRepresentationEquivCharTwist
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (p : ℤ) :
    ((hM.restrictScalars L.twist).cohomologyGradingRepresentation p).Equiv
      ((hM.cohomologyGradingRepresentation p).charTwist L.monodromy) :=
  .mk (hM.restrictScalarsCohomologyGradingEquiv L.twist p) fun g ↦
    LinearMap.ext fun x ↦ Subtype.ext <|
      (L.coe_restrictScalarsCohomologyGradingEquiv_cohomologyGradingRepresentation hM p g x).trans
        ((Submodule.coe_smul _ _).symm.trans (congrArg Subtype.val
          (Representation.charTwist_apply_apply L.monodromy (hM.cohomologyGradingRepresentation p)
            g _).symm))

/-- The equivalence `H^p(𝓕 ⊗ L) ≅ H^p(𝓕)` sends a class to the class of the same cycle. -/
@[simp]
theorem cohomologyGradingRepresentationEquivCharTwist_apply
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (p : ℤ)
    (x : (hM.restrictScalars L.twist).cohomologyGrading p) :
    L.cohomologyGradingRepresentationEquivCharTwist hM p x =
      hM.restrictScalarsCohomologyGradingEquiv L.twist p x :=
  (rfl)

/-- **The homology of `𝓕 ⊗ L` in a single degree is the homology of `𝓕` in that degree tensored
with `L`**: `H_q(𝓕 ⊗ L) ≅ H_q(𝓕) ⊗ L` as representations of the fundamental group (the source's
§2.3), stated in the cohomological degree `p = -q`. A class is sent to the class of the same cycle,
tensored with `1` (`TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivTprod_apply`). -/
noncomputable def cohomologyGradingRepresentationEquivTprod
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (p : ℤ) :
    ((hM.restrictScalars L.twist).cohomologyGradingRepresentation p).Equiv
      ((hM.cohomologyGradingRepresentation p).tprod
        (Representation.ofLinearCharacter L.monodromy)) :=
  (L.cohomologyGradingRepresentationEquivCharTwist hM p).trans
    (Representation.tprodOfLinearCharacterEquivCharTwist _ _).symm

/-- The equivalence `H^p(𝓕 ⊗ L) ≅ H^p(𝓕) ⊗ L` sends a class to the class of the same cycle,
tensored with `1`. -/
@[simp]
theorem cohomologyGradingRepresentationEquivTprod_apply
    (hM : IsDGRightModule (loopChain_isDGAlgebra B b R) ℳ dM) (p : ℤ)
    (x : (hM.restrictScalars L.twist).cohomologyGrading p) :
    L.cohomologyGradingRepresentationEquivTprod hM p x =
      L.cohomologyGradingRepresentationEquivCharTwist hM p x ⊗ₜ[R] (1 : R) :=
  Representation.tprodOfLinearCharacterEquivCharTwist_symm_apply L.monodromy
    (hM.cohomologyGradingRepresentation p) _

end RankOneLocalSystem

end Homology

end TauCeti

end
