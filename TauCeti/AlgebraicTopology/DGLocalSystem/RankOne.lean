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

Rank-one local systems form a commutative group under the tensor product of their characters
(`L ⊗ L'` is written `L * L'`), and twisting is multiplicative: `Φ^{L ⊗ L'} = Φ^L ∘ Φ^{L'}`
(`TauCeti.RankOneLocalSystem.twist_mul`). Hence `𝓕 ⊗ (L ⊗ L') ≅ (𝓕 ⊗ L) ⊗ L'`
(`TauCeti.RankOneLocalSystem.tensorMul`), and twisting by `L` is an autoequivalence of DG local
systems with inverse the twist by `L⁻¹` (`TauCeti.RankOneLocalSystem.tensorEquivalence`). Along a
based map `f`, the pullback `f^*L` acts on a loop through its image under `f`; the twist is natural
(`TauCeti.RankOneLocalSystem.loopChainMap_comp_twist_pullback`), so pulling back commutes with
twisting: `f^*𝓕 ⊗ f^*L ≅ f^*(𝓕 ⊗ L)` (`TauCeti.RankOneLocalSystem.pullbackTensorIso`). These are the
operations by which rank-one coefficient systems are assembled from simpler ones, such as pullbacks
of orientation local systems and their inverses.

As a classical local system, `L` is the representation of `π₁(B, b)` on `R` through its monodromy
`TauCeti.RankOneLocalSystem.monodromy`, the character sending the inverse of the class of a Moore
loop `γ` to `ρ γ`. A rank-one local system is determined by its monodromy, and every character
`π₁(B, b) →* Rˣ` is the monodromy of one (`TauCeti.RankOneLocalSystem.ofMonodromy`): the monodromy
is an isomorphism from the group of rank-one local systems to the group of characters of the
fundamental group (`TauCeti.RankOneLocalSystem.monodromyEquiv`), compatible with pullback
(`TauCeti.RankOneLocalSystem.monodromy_pullback`).

On homology, twisting by `L` tensors with this representation: `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L` as
representations of the fundamental group
(`TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod`), through the identification of
the homology of the restriction of `𝓕` along `Φ^L` with that of `𝓕`. Equivalently, the
representation on `H(𝓕 ⊗ L)` is the one on `H(𝓕)` rescaled by the monodromy
(`TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivCharTwist`). The point is that the class
of the point chain of `γ` in `H(C_*(Ω_b B))` is scaled by `ρ γ` under `Φ^L`. These statements
concern the total homology `H(𝓕)`, the direct sum of the `H_q(𝓕)`. The identification preserves
degrees, so they restrict to each degree: `H_q(𝓕 ⊗ L) ≅ H_q(𝓕) ⊗ L`
(`TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivTprod`), stated in the
cohomological degree `p = -q`.

## Main definitions

* `TauCeti.RankOneLocalSystem B b R`: rank-one local systems on `(B, b)`.
* `TauCeti.RankOneLocalSystem.twist L`: the DG algebra automorphism `Φ^L` of `C_*(Ω_b B)`.
* `TauCeti.RankOneLocalSystem.tensor L`: the functor `𝓕 ↦ 𝓕 ⊗ L` on DG local systems.
* `TauCeti.RankOneLocalSystem.tensorOne`, `TauCeti.RankOneLocalSystem.tensorMul`: twisting by the
  trivial local system, and by a tensor product.
* `TauCeti.RankOneLocalSystem.tensorEquivalence L`: the autoequivalence `𝓕 ↦ 𝓕 ⊗ L`.
* `TauCeti.RankOneLocalSystem.pullback L f hf`: the pullback `f^*L` along a based map.
* `TauCeti.RankOneLocalSystem.pullbackTensorIso`: `f^*𝓕 ⊗ f^*L ≅ f^*(𝓕 ⊗ L)`.
* `TauCeti.RankOneLocalSystem.twistCocycle L m`: the twisted cocycle `m^L`.
* `TauCeti.RankOneLocalSystem.monodromy L`: the monodromy character `π₁(B, b) →* Rˣ`.
* `TauCeti.RankOneLocalSystem.ofMonodromy χ`: the rank-one local system with monodromy `χ`.
* `TauCeti.RankOneLocalSystem.monodromyEquiv`: rank-one local systems are the characters of the
  fundamental group.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivTprod`: `H(𝓕 ⊗ L) ≅ H(𝓕) ⊗ L`.
* `TauCeti.RankOneLocalSystem.cohomologyRepresentationEquivCharTwist`: the same, with `L` absorbed
  into the twist of the representation on `H(𝓕)` by the monodromy.
* `TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivTprod`: `H_q(𝓕 ⊗ L) ≅ H_q(𝓕) ⊗ L`
  in each degree.
* `TauCeti.RankOneLocalSystem.cohomologyGradingRepresentationEquivCharTwist`: the same, with `L`
  absorbed into the twist.

## Main results

* `TauCeti.RankOneLocalSystem.twist_mul`: `Φ^{L ⊗ L'} = Φ^L ∘ Φ^{L'}`.
* `TauCeti.RankOneLocalSystem.twist_comp_twist_inv`: `Φ^L` is invertible.
* `TauCeti.RankOneLocalSystem.loopChainMap_comp_twist_pullback`:
  `C_*(Ωf) ∘ Φ^{f^*L} = Φ^L ∘ C_*(Ωf)`.
* `TauCeti.RankOneLocalSystem.monodromy_pullback`: the monodromy of `f^*L` is that of `L` composed
  with `π₁(f)`.
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

/-- The **tensor product `L ⊗ L'`** of rank-one local systems: a loop acts by the product of the
units by which it acts on `L` and on `L'`. -/
instance : Mul (RankOneLocalSystem B b R) where
  mul L L' :=
    { ρ := L.ρ * L'.ρ
      eq_of_joined := fun _ _ h ↦ by
        rw [MonoidHom.mul_apply, MonoidHom.mul_apply, L.eq_of_joined h, L'.eq_of_joined h] }

@[simp]
theorem mul_ρ (L' : RankOneLocalSystem B b R) : (L * L').ρ = L.ρ * L'.ρ :=
  rfl

/-- Rank-one local systems form a commutative group under the tensor product, with unit the
trivial local system and inverse the dual local system. -/
instance : CommGroup (RankOneLocalSystem B b R) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc L₁ L₂ L₃ := RankOneLocalSystem.ext (mul_assoc L₁.ρ L₂.ρ L₃.ρ)
  one_mul L := RankOneLocalSystem.ext (one_mul L.ρ)
  mul_one L := RankOneLocalSystem.ext (mul_one L.ρ)
  inv_mul_cancel L := RankOneLocalSystem.ext (inv_mul_cancel L.ρ)
  mul_comm L₁ L₂ := RankOneLocalSystem.ext (mul_comm L₁.ρ L₂.ρ)

/-- The action of a rank-one local system, as a homomorphism of groups. -/
private def ρHom : RankOneLocalSystem B b R →* (MooreLoopSpace B b →* Rˣ) where
  toFun L := L.ρ
  map_one' := one_ρ
  map_mul' := mul_ρ

@[simp]
theorem div_ρ (L' : RankOneLocalSystem B b R) : (L / L').ρ = L.ρ / L'.ρ :=
  map_div ρHom L L'

@[simp]
theorem pow_ρ (n : ℕ) : (L ^ n).ρ = L.ρ ^ n :=
  map_pow ρHom L n

@[simp]
theorem zpow_ρ (n : ℤ) : (L ^ n).ρ = L.ρ ^ n :=
  map_zpow ρHom L n

/-- The twist of the trivial local system is the identity. -/
@[simp]
theorem twist_one :
    (1 : RankOneLocalSystem B b R).twist = DGAlgHom.id (loopChain_isDGAlgebra B b R) := by
  have h : (1 : RankOneLocalSystem B b R).character = 1 := by
    ext γ
    simp
  rw [twist, ← cubicalChainTwist_one (G := MooreLoopSpace B b) (R := R)]
  congr

/-- **Twisting is multiplicative**: the twist `Φ^{L ⊗ L'}` of a tensor product is the composite
`Φ^L ∘ Φ^{L'}`. -/
theorem twist_mul (L' : RankOneLocalSystem B b R) : (L * L').twist = L.twist.comp L'.twist := by
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

/-- Twisting by the trivial rank-one local system is isomorphic to the identity functor. -/
def tensorOne : (1 : RankOneLocalSystem B b R).tensor ≅ 𝟭 (DGLocalSystem.{uM} B b R) :=
  eqToIso (by rw [tensor, twist_one]) ≪≫ DGRightModuleCat.restrictScalarsId

/-- The component of `tensorOne` at `𝓕`. -/
@[simp]
theorem tensorOne_hom_app (𝓕 : DGLocalSystem.{uM} B b R) :
    tensorOne.hom.app 𝓕 =
      eqToHom (by rw [tensor, twist_one]) ≫ (DGRightModuleCat.restrictScalarsIdApp 𝓕).hom := by
  rw [tensorOne, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, ← Iso.app_hom,
    DGRightModuleCat.restrictScalarsId_app]

/-- The component of the inverse of `tensorOne` at `𝓕`. -/
@[simp]
theorem tensorOne_inv_app (𝓕 : DGLocalSystem.{uM} B b R) :
    tensorOne.inv.app 𝓕 =
      (DGRightModuleCat.restrictScalarsIdApp 𝓕).inv ≫ eqToHom (by rw [tensor, twist_one]) := by
  rw [tensorOne, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, ← Iso.app_inv,
    DGRightModuleCat.restrictScalarsId_app]

/-- Twisting by a tensor product of rank-one local systems is twisting by each factor in turn:
`𝓕 ⊗ (L ⊗ L') ≅ (𝓕 ⊗ L) ⊗ L'`. -/
def tensorMul (L' : RankOneLocalSystem B b R) :
    (L * L').tensor ≅ (L.tensor ⋙ L'.tensor : DGLocalSystem.{uM} B b R ⥤ _) :=
  eqToIso (by rw [tensor, twist_mul]) ≪≫ DGRightModuleCat.restrictScalarsComp L'.twist L.twist

/-- The component of `tensorMul` at `𝓕`. -/
@[simp]
theorem tensorMul_hom_app (L' : RankOneLocalSystem B b R) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.tensorMul L').hom.app 𝓕 =
      eqToHom (by rw [tensor, twist_mul]) ≫
        (DGRightModuleCat.restrictScalarsCompApp L'.twist L.twist 𝓕).hom := by
  rw [tensorMul, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, ← Iso.app_hom,
    DGRightModuleCat.restrictScalarsComp_app]

/-- The component of the inverse of `tensorMul` at `𝓕`. -/
@[simp]
theorem tensorMul_inv_app (L' : RankOneLocalSystem B b R) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.tensorMul L').inv.app 𝓕 =
      (DGRightModuleCat.restrictScalarsCompApp L'.twist L.twist 𝓕).inv ≫
        eqToHom (by rw [tensor, twist_mul]) := by
  rw [tensorMul, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, ← Iso.app_inv,
    DGRightModuleCat.restrictScalarsComp_app]

/-- **Twisting by `L` is an autoequivalence** of DG local systems, with inverse the twist by
`L⁻¹`. -/
def tensorEquivalence : DGLocalSystem.{uM} B b R ≌ DGLocalSystem.{uM} B b R :=
  .mk L.tensor L⁻¹.tensor
    (tensorOne.symm ≪≫ eqToIso (by rw [mul_inv_cancel]) ≪≫ L.tensorMul L⁻¹)
    ((L⁻¹.tensorMul L).symm ≪≫ eqToIso (by rw [inv_mul_cancel]) ≪≫ tensorOne)

@[simp]
theorem tensorEquivalence_functor : L.tensorEquivalence.{uM}.functor = L.tensor :=
  (rfl)

@[simp]
theorem tensorEquivalence_inverse : L.tensorEquivalence.{uM}.inverse = L⁻¹.tensor :=
  (rfl)

/-- Moore loops with the same class in the fundamental group act by the same unit. -/
theorem ρ_eq_of_fundamentalGroupHom_eq {γ δ : MooreLoopSpace B b}
    (h : MooreLoopSpace.fundamentalGroupHom b γ = MooreLoopSpace.fundamentalGroupHom b δ) :
    L.ρ γ = L.ρ δ :=
  L.eq_of_joined (MooreLoopSpace.fundamentalGroupHom_eq_fundamentalGroupHom_iff.1 h)

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

/-- The monodromy of the class of a Moore loop `γ` is the inverse of the unit by which `γ`
acts. -/
theorem monodromy_fundamentalGroupHom (γ : MooreLoopSpace B b) :
    L.monodromy (MooreLoopSpace.fundamentalGroupHom b γ) = (L.ρ γ)⁻¹ := by
  rw [← L.monodromy_fundamentalGroupHom_inv, map_inv, inv_inv]

/-- The monodromy, read on Moore loops through their classes, is the inverse of the action. -/
theorem monodromy_comp_fundamentalGroupHom :
    L.monodromy.comp (MooreLoopSpace.fundamentalGroupHom b) = L.ρ⁻¹ :=
  MonoidHom.ext fun γ ↦ by
    rw [MonoidHom.comp_apply, monodromy_fundamentalGroupHom, MonoidHom.inv_apply]

/-- The monodromy of a tensor product is the product of the monodromies. -/
@[simp]
theorem monodromy_mul (L' : RankOneLocalSystem B b R) :
    (L * L').monodromy = L.monodromy * L'.monodromy :=
  (MonoidHom.cancel_right (MooreLoopSpace.fundamentalGroupHom_surjective b)).1 <| by
    rw [monodromy_comp_fundamentalGroupHom, MonoidHom.mul_comp, monodromy_comp_fundamentalGroupHom,
      monodromy_comp_fundamentalGroupHom, mul_ρ]
    exact mul_inv L.ρ L'.ρ

/-- The **rank-one local system with monodromy `χ`**: a Moore loop acts by the value of `χ` at the
inverse of its class. -/
def ofMonodromy (χ : FundamentalGroup B b →* Rˣ) : RankOneLocalSystem B b R where
  ρ := (χ.comp (MooreLoopSpace.fundamentalGroupHom b))⁻¹
  eq_of_joined _ _ h := by
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MooreLoopSpace.fundamentalGroupHom_eq_fundamentalGroupHom_iff.2 h]

@[simp]
theorem ofMonodromy_ρ_apply (χ : FundamentalGroup B b →* Rˣ) (γ : MooreLoopSpace B b) :
    (ofMonodromy χ).ρ γ = (χ (MooreLoopSpace.fundamentalGroupHom b γ))⁻¹ :=
  (rfl)

/-- The monodromy of `ofMonodromy χ` is `χ`. -/
@[simp]
theorem monodromy_ofMonodromy (χ : FundamentalGroup B b →* Rˣ) :
    (ofMonodromy χ).monodromy = χ :=
  (MonoidHom.cancel_right (MooreLoopSpace.fundamentalGroupHom_surjective b)).1 <|
    MonoidHom.ext fun γ ↦ by
      rw [MonoidHom.comp_apply, monodromy_fundamentalGroupHom, ofMonodromy_ρ_apply, inv_inv,
        MonoidHom.comp_apply]

/-- A rank-one local system is the one with its monodromy. -/
@[simp]
theorem ofMonodromy_monodromy : ofMonodromy L.monodromy = L :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by
    rw [ofMonodromy_ρ_apply, monodromy_fundamentalGroupHom, inv_inv]

variable (B b R) in
/-- **Rank-one local systems are classified by their monodromy**: the monodromy is an isomorphism
from the group of rank-one local systems on `(B, b)` to the group of characters
`π₁(B, b) →* Rˣ`. -/
def monodromyEquiv : RankOneLocalSystem B b R ≃* (FundamentalGroup B b →* Rˣ) where
  toFun L := L.monodromy
  invFun := ofMonodromy
  left_inv := ofMonodromy_monodromy
  right_inv := monodromy_ofMonodromy
  map_mul' := monodromy_mul

@[simp]
theorem monodromyEquiv_apply : monodromyEquiv B b R L = L.monodromy :=
  (rfl)

@[simp]
theorem monodromyEquiv_symm_apply (χ : FundamentalGroup B b →* Rˣ) :
    (monodromyEquiv B b R).symm χ = ofMonodromy χ :=
  (rfl)

/-- The trivial rank-one local system has trivial monodromy. -/
@[simp]
theorem monodromy_one : (1 : RankOneLocalSystem B b R).monodromy = 1 :=
  map_one (monodromyEquiv B b R)

/-- The monodromy of the inverse local system is the inverse character. -/
@[simp]
theorem monodromy_inv : L⁻¹.monodromy = L.monodromy⁻¹ :=
  map_inv (monodromyEquiv B b R) L

section Pullback

variable {B' B'' : Type*} [TopologicalSpace B'] [TopologicalSpace B''] {b' : B'} {b'' : B''}

/-- The **pullback `f^*L`** of a rank-one local system along a based map
`f : (B', b') → (B, b)`: a loop acts by the unit by which its image acts on `L`. -/
def pullback (f : C(B', B)) (hf : f b' = b) : RankOneLocalSystem B' b' R where
  ρ := L.ρ.comp (MooreLoopSpace.map f hf : MooreLoopSpace B' b' →* MooreLoopSpace B b)
  eq_of_joined _ _ h := L.eq_of_joined (h.map (MooreLoopSpace.map f hf).continuous)

@[simp]
theorem pullback_ρ_apply (f : C(B', B)) (hf : f b' = b) (γ : MooreLoopSpace B' b') :
    (L.pullback f hf).ρ γ = L.ρ (MooreLoopSpace.map f hf γ) :=
  (rfl)

@[simp]
theorem pullback_one (f : C(B', B)) (hf : f b' = b) :
    (1 : RankOneLocalSystem B b R).pullback f hf = 1 :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp

@[simp]
theorem pullback_mul (L' : RankOneLocalSystem B b R) (f : C(B', B)) (hf : f b' = b) :
    (L * L').pullback f hf = L.pullback f hf * L'.pullback f hf :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp

@[simp]
theorem pullback_inv (f : C(B', B)) (hf : f b' = b) : L⁻¹.pullback f hf = (L.pullback f hf)⁻¹ :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp

@[simp]
theorem pullback_id : L.pullback (.id B) (ContinuousMap.id_apply b) = L :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp

theorem pullback_comp (g : C(B', B)) (f : C(B'', B')) (hg : g b' = b) (hf : f b'' = b') :
    L.pullback (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) =
      (L.pullback g hg).pullback f hf :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by simp [MooreLoopSpace.map_comp g f hg hf]

/-- The monodromy of a pullback is the monodromy precomposed with the induced map of fundamental
groups. -/
@[simp]
theorem monodromy_pullback (f : C(B', B)) (hf : f b' = b) :
    (L.pullback f hf).monodromy = L.monodromy.comp (FundamentalGroup.mapOfEq f hf) :=
  (MonoidHom.cancel_right (MooreLoopSpace.fundamentalGroupHom_surjective b')).1 <|
    MonoidHom.ext fun γ ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        ← MooreLoopSpace.fundamentalGroupHom_map, monodromy_fundamentalGroupHom,
        monodromy_fundamentalGroupHom, pullback_ρ_apply]

/-- **The twist is natural**: `C_*(Ωf) ∘ Φ^{f^*L} = Φ^L ∘ C_*(Ωf)`. -/
theorem loopChainMap_comp_twist_pullback (f : C(B', B)) (hf : f b' = b) :
    (loopChainMap R f hf).comp (L.pullback f hf).twist = L.twist.comp (loopChainMap R f hf) := by
  have h : ⇑(L.pullback f hf).character =
      ⇑L.character ∘ (MooreLoopSpace.map f hf).toContinuousMap :=
    funext fun γ ↦ by simp
  refine cubicalChain_dgAlgHom_ext fun n y ↦ ?_
  rw [DGAlgHom.comp_apply, DGAlgHom.comp_apply, twist, twist, cubicalChainTwist_lof,
    loopChainMap_lof, loopChainMap_lof, cubicalChainTwist_lof, h,
    ← LinearMap.comp_apply (NormalizedCubicalChain.map R _ n),
    NormalizedCubicalChain.map_comp_twist, LinearMap.comp_apply]

/-- **Pullback commutes with twisting**: `f^*𝓕 ⊗ f^*L ≅ f^*(𝓕 ⊗ L)`, naturally in `𝓕`. -/
def pullbackTensorIso (f : C(B', B)) (hf : f b' = b) :
    (DGLocalSystem.pullback R f hf ⋙ (L.pullback f hf).tensor :
        DGLocalSystem.{uM} B b R ⥤ DGLocalSystem.{uM} B' b' R) ≅
      L.tensor ⋙ DGLocalSystem.pullback R f hf :=
  (DGRightModuleCat.restrictScalarsComp (L.pullback f hf).twist (loopChainMap R f hf)).symm ≪≫
    eqToIso (by rw [L.loopChainMap_comp_twist_pullback f hf]) ≪≫
    DGRightModuleCat.restrictScalarsComp (loopChainMap R f hf) L.twist

/-- The component of `pullbackTensorIso` at `𝓕`. -/
@[simp]
theorem pullbackTensorIso_hom_app (f : C(B', B)) (hf : f b' = b) (𝓕 : DGLocalSystem.{uM} B b R) :
    (L.pullbackTensorIso f hf).hom.app 𝓕 =
      (DGRightModuleCat.restrictScalarsCompApp (L.pullback f hf).twist (loopChainMap R f hf)
          𝓕).inv ≫
        eqToHom (by rw [L.loopChainMap_comp_twist_pullback f hf]) ≫
          (DGRightModuleCat.restrictScalarsCompApp (loopChainMap R f hf) L.twist 𝓕).hom := by
  rw [pullbackTensorIso, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    Iso.symm_hom, ← Iso.app_inv, DGRightModuleCat.restrictScalarsComp_app, eqToIso.hom,
    eqToHom_app, ← Iso.app_hom, DGRightModuleCat.restrictScalarsComp_app]

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
