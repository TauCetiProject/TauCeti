/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units

/-!
# Integration of continuous characters and pushforward along homomorphisms

For a locally compact topological monoid `G` and a topological commutative ring `R`, Mathlib makes
the measures `D(G, R)` into an `R`-algebra under the right-handed convolution
`(μ * ν) f = μ (x ↦ ν (y ↦ f (x * y)))`. This file constructs the two basic families of `R`-algebra
homomorphisms out of this convolution algebra.

A continuous character `κ : G →ₜ* R` is an eigenfunction of convolution: convolving it on the right
with `ν` multiplies it by the scalar `ν κ` (`convolveFunRight_continuousMonoidHom`). Hence
`μ ↦ μ κ` is multiplicative for convolution, and it is bundled as the `R`-algebra homomorphism
`characterIntegralAlgHom κ : D(G, R) →ₐ[R] R`. For the trivial character this is the total mass
`μ ↦ μ 1`, so the total mass of a convolution is the product of the total masses
(`mul_apply_one`). These character integrals are what pseudo-measures are evaluated against.

Pushforward of measures along a continuous monoid homomorphism `φ : G →ₜ* H` is multiplicative for
convolution, and is bundled as `mapAlgHom φ : D(G, R) →ₐ[R] D(H, R)`; character integration is
natural for it (`characterIntegralAlgHom_comp_mapAlgHom`).

## Main definitions

* `ContinuousMonoidHom.characterIntegralAlgHom κ`: the `R`-algebra homomorphism `μ ↦ μ κ`
  attached to a continuous character `κ : G →ₜ* R`.
* `ContinuousMonoidHom.mapAlgHom φ`: pushforward along a continuous monoid homomorphism
  `φ : G →ₜ* H`, as an `R`-algebra homomorphism.

## Main results

* `AbstractMeasure.algebraMap_apply`: the scalar measure `r` integrates `f` to `r * f 1`.
* `AbstractMeasure.convolveFunRight_continuousMonoidHom`: convolution against a character.
* `AbstractMeasure.mul_apply_one`: the total mass of a convolution.
* `ContinuousMonoidHom.characterIntegralAlgHom_diracHom`: the character integral recovers the
  character on Dirac measures.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.6,
  Definition 3.34 and Lemma 3.36.
-/

public noncomputable section

open scoped AbstractMeasure

variable {G H R : Type*} [TopologicalSpace G] [TopologicalSpace H]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace AbstractMeasure

variable [Monoid G] [ContinuousMul G]

/-- A continuous character is an eigenfunction of right convolution by any measure `ν`, with
eigenvalue `ν κ`. -/
theorem convolveFunRight_continuousMonoidHom (ν : D(G, R)) (κ : G →ₜ* R) :
    convolveFunRight ν (κ : C(G, R)) = ν κ • (κ : C(G, R)) := by
  ext x
  rw [convolveFunRight_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm, ← smul_eq_mul,
    ← map_smul ν ((κ : C(G, R)) x) (κ : C(G, R))]
  congr 1
  ext y
  simp

variable [LocallyCompactSpace G]

/-- The scalar measure `r ∈ R` is `r` times the Dirac measure at `1`. -/
@[simp]
theorem algebraMap_apply (r : R) (f : C(G, R)) : algebraMap R D(G, R) r f = r * f 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

end AbstractMeasure

namespace ContinuousMonoidHom

section Monoid

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]

/-- Integration against a continuous character `κ : G →ₜ* R`, `μ ↦ μ κ`, as an `R`-algebra
homomorphism from the convolution algebra `D(G, R)` to `R`. -/
def characterIntegralAlgHom (κ : G →ₜ* R) : D(G, R) →ₐ[R] R where
  toFun μ := μ κ
  map_one' := by simp
  map_mul' μ ν := by
    rw [AbstractMeasure.mul_apply, AbstractMeasure.convolveFunRight_continuousMonoidHom,
      map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by simp [AbstractMeasure.algebraMap_apply]

/-- The character integral `characterIntegralAlgHom κ` evaluates a measure `μ` at `κ`. -/
@[simp]
theorem characterIntegralAlgHom_apply (κ : G →ₜ* R) (μ : D(G, R)) :
    characterIntegralAlgHom κ μ = μ κ :=
  (rfl)

/-- The character integral of the Dirac measure at `g` is the value `κ g`. -/
theorem characterIntegralAlgHom_dirac (κ : G →ₜ* R) (g : G) :
    characterIntegralAlgHom κ (AbstractMeasure.dirac R g) = κ g := by
  simp

/-- The integral of the trivial character is the total mass `μ 1`. It has high priority so that
`simp` reaches `μ 1` rather than unfolding by `characterIntegralAlgHom_apply` to `μ ↑1`. -/
@[simp high]
theorem characterIntegralAlgHom_one_character (μ : D(G, R)) :
    characterIntegralAlgHom 1 μ = μ 1 := by
  have h : ((1 : G →ₜ* R) : C(G, R)) = 1 := by
    ext
    simp
  rw [characterIntegralAlgHom_apply, h]

/-- On Dirac measures, the character integral recovers the character. -/
@[simp]
theorem characterIntegralAlgHom_diracHom (κ : G →ₜ* R) :
    ((characterIntegralAlgHom κ : D(G, R) →* R)).comp AbstractMeasure.diracHom = κ := by
  ext g
  simp

end Monoid

section MapAlgHom

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  [Monoid H] [ContinuousMul H] [LocallyCompactSpace H]

/-- Pushforward of measures along a continuous monoid homomorphism `φ : G →ₜ* H`, as an
`R`-algebra homomorphism between the convolution algebras. -/
def mapAlgHom (φ : G →ₜ* H) : D(G, R) →ₐ[R] D(H, R) where
  toFun := AbstractMeasure.map (φ : C(G, H))
  map_one' := by simp [AbstractMeasure.one_def]
  map_mul' μ ν := by
    ext f
    simp only [AbstractMeasure.map_apply, AbstractMeasure.mul_apply]
    congr 1
    ext x
    simp only [ContinuousMap.comp_apply, AbstractMeasure.convolveFunRight_apply,
      AbstractMeasure.map_apply]
    congr 1
    ext y
    simp
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    ext f
    simp [AbstractMeasure.algebraMap_apply]

/-- The algebra homomorphism `mapAlgHom φ` sends `μ` to its pushforward `map φ μ`. -/
@[simp]
theorem mapAlgHom_apply (φ : G →ₜ* H) (μ : D(G, R)) :
    mapAlgHom φ μ = AbstractMeasure.map (φ : C(G, H)) μ :=
  (rfl)

/-- The linear map underlying `mapAlgHom φ` is the pushforward `map φ`. -/
@[simp]
theorem mapAlgHom_toLinearMap (φ : G →ₜ* H) :
    (mapAlgHom φ).toLinearMap = (AbstractMeasure.map (φ : C(G, H)) : D(G, R) →ₗ[R] D(H, R)) :=
  (rfl)

/-- Pushforward along the identity is the identity. -/
@[simp]
theorem mapAlgHom_id : mapAlgHom (ContinuousMonoidHom.id G) = AlgHom.id R D(G, R) :=
  AlgHom.ext fun _ ↦ AbstractMeasure.map_id _

/-- Pushforward along a composite is the composite of the pushforwards. -/
@[simp]
theorem mapAlgHom_comp {K : Type*} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    [LocallyCompactSpace K] (ψ : H →ₜ* K) (φ : G →ₜ* H) :
    mapAlgHom (ψ.comp φ) = (mapAlgHom ψ).comp (mapAlgHom φ : D(G, R) →ₐ[R] D(H, R)) := by
  ext μ f
  simp only [AlgHom.comp_apply, mapAlgHom_apply, AbstractMeasure.map_apply]
  exact congrArg μ (ContinuousMap.ext fun _ ↦ by simp)

/-- Integrating a character against a pushforward integrates the pulled-back character. -/
@[simp]
theorem characterIntegralAlgHom_comp_mapAlgHom (φ : G →ₜ* H) (κ : H →ₜ* R) :
    (characterIntegralAlgHom κ).comp (mapAlgHom φ) =
      (characterIntegralAlgHom (κ.comp φ) : D(G, R) →ₐ[R] R) := by
  ext μ
  simp only [AlgHom.comp_apply, mapAlgHom_apply, characterIntegralAlgHom_apply,
    AbstractMeasure.map_apply]
  exact congrArg μ (ContinuousMap.ext fun _ ↦ by simp)

end MapAlgHom

end ContinuousMonoidHom

namespace AbstractMeasure

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]

open ContinuousMonoidHom in
/-- The total mass of a convolution is the product of the total masses. -/
@[simp]
theorem mul_apply_one (μ ν : D(G, R)) : (μ * ν) 1 = μ 1 * ν 1 := by
  simpa only [characterIntegralAlgHom_one_character] using map_mul (characterIntegralAlgHom 1) μ ν

end AbstractMeasure

namespace ContinuousMonoidHom

/-! The character integrals on the sign group `ℤˣ = {±1}` over `ℤ`. -/

open AbstractMeasure

/-- The trivial character integrates `δ₁ + δ₋₁` to its total mass `2`. -/
example : characterIntegralAlgHom (1 : ℤˣ →ₜ* ℤ) (dirac ℤ 1 + dirac ℤ (-1)) = 2 := by
  simp only [map_add, characterIntegralAlgHom_dirac, ContinuousMonoidHom.coe_one, Pi.one_apply]
  rfl

/-- The sign character integrates `δ₁ + δ₋₁` to `0` and `δ₁ - δ₋₁` to `2`. -/
example :
    let κ : ℤˣ →ₜ* ℤ := ⟨Units.coeHom ℤ, Units.continuous_val⟩
    κ.characterIntegralAlgHom (dirac ℤ 1 + dirac ℤ (-1)) = 0 ∧
      κ.characterIntegralAlgHom (dirac ℤ 1 - dirac ℤ (-1)) = 2 := by
  intro κ
  simp only [map_add, map_sub, characterIntegralAlgHom_dirac]
  exact ⟨rfl, rfl⟩

end ContinuousMonoidHom
