/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# The completed integer rings of an extension of Dedekind domains

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime
of `B` lying over the height-one prime `v` of `R`. The canonical map `K_v → L_w` restricts to a
ring homomorphism `adicCompletionIntegersExtension : 𝒪_v →+* 𝒪_w` between the rings of integers
of the two completions.

This file turns that restriction into an algebra structure of `𝒪_w` over `𝒪_v`, in the
`AdicCompletionExtension` scope where the algebra structure of `L_w` over `K_v` already lives,
and proves the facts needed to use the extension `𝒪_w / 𝒪_v` as an extension of Dedekind domains:
it is compatible with `L_w` as a `K_v`-algebra, it is torsion-free, it is compatible with the
global map `R → B`, and the maximal ideal of `𝒪_w` lies over that of `𝒪_v`. These are the
hypotheses that ideal-theoretic constructions such as `differentIdeal 𝒪_v 𝒪_w`, `Ideal.LiesOver`,
and the ramification index and inertia degree of `𝒪_w / 𝒪_v` take as input, and they make the
local extension comparable with the global one along `B → 𝒪_w`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtensionAlgebra`: the algebra
  structure of `𝒪_w` over `𝒪_v` given by `adicCompletionIntegersExtension`, available in the
  `AdicCompletionExtension` scope.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtension_injective`: the map on
  completed integer rings is injective.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtension_algebraMap`: it extends the
  global map `R → B`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isScalarTower`: `𝒪_v`, `𝒪_w` and
  `L_w` form a scalar tower, so the two ways of letting `𝒪_v` act on `L_w` agree.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isTorsionFree`: `𝒪_w` is a
  torsion-free `𝒪_v`-module.
* `IsDedekindDomain.HeightOneSpectrum.isLocalHom_algebraMap_adicCompletionIntegers`: the
  canonical map `𝒪_v → 𝒪_w` is a local ring homomorphism.
* `IsDedekindDomain.HeightOneSpectrum.maximalIdeal_adicCompletionIntegers_liesOver`: the maximal
  ideal of `𝒪_w` lies over the maximal ideal of `𝒪_v`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4 and §6.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L)

/-- The map `𝒪_v → 𝒪_w` on completed integer rings is injective: it is a restriction of a ring
homomorphism out of the field `K_v`. -/
theorem adicCompletionIntegersExtension_injective :
    Function.Injective (adicCompletionIntegersExtension K L v w) := by
  intro x y h
  apply Subtype.val_injective
  apply (adicCompletionExtension K L v w).injective
  rw [← coe_adicCompletionIntegersExtension, ← coe_adicCompletionIntegersExtension, h]

/-- The map `𝒪_v → 𝒪_w` on completed integer rings extends the global map `R → B`. -/
@[simp]
theorem adicCompletionIntegersExtension_algebraMap (r : R) :
    adicCompletionIntegersExtension K L v w (algebraMap R (v.adicCompletionIntegers K) r) =
      algebraMap B (w.adicCompletionIntegers L) (algebraMap R B r) := by
  apply Subtype.val_injective
  rw [coe_adicCompletionIntegersExtension, algebraMap_adicCompletionIntegers_apply,
    algebraMap_adicCompletionIntegers_apply, adicCompletionExtension_coe,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L]

/-- The algebra structure on `𝒪_w` over `𝒪_v` induced by `adicCompletionIntegersExtension`,
available in the `AdicCompletionExtension` scope. -/
@[reducible]
def adicCompletionIntegersExtensionAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (adicCompletionIntegersExtension K L v w).toAlgebra

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtensionAlgebra

/-- The algebra map of `adicCompletionIntegersExtensionAlgebra` is
`adicCompletionIntegersExtension`. -/
@[simp]
theorem algebraMap_adicCompletionIntegersExtensionAlgebra :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      adicCompletionIntegersExtension K L v w :=
  RingHom.algebraMap_toAlgebra _

/-- The completed integer rings `𝒪_v ⊆ 𝒪_w` and the completion `L_w` form a scalar tower. Here
`𝒪_v` acts on `L_w` through `K_v`, so this says the two ways of letting `𝒪_v` act on `L_w`
agree. -/
theorem adicCompletionIntegers_isScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K),
      algebraMap_adicCompletionExtensionAlgebra, algebraMap_adicCompletionIntegersExtensionAlgebra]
    exact (coe_adicCompletionIntegersExtension K L v w x).symm

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isScalarTower

/-- `𝒪_w` is a torsion-free `𝒪_v`-module. -/
theorem adicCompletionIntegers_isTorsionFree :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective,
    algebraMap_adicCompletionIntegersExtensionAlgebra]
  exact adicCompletionIntegersExtension_injective K L v w

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isTorsionFree

/-- The canonical map `𝒪_v → 𝒪_w` of completed integer rings is a local ring homomorphism. -/
theorem isLocalHom_algebraMap_adicCompletionIntegers :
    IsLocalHom (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
  rw [algebraMap_adicCompletionIntegersExtensionAlgebra]
  refine ⟨fun x hx ↦ IsLocalRing.notMem_maximalIdeal.mp ?_⟩
  rw [← comap_maximalIdeal_adicCompletionIntegersExtension K L v w, Ideal.mem_comap]
  exact IsLocalRing.notMem_maximalIdeal.mpr hx

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isLocalHom_algebraMap_adicCompletionIntegers

/-- The maximal ideal of `𝒪_w` lies over the maximal ideal of `𝒪_v`. -/
theorem maximalIdeal_adicCompletionIntegers_liesOver :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  ⟨by
    rw [Ideal.under_def, algebraMap_adicCompletionIntegersExtensionAlgebra,
      comap_maximalIdeal_adicCompletionIntegersExtension]⟩

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.maximalIdeal_adicCompletionIntegers_liesOver

end Extension

end IsDedekindDomain.HeightOneSpectrum
