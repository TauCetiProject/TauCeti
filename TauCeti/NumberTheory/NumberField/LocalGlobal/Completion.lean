/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Canonical maps between number-field completions

Let `L/K` be an extension of number fields, and let `w` be a finite place of `L` above a finite
place `v` of `K`. The embedding `K → L` extends uniquely to a continuous map `K_v → L_w`.
This file packages that map as the algebra homomorphism `completionAlgHom`, provides the algebra
and topological scalar structures it induces in the `AdicCompletionExtension` scope, and proves
its compatibility in towers.

The underlying continuous ring homomorphism is
`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`. Packaging it over `K` is what makes
the completion map usable by scalar extension and tensor-product constructions without choosing
an unrelated algebra structure on `L_w` over `K_v`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.completionAlgHom`: the canonical `K`-algebra homomorphism
  `K_v → L_w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.continuous_completionAlgHom`: continuity of the canonical
  map.
* `IsDedekindDomain.HeightOneSpectrum.eq_completionAlgHom_of_continuous`: its continuous
  universal property.
* `IsDedekindDomain.HeightOneSpectrum.completionAlgHom_comp`: compatibility in a tower of number
  fields.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The canonical map `K_v → L_w` for a finite place `w` of `L` above a finite place `v` of
`K`, as a `K`-algebra homomorphism. -/
def completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    v.adicCompletion K →ₐ[K] w.adicCompletion L where
  toRingHom := v.adicCompletionExtension K L w
  commutes' x := v.adicCompletionExtension_coe K L w x

/-- The algebra map of the canonical completion algebra is `completionAlgHom`.

Not `@[simp]`: `algebraMap_adicCompletionExtensionAlgebra` already simplifies the left-hand side
to the underlying `adicCompletionExtension`, so the `simpNF` linter rejects this wrapper theorem. -/
theorem algebraMap_eq_completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) =
      (completionAlgHom v w).toRingHom := by
  rw [algebraMap_adicCompletionExtensionAlgebra]
  -- The `toRingHom` field of the number-field wrapper is the generic completion extension.
  rfl

/-- The canonical map between completions is continuous. -/
theorem continuous_completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Continuous (completionAlgHom v w) :=
  v.continuous_adicCompletionExtension K L w

/-- A continuous ring homomorphism `K_v → L_w` extending `K → L` is the canonical completion
map. -/
theorem eq_completionAlgHom_of_continuous {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (f : v.adicCompletion K →+* w.adicCompletion L) (hf : Continuous f)
    (hcomp : ∀ x : K, f (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x)) :
    f = (completionAlgHom v w).toRingHom :=
  v.eq_adicCompletionExtension_of_continuous K L w hf hcomp

/-- The canonical map from a completion to itself is the identity. -/
@[simp]
theorem completionAlgHom_self (v : HeightOneSpectrum (𝒪 K)) :
    let _ : @Ideal.LiesOver (𝒪 K) _ (𝒪 K) _
      (NumberField.inst_ringOfIntegersAlgebra (K := K) (L := K))
      v.asIdeal v.asIdeal := ⟨by
        -- The self-extension algebra map on rings of integers reduces definitionally to
        -- `RingHom.id`; expose that normal form before proving that the ideal lies over itself.
        change v.asIdeal = Ideal.comap (RingHom.id _) v.asIdeal
        simp⟩
    completionAlgHom v v = AlgHom.id K (v.adicCompletion K) := by
  let _ : Algebra (𝒪 K) (𝒪 K) :=
    NumberField.inst_ringOfIntegersAlgebra (K := K) (L := K)
  let _ : @Ideal.LiesOver (𝒪 K) _ (𝒪 K) _
      (NumberField.inst_ringOfIntegersAlgebra (K := K) (L := K)) v.asIdeal v.asIdeal :=
    ⟨by
      -- As in the statement, normalize the self-extension algebra map to `RingHom.id`.
      change v.asIdeal = Ideal.comap (RingHom.id _) v.asIdeal
      simp⟩
  apply AlgHom.coe_ringHom_injective
  symm
  apply v.eq_adicCompletionExtension_of_continuous K K v
  · exact continuous_id
  · intro x
    simp

/-- The global field, its completion, and the completion of an extension form a scalar tower for
the canonical completion algebra. -/
theorem completionIsScalarTower {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq_completionAlgHom]
    exact ((completionAlgHom v w).commutes x).symm

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.completionIsScalarTower

/-- Scalar multiplication by `K_v` on `L_w` is continuous for the canonical completion
algebra. -/
theorem completionContinuousSMul {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  apply continuousSMul_of_algebraMap
  rw [algebraMap_eq_completionAlgHom]
  exact continuous_completionAlgHom v w

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.completionContinuousSMul

/-- Canonical completion maps compose in a tower of number fields. -/
theorem completionAlgHom_comp {M L : Type*} [Field M] [NumberField M] [Algebra K M]
    [Field L] [NumberField L] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    (v : HeightOneSpectrum (𝒪 K)) (u : HeightOneSpectrum (𝒪 M))
    (w : HeightOneSpectrum (𝒪 L)) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] :
    letI : w.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans w.asIdeal u.asIdeal v.asIdeal
    ((completionAlgHom u w).restrictScalars K).comp (completionAlgHom v u) =
      completionAlgHom v w := by
  let _ : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal u.asIdeal v.asIdeal
  apply AlgHom.coe_ringHom_injective
  -- After forgetting the `AlgHom` structure, `restrictScalars` and `AlgHom.comp` reduce to the
  -- composition of the underlying canonical completion ring maps.
  change (u.adicCompletionExtension M L w).comp (v.adicCompletionExtension K M u) =
    v.adicCompletionExtension K L w
  apply v.eq_adicCompletionExtension_of_continuous K L w
  · exact (u.continuous_adicCompletionExtension M L w).comp
      (v.continuous_adicCompletionExtension K M u)
  · intro x
    simp only [RingHom.comp_apply]
    rw [v.adicCompletionExtension_coe K M u x,
      u.adicCompletionExtension_coe M L w (algebraMap K M x),
      IsScalarTower.algebraMap_apply K M L]

end IsDedekindDomain.HeightOneSpectrum
