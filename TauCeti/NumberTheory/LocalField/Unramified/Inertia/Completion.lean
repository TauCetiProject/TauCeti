/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import TauCeti.Analysis.Normed.Field.AlgEquiv
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.Topology.Algebra.UniformRing
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.NumberTheory.LocalField.RootsOfUnity.AlgebraicClosure

/-!
# Inertia on roots of unity in the completed algebraic closure

An automorphism of the algebraic closure of a nonarchimedean local field extends continuously
to its completion. Inertia still fixes every root of unity of order prime to the residue
characteristic there: completion introduces no new such roots. This allows analytic
uniformizations over a complete field to use the arithmetic inertia group.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
-/

public noncomputable section

open UniformSpace ValuativeRel

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- The continuous extension of inertia to the completed algebraic closure fixes the roots
of unity of order prime to the residue characteristic. -/
theorem apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one_completion
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    {m : ℕ} (hm : m.Coprime (ringChar 𝓀[K])) :
    letI := spectralNorm.normedField K (AlgebraicClosure K)
    letI := spectralNorm.normedAlgebra K (AlgebraicClosure K)
    ∀ {ζ : Completion (AlgebraicClosure K)}, ζ ^ m = 1 →
      Completion.mapAlgEquiv σ σ.isometry_of_isAlgebraic.continuous
        σ.symm.isometry_of_isAlgebraic.continuous ζ = ζ := by
  let := spectralNorm.normedField K (AlgebraicClosure K)
  let := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  intro ζ hζ
  have : NeZero m := ⟨ne_zero_of_coprime_ringChar hm⟩
  let := hasEnoughRootsOfUnity_algebraicClosure_of_coprime_ringChar K hm
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) m
  have hmap := hη.map_rootsOfUnity
    (algebraMap (AlgebraicClosure K) (Completion (AlgebraicClosure K))).injective
  let u : (Completion (AlgebraicClosure K))ˣ :=
    Units.ofPowEqOne ζ m hζ (NeZero.ne m)
  have hu : u ∈ rootsOfUnity m (Completion (AlgebraicClosure K)) := by
    rw [mem_rootsOfUnity, Units.ext_iff]
    exact hζ
  obtain ⟨ξ, hξ, hξu⟩ := hmap.symm ▸ hu
  have heq : algebraMap (AlgebraicClosure K) (Completion (AlgebraicClosure K))
      (ξ : AlgebraicClosure K) = ζ := congrArg Units.val hξu
  have hξpow : (ξ : AlgebraicClosure K) ^ m = 1 := by
    have := (mem_rootsOfUnity m ξ).mp hξ
    exact congrArg Units.val this
  have hfix : σ (ξ : AlgebraicClosure K) = ξ :=
    apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hm hξpow
  rw [← heq]
  -- The algebra map into the completion is its canonical dense embedding.
  simp only [Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
    Completion.mapAlgEquiv_coe, hfix]

end TauCeti
