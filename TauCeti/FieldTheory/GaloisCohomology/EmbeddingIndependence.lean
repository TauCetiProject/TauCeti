/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic

/-!
# Independence of embeddings in first Galois cohomology

For a field extension `L/K`, compatible coefficient maps along embeddings `Kˢ → Lˢ` induce
the same map on explicit `H¹` if precomposing an embedding by an automorphism of `Kˢ`
precomposes its coefficient map by the action of that automorphism. Two embeddings differ by
such an automorphism, and conjugation of compatible pairs acts trivially on `H¹`.

This is the embedding-independence consequence of the conjugation formalism in Neukirch,
Schmidt and Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5.
-/

public section

namespace TauCeti.ContCohomology

universe uK uL uM uN

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [Algebra K L]

/-- Pullbacks on explicit `H¹` along embeddings of separable closures are independent of the
embedding when the coefficient maps are equivariant and precomposition by an automorphism
agrees with its action on coefficients. This follows from conjugation invariance in Neukirch,
Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §5. -/
theorem explicitMap1_absoluteGaloisGroupMap_eq
    {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup L) N] [ContinuousSMul (AbsoluteGaloisGroup L) N]
    (F : (SeparableClosure K →ₐ[K] SeparableClosure L) → M →+ N)
    (hF : ∀ τ (g : AbsoluteGaloisGroup L) (m : M),
      F τ (absoluteGaloisGroupMap τ g • m) = g • F τ m)
    (hFcomp : ∀ τ (h : AbsoluteGaloisGroup K) (m : M),
      F (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) m = F τ (h • m))
    (τ τ' : SeparableClosure K →ₐ[K] SeparableClosure L) :
    explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N (absoluteGaloisGroupMap τ)
        (F τ) continuous_of_discreteTopology (hF τ) =
      explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N
        (absoluteGaloisGroupMap τ') (F τ') continuous_of_discreteTopology (hF τ') := by
  obtain ⟨h, rfl⟩ := τ.exists_comp_eq_of_normal τ'
  exact (explicitMap1_eq_of_conj _ _ _ _ _ _ _ _ _ _ h
    (absoluteGaloisGroupMap_comp τ h) (hFcomp τ h)).symm

end TauCeti.ContCohomology
