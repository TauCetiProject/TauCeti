/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuity of derivations for the module topology

Let `A` be a topological commutative ring and `B` a finite `A`-algebra equipped with the `A`-module
topology (`IsModuleTopology A B`). Because `B` admits a surjective `A`-linear map from a finite
power `Fin n → A` — which is a quotient map for the module topologies — the Leibniz rule expresses
any derivation `δ : B → M` on `B` in terms of its restriction `δ.compAlgebraMap A : A → M` and the
values of `δ` on a finite generating set.

Consequently, for any topological `B`-module `M` with continuous addition and continuous `B`-scalar
multiplication, a derivation `δ : B → M` is continuous on `B` if and only if its restriction to `A`
is continuous (`Derivation.continuous_iff_continuous_compAlgebraMap`). No basis, Hausdorffness, or
separability assumption on `B` or `M` is required.

## Main results

* `Derivation.continuous_compAlgebraMap`: restricting a continuous derivation along `algebraMap A B`
  gives a continuous derivation on `A`.
* `Derivation.continuous_of_continuous_compAlgebraMap`: on a module-finite `A`-algebra with the
  `A`-module topology, continuity on `A` implies continuity on `B`.
* `Derivation.continuous_iff_continuous_compAlgebraMap`: a derivation on `B` is continuous if and
  only if its restriction to `A` is continuous.
-/

public section

namespace Derivation

/-- Restricting a continuous derivation along `algebraMap A B` yields a continuous derivation on `A`
when `A` is a topological semiring and `B` carries the `A`-module topology. -/
theorem continuous_compAlgebraMap {R A B M : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommMonoid M] [Module R M] [Module A M] [Module B M] [IsScalarTower A B M]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M]
    [IsTopologicalSemiring A] [IsModuleTopology A B]
    {δ : Derivation R B M} (hδ : Continuous δ) :
    Continuous (δ.compAlgebraMap A) := by
  have : ContinuousAdd B := IsModuleTopology.toContinuousAdd A B
  exact hδ.comp (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A B))

section Finite

variable {R A B M : Type*} [CommSemiring R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommMonoid M] [Module R M] [Module A M] [Module B M] [IsScalarTower A B M]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M]
  [IsTopologicalSemiring A] [IsModuleTopology A B] [Module.Finite A B]
  [ContinuousAdd M] [ContinuousSMul B M]

/-- A derivation `δ : B → M` of a finite `A`-algebra carrying the `A`-module topology into a
topological `B`-module is continuous whenever its restriction to `A` is continuous. -/
theorem continuous_of_continuous_compAlgebraMap
    {δ : Derivation R B M} (hδ : Continuous (δ.compAlgebraMap A)) :
    Continuous δ := by
  have : ContinuousAdd B := IsModuleTopology.toContinuousAdd A B
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  rw [Topology.IsQuotientMap.continuous_iff (IsModuleTopology.isQuotientMap_of_surjective hf)]
  have hsum : (δ ∘ f : (Fin n → A) → M) = fun c ↦ ∑ i : Fin n,
        (Algebra.linearMap A B (c i) • δ (f (Pi.single i 1)) +
          f (Pi.single i 1) • δ.compAlgebraMap A (c i)) := by
    ext c
    simp only [Function.comp_apply]
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hci : Pi.single i (c i) = c i • Pi.single i (1 : A) := by
      ext j
      by_cases hij : j = i <;> simp [hij]
    rw [hci, LinearMap.map_smul, Algebra.smul_def, δ.leibniz]
    rfl
  have : Continuous (Algebra.linearMap A B) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A B)
  rw [hsum]
  fun_prop

/-- A derivation `δ : B → M` of a finite `A`-algebra carrying the `A`-module topology into a
topological `B`-module is continuous if and only if its restriction to `A` is continuous. -/
theorem continuous_iff_continuous_compAlgebraMap (δ : Derivation R B M) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap A) :=
  ⟨continuous_compAlgebraMap, continuous_of_continuous_compAlgebraMap⟩

end Finite

end Derivation
