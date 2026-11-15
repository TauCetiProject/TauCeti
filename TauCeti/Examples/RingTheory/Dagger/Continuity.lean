/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.IntSubring
public import TauCeti.RingTheory.Dagger.FiniteExtension
public import Mathlib.Algebra.DualNumber

/-!
# Canonical topology, automatic continuity, and power-bounded elements on concrete dagger algebras

On `K` and `K⟨X⟩†`, `affinoidTopology` and `intSubring` recover the norm topology, the valuation
ring `{c : K | ‖c‖ ≤ 1}`, and `K°⟨X⟩†`. On the nonreduced dual-number dagger algebra `K[ε]`,
`affinoidTopology K K[ε]` remains Hausdorff and Tate, while `intSubring K K[ε]` contains the entire
nilpotent line `K • ε` and therefore contains elements of arbitrarily large residue norm.
-/

public section

open TauCeti TauCeti.Dagger
open scoped DualNumber

namespace TauCeti.Examples.DaggerContinuity

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- On the base field and the univariate Monsky–Washnitzer algebra, `affinoidTopology` and
-- `intSubring` recover the standard norm and integral structures.
example : affinoidTopology K K = (inferInstance : TopologicalSpace K) :=
  affinoidTopology_self

example : (intSubring K K : Set K) = Metric.closedBall 0 1 :=
  coe_intSubring_self

example : washnitzerAlgebra.X (Fin 1) K 0 ∈ intSubring K (washnitzerAlgebra (Fin 1) K) :=
  mem_intSubring_washnitzerAlgebra_iff.mpr (by simpa using X_mem_intWashnitzerAlgebra (0 : Fin 1))

section DualNumbers

/-- `K[ε]` is a finite `K`-module via its underlying product `K × K`. -/
local instance moduleFiniteDualNumber : Module.Finite K K[ε] :=
  inferInstanceAs (Module.Finite K (K × K))

/-- `K[ε]` is a `K`-dagger algebra as a finite `K`-algebra. -/
local instance isDaggerAlgebraDualNumber : IsDaggerAlgebra K K[ε] :=
  IsDaggerAlgebra.of_finite (A := K)

-- Even though `K[ε]` is nonreduced, its canonical affinoid topology is Hausdorff and Tate.
example :
    letI := affinoidTopology K K[ε]
    T2Space K[ε] :=
  t2Space_affinoidTopology K K[ε]

example :
    letI := affinoidTopology K K[ε]
    letI := isTopologicalRing_affinoidTopology K K[ε]
    Huber.IsTateRing K[ε] :=
  isTateRing_affinoidTopology K K[ε]

-- Every scalar multiple `c • ε` has supremum seminorm `0` and lies in `intSubring K K[ε]`,
-- and for large `c` its residue norm strictly exceeds `1`.
example (c : K) : supSeminorm K (c • (ε : K[ε])) = 0 :=
  IsDaggerAlgebra.supSeminorm_eq_zero_iff.mpr ⟨2, by ext <;> simp [sq]⟩

example :
    letI := residueNormedCommRing K K[ε]
    ∃ x ∈ intSubring K K[ε], 1 < ‖x‖ := by
  let _ := residueNormedCommRing K K[ε]
  let _ := residueNormedAlgebra K K[ε]
  have hε_ne : (ε : K[ε]) ≠ 0 := fun h ↦ by simpa using congrArg TrivSqZeroExt.snd h
  have hε_pos : 0 < ‖(ε : K[ε])‖ := norm_pos_iff.mpr hε_ne
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (1 / ‖(ε : K[ε])‖)
  refine ⟨c • (ε : K[ε]), ?_, ?_⟩
  · exact IsNilpotent.mem_intSubring ⟨2, by ext <;> simp [sq]⟩
  · rw [norm_smul]
    exact (div_lt_iff₀ hε_pos).mp hc

-- The augmentation `K[ε] →ₐ[K] K` is automatically continuous, induces a surjection on
-- completions, and maps `intSubring K K[ε]` into `intSubring K K`.
example :
    letI := affinoidTopology K K[ε]
    letI := affinoidTopology K K
    Continuous (TrivSqZeroExt.fstHom K K K) :=
  IsDaggerAlgebra.continuous_algHom_affinoidTopology K (TrivSqZeroExt.fstHom K K K)

example : Function.Surjective (completion.map (TrivSqZeroExt.fstHom K K K)) :=
  completion.map_surjective (φ := TrivSqZeroExt.fstHom K K K)
    fun c ↦ ⟨algebraMap K K[ε] c, by simp⟩

end DualNumbers

end TauCeti.Examples.DaggerContinuity
