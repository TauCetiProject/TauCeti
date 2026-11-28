/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Ideal.Operations

/-!
# Trace membership in an ideal for endomorphisms valued in J • ⊤

Over a commutative ring R, any R-linear functional maps the submodule J • ⊤ into the ideal
J. Consequently, an endomorphism of a finite free R-module whose values all lie in J • ⊤ has
trace in J, and two endomorphisms that are congruent modulo J • ⊤ have traces congruent modulo
J.

## Main results

* TauCeti.smul_top_le_comap_ideal: for any l : Module.Dual R M and J : Ideal R,
  J • ⊤ ≤ Submodule.comap l J.
* TauCeti.trace_mem_of_forall_mem_smul_top: if  : Module.End R M maps every vector of a
  finite free R-module M into J • ⊤, then LinearMap.trace R M f ∈ J.
* TauCeti.trace_sub_mem_of_forall_sub_mem_smul_top: if  v - g v ∈ J • ⊤ for all  : M,
  then LinearMap.trace R M f - LinearMap.trace R M g ∈ J.

## Provenance

TauCeti.trace_mem_of_forall_mem_smul_top is adapted from
New.Average.trace_mem_of_forall_mem_smul_top in
src/New/UpperBound/ElementaryDivisors/InvariantAverage.lean in grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Any R-linear functional l : Module.Dual R M carries J • ⊤ into the ideal J. -/
theorem smul_top_le_comap_ideal (J : Ideal R) (l : Module.Dual R M) :
    J • (⊤ : Submodule R M) ≤ Submodule.comap l J :=
  Submodule.smul_le.mpr fun _ hc v _ ↦ by
    simpa [LinearMap.map_smul, smul_eq_mul] using J.mul_mem_right (l v) hc

/-- An endomorphism of a finite free R-module whose values lie in J • ⊤ has trace in J. -/
theorem trace_mem_of_forall_mem_smul_top [Module.Free R M] [Module.Finite R M] {J : Ideal R}
    {f : Module.End R M} (hf : ∀ v : M, f v ∈ J • (⊤ : Submodule R M)) :
    LinearMap.trace R M f ∈ J := by
  let b := Module.Free.chooseBasis R M
  rw [LinearMap.trace_eq_matrix_trace R b]
  refine J.sum_mem fun i _ ↦ ?_
  simpa [LinearMap.toMatrix_apply] using smul_top_le_comap_ideal J (b.coord i) (hf (b i))

/-- Two endomorphisms of a finite free R-module that agree modulo J • ⊤ have traces that
agree modulo J. -/
theorem trace_sub_mem_of_forall_sub_mem_smul_top [Module.Free R M] [Module.Finite R M]
    {J : Ideal R} {f g : Module.End R M}
    (hfg : ∀ v : M, f v - g v ∈ J • (⊤ : Submodule R M)) :
    LinearMap.trace R M f - LinearMap.trace R M g ∈ J := by
  rw [← map_sub]
  exact trace_mem_of_forall_mem_smul_top fun v ↦ by simpa using hfg v

end TauCeti
