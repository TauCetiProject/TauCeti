/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
import TauCeti.LinearAlgebra.Trace.Exact

/-!
# The subspace on which a representation acts through a character

For a representation `ρ` of a monoid `G` on `V` and a character `c : G →* k`, the vectors `v` with
`ρ g v = c g • v` for every `g` form a `G`-stable subspace `ρ.charSpace c`, the intersection of the
eigenspaces of the `ρ g` for the eigenvalues `c g`. For `c = 1` it is the subspace of invariants.

Over a field, with `V` finite-dimensional, the trace of `ρ g` splits along this subspace as
`dim (ρ.charSpace c) * c g` plus the trace of the induced action on the quotient.

## Main definitions

* `Representation.charSpace ρ c`: the vectors on which `G` acts through `c`.

## Main results

* `Representation.mem_charSpace`: membership is the equation `ρ g v = c g • v` for every `g`.
* `Representation.charSpace_le_comap`: `ρ.charSpace c` is `G`-stable.
* `Representation.trace_eq_finrank_charSpace_mul_add`: the splitting of the trace.
-/

public section

open Module

namespace Representation

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The vectors on which the representation `ρ` acts through the character `c`. -/
def charSpace (ρ : Representation k G V) (c : G →* k) : Submodule k V :=
  ⨅ g, Module.End.eigenspace (ρ g) (c g)

@[simp]
theorem mem_charSpace {ρ : Representation k G V} {c : G →* k} {v : V} :
    v ∈ ρ.charSpace c ↔ ∀ g, ρ g v = c g • v := by
  simp [charSpace]

/-- The subspace on which `ρ` acts through a character is `G`-stable. -/
theorem charSpace_le_comap (ρ : Representation k G V) (c : G →* k) (h : G) :
    ρ.charSpace c ≤ (ρ.charSpace c).comap (ρ h) := by
  intro v hv
  rw [Submodule.mem_comap, mem_charSpace]
  rw [mem_charSpace] at hv
  intro g
  rw [← mul_apply_eq_comp, ← map_mul, hv, hv, map_mul, mul_smul]

/-- The trace of `ρ g` splits along the vectors on which `G` acts through `c`. -/
theorem trace_eq_finrank_charSpace_mul_add {F : Type*} [Field F] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V) (c : G →* F) (g : G) :
    LinearMap.trace F V (ρ g) = finrank F (ρ.charSpace c) * c g +
      LinearMap.trace F _ (ρ.quotient _ (charSpace_le_comap ρ c) g) := by
  have hU (v) (hv : v ∈ ρ.charSpace c) : ρ g v ∈ ρ.charSpace c := charSpace_le_comap ρ c g hv
  have hres : (ρ g).restrict hU = c g • LinearMap.id := by
    ext ⟨v, hv⟩
    simp [LinearMap.restrict_apply, (mem_charSpace.mp hv) g]
  rw [LinearMap.trace_eq_add_of_exact (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (fN := (ρ g).restrict hU)
    (fQ := ρ.quotient _ (charSpace_le_comap ρ c) g) (by ext; simp) (by ext; simp), hres,
    map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end Representation
