/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.MapCLM
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Hilbert direct sums of unitary representations

A family of unitary continuous representations `π i` of a monoid `G` on inner product spaces
`H i` can be summed over an arbitrary index type: `G` acts coordinatewise on the Hilbert direct sum
`lp H 2`, each operator being the direct sum `lp.mapCLM` of the uniformly bounded family
`fun i ↦ π i g`. The result is again unitary, it sends coordinate vectors to coordinate vectors,
and a vector of the sum is invariant under an element exactly when each of its coordinates is.

Direct sums of this kind assemble a single representation out of a family of witnesses, which is
how properties of representations stated with a quantifier over families (almost invariant vectors,
Kazhdan pairs) are reduced to a single representation.
-/

public section

noncomputable section

open scoped ENNReal

namespace ContRepresentation

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Monoid G] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)]

/-- The Hilbert direct sum of a family of unitary representations, acting coordinatewise on
`lp H 2`. -/
def hilbertSum (π : ∀ i, ContRepresentation 𝕜 G (H i)) (hπ : ∀ i, (π i).IsUnitary) :
    ContRepresentation 𝕜 G (lp H 2) :=
  .ofMonoidHom
    { toFun g := lp.mapCLM 2 (fun i ↦ π i g) zero_le_one fun i ↦ (hπ i).norm_le_one g
      map_one' := by ext x i; simp
      map_mul' g h := by ext x i; simp [mul_apply_eq_comp] }

variable (π : ∀ i, ContRepresentation 𝕜 G (H i)) (hπ : ∀ i, (π i).IsUnitary)

/-- The Hilbert direct sum of representations acts coordinatewise. -/
@[simp]
theorem hilbertSum_apply_apply (g : G) (x : lp H 2) (i : ι) :
    hilbertSum π hπ g x i = π i g (x i) :=
  (rfl)

/-- The Hilbert direct sum of unitary representations is unitary. -/
theorem isUnitary_hilbertSum : (hilbertSum π hπ).IsUnitary :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦
    le_antisymm (lp.norm_mono (by norm_num) fun i ↦ by simp [(hπ i).norm_map])
      (lp.norm_mono (by norm_num) fun i ↦ by simp [(hπ i).norm_map])

/-- The Hilbert direct sum of representations sends the coordinate vector `single i v` to the
coordinate vector `single i (π i g v)`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (g : G) (i : ι) (v : H i) :
    hilbertSum π hπ g (lp.single 2 i v) = lp.single 2 i (π i g v) :=
  lp.mapCLM_single _ zero_le_one (fun i ↦ (hπ i).norm_le_one g) i v

/-- A vector of the Hilbert direct sum is fixed by `g` exactly when each of its coordinates is. -/
theorem hilbertSum_apply_eq_self_iff (g : G) (x : lp H 2) :
    hilbertSum π hπ g x = x ↔ ∀ i, π i g (x i) = x i := by
  simp [lp.ext_iff, funext_iff]

/-- A vector of the Hilbert direct sum is invariant exactly when each of its coordinates is. -/
theorem mem_invariants_hilbertSum_iff (x : lp H 2) :
    x ∈ (hilbertSum π hπ).invariants ↔ ∀ i, x i ∈ (π i).invariants := by
  simp only [mem_invariants, hilbertSum_apply_eq_self_iff]
  exact forall_comm

/-- Restricting a Hilbert direct sum along a monoid homomorphism gives the Hilbert direct sum of
the restrictions. -/
theorem restrict_hilbertSum {S : Type*} [Monoid S] (φ : S →* G) :
    (hilbertSum π hπ).restrict φ =
      hilbertSum (fun i ↦ (π i).restrict φ) fun i ↦ (hπ i).restrict φ :=
  (rfl)

end ContRepresentation
