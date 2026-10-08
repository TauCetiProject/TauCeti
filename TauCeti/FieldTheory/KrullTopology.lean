/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Stabilizers for the Krull topology are open

`Mathlib/FieldTheory/KrullTopology.lean` supplies the Krull topology on `Gal(L/K)` together with
`stabilizer_isOpen_of_isIntegral`, the fact that a point of an integral extension `L/K` has an
**open** stabilizer. This file draws the consequence for a *unit* of `L`, an automorphism fixing
a unit being exactly one that fixes the underlying element, and the pointwise form for a single
element integral over `K`, with no hypothesis on the extension `L/K`: the orbit map `σ ↦ σ x` is
locally constant.

Through Mathlib's `continuousSMul_iff_stabilizer_isOpen` this is what makes the units of an
algebraic extension a *discrete module* over the Galois group, in the sense continuous cohomology
asks for; `TauCeti.unitsCoeff_continuousSMul` is that consequence for a separable closure.

## Main results

* `TauCeti.stabilizer_isOpen_units`: the stabilizer of a unit of `L` is an open subgroup of
  `Gal(L/K)`.
* `IsIntegral.isLocallyConstant_apply`: for `x` integral over `K`, the orbit map
  `σ ↦ σ x` on `Gal(L/K)` is locally constant.
* `IntermediateField.isOpen_ker_comp_restrictNormalHom`: a character of `Gal(E/K)` for a finite
  normal intermediate field `E`, read on `Gal(L/K)` through restriction, has open kernel.
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The stabilizer of a unit of an integral extension is open: an automorphism fixes a unit
exactly when it fixes the underlying element. -/
theorem stabilizer_isOpen_units [Algebra.IsIntegral K L] (u : Lˣ) :
    IsOpen (MulAction.stabilizer Gal(L/K) u : Set Gal(L/K)) := by
  convert stabilizer_isOpen_of_isIntegral (K := K) (u : L) using 2
  ext σ
  simp [MulAction.mem_stabilizer_iff, Units.ext_iff]

open scoped IntermediateField Pointwise Topology in
/-- **The orbit map of an integral element is locally constant** for the Krull topology: near `σ₀`
lie the automorphisms `σ₀ * τ` with `τ` fixing the finite extension `K⟮x⟯`, and these all send `x`
to `σ₀ x`. Unlike `stabilizer_isOpen_of_isIntegral`, nothing is asked of `L / K`, so `L` may be
transcendental over `K`. -/
theorem _root_.IsIntegral.isLocallyConstant_apply {x : L} (hx : IsIntegral K x) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ σ x := by
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  have hmem : σ₀ ∈ σ₀ • (K⟮x⟯.fixingSubgroup : Set Gal(L/K)) := ⟨1, one_mem _, mul_one σ₀⟩
  filter_upwards [(K⟮x⟯.fixingSubgroup_isOpen.leftCoset σ₀).mem_nhds hmem]
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [smul_eq_mul, AlgEquiv.mul_apply]
  rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
    (IntermediateField.mem_adjoin_simple_self K x)]

/-- **A character of a finite normal layer has open kernel**: a character of `Gal(E/K)` for a
finite normal intermediate field `E`, read on `Gal(L/K)` through restriction to `E`, vanishes on
the open subgroup fixing `E`. -/
theorem _root_.IntermediateField.isOpen_ker_comp_restrictNormalHom {A : Type*} [AddGroup A]
    (E : IntermediateField K L) [FiniteDimensional K E] [Normal K E]
    (χ : Additive Gal(E/K) →+ A) :
    IsOpen ((χ.comp (AlgEquiv.restrictNormalHom (K₁ := L) E).toAdditive).ker :
      Set (Additive Gal(L/K))) := by
  refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup E.fixingSubgroup)
    (fun x hx ↦ ?_) (E.fixingSubgroup_isOpen.preimage continuous_toMul)
  rw [Additive.mem_toAddSubgroup, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker] at hx
  simp [hx]

end TauCeti
