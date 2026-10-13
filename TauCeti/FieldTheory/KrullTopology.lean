/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Openness and local constancy for the Krull topology

`Mathlib/FieldTheory/KrullTopology.lean` supplies the Krull topology on `Gal(L/K)`. For an element
`x` integral over `K`, the orbit map `σ ↦ σ x` is locally constant. Consequently, a unit whose
underlying element is integral over `K` has an open stabilizer. Both results apply to arbitrary
field extensions `L/K`, including transcendental extensions.

Through Mathlib's `continuousSMul_iff_stabilizer_isOpen` this is what makes the units of an
algebraic extension a *discrete module* over the Galois group, in the sense continuous cohomology
asks for; `TauCeti.unitsCoeff_continuousSMul` is that consequence for a separable closure.

## Main results

* `IsIntegral.isLocallyConstant_apply`: for `x` integral over `K`, the orbit map
  `σ ↦ σ x` on `Gal(L/K)` is locally constant.
* `Matrix.isLocallyConstant_map`: the orbit map of a finite matrix with integral entries is
  locally constant.
* `Units.stabilizer_isOpen_of_isIntegral`: the stabilizer of a unit of `L` whose underlying
  element is integral over `K` is open in `Gal(L/K)`.
* `IntermediateField.isOpen_ker_comp_restrictNormalHom`: an additive homomorphism from
  `Gal(E/K)` for a finite normal intermediate field `E`, read on `Gal(L/K)` through restriction,
  has open kernel.
-/

public section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open scoped IntermediateField Pointwise Topology in
/-- The orbit map of an integral element is locally constant for the Krull topology.
The extension `L/K` may be transcendental. -/
theorem IsIntegral.isLocallyConstant_apply {x : L} (hx : IsIntegral K x) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ σ x := by
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  have hmem : σ₀ ∈ σ₀ • (K⟮x⟯.fixingSubgroup : Set Gal(L/K)) := ⟨1, one_mem _, mul_one σ₀⟩
  filter_upwards [(K⟮x⟯.fixingSubgroup_isOpen.leftCoset σ₀).mem_nhds hmem]
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [smul_eq_mul, AlgEquiv.mul_apply]
  rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
    (IntermediateField.mem_adjoin_simple_self K x)]

/-- **The orbit map of a finite matrix with integral entries is locally constant** for the Krull
topology: `σ ↦ M.map σ`, the entrywise action of `Gal(L/K)` on `M`, is locally constant. -/
theorem Matrix.isLocallyConstant_map {m n : Type*} [Finite m] [Finite n]
    {M : Matrix m n L} (hM : ∀ i j, IsIntegral K (M i j)) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ M.map σ := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  filter_upwards [Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦
    (IsLocallyConstant.iff_eventually_eq _).1 (hM i j).isLocallyConstant_apply σ₀] with σ hσ
  exact Matrix.ext fun i j ↦ hσ i j

/-- The stabilizer of a unit whose underlying element is integral over `K` is open for the
Krull topology. The extension `L/K` may be transcendental. -/
theorem Units.stabilizer_isOpen_of_isIntegral (u : Lˣ) (hu : IsIntegral K (u : L)) :
    IsOpen (MulAction.stabilizer Gal(L/K) u : Set Gal(L/K)) := by
  convert hu.isLocallyConstant_apply.isOpen_fiber (u : L) using 1
  ext σ
  simp [MulAction.mem_stabilizer_iff, Units.ext_iff]

/-- An additive homomorphism from `Gal(E/K)` for a finite normal intermediate field `E`,
composed with restriction from `Gal(L/K)`, has open kernel. -/
theorem IntermediateField.isOpen_ker_comp_restrictNormalHom {A : Type*} [AddZeroClass A]
    (E : IntermediateField K L) [FiniteDimensional K E] [Normal K E]
    (χ : Additive Gal(E/K) →+ A) :
    IsOpen ((χ.comp (AlgEquiv.restrictNormalHom (K₁ := L) E).toAdditive).ker :
      Set (Additive Gal(L/K))) := by
  refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup E.fixingSubgroup)
    (fun x hx ↦ ?_) (E.fixingSubgroup_isOpen.preimage continuous_toMul)
  rw [Additive.mem_toAddSubgroup, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker] at hx
  simp [hx]
