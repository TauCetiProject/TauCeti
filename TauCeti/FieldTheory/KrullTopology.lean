/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.GroupAction.AlgHom
public import TauCeti.Topology.Algebra.GroupAction.ForcedDiscrete
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Openness, local constancy and conjugation for the Krull topology

`Mathlib/FieldTheory/KrullTopology.lean` supplies the Krull topology on `Gal(L/K)`. For an element
`x` integral over `K`, the orbit map `σ ↦ σ x` is locally constant. Consequently, a unit whose
underlying element is integral over `K` has an open stabilizer. Both results apply to arbitrary
field extensions `L/K`, including transcendental extensions. An isomorphism of extensions
`L ≃ₐ[K] L'` conjugates `Gal(L/K)` onto `Gal(L'/K)` continuously, so Galois groups of isomorphic
extensions are isomorphic as topological groups.

Through Mathlib's `continuousSMul_iff_stabilizer_isOpen` this is what makes the units of an
algebraic extension a *discrete module* over the Galois group, in the sense continuous cohomology
asks for; `TauCeti.unitsCoeff_continuousSMul` is that consequence for a separable closure. The
additive counterpart is `TauCeti.continuousSMul_forcedDiscrete`: an algebraic extension `L`, with
the discrete topology imposed by `TauCeti.ForcedDiscrete`, is a discrete `Gal(L/K)`-module.

## Main results

* `IsIntegral.isLocallyConstant_apply`: for `x` integral over `K`, the orbit map
  `σ ↦ σ x` on `Gal(L/K)` is locally constant.
* `Matrix.isLocallyConstant_map`: the orbit map of a finite matrix with integral entries is
  locally constant.
* `Units.stabilizer_isOpen_of_isIntegral`: the stabilizer of a unit of `L` whose underlying
  element is integral over `K` is open in `Gal(L/K)`.
* `AlgHom.stabilizer_isOpen`: the stabilizer of a point `A →ₐ[K] L` of a finite-dimensional
  `K`-algebra, under the postcomposition action of `Gal(L/K)`, is open.
* `AlgEquiv.autCongr_mem_fixingSubgroup_iff`: conjugation by `e : L ≃ₐ[K] L'` carries the
  subgroup fixing `e⁻¹(E)` onto the subgroup fixing `E`.
* `AlgEquiv.continuous_autCongr`: an isomorphism of field extensions `L ≃ₐ[K] L'` induces a
  continuous isomorphism `Gal(L/K) ≃* Gal(L'/K)` by conjugation.
* `IntermediateField.isOpen_ker_comp_restrictNormalHom`: an additive homomorphism from
  `Gal(E/K)` for a finite normal intermediate field `E`, read on `Gal(L/K)` through restriction,
  has open kernel.
* `TauCeti.continuousSMul_forcedDiscrete`: for an algebraic extension `L/K`, `ForcedDiscrete L` is
  a discrete `Gal(L/K)`-module.
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

/-- **The stabilizer of a point of a finite algebra is open.** For a finite-dimensional algebra
`A` over `K`, the subgroup of `Gal(L/K)` fixing a point `φ : A →ₐ[K] L` is open in the Krull
topology: it contains the subgroup fixing the finite extension of `K` generated by the values of
`φ` on a spanning set of `A`. The extension `L/K` may be transcendental. -/
theorem AlgHom.stabilizer_isOpen {A : Type*} [Ring A] [Algebra K A] [Module.Finite K A]
    (φ : A →ₐ[K] L) : IsOpen (MulAction.stabilizer Gal(L/K) φ : Set Gal(L/K)) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := A)
  let E := IntermediateField.adjoin K (φ '' s)
  have : FiniteDimensional K E := by
    have : _root_.Finite (φ '' s) := (s.finite_toSet.image φ).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    exact (Algebra.IsIntegral.isIntegral a).map φ
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) E.fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  refine AlgHom.toLinearMap_injective (LinearMap.ext_on hs fun a ha ↦ ?_)
  have hE : φ a ∈ E := IntermediateField.subset_adjoin _ _ ⟨a, ha, rfl⟩
  simpa using (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ (φ a) hE

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

/-- **Conjugation transports fixing subgroups.** For an isomorphism `e : L ≃ₐ[K] L'` of field
extensions of `K`, the conjugate `e ∘ σ ∘ e⁻¹` of `σ ∈ Gal(L/K)` fixes an intermediate field `E`
of `L'` exactly when `σ` fixes `e⁻¹(E)`. -/
theorem AlgEquiv.autCongr_mem_fixingSubgroup_iff {L' : Type*} [Field L'] [Algebra K L']
    (e : L ≃ₐ[K] L') (E : IntermediateField K L') {σ : Gal(L/K)} :
    e.autCongr σ ∈ E.fixingSubgroup ↔ σ ∈ (E.map e.symm.toAlgHom).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h _ ⟨x, hx, hxy⟩ ↦ ?_, fun h x hx ↦ ?_⟩
  · have hσ := h x hx
    rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
      ← AlgEquiv.eq_symm_apply] at hσ
    rwa [← hxy]
  · rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
      h (e.symm x) ⟨x, hx, rfl⟩, AlgEquiv.apply_symm_apply]

/-- **Conjugation by an isomorphism of extensions is continuous for the Krull topologies.** For an
isomorphism `e : L ≃ₐ[K] L'` of field extensions of `K`, the isomorphism of Galois groups
`e.autCongr : σ ↦ e ∘ σ ∘ e⁻¹` maps the subgroup fixing `e⁻¹(E)` into the subgroup fixing `E`,
for every finite-dimensional intermediate field `E` of `L'`. The extensions may be
transcendental. -/
theorem AlgEquiv.continuous_autCongr {L' : Type*} [Field L'] [Algebra K L'] (e : L ≃ₐ[K] L') :
    Continuous e.autCongr := by
  refine continuous_of_continuousAt_one e.autCongr fun s hs ↦ ?_
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, _, hEs⟩ := hs
  have : FiniteDimensional K (E.map e.symm.toAlgHom) :=
    (IntermediateField.intermediateFieldMap e.symm E).toLinearEquiv.finiteDimensional
  refine Filter.mem_map.2 <| (krullTopology_mem_nhds_one_iff K L _).2
    ⟨E.map e.symm.toAlgHom, inferInstance,
      fun σ hσ ↦ hEs ((e.autCongr_mem_fixingSubgroup_iff E).2 hσ)⟩

namespace TauCeti

/-- **`L` is a discrete `Gal(L/K)`-module for an algebraic extension `L/K`**: every element of `L`
is integral over `K`, so its stabilizer is open for the Krull topology. -/
instance continuousSMul_forcedDiscrete [Algebra.IsIntegral K L] :
    ContinuousSMul Gal(L/K) (ForcedDiscrete L) :=
  (ForcedDiscrete.continuousSMul_iff L).2 stabilizer_isOpen_of_isIntegral

end TauCeti
