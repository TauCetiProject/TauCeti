/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
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
* `IsLocallyConstant.of_mul_eq_of_fixes`: a function on `Gal(L/K)` invariant under right
  multiplication by the automorphisms fixing a finite set of integral elements is locally constant.
* `Units.stabilizer_isOpen_of_isIntegral`: the stabilizer of a unit of `L` whose underlying
  element is integral over `K` is open in `Gal(L/K)`.
* `AlgHom.stabilizer_isOpen`: the stabilizer of a point `A →ₐ[K] L` of a finite-dimensional
  `K`-algebra, under the postcomposition action of `Gal(L/K)`, is open.
* `AlgEquiv.autCongr_mem_fixingSubgroup_iff`: conjugation by `e : L ≃ₐ[K] L'` carries the
  subgroup fixing `e⁻¹(E)` onto the subgroup fixing `E`.
* `AlgEquiv.continuous_autCongr`, `AlgEquiv.autContinuousCongr`: an isomorphism of field
  extensions `L ≃ₐ[K] L'` induces a topological group isomorphism `Gal(L/K) ≃ₜ* Gal(L'/K)` by
  conjugation.
* `AlgEquiv.continuous_restrictScalarsHom`, `AlgEquiv.isClosed_range_restrictScalarsHom`,
  `AlgEquiv.restrictScalarsHomRangeEquiv`: for any field tower `F → K → L`, restriction of scalars
  `Gal(L/K) →* Gal(L/F)` is continuous, and when `K/F` is algebraic its image is closed and
  isomorphic as a topological group to `Gal(L/K)`.
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

/-- **A function invariant under the subgroup fixing a finite set is locally constant** for the
Krull topology: if `f (σ * u) = f σ` whenever `u` fixes every element of a finite set `s` of
elements integral over `K`, then `f` is locally constant on `Gal(L/K)`. The extension `L/K` may be
transcendental. -/
theorem IsLocallyConstant.of_mul_eq_of_fixes {X : Type*} {f : Gal(L/K) → X} (s : Finset L)
    (hs : ∀ x ∈ s, IsIntegral K x)
    (hf : ∀ σ u : Gal(L/K), (∀ x ∈ s, u x = x) → f (σ * u) = f σ) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  filter_upwards [(Filter.eventually_all_finset s).2 fun x hx ↦
    (IsLocallyConstant.iff_eventually_eq _).1 (hs x hx).isLocallyConstant_apply σ₀] with σ hσ
  -- `σ = σ₀ * u`, where `u = σ₀⁻¹ * σ` fixes `s`
  have h := hf σ₀ (σ₀⁻¹ * σ) fun x hx ↦ by
    rw [AlgEquiv.mul_apply, hσ x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rwa [mul_inv_cancel_left] at h

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

/-- **An isomorphism of field extensions induces an isomorphism of topological Galois groups.**
Conjugation by `e : L ≃ₐ[K] L'` upgrades `e.autCongr` to a topological group isomorphism
`Gal(L/K) ≃ₜ* Gal(L'/K)` for the Krull topologies. -/
def AlgEquiv.autContinuousCongr {L' : Type*} [Field L'] [Algebra K L'] (e : L ≃ₐ[K] L') :
    Gal(L/K) ≃ₜ* Gal(L'/K) where
  __ := e.autCongr
  continuous_toFun := e.continuous_autCongr
  continuous_invFun := e.symm.continuous_autCongr

@[simp]
theorem AlgEquiv.autContinuousCongr_apply {L' : Type*} [Field L'] [Algebra K L']
    (e : L ≃ₐ[K] L') (σ : Gal(L/K)) : e.autContinuousCongr σ = e.autCongr σ :=
  (rfl)

@[simp]
theorem AlgEquiv.autContinuousCongr_refl :
    (AlgEquiv.refl : L ≃ₐ[K] L).autContinuousCongr = ContinuousMulEquiv.refl _ := by
  ext σ x
  rfl

@[simp]
theorem AlgEquiv.autContinuousCongr_symm {L' : Type*} [Field L'] [Algebra K L']
    (e : L ≃ₐ[K] L') : e.autContinuousCongr.symm = e.symm.autContinuousCongr :=
  (rfl)

@[simp]
theorem AlgEquiv.autContinuousCongr_trans {L' L'' : Type*} [Field L'] [Field L'']
    [Algebra K L'] [Algebra K L''] (e₁ : L ≃ₐ[K] L') (e₂ : L' ≃ₐ[K] L'') :
    e₁.autContinuousCongr.trans e₂.autContinuousCongr = (e₁.trans e₂).autContinuousCongr := by
  ext σ x
  rfl

section RestrictScalars

/-- **Restriction of scalars on Galois groups is continuous for the Krull topologies.**
For any tower of fields `F → K → L`, the canonical injection
`AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)` is continuous; neither algebraicity nor
normality is needed. -/
theorem AlgEquiv.continuous_restrictScalarsHom (F : Type*) [Field F] [Algebra F K] [Algebra F L]
    [IsScalarTower F K L] :
    Continuous (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)) := by
  refine continuous_of_continuousAt_one _ fun U hU ↦ ?_
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, _, hEU⟩ := hU
  let b := Module.finBasis F E
  let E' := IntermediateField.adjoin K (Set.range fun i ↦ (b i : L))
  have : FiniteDimensional K E' := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := F) (b i)).map E.val).tower_top
  refine Filter.mem_map.2 <| (krullTopology_mem_nhds_one_iff K L _).2
    ⟨E', inferInstance, fun τ hτ ↦ hEU <| (IntermediateField.mem_fixingSubgroup_iff E _).2 ?_⟩
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : L) := by
    simpa only [map_sum, map_smul, IntermediateField.coe_val] using
      congrArg E.val (b.sum_repr ⟨x, hx⟩).symm
  rw [AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalars_apply, hx', map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← AlgEquiv.restrictScalars_apply F, map_smul, AlgEquiv.restrictScalars_apply,
    (IntermediateField.mem_fixingSubgroup_iff E' τ).mp hτ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]

/-- **The image of restriction of scalars is closed in the Krull topology** when the base field
extension `K/F` is algebraic: an automorphism of `L/F` comes from `Gal(L/K)` precisely when it
fixes each element of `K` in `L`, and each point stabilizer is clopen by
`IsIntegral.isLocallyConstant_apply`. Neither algebraicity nor normality of `L/K` is needed. -/
theorem AlgEquiv.isClosed_range_restrictScalarsHom (F : Type*) [Field F] [Algebra F K]
    [Algebra F L] [IsScalarTower F K L] [Algebra.IsAlgebraic F K] :
    IsClosed ((AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range : Set Gal(L/F)) := by
  have hrange : ((AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range : Set Gal(L/F)) =
      ⋂ c : K, {σ : Gal(L/F) | σ (algebraMap K L c) = algebraMap K L c} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_range, AlgEquiv.restrictScalarsHom_apply,
      Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun ⟨τ, hτ⟩ c ↦ hτ ▸ τ.commutes c, fun h ↦ ⟨{ σ with commutes' := h }, rfl⟩⟩
  rw [hrange]
  exact isClosed_iInter fun c ↦
    ((Algebra.IsIntegral.isIntegral (R := F) c).algebraMap).isLocallyConstant_apply.isClosed_fiber _

private noncomputable def restrictScalarsHomRangeMulEquiv (F K L : Type*) [Field F] [Field K]
    [Field L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] :
    Gal(L/K) ≃* (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range :=
  MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective F)

private theorem restrictScalarsHomRangeMulEquiv_symm_apply_apply {F K L : Type*} [Field F]
    [Field K] [Field L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    (σ : (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range) (x : L) :
    (restrictScalarsHomRangeMulEquiv F K L).symm σ x = (σ : Gal(L/F)) x := by
  have h := congrArg (fun u : (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range ↦
      (u : Gal(L/F)) x)
    ((restrictScalarsHomRangeMulEquiv F K L).apply_symm_apply σ)
  exact h

private theorem continuous_restrictScalarsHomRangeMulEquiv_symm (F K L : Type*) [Field F]
    [Field K] [Field L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Algebra.IsAlgebraic F K] :
    Continuous (restrictScalarsHomRangeMulEquiv F K L).symm := by
  refine continuous_of_continuousAt_one (restrictScalarsHomRangeMulEquiv F K L).symm.toMonoidHom
    fun U hU ↦ ?_
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, _, hEU⟩ := hU
  let b := Module.finBasis K E
  let E₀ := IntermediateField.adjoin F (Set.range fun i ↦ (b i : L))
  have : FiniteDimensional F E₀ := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    exact isIntegral_trans (A := K) _ ((Algebra.IsIntegral.isIntegral (R := K) (b i)).map E.val)
  have hnhds : (Subtype.val ⁻¹' (E₀.fixingSubgroup : Set Gal(L/F))) ∈
      nhds (1 : (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range) :=
    continuous_subtype_val.continuousAt (E₀.fixingSubgroup_isOpen.mem_nhds (one_mem _))
  refine Filter.mem_map.2 (Filter.mem_of_superset hnhds fun σ hσ ↦ hEU ?_)
  rw [MulEquiv.coe_toMonoidHom, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : L) := by
    simpa only [map_sum, map_smul, IntermediateField.coe_val] using
      congrArg E.val (b.sum_repr ⟨x, hx⟩).symm
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, restrictScalarsHomRangeMulEquiv_symm_apply_apply,
    (IntermediateField.mem_fixingSubgroup_iff E₀ _).mp hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]

/-- **Restriction of scalars embeds `Gal(L/K)` as a topological subgroup of `Gal(L/F)`** when `K/F`
is algebraic: `AlgEquiv.restrictScalarsHom F` induces a topological group isomorphism
`Gal(L/K) ≃ₜ* (AlgEquiv.restrictScalarsHom F).range` for the Krull topologies, with no normality or
algebraicity assumption on `L/K`. -/
noncomputable def AlgEquiv.restrictScalarsHomRangeEquiv (F K L : Type*) [Field F] [Field K]
    [Field L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Algebra.IsAlgebraic F K] :
    Gal(L/K) ≃ₜ* (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range where
  __ := restrictScalarsHomRangeMulEquiv F K L
  continuous_toFun := (AlgEquiv.continuous_restrictScalarsHom F).subtype_mk _
  continuous_invFun := continuous_restrictScalarsHomRangeMulEquiv_symm F K L

@[simp]
theorem AlgEquiv.coe_restrictScalarsHomRangeEquiv_apply {F : Type*} [Field F] [Algebra F K]
    [Algebra F L] [IsScalarTower F K L] [Algebra.IsAlgebraic F K] (τ : Gal(L/K)) :
    (AlgEquiv.restrictScalarsHomRangeEquiv F K L τ : Gal(L/F)) = τ.restrictScalars F :=
  (rfl)

@[simp]
theorem AlgEquiv.restrictScalarsHomRangeEquiv_symm_restrictScalars {F : Type*} [Field F]
    [Algebra F K] [Algebra F L] [IsScalarTower F K L] [Algebra.IsAlgebraic F K] (τ : Gal(L/K))
    (hτ : τ.restrictScalars F ∈ (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range) :
    (AlgEquiv.restrictScalarsHomRangeEquiv F K L).symm ⟨τ.restrictScalars F, hτ⟩ = τ := by
  apply (AlgEquiv.restrictScalarsHomRangeEquiv F K L).injective
  ext x
  simp

@[simp]
theorem AlgEquiv.restrictScalars_restrictScalarsHomRangeEquiv_symm {F : Type*} [Field F]
    [Algebra F K] [Algebra F L] [IsScalarTower F K L] [Algebra.IsAlgebraic F K]
    (σ : (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range) :
    ((AlgEquiv.restrictScalarsHomRangeEquiv F K L).symm σ).restrictScalars F = (σ : Gal(L/F)) := by
  rw [← AlgEquiv.coe_restrictScalarsHomRangeEquiv_apply (F := F) (K := K) (L := L),
    ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem AlgEquiv.restrictScalarsHomRangeEquiv_symm_apply_apply {F : Type*} [Field F] [Algebra F K]
    [Algebra F L] [IsScalarTower F K L] [Algebra.IsAlgebraic F K]
    (σ : (AlgEquiv.restrictScalarsHom F : Gal(L/K) →* Gal(L/F)).range) (x : L) :
    (AlgEquiv.restrictScalarsHomRangeEquiv F K L).symm σ x = (σ : Gal(L/F)) x := by
  rw [← AlgEquiv.restrictScalars_apply F,
    AlgEquiv.restrictScalars_restrictScalarsHomRangeEquiv_symm]

end RestrictScalars

namespace TauCeti

/-- **`L` is a discrete `Gal(L/K)`-module for an algebraic extension `L/K`**: every element of `L`
is integral over `K`, so its stabilizer is open for the Krull topology. -/
instance continuousSMul_forcedDiscrete [Algebra.IsIntegral K L] :
    ContinuousSMul Gal(L/K) (ForcedDiscrete L) :=
  (ForcedDiscrete.continuousSMul_iff L).2 stabilizer_isOpen_of_isIntegral

end TauCeti
