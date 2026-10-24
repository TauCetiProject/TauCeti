/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.OneOne
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The topology of `Spin(1, 1)`

The real Spin group `Spin(1, 1)` of signature `(1, 1)` is algebraically
`μ₂(ℝ) × ℝ`, its elements being `ζ (cosh t + sinh t z)` with `ζ = ±1`, `t : ℝ` and `z = e₁ e₂`
(`CliffordAlgebra.realCliffordSpinOneOneEquiv`). This file shows that, for the subspace topology
from the Clifford algebra, this is an isomorphism of topological groups. Consequently
`Spin(1, 1)` has exactly two connected components: the identity component is the group of
hyperbolic rotations `cosh t + sinh t z`, a copy of `(ℝ, +)`, and the other component is its
negative. In particular `Spin(1, 1)` is not connected.

The inverse map is explicit. In the matrix model `TauCeti.realCliffordOneOneEquivMatrix`, the
element `ζ (cosh t + sinh t z)` is `!![ζ cosh t, ζ sinh t; ζ sinh t, ζ cosh t]`, so `ζ` is the sign
of the top left entry and `t` is the inverse hyperbolic sine of `ζ` times the top right entry.
Both entries are continuous, because every linear map out of the Clifford algebra is continuous
for its module topology (`IsModuleTopology.continuous_of_linearMap`).

## Main definitions

* `CliffordAlgebra.realCliffordSpinOneOneContinuousMulEquiv`: the isomorphism of topological
  groups `μ₂(ℝ) × ℝ ≃ₜ* Spin(1, 1)`.

## Main results

* `CliffordAlgebra.isEmbedding_realCliffordSpinOneOneHyperbolicRotation`: the hyperbolic rotations
  embed `(ℝ, +)` into `Spin(1, 1)`.
* `CliffordAlgebra.connectedComponent_one_realCliffordSpinGroup_one_one` and
  `CliffordAlgebra.connectedComponentOfOne_realCliffordSpinGroup_one_one`: the identity component
  of `Spin(1, 1)` is the group of hyperbolic rotations.
* `CliffordAlgebra.index_connectedComponentOfOne_realCliffordSpinGroup_one_one`: the identity
  component has index two, so `Spin(1, 1)` has two connected components.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open TauCeti Real

namespace CliffordAlgebra

/-- The forward map `(ζ, t) ↦ ζ (cosh t + sinh t z)` is continuous. -/
private theorem continuous_realCliffordSpinOneOneEquiv :
    Continuous realCliffordSpinOneOneEquiv := by
  rw [continuous_induced_rng]
  have : ((↑) ∘ realCliffordSpinOneOneEquiv : _ → CliffordAlgebra (realCliffordForm 1 1)) =
      fun p ↦ algebraMap ℝ _ (((p.1 : ℝˣ) : ℝ) * cosh p.2.toAdd) +
        (((p.1 : ℝˣ) : ℝ) * sinh p.2.toAdd) • realCliffordOneOneVolume :=
    funext coe_realCliffordSpinOneOneEquiv_apply
  rw [this]
  have := continuous_algebraMap ℝ (CliffordAlgebra (realCliffordForm 1 1))
  fun_prop

/-- The top left entry of a Spin element in the matrix model: `ζ cosh t`. -/
private noncomputable def coeffOne (x : realCliffordSpinGroup 1 1) : ℝ :=
  realCliffordOneOneEquivMatrix (x : CliffordAlgebra (realCliffordForm 1 1)) 0 0

/-- The top right entry of a Spin element in the matrix model: `ζ sinh t`. -/
private noncomputable def coeffVol (x : realCliffordSpinGroup 1 1) : ℝ :=
  realCliffordOneOneEquivMatrix (x : CliffordAlgebra (realCliffordForm 1 1)) 0 1

private theorem coeffOne_realCliffordSpinOneOneEquiv (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    coeffOne (realCliffordSpinOneOneEquiv p) = ((p.1 : ℝˣ) : ℝ) * cosh p.2.toAdd := by
  rw [coeffOne, coe_realCliffordSpinOneOneEquiv_apply,
    realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume]
  simp

private theorem coeffVol_realCliffordSpinOneOneEquiv (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    coeffVol (realCliffordSpinOneOneEquiv p) = ((p.1 : ℝˣ) : ℝ) * sinh p.2.toAdd := by
  rw [coeffVol, coe_realCliffordSpinOneOneEquiv_apply,
    realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume]
  simp

private theorem continuous_coeffOne : Continuous coeffOne :=
  ((IsModuleTopology.continuous_of_linearMap realCliffordOneOneEquivMatrix.toLinearMap).comp
    continuous_subtype_val).matrix_elem 0 0

private theorem continuous_coeffVol : Continuous coeffVol :=
  ((IsModuleTopology.continuous_of_linearMap realCliffordOneOneEquivMatrix.toLinearMap).comp
    continuous_subtype_val).matrix_elem 0 1

/-- The sign `ζ`, read off from the sign of `ζ cosh t`. -/
private noncomputable def spinSign (x : realCliffordSpinGroup 1 1) : rootsOfUnity 2 ℝ :=
  if 0 < coeffOne x then 1 else negOneRootsOfUnity

/-- The explicit inverse of `realCliffordSpinOneOneEquiv`. -/
private noncomputable def spinInv (x : realCliffordSpinGroup 1 1) :
    rootsOfUnity 2 ℝ × Multiplicative ℝ :=
  (spinSign x, Multiplicative.ofAdd (arsinh (((spinSign x : ℝˣ) : ℝ) * coeffVol x)))

private theorem spinInv_realCliffordSpinOneOneEquiv (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    spinInv (realCliffordSpinOneOneEquiv p) = p := by
  obtain ⟨ζ, t⟩ := p
  have hsign : spinSign (realCliffordSpinOneOneEquiv (ζ, t)) = ζ := by
    rw [spinSign, coeffOne_realCliffordSpinOneOneEquiv]
    rcases eq_one_or_eq_negOneRootsOfUnity ζ with rfl | rfl
    · simp [cosh_pos]
    · simp [negOneRootsOfUnity, (cosh_pos _).le]
  have hζ : ((ζ : ℝˣ) : ℝ) * ((ζ : ℝˣ) : ℝ) = 1 := by
    rw [← sq]
    exact_mod_cast (mem_rootsOfUnity' 2 (ζ : ℝˣ)).mp ζ.2
  rw [spinInv, hsign, coeffVol_realCliffordSpinOneOneEquiv, ← mul_assoc, hζ, one_mul,
    arsinh_sinh, ofAdd_toAdd]

private theorem continuous_spinSign : Continuous spinSign := by
  have hneg : (negOneRootsOfUnity : rootsOfUnity 2 ℝ) ≠ 1 :=
    negOneRootsOfUnity_ne_one (by norm_num)
  -- `ζ cosh t` never vanishes, so both signs cut out open sets.
  have hne (x : realCliffordSpinGroup 1 1) : coeffOne x ≠ 0 := by
    obtain ⟨⟨ζ, t⟩, rfl⟩ := realCliffordSpinOneOneEquiv.surjective x
    rw [coeffOne_realCliffordSpinOneOneEquiv]
    exact mul_ne_zero (Units.ne_zero _) (cosh_pos _).ne'
  rw [continuous_discrete_rng]
  intro ζ
  rcases eq_one_or_eq_negOneRootsOfUnity ζ with rfl | rfl
  · convert isOpen_lt (continuous_const (y := (0 : ℝ))) continuous_coeffOne using 1
    ext x
    by_cases hx : 0 < coeffOne x <;> simp [spinSign, hx, hneg]
  · convert isOpen_lt continuous_coeffOne (continuous_const (y := (0 : ℝ))) using 1
    ext x
    by_cases hx : 0 < coeffOne x
    · simp [spinSign, hx, hneg.symm, hx.le]
    · simp [spinSign, hx, lt_of_le_of_ne (not_lt.mp hx) (hne x)]

/-- **`Spin(1, 1) ≅ μ₂(ℝ) × ℝ` as topological groups.** The isomorphism
`(ζ, t) ↦ ζ (cosh t + sinh t z)` of `CliffordAlgebra.realCliffordSpinOneOneEquiv` is a
homeomorphism for the subspace topology of `Spin(1, 1)` in `Cliff(1, 1)`. -/
noncomputable def realCliffordSpinOneOneContinuousMulEquiv :
    rootsOfUnity 2 ℝ × Multiplicative ℝ ≃ₜ* realCliffordSpinGroup 1 1 where
  toMulEquiv := realCliffordSpinOneOneEquiv
  continuous_toFun := continuous_realCliffordSpinOneOneEquiv
  continuous_invFun := by
    have h : (realCliffordSpinOneOneEquiv.symm : realCliffordSpinGroup 1 1 → _) = spinInv :=
      funext fun x ↦ by
        obtain ⟨p, rfl⟩ := realCliffordSpinOneOneEquiv.surjective x
        rw [MulEquiv.symm_apply_apply, spinInv_realCliffordSpinOneOneEquiv]
    -- The inverse field is the inverse of `realCliffordSpinOneOneEquiv`, which is `spinInv`.
    change Continuous realCliffordSpinOneOneEquiv.symm
    rw [h]
    have hσ : Continuous fun x ↦ ((spinSign x : ℝˣ) : ℝ) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_spinSign)
    exact continuous_spinSign.prodMk
      (continuous_ofAdd.comp (continuous_arsinh.comp (hσ.mul continuous_coeffVol)))

@[simp]
theorem coe_realCliffordSpinOneOneContinuousMulEquiv :
    ⇑realCliffordSpinOneOneContinuousMulEquiv = realCliffordSpinOneOneEquiv :=
  (rfl)

@[simp]
theorem coe_realCliffordSpinOneOneContinuousMulEquiv_symm :
    ⇑realCliffordSpinOneOneContinuousMulEquiv.symm = realCliffordSpinOneOneEquiv.symm :=
  (rfl)

/-- The sign of a Spin element is locally constant. -/
theorem continuous_realCliffordSpinOneOneSign : Continuous realCliffordSpinOneOneSign := by
  rw [funext realCliffordSpinOneOneSign_apply, ← coe_realCliffordSpinOneOneContinuousMulEquiv_symm]
  exact continuous_fst.comp realCliffordSpinOneOneContinuousMulEquiv.symm.continuous

private theorem realCliffordSpinOneOneHyperbolicRotation_eq_comp :
    (realCliffordSpinOneOneHyperbolicRotation : Multiplicative ℝ → _) =
      realCliffordSpinOneOneContinuousMulEquiv ∘ Prod.mk 1 :=
  funext fun t ↦ (realCliffordSpinOneOneEquiv_one_mk t).symm

/-- The hyperbolic rotations embed `(ℝ, +)` into `Spin(1, 1)` as topological groups. -/
theorem isEmbedding_realCliffordSpinOneOneHyperbolicRotation :
    Topology.IsEmbedding realCliffordSpinOneOneHyperbolicRotation := by
  rw [realCliffordSpinOneOneHyperbolicRotation_eq_comp]
  exact realCliffordSpinOneOneContinuousMulEquiv.toHomeomorph.isEmbedding.comp
    (isEmbedding_prodMkRight 1)

/-- **The identity component of `Spin(1, 1)`** is the group of hyperbolic rotations
`cosh t + sinh t z`. -/
theorem connectedComponent_one_realCliffordSpinGroup_one_one :
    connectedComponent (1 : realCliffordSpinGroup 1 1) =
      Set.range realCliffordSpinOneOneHyperbolicRotation := by
  apply subset_antisymm
  · -- The hyperbolic rotations are the kernel of the locally constant sign, hence clopen.
    have h : Set.range realCliffordSpinOneOneHyperbolicRotation =
        realCliffordSpinOneOneSign ⁻¹' {1} := by
      rw [← MonoidHom.coe_range, ← ker_realCliffordSpinOneOneSign, MonoidHom.coe_ker]
    rw [h]
    exact ((isClopen_discrete {1}).preimage
      continuous_realCliffordSpinOneOneSign).connectedComponent_subset (by simp)
  · -- They are the continuous image of the real line through `1`.
    rw [← Multiplicative.ofAdd.surjective.range_comp]
    exact (isPreconnected_range
      (isEmbedding_realCliffordSpinOneOneHyperbolicRotation.continuous.comp
        continuous_ofAdd)).subset_connectedComponent ⟨0, by simp⟩

/-- The identity component of `Spin(1, 1)`, as a subgroup, is the group of hyperbolic rotations. -/
theorem connectedComponentOfOne_realCliffordSpinGroup_one_one :
    Subgroup.connectedComponentOfOne (realCliffordSpinGroup 1 1) =
      realCliffordSpinOneOneHyperbolicRotation.range :=
  SetLike.coe_injective connectedComponent_one_realCliffordSpinGroup_one_one

/-- **`Spin(1, 1)` has two connected components**: its identity component has index two. -/
theorem index_connectedComponentOfOne_realCliffordSpinGroup_one_one :
    (Subgroup.connectedComponentOfOne (realCliffordSpinGroup 1 1)).index = 2 := by
  rw [connectedComponentOfOne_realCliffordSpinGroup_one_one, ← ker_realCliffordSpinOneOneSign,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr realCliffordSpinOneOneSign_surjective,
    Subgroup.card_top]
  exact card_rootsOfUnity_two two_ne_zero

end CliffordAlgebra
