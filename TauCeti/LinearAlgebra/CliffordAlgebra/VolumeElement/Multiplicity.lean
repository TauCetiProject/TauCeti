/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.RingTheory.Morita.ModuleEnd

/-!
# The two multiplicity spaces of an odd-dimensional Clifford module

For an oriented odd-dimensional Euclidean space with `Q v = -‖v‖²`, the normalized
complex volume `ω` is central and squares to one. Its two eigenspaces in any module `E`
are therefore Clifford submodules, rather than the half-spin subspaces of an
even-dimensional module. Their sum is an isomorphism of Clifford modules.

The even Clifford algebra acts on an odd-dimensional spinor space `S` as all of
`End S`. Applying Morita evaluation separately to the two volume submodules gives

`(S ⊗ Hom_even(S, E⁺)) × (S ⊗ Hom_even(S, E⁻)) ≃ E`.

This complex-linear decomposition also intertwines the even Clifford action. On its two
factors the central volume acts by `+1` and `-1`, respectively. Evaluation is literally
`(s ⊗ T, t ⊗ U) ↦ T s + U t`; the inverse first applies the central projections
`(1 ± ω)/2` and then the usual inverse Morita evaluation. Neither finite dimension
nor a topology on `E` is required. The odd-dimensional Fock module supplies the
hypothesis on `S`, including in dimension one: its even action is the algebra isomorphism
`TauCeti.SpinPolarizationData.evenCliffordEquivEnd`. The evaluation used here is
`TauCeti.isotypicTensorEquivOfBijective`, applied to each volume submodule.

## Main definitions

* `CliffordAlgebra.oddVolumeSubmodule`: a volume eigenspace as a Clifford submodule.
* `CliffordAlgebra.oddVolumeDecomposition`: the Clifford-linear sum of the two submodules.
* `CliffordAlgebra.oddVolumeMultiplicityEquiv`: evaluation from the two tensor products.

## Main results

* `CliffordAlgebra.complexVolume_smul_oddVolumeMultiplicityEquiv`: the volume labels of
  the two tensor factors are `+1` and `-1`.
* `CliffordAlgebra.map_oddVolumeMultiplicityEquiv`: naturality by postcomposition on
  the two multiplicity spaces.
* `CliffordAlgebra.finrank_eq_mul_add_finrank_oddVolumeMultiplicity`: the dimension is
  `dim S` times the sum of the two multiplicities.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* T. Y. Lam, *Lectures on Modules and Rings* (1999), Chapter 7, for Morita evaluation.
-/

public section

noncomputable section

open Module TauCeti
open scoped TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  (Q : QuadraticForm ℝ V) (o : Orientation ℝ V (Fin n)) (hn : Odd n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

/-- A volume eigenspace in odd dimension, with its full Clifford-module structure.
No definiteness hypothesis is needed for stability under the algebra action. -/
def oddVolumeSubmodule (μ : ℂ) : Submodule (CliffordAlgebra (Q.baseChange ℂ)) E where
  carrier := (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' a _ hx := smul_mem_eigenspace_complexVolume_of_odd o hn a hx

/-- Membership in a volume submodule is the volume eigenvector equation. -/
@[simp]
theorem mem_oddVolumeSubmodule (μ : ℂ) (x : E) :
    x ∈ oddVolumeSubmodule (E := E) Q o hn μ ↔ complexVolume Q o • x = μ • x :=
  Module.End.mem_eigenspace_iff

/-- Forgetting Clifford scalars recovers the ordinary complex volume eigenspace. -/
@[simp]
theorem oddVolumeSubmodule_restrictScalars (μ : ℂ) :
    (oddVolumeSubmodule (E := E) Q o hn μ).restrictScalars ℂ =
      (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ := (rfl)

/-- Reversing orientation interchanges the volume labels. -/
theorem oddVolumeSubmodule_neg_orientation (μ : ℂ) :
    oddVolumeSubmodule (E := E) Q (-o) hn μ = oddVolumeSubmodule (E := E) Q o hn (-μ) := by
  ext x
  simp only [mem_oddVolumeSubmodule, complexVolume_neg_orientation, neg_smul]
  exact neg_eq_iff_eq_neg

section Naturality

variable {F : Type*} [AddCommGroup F] [Module ℂ F]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F]

/-- A Clifford-module map restricts to each volume submodule, preserving its label. -/
def _root_.LinearMap.cliffordVolumeRestrict
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F) (μ : ℂ) :
    oddVolumeSubmodule (E := E) Q o hn μ →ₗ[CliffordAlgebra (Q.baseChange ℂ)]
      oddVolumeSubmodule (E := F) Q o hn μ :=
  g.restrict fun x hx ↦ by
    rw [mem_oddVolumeSubmodule] at hx ⊢
    rw [← g.map_smul, hx, LinearMap.map_smul_of_tower]

/-- The restricted map has the same value in the ambient module. -/
@[simp]
theorem _root_.LinearMap.coe_cliffordVolumeRestrict_apply
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F) (μ : ℂ)
    (x : oddVolumeSubmodule (E := E) Q o hn μ) :
    (g.cliffordVolumeRestrict Q o hn μ x : F) = g x := (rfl)

end Naturality

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ

/-- The volume submodules with labels `+1` and `-1` are complementary as Clifford modules. -/
theorem isCompl_oddVolumeSubmodule :
    IsCompl (oddVolumeSubmodule (E := E) Q o hn 1) (oddVolumeSubmodule (E := E) Q o hn (-1)) := by
  rw [← Submodule.isCompl_restrictScalars_iff ℂ]
  simpa only [oddVolumeSubmodule_restrictScalars] using isCompl_eigenspace_complexVolume o hQ

/-- The sum of the two volume submodules is a Clifford-linear isomorphism onto the module. -/
def oddVolumeDecomposition :
    (oddVolumeSubmodule (E := E) Q o hn 1 × oddVolumeSubmodule (E := E) Q o hn (-1)) ≃ₗ[
      CliffordAlgebra (Q.baseChange ℂ)] E :=
  Submodule.prodEquivOfIsCompl _ _ (isCompl_oddVolumeSubmodule (E := E) Q o hn hQ)

/-- The volume decomposition adds the two summands. -/
@[simp]
theorem oddVolumeDecomposition_apply
    (x : oddVolumeSubmodule (E := E) Q o hn 1 × oddVolumeSubmodule (E := E) Q o hn (-1)) :
    oddVolumeDecomposition Q o hn hQ x = (x.1 : E) + x.2 :=
  Submodule.coe_prodEquivOfIsCompl' _ _ _ x

private theorem oddVolumeDecomposition_symm_apply (x : E) :
    (oddVolumeDecomposition Q o hn hQ).symm x =
      (⟨halfOneAdd ℂ (complexVolume Q o) • x,
        halfOneAdd_smul_mem_eigenspace_complexVolume o hQ x⟩,
      ⟨halfOneAdd ℂ (-complexVolume Q o) • x,
        halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ x⟩) := by
  rw [LinearEquiv.symm_apply_eq, oddVolumeDecomposition_apply]
  exact (halfOneAdd_smul_add_halfOneAdd_neg_smul ℂ (complexVolume Q o) x).symm

/-- The positive component of the inverse is the central projection `(1 + ω)/2`. -/
@[simp]
theorem coe_oddVolumeDecomposition_symm_fst (x : E) :
    ((oddVolumeDecomposition Q o hn hQ).symm x).1.val =
      halfOneAdd ℂ (complexVolume Q o) • x := by
  rw [oddVolumeDecomposition_symm_apply]

/-- The negative component of the inverse is the central projection `(1 - ω)/2`. -/
@[simp]
theorem coe_oddVolumeDecomposition_symm_snd (x : E) :
    ((oddVolumeDecomposition Q o hn hQ).symm x).2.val =
      halfOneAdd ℂ (-complexVolume Q o) • x := by
  rw [oddVolumeDecomposition_symm_apply]

section Multiplicity

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (even (Q.baseChange ℂ)) S] [IsScalarTower ℂ (even (Q.baseChange ℂ)) S]
  [FiniteDimensional ℂ S]
  (hS : Function.Bijective (Algebra.lsmul ℂ ℂ S :
    even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

/-- Evaluation from the two volume-labelled multiplicity spaces of an arbitrary odd
Clifford module. It intertwines the even Clifford action, while the volume acts by
`+1` and `-1` on the two target summands. -/
def oddVolumeMultiplicityEquiv :
    ((S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1)) ×
      (S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1)))) ≃ₗ[ℂ] E := by
  -- Select the native left-factor scalar towers explicitly: inference through the even
  -- subalgebra and its two Hom spaces otherwise exceeds the typeclass search limit.
  letI : IsScalarTower ℂ (even (Q.baseChange ℂ))
      (S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1)) :=
    TensorProduct.isScalarTower_left
  letI : IsScalarTower ℂ (even (Q.baseChange ℂ))
      (S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :=
    TensorProduct.isScalarTower_left
  exact (((isotypicTensorEquivOfBijective hS).prodCongr
    (isotypicTensorEquivOfBijective hS)).trans
      ((oddVolumeDecomposition Q o hn hQ).restrictScalars
        (even (Q.baseChange ℂ)))).restrictScalars ℂ

/-- Evaluation on arbitrary tensors is the sum of the two ordinary Morita evaluations. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_apply
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    oddVolumeMultiplicityEquiv Q o hn hQ hS (x, y) =
      ↑(isotypicEval ℂ x) + ↑(isotypicEval ℂ y) := by
  simp [oddVolumeMultiplicityEquiv]

/-- The multiplicity equivalence intertwines the even Clifford action on the first
factor of each tensor product with the given action on the module. -/
theorem oddVolumeMultiplicityEquiv_smul (a : even (Q.baseChange ℂ))
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    oddVolumeMultiplicityEquiv Q o hn hQ hS (a • x, a • y) =
      a • oddVolumeMultiplicityEquiv Q o hn hQ hS (x, y) := by
  simp [smul_add]

/-- The central volume acts with opposite signs on the two multiplicity factors. -/
theorem complexVolume_smul_oddVolumeMultiplicityEquiv
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    complexVolume Q o • oddVolumeMultiplicityEquiv Q o hn hQ hS (x, y) =
      oddVolumeMultiplicityEquiv Q o hn hQ hS (x, -y) := by
  have hx := (mem_oddVolumeSubmodule (E := E) Q o hn 1 ↑(isotypicEval ℂ x)).mp
    (isotypicEval ℂ x).property
  have hy := (mem_oddVolumeSubmodule (E := E) Q o hn (-1) ↑(isotypicEval ℂ y)).mp
    (isotypicEval ℂ y).property
  simp [oddVolumeMultiplicityEquiv_apply, smul_add, hx, hy]

/-- The inverse first projects to the positive volume submodule, then applies inverse
Morita evaluation. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_symm_fst (x : E) :
    ((oddVolumeMultiplicityEquiv Q o hn hQ hS).symm x).1 =
      (isotypicTensorEquivOfBijective hS).symm
        ((oddVolumeDecomposition Q o hn hQ).symm x).1 := (rfl)

/-- The inverse first projects to the negative volume submodule, then applies inverse
Morita evaluation. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_symm_snd (x : E) :
    ((oddVolumeMultiplicityEquiv Q o hn hQ hS).symm x).2 =
      (isotypicTensorEquivOfBijective hS).symm
        ((oddVolumeDecomposition Q o hn hQ).symm x).2 := (rfl)

section Naturality

variable {F : Type*} [AddCommGroup F] [Module ℂ F]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F]

/-- A Clifford-module map acts on each multiplicity space by postcomposition, without
mixing the two volume labels. -/
theorem map_oddVolumeMultiplicityEquiv
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F)
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    g (oddVolumeMultiplicityEquiv Q o hn hQ hS (x, y)) =
      oddVolumeMultiplicityEquiv Q o hn hQ hS
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := even (Q.baseChange ℂ)) (M := S))
          (LinearMap.compRight ℂ ((g.cliffordVolumeRestrict Q o hn 1).restrictScalars
            (even (Q.baseChange ℂ)))) x,
        TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := even (Q.baseChange ℂ)) (M := S))
          (LinearMap.compRight ℂ ((g.cliffordVolumeRestrict Q o hn (-1)).restrictScalars
            (even (Q.baseChange ℂ)))) y) := by
  simp [oddVolumeMultiplicityEquiv_apply]

end Naturality

include hS in
/-- In finite dimension, the two volume-labelled multiplicities account for the whole
module dimension. A finite-dimensional hypothesis on `E` is needed for natural-number
`finrank`, which is zero on infinite-dimensional spaces. -/
theorem finrank_eq_mul_add_finrank_oddVolumeMultiplicity [FiniteDimensional ℂ E] :
    finrank ℂ E = finrank ℂ S *
      (finrank ℂ (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1) +
        finrank ℂ (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) := by
  have hfinite (μ : ℂ) : FiniteDimensional ℂ (oddVolumeSubmodule (E := E) Q o hn μ) :=
    Module.Finite.of_injective
      ((oddVolumeSubmodule (E := E) Q o hn μ).subtype.restrictScalars ℂ) Subtype.val_injective
  let := hfinite 1
  let := hfinite (-1)
  rw [← ((oddVolumeDecomposition (E := E) Q o hn hQ).restrictScalars ℂ).finrank_eq,
    Module.finrank_prod,
    finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
      (M := oddVolumeSubmodule (E := E) Q o hn 1) hS,
    finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
      (M := oddVolumeSubmodule (E := E) Q o hn (-1)) hS, mul_add]

end Multiplicity

end CliffordAlgebra
