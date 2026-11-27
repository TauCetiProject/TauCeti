/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.RingTheory.Morita.CentralIdempotent
-- Private: scalar-eigenvalue transport, center of `Module.End`, nondegeneracy of `-‖·‖²`,
-- simplicity of the Clifford algebra and its even subalgebra, odd-even algebra splitting,
-- zero-dimensional Clifford algebra equivalences, finite-dimensionality from surjective actions
-- onto endomorphism algebras, anticommuting eigenspace equivalences, and simple-semisimple module
-- generators are used only inside proofs and non-exposed definitions.
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import TauCeti.Algebra.Module.LinearMap.SMul
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even
import TauCeti.LinearAlgebra.CliffordAlgebra.OddSplitting
import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Eigenspace.Anticommute
import TauCeti.RingTheory.SimpleModule.Basic

/-!
# The two multiplicity spaces and two-factor evaluation of an odd-dimensional Clifford module

For an oriented odd-dimensional Euclidean space with `Q v = -‖v‖²`, the normalized
complex volume `ω` is central and squares to one. Its two eigenspaces in any module `E`
are therefore Clifford submodules (`CliffordAlgebra.oddVolumeSubmodule`), rather than the
half-spin subspaces of an even-dimensional module. Their sum is an isomorphism of Clifford
modules (`CliffordAlgebra.oddVolumeDecomposition`).

This file develops Morita evaluation in odd dimension at two levels:

1. **Over the even subalgebra**: the even Clifford algebra acts on a single odd-dimensional
   spinor space `S` as all of `End S`, giving the complex-linear decomposition
   `(S ⊗ Hom_even(S, E⁺)) × (S ⊗ Hom_even(S, E⁻)) ≃ₗ[ℂ] E`
   (`CliffordAlgebra.oddVolumeMultiplicityEquiv`).
2. **Over the full Clifford algebra (two-factor odd evaluation)**: for a nontrivial module `S`
   on which `CliffordAlgebra (Q.baseChange ℂ)` surjects onto `End_ℂ S`, necessarily
   `dim_ℂ S = 2 ^ ⌊n / 2⌋` (`CliffordAlgebra.finrank_eq_two_pow_of_surjective_lsmul`). When `ω`
   acts on `S` by a scalar `μ`, necessarily `μ = ±1` and `n = 0` or `n` is odd, the even subalgebra
   already acts bijectively on `S` (`CliffordAlgebra.bijective_lsmul_even_of_surjective_lsmul`),
   and in odd dimension single-factor evaluation `S ⊗ Hom_Cl(S, E) ≃ₗ[Cl] E^μ`
   (`CliffordAlgebra.oddVolumeFactorEquiv`) identifies the `μ`-labelled tensor product with the
   `μ`-volume submodule. Cross-labelled intertwiners `Hom_Cl(S_∓, E^±)` vanish, while matched
   intertwiners land in `E^±` (`CliffordAlgebra.apply_mem_oddVolumeSubmodule`) and restrict
   isomorphically to `Hom_even(S_±, E^±)` (`CliffordAlgebra.oddVolumeSubmoduleRestrictEvenEquiv`).
   Given nontrivial spinor factors `S_+` and `S_-` with labels `+1` and `-1`, the dimension `n` is
   forced to be odd, the combined action identifies the full Clifford algebra with
   `End_ℂ S_+ × End_ℂ S_-` (`CliffordAlgebra.bijective_lsmul_prod_of_complexVolume_smul`), and
   assembling both evaluations gives the full Clifford-module isomorphism

   `(S_+ ⊗ Hom_Cl(S_+, E)) × (S_- ⊗ Hom_Cl(S_-, E)) ≃ₗ[Cl] E`

   (`CliffordAlgebra.oddVolumeTwoFactorEquiv`). Neither finite dimension nor a topology on `E` is
   required. Reversing the orientation interchanges the two factors, and any invertible grading
   operator anticommuting with Clifford multiplication anticommutes with `ω` in odd dimension and
   therefore forces the two volume submodules and multiplicity spaces to have equal dimension.

## Main definitions

* `CliffordAlgebra.oddVolumeSubmodule`: a volume eigenspace as a Clifford submodule.
* `CliffordAlgebra.oddVolumeDecomposition`: the Clifford-linear sum of the two submodules.
* `CliffordAlgebra.oddVolumeMultiplicityEquiv`: even-subalgebra evaluation from the two tensor
  products.
* `CliffordAlgebra.oddVolumeSubmoduleRestrictEvenEquiv`: canonical identification
  `Hom_Cl(S, E^μ) ≃ₗ[ℂ] Hom_even(S, E^μ)` for `μ ≠ 0`.
* `CliffordAlgebra.oddVolumeFactorEquiv`: single-factor Clifford evaluation
  `S ⊗ Hom_Cl(S, E) ≃ₗ[Cl] E^μ`.
* `CliffordAlgebra.oddVolumeTwoFactorEquiv`: two-factor Clifford evaluation
  `(S_+ ⊗ Hom_Cl(S_+, E)) × (S_- ⊗ Hom_Cl(S_-, E)) ≃ₗ[Cl] E`.
* `CliffordAlgebra.oddVolumeSubmoduleEquivOfAnticommute`: the `ℂ`-linear equivalence
  `E^μ ≃ₗ[ℂ] E^{-μ}` induced by an invertible grading anticommuting with vectors in odd dimension.

## Main results

* `CliffordAlgebra.apply_mem_oddVolumeSubmodule`,
  `CliffordAlgebra.subsingleton_linearMap_of_complexVolume_smul_ne`, and
  `CliffordAlgebra.subsingleton_linearMap_oddVolumeSubmodule_of_ne`: matched intertwiners land in
  `E^μ` and cross-labelled intertwiners vanish for `μ ≠ ν`.
* `CliffordAlgebra.exists_complexVolume_smul_eq_of_surjective_lsmul`,
  `CliffordAlgebra.eq_zero_or_odd_of_complexVolume_smul`, and
  `CliffordAlgebra.odd_of_complexVolume_smul_eq_self_neg`: in odd dimension `ω` acts by a scalar
  on any module with surjective Clifford action; conversely, a scalar volume action on a nontrivial
  module forces `n = 0` or `n` odd, and opposite-sign nontrivial factors force `n` odd.
* `CliffordAlgebra.bijective_lsmul_even_of_surjective_lsmul` and
  `CliffordAlgebra.finrank_eq_two_pow_of_surjective_lsmul`: a spinor factor with scalar volume
  action restricts bijectively to `even (Q.baseChange ℂ)`, and every nontrivial module with
  surjective Clifford action onto `End_ℂ S` has dimension `2 ^ (n / 2)`.
* `CliffordAlgebra.bijective_lsmul_prod_of_complexVolume_smul`: opposite-sign spinor factors split
  `CliffordAlgebra (Q.baseChange ℂ)` onto `End_ℂ S_+ × End_ℂ S_-`.
* `CliffordAlgebra.finrank_oddVolumeSubmodule_eq_two_pow_mul_finrank_linearMap` and
  `CliffordAlgebra.finrank_eq_two_pow_mul_add_finrank_linearMap`: dimension formulas for the
  individual volume submodules and the ambient module.
* `CliffordAlgebra.apply_complexVolume_smul_of_odd` and
  `CliffordAlgebra.finrank_linearMap_eq_of_anticommute`: an invertible grading anticommutes with
  `ω` in odd dimension and equalizes spinor-factor multiplicities.

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

variable {Q}

/-- Membership in a volume submodule is the volume eigenvector equation. -/
@[simp]
theorem mem_oddVolumeSubmodule {o : Orientation ℝ V (Fin n)} {hn : Odd n} {μ : ℂ} {x : E} :
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
  g.restrict fun _ hx ↦ mem_oddVolumeSubmodule.mpr (g.smul_apply_of_smul_eq
    (mem_oddVolumeSubmodule.mp hx))

/-- The restricted map has the same value in the ambient module. -/
@[simp]
theorem _root_.LinearMap.coe_cliffordVolumeRestrict_apply
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F) (μ : ℂ)
    (x : oddVolumeSubmodule (E := E) Q o hn μ) :
    (g.cliffordVolumeRestrict o hn μ x : F) = g x := (rfl)

end Naturality

/-! ### Volume decomposition and even-subalgebra multiplicity spaces -/

section Decomposition

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
  Submodule.prodEquivOfIsCompl _ _ (isCompl_oddVolumeSubmodule (E := E) o hn hQ)

/-- The volume decomposition adds the two summands. -/
@[simp]
theorem oddVolumeDecomposition_apply
    (x : oddVolumeSubmodule (E := E) Q o hn 1 × oddVolumeSubmodule (E := E) Q o hn (-1)) :
    oddVolumeDecomposition o hn hQ x = (x.1 : E) + x.2 :=
  Submodule.coe_prodEquivOfIsCompl' _ _ _ x

private theorem oddVolumeDecomposition_symm_apply (x : E) :
    (oddVolumeDecomposition o hn hQ).symm x =
      (⟨halfOneAdd ℂ (complexVolume Q o) • x,
        halfOneAdd_smul_mem_eigenspace_complexVolume o hQ x⟩,
      ⟨halfOneAdd ℂ (-complexVolume Q o) • x,
        halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ x⟩) := by
  rw [LinearEquiv.symm_apply_eq, oddVolumeDecomposition_apply]
  exact (halfOneAdd_smul_add_halfOneAdd_neg_smul ℂ (complexVolume Q o) x).symm

/-- The positive component of the inverse is the central projection `(1 + ω)/2`. -/
@[simp]
theorem coe_oddVolumeDecomposition_symm_fst (x : E) :
    ((oddVolumeDecomposition o hn hQ).symm x).1.val =
      halfOneAdd ℂ (complexVolume Q o) • x := by
  rw [oddVolumeDecomposition_symm_apply]

/-- The negative component of the inverse is the central projection `(1 - ω)/2`. -/
@[simp]
theorem coe_oddVolumeDecomposition_symm_snd (x : E) :
    ((oddVolumeDecomposition o hn hQ).symm x).2.val =
      halfOneAdd ℂ (-complexVolume Q o) • x := by
  rw [oddVolumeDecomposition_symm_apply]

section Multiplicity

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (even (Q.baseChange ℂ)) S] [IsScalarTower ℂ (even (Q.baseChange ℂ)) S]
  (hS : Function.Bijective (Algebra.lsmul ℂ ℂ S :
    even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

/-- Evaluation from the two volume-labelled multiplicity spaces of an arbitrary odd
Clifford module. It intertwines the even Clifford action, while the volume acts by
`+1` and `-1` on the two target summands. -/
def oddVolumeMultiplicityEquiv :
    ((S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1)) ×
      (S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1)))) ≃ₗ[ℂ] E := by
  have := _root_.Module.Finite.of_surjective_end _ hS.2
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
      ((oddVolumeDecomposition o hn hQ).restrictScalars
        (even (Q.baseChange ℂ)))).restrictScalars ℂ

/-- Evaluation on arbitrary tensors is the sum of the two ordinary Morita evaluations. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_apply
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    oddVolumeMultiplicityEquiv o hn hQ hS (x, y) =
      ↑(isotypicEval ℂ x) + ↑(isotypicEval ℂ y) := by
  simp [oddVolumeMultiplicityEquiv]

/-- The multiplicity equivalence intertwines the even Clifford action on the first
factor of each tensor product with the given action on the module. -/
theorem oddVolumeMultiplicityEquiv_smul (a : even (Q.baseChange ℂ))
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    oddVolumeMultiplicityEquiv o hn hQ hS (a • x, a • y) =
      a • oddVolumeMultiplicityEquiv o hn hQ hS (x, y) := by
  simp [smul_add]

/-- The central volume acts with opposite signs on the two multiplicity factors. -/
theorem complexVolume_smul_oddVolumeMultiplicityEquiv
    (x : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn 1))
    (y : S ⊗[ℂ] (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn (-1))) :
    complexVolume Q o • oddVolumeMultiplicityEquiv o hn hQ hS (x, y) =
      oddVolumeMultiplicityEquiv o hn hQ hS (x, -y) := by
  have hx := mem_oddVolumeSubmodule.mp (isotypicEval ℂ x).property
  have hy := mem_oddVolumeSubmodule.mp (isotypicEval ℂ y).property
  simp [oddVolumeMultiplicityEquiv_apply, smul_add, hx, hy]

/-- The inverse first projects to the positive volume submodule, then applies inverse
Morita evaluation. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_symm_fst [FiniteDimensional ℂ S] (x : E) :
    ((oddVolumeMultiplicityEquiv o hn hQ hS).symm x).1 =
      (isotypicTensorEquivOfBijective hS).symm
        ((oddVolumeDecomposition o hn hQ).symm x).1 := (rfl)

/-- The inverse first projects to the negative volume submodule, then applies inverse
Morita evaluation. -/
@[simp]
theorem oddVolumeMultiplicityEquiv_symm_snd [FiniteDimensional ℂ S] (x : E) :
    ((oddVolumeMultiplicityEquiv o hn hQ hS).symm x).2 =
      (isotypicTensorEquivOfBijective hS).symm
        ((oddVolumeDecomposition o hn hQ).symm x).2 := (rfl)

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
    g (oddVolumeMultiplicityEquiv o hn hQ hS (x, y)) =
      oddVolumeMultiplicityEquiv o hn hQ hS
        (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := even (Q.baseChange ℂ)) (M := S))
          (LinearMap.compRight ℂ ((g.cliffordVolumeRestrict o hn 1).restrictScalars
            (even (Q.baseChange ℂ)))) x,
        TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := even (Q.baseChange ℂ)) (M := S))
          (LinearMap.compRight ℂ ((g.cliffordVolumeRestrict o hn (-1)).restrictScalars
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
  have := _root_.Module.Finite.of_surjective_end _ hS.2
  have hfinite (μ : ℂ) : FiniteDimensional ℂ (oddVolumeSubmodule (E := E) Q o hn μ) :=
    Module.Finite.of_injective
      ((oddVolumeSubmodule (E := E) Q o hn μ).subtype.restrictScalars ℂ) Subtype.val_injective
  have := hfinite 1
  have := hfinite (-1)
  rw [← ((oddVolumeDecomposition (E := E) o hn hQ).restrictScalars ℂ).finrank_eq,
    Module.finrank_prod,
    finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
      (M := oddVolumeSubmodule (E := E) Q o hn 1) hS,
    finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul
      (M := oddVolumeSubmodule (E := E) Q o hn (-1)) hS, mul_add]

end Multiplicity

end Decomposition

/-! ### Intertwiners over the full Clifford algebra -/

section Intertwiners

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]

/-- If `ω` acts on `S` by `μ`, every Clifford-linear map out of `S` lands in the `μ`-volume
submodule. -/
theorem apply_mem_oddVolumeSubmodule {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (f : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) (s : S) :
    f s ∈ oddVolumeSubmodule (E := E) Q o hn μ :=
  mem_oddVolumeSubmodule.mpr (f.smul_apply_of_smul_eq (hω s))

/-- **Cross-eigenvalue vanishing for the complex volume.** In any dimension and for any quadratic
form `Q`, if `complexVolume Q o` acts on `S` by `μ` and on `E` by `ν` with `μ ≠ ν`, every
Clifford-linear map `S →ₗ[Cℓ] E` is zero. -/
theorem subsingleton_linearMap_of_complexVolume_smul_ne {μ ν : ℂ}
    (hωS : ∀ s : S, complexVolume Q o • s = μ • s)
    (hωE : ∀ x : E, complexVolume Q o • x = ν • x) (hne : μ ≠ ν) :
    Subsingleton (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) :=
  subsingleton_linearMap_of_smul_eq_of_ne (z := complexVolume Q o) hωS hωE hne

/-- **Cross-labelled intertwiners vanish**: if `ω` acts on `S` by `μ` and `μ ≠ ν`, there is no
nonzero Clifford-linear map from `S` into `oddVolumeSubmodule Q o hn ν`. -/
theorem subsingleton_linearMap_oddVolumeSubmodule_of_ne {μ ν : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) (hne : μ ≠ ν) :
    Subsingleton
      (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn ν) :=
  subsingleton_linearMap_of_complexVolume_smul_ne o hω
    (fun x ↦ Subtype.ext (mem_oddVolumeSubmodule.mp x.property)) hne

end Intertwiners

/-! ### Scalar volume eigenvalues and restriction of intertwiners to the even subalgebra -/

section ScalarVolume

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]

/-- On any nontrivial module, if `complexVolume Q o` squares to `1` and acts by a scalar
`ω • s = μ • s`, then `μ = 1` or `μ = -1`. -/
theorem eq_one_or_eq_neg_one_of_complexVolume_smul_of_mul_self_eq_one [Nontrivial S]
    (hsq : complexVolume Q o * complexVolume Q o = 1) {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    μ = 1 ∨ μ = -1 := by
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  refine mul_self_eq_one_iff.mp (smul_left_injective ℂ hs ?_)
  dsimp only
  rw [one_smul, mul_smul, ← hω, ← hω, ← mul_smul, hsq, one_smul]

/-- On any nontrivial module with `Q v = -‖v‖²`, a scalar volume action `ω • s = μ • s` satisfies
`μ = 1` or `μ = -1`. -/
theorem eq_one_or_eq_neg_one_of_complexVolume_smul [Nontrivial S]
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    μ = 1 ∨ μ = -1 :=
  eq_one_or_eq_neg_one_of_complexVolume_smul_of_mul_self_eq_one o (complexVolume_mul_self o hQ) hω

end ScalarVolume

section RestrictEven

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]

include hn

private theorem complexVolume_mem_evenOdd_one :
    complexVolume Q o ∈ evenOdd (Q.baseChange ℂ) 1 := by
  refine involute_eq_neg_iff.1 ?_
  rw [involute_complexVolume, hn.neg_one_pow, neg_one_smul]

private theorem complexVolume_mul_ι_mem_even (w : ℂ ⊗[ℝ] V) :
    complexVolume Q o * ι (Q.baseChange ℂ) w ∈ even (Q.baseChange ℂ) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule, ← h11]
  exact SetLike.mul_mem_graded (complexVolume_mem_evenOdd_one o hn) (ι_mem_evenOdd_one _ w)

private theorem oddVolumeSubmodule_map_smul_of_even {μ : ℂ} (hμ : μ ≠ 0)
    (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (g : S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn μ)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) :
    g (a • s) = a • g s := by
  induction a using CliffordAlgebra.induction generalizing s with
  | algebraMap c =>
    simp [Algebra.algebraMap_eq_smul_one, smul_assoc]
  | ι w =>
    have hcomm := complexVolume_mul_ι_of_odd (Q := Q) o hn w
    let u : even (Q.baseChange ℂ) :=
      ⟨complexVolume Q o * ι (Q.baseChange ℂ) w, complexVolume_mul_ι_mem_even o hn w⟩
    apply Subtype.ext
    apply smul_right_injective E hμ
    calc
      μ • (g (ι (Q.baseChange ℂ) w • s) : E) =
          (g (μ • (ι (Q.baseChange ℂ) w • s)) : E) := by
        rw [g.map_smul_of_tower μ, Submodule.coe_smul_of_tower]
      _ = (g (u • s) : E) := by
        congr 1
        rw [Subalgebra.smul_def]
        dsimp only [u]
        rw [hcomm, mul_smul, hω, smul_comm]
      _ = (complexVolume Q o * ι (Q.baseChange ℂ) w) • (g s : E) := by
        rw [g.map_smul, Submodule.coe_smul_of_tower, Subalgebra.smul_def]
      _ = μ • (ι (Q.baseChange ℂ) w • (g s : E)) := by
        rw [hcomm, mul_smul, mem_oddVolumeSubmodule.mp (g s).property, smul_comm]
  | mul a b ha hb => rw [mul_smul, ha, hb, mul_smul]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]

/-- When `μ ≠ 0` and `ω` acts on `S` by `μ`, restricting scalars from the full Clifford algebra to
`even (Q.baseChange ℂ)` is a linear equivalence on intertwiners into `E^μ`: any `even`-linear map
already commutes with odd generators because `ω · c(w)` is even and `ω` acts by the same nonzero
scalar `μ` on source and target. -/
def oddVolumeSubmoduleRestrictEvenEquiv {μ : ℂ} (hμ : μ ≠ 0)
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn μ) ≃ₗ[ℂ]
      (S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn μ) where
  toFun f := f.restrictScalars (even (Q.baseChange ℂ))
  invFun g :=
    { toFun := g
      map_add' := g.map_add
      map_smul' a s := by
        rw [RingHom.id_apply]
        exact oddVolumeSubmodule_map_smul_of_even o hn hμ hω g a s }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Applying `oddVolumeSubmoduleRestrictEvenEquiv` restricts scalars to `even (Q.baseChange ℂ)`. -/
@[simp]
theorem oddVolumeSubmoduleRestrictEvenEquiv_apply {μ : ℂ} (hμ : μ ≠ 0)
    (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (f : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn μ) :
    oddVolumeSubmoduleRestrictEvenEquiv o hn hμ hω f =
      f.restrictScalars (even (Q.baseChange ℂ)) :=
  (rfl)

/-- Coercing the inverse of `oddVolumeSubmoduleRestrictEvenEquiv` to `E` applies the underlying map.
-/
@[simp]
theorem coe_oddVolumeSubmoduleRestrictEvenEquiv_symm_apply {μ : ℂ} (hμ : μ ≠ 0)
    (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (g : S →ₗ[even (Q.baseChange ℂ)] oddVolumeSubmodule (E := E) Q o hn μ) (s : S) :
    ((oddVolumeSubmoduleRestrictEvenEquiv o hn hμ hω).symm g s : E) = g s :=
  (rfl)

end RestrictEven

/-! ### Single-factor evaluation over the full Clifford algebra -/

section SingleFactor

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]

private theorem smul_complexVolume_smul_eq_self {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) M]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) M]
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) {x : M} (hx : complexVolume Q o • x = μ • x) :
    (μ • complexVolume Q o) • x = x := by
  rw [smul_assoc, hx, smul_smul, mul_self_eq_one_iff.mpr hμ, one_smul]

private theorem halfOneAdd_smul_complexVolume_smul_eq {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) M]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) M]
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) {x : M} (hx : complexVolume Q o • x = μ • x) :
    halfOneAdd ℂ (μ • complexVolume Q o) • x = x := by
  rw [halfOneAdd_def, smul_assoc, add_smul, one_smul, smul_complexVolume_smul_eq_self o hμ hx,
    ← two_smul ℂ x, invOf_smul_smul]

private theorem halfOneAdd_neg_smul_complexVolume_smul_eq {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) M]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) M]
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) {x : M} (hx : complexVolume Q o • x = μ • x) :
    halfOneAdd ℂ (-(μ • complexVolume Q o)) • x = 0 := by
  rw [halfOneAdd_def, smul_assoc, add_smul, one_smul, neg_smul,
    smul_complexVolume_smul_eq_self o hμ hx, add_neg_cancel, smul_zero]

private theorem halfOneAdd_complexVolume_mem_center (hn : Odd n) {μ : ℂ} :
    halfOneAdd ℂ (μ • complexVolume Q o) ∈ Set.center (CliffordAlgebra (Q.baseChange ℂ)) :=
  Semigroup.mem_center_iff.mpr fun a ↦
    (commute_halfOneAdd ℂ
      ((Commute.symm
        (Subalgebra.mem_center_iff.mp (complexVolume_mem_center o hn) a)).smul_left μ)).symm

/-- **Central volume acts by a scalar on a spinor factor.** In odd dimension, if
`CliffordAlgebra (Q.baseChange ℂ)` surjects onto `Module.End ℂ S`, then `complexVolume Q o` acts
on `S` by a scalar `μ : ℂ`. -/
theorem exists_complexVolume_smul_eq_of_surjective_lsmul (hn : Odd n)
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)) :
    ∃ μ : ℂ, ∀ s : S, complexVolume Q o • s = μ • s := by
  obtain ⟨μ, _, hμ⟩ := Module.End.mem_center_iff.mp
    (Set.image_center_subset hsurj ⟨complexVolume Q o,
      Semigroup.mem_center_iff.mpr
        (Subalgebra.mem_center_iff.mp (complexVolume_mem_center (Q := Q) o hn)),
      rfl⟩)
  exact ⟨μ, fun s ↦ LinearMap.congr_fun hμ s⟩

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ

omit [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S] in
private theorem ne_zero_of_complexVolume_smul [Nontrivial S] {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) : μ ≠ 0 := by
  rcases eq_one_or_eq_neg_one_of_complexVolume_smul o hQ hω with rfl | rfl <;> norm_num

private theorem smul_complexVolume_mul_self {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    (μ • complexVolume Q o) * (μ • complexVolume Q o) = 1 := by
  rw [smul_mul_smul_comm, mul_self_eq_one_iff.mpr hμ, complexVolume_mul_self o hQ, one_smul]

include hn in
private theorem isSimpleRing_even_baseChange :
    IsSimpleRing ↥(even (Q.baseChange ℂ)) := by
  refine TauCeti.CliffordAlgebra.isSimpleRing_even_of_odd_finrank
    (QuadraticForm.Nondegenerate.baseChange (A := ℂ)
      (QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ)) ?_
  rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  exact hn

private theorem bijective_lsmul_of_surjective_lsmul_of_even [Nontrivial S]
    (heven : Even (finrank ℝ V))
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)) :
    Function.Bijective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) := by
  have : IsSimpleRing (CliffordAlgebra (Q.baseChange ℂ)) :=
    isSimpleRing_of_even_finrank
      (QuadraticForm.Nondegenerate.baseChange (A := ℂ)
        (QuadraticForm.nondegenerate_of_eq_neg_norm_sq hQ))
      (by rw [Module.finrank_baseChange]; exact heven)
  exact ⟨(Algebra.lsmul ℂ ℂ S :
    CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S).toRingHom.injective, hsurj⟩

private theorem exists_sign_complexVolume_smul_eq_of_surjective_lsmul [Nontrivial S]
    (hodd : Odd (finrank ℝ V))
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)) :
    letI : Fact (finrank ℝ V = finrank ℝ V) := ⟨rfl⟩
    ∃ μ : ℂ, (μ = 1 ∨ μ = -1) ∧
      ∀ s : S, complexVolume Q (stdOrthonormalBasis ℝ V).toBasis.orientation • s = μ • s := by
  let : Fact (finrank ℝ V = finrank ℝ V) := ⟨rfl⟩
  obtain ⟨μ, hω⟩ := exists_complexVolume_smul_eq_of_surjective_lsmul
    (stdOrthonormalBasis ℝ V).toBasis.orientation hodd hsurj
  exact ⟨μ, eq_one_or_eq_neg_one_of_complexVolume_smul _ hQ hω, hω⟩

/-- **A scalar volume action forces dimension zero or odd.** Under `Q v = -‖v‖²`, if
`complexVolume Q o` acts by a scalar on a nontrivial `CliffordAlgebra (Q.baseChange ℂ)`-module `S`,
then `n = 0` or `Odd n` (in positive even dimension, vectors anticommute with `ω` and would have to
annihilate `S`, contradicting nondegeneracy). -/
theorem eq_zero_or_odd_of_complexVolume_smul [Nontrivial S] {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    n = 0 ∨ Odd n := by
  rcases Nat.even_or_odd n with heven | hodd
  · left
    by_contra hn0
    have hpos : 0 < finrank ℝ V := by
      rw [Fact.out (p := finrank ℝ V = n)]
      exact Nat.pos_of_ne_zero hn0
    have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    have hne : μ ≠ -μ := by
      rcases eq_one_or_eq_neg_one_of_complexVolume_smul o hQ hω with rfl | rfl <;> norm_num
    set c : CliffordAlgebra (Q.baseChange ℂ) := ι (Q.baseChange ℂ) (1 ⊗ₜ v)
    have hcs : c • s = 0 := by
      have hneg : c • s ∈ (Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace (-μ) :=
        ι_smul_mem_eigenspace_complexVolume_neg o heven (1 ⊗ₜ v) (by simpa using hω s)
      have hpos' : c • s ∈ (Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace μ := by
        simpa using hω (c • s)
      exact Submodule.disjoint_def.mp
        ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).disjoint_genEigenspace hne 1 1)
        (c • s) hpos' hneg
    have hsq : c * c = algebraMap ℂ (CliffordAlgebra (Q.baseChange ℂ)) (-(‖v‖ ^ 2 : ℂ)) := by
      simp [c, ι_sq_scalar, QuadraticForm.baseChange_tmul, hQ]
    have hnorm : (-(‖v‖ ^ 2 : ℂ)) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)))
    have h0 : (-(‖v‖ ^ 2 : ℂ)) • s = 0 := by
      rw [← algebraMap_smul (CliffordAlgebra (Q.baseChange ℂ)), ← hsq, mul_smul, hcs, smul_zero]
    exact hs ((smul_eq_zero.mp h0).resolve_left hnorm)
  · exact Or.inr hodd

private def oddSpinorSplitEquiv {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ]
      (↥(even (Q.baseChange ℂ)) × ↥(even (Q.baseChange ℂ))) :=
  have hcomm (x : ↥(even (Q.baseChange ℂ))) :
      Commute (μ • complexVolume Q o) (x : CliffordAlgebra (Q.baseChange ℂ)) :=
    (Commute.symm
      (Subalgebra.mem_center_iff.mp (complexVolume_mem_center o hn)
        (x : CliffordAlgebra (Q.baseChange ℂ)))).smul_left μ
  have hodd : μ • complexVolume Q o ∈ evenOdd (Q.baseChange ℂ) 1 :=
    Submodule.smul_mem _ μ (complexVolume_mem_evenOdd_one o hn)
  equivEvenProd (Q.baseChange ℂ) (μ • complexVolume Q o) hcomm hodd
    (smul_complexVolume_mul_self o hQ hμ)

private theorem coe_oddSpinorSplitEquiv_apply_fst {μ : ℂ} (hμ : μ = 1 ∨ μ = -1)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    ((oddSpinorSplitEquiv o hn hQ hμ a).1 : CliffordAlgebra (Q.baseChange ℂ)) =
      halfOneAdd ℂ (μ • complexVolume Q o) * a +
        halfOneAdd ℂ (-(μ • complexVolume Q o)) * involute a :=
  coe_equivEvenProd_apply_fst (Q.baseChange ℂ) (μ • complexVolume Q o) _ _ _ a

private theorem coe_oddSpinorSplitEquiv_apply_snd {μ : ℂ} (hμ : μ = 1 ∨ μ = -1)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    ((oddSpinorSplitEquiv o hn hQ hμ a).2 : CliffordAlgebra (Q.baseChange ℂ)) =
      halfOneAdd ℂ (-(μ • complexVolume Q o)) * a +
        halfOneAdd ℂ (μ • complexVolume Q o) * involute a :=
  coe_equivEvenProd_apply_snd (Q.baseChange ℂ) (μ • complexVolume Q o) _ _ _ a

private theorem eq_halfOneAdd_mul_oddSpinorSplitEquiv {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    a = halfOneAdd ℂ (μ • complexVolume Q o) *
        ((oddSpinorSplitEquiv o hn hQ hμ a).1 : CliffordAlgebra (Q.baseChange ℂ)) +
      halfOneAdd ℂ (-(μ • complexVolume Q o)) *
        ((oddSpinorSplitEquiv o hn hQ hμ a).2 : CliffordAlgebra (Q.baseChange ℂ)) := by
  conv_lhs => rw [← (oddSpinorSplitEquiv o hn hQ hμ).symm_apply_apply a]
  exact equivEvenProd_symm_apply (Q.baseChange ℂ) (μ • complexVolume Q o) _ _ _ _

private theorem lsmul_oddSpinorSplitEquiv_fst {μ : ℂ} (hμ : μ = 1 ∨ μ = -1)
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    Algebra.lsmul ℂ ℂ S ((oddSpinorSplitEquiv o hn hQ hμ a).1 :
        CliffordAlgebra (Q.baseChange ℂ)) =
      Algebra.lsmul ℂ ℂ S a := by
  ext s
  conv_rhs => rw [eq_halfOneAdd_mul_oddSpinorSplitEquiv o hn hQ hμ a]
  simp only [Algebra.lsmul_coe, add_smul, mul_smul]
  rw [halfOneAdd_smul_complexVolume_smul_eq o hμ (hω _),
    halfOneAdd_neg_smul_complexVolume_smul_eq o hμ (hω _), add_zero]

private theorem halfOneAdd_mul_oddSpinorSplitEquiv_fst {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1) (a : CliffordAlgebra (Q.baseChange ℂ)) :
    halfOneAdd ℂ (μ • complexVolume Q o) *
        ((oddSpinorSplitEquiv o hn hQ hμ a).1 : CliffordAlgebra (Q.baseChange ℂ)) =
      halfOneAdd ℂ (μ • complexVolume Q o) * a := by
  have hsq := smul_complexVolume_mul_self o hQ hμ
  conv_rhs => rw [eq_halfOneAdd_mul_oddSpinorSplitEquiv o hn hQ hμ a]
  rw [mul_add, ← mul_assoc, (isIdempotentElem_halfOneAdd ℂ hsq).eq, ← mul_assoc,
    halfOneAdd_mul_halfOneAdd_neg ℂ hsq, zero_mul, add_zero]

/-- **A spinor factor with scalar volume action restricts bijectively to the even subalgebra.** If
`Cℓ` surjects onto `End_ℂ S` for a nontrivial `S` and `ω` acts on `S` by a scalar `μ` (which forces
`n = 0` or `n` odd), then `even (Q.baseChange ℂ)` acts on `S` by an algebra isomorphism onto
`End_ℂ S`. -/
theorem bijective_lsmul_even_of_surjective_lsmul [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    Function.Bijective
      (Algebra.lsmul ℂ ℂ S : even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) := by
  rcases eq_zero_or_odd_of_complexVolume_smul o hQ hω with rfl | hn
  · have : Subsingleton V := finrank_zero_iff.mp (Fact.out (p := finrank ℝ V = 0))
    have htop : even (Q.baseChange ℂ) = ⊤ := even_eq_top_of_subsingleton (Q.baseChange ℂ)
    have hbij := bijective_lsmul_of_surjective_lsmul_of_even hQ
      (by rw [Fact.out (p := finrank ℝ V = 0)]; exact Even.zero) hsurj
    refine ⟨hbij.1.comp Subtype.val_injective, fun f ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hsurj f
    exact ⟨⟨a, htop ▸ Algebra.mem_top⟩, LinearMap.ext fun s ↦ Subalgebra.smul_def _ s⟩
  · have := isSimpleRing_even_baseChange hn hQ
    have hμ := eq_one_or_eq_neg_one_of_complexVolume_smul o hQ hω
    refine ⟨(Algebra.lsmul ℂ ℂ S : even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S).toRingHom.injective,
      fun f ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hsurj f
    exact ⟨(oddSpinorSplitEquiv o hn hQ hμ a).1, lsmul_oddSpinorSplitEquiv_fst o hn hQ hμ hω a⟩

/-- **Dimension of a spinor factor.** Every nontrivial module `S` onto whose endomorphisms the
complexified Clifford algebra of `Q v = -‖v‖²` surjects has complex dimension
`2 ^ (finrank ℝ V / 2)`. -/
theorem finrank_eq_two_pow_of_surjective_lsmul [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)) :
    finrank ℂ S = 2 ^ (finrank ℝ V / 2) := by
  rcases Nat.even_or_odd (finrank ℝ V) with heven | hodd
  · rw [finrank_eq_two_pow_of_bijective _
      (bijective_lsmul_of_surjective_lsmul_of_even hQ heven hsurj), Module.finrank_baseChange]
  · obtain ⟨μ, -, hω⟩ := exists_sign_complexVolume_smul_eq_of_surjective_lsmul hQ hodd hsurj
    have : Fact (finrank ℝ V = finrank ℝ V) := ⟨rfl⟩
    have := _root_.Module.Finite.of_surjective_end _ hsurj
    have hbij := bijective_lsmul_even_of_surjective_lsmul _ hQ hsurj hω
    have heq := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
    rw [finrank_even, Module.finrank_baseChange, Module.finrank_linearMap] at heq
    have hpow : 2 ^ (finrank ℝ V - 1) = 2 ^ (finrank ℝ V / 2) * 2 ^ (finrank ℝ V / 2) := by
      rw [← pow_add]
      congr 1
      obtain ⟨l, hl⟩ := hodd
      omega
    exact Nat.mul_self_inj.mp (heq.symm.trans hpow)

private theorem fixedSubmodule_smulLeft_eq_oddVolumeSubmodule {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1)
    (hc : halfOneAdd ℂ (μ • complexVolume Q o) ∈
      Set.center (CliffordAlgebra (Q.baseChange ℂ))) :
    (Module.End.smulLeft (M := E) (halfOneAdd ℂ (μ • complexVolume Q o)) hc).fixedSubmodule =
      oddVolumeSubmodule (E := E) Q o hn μ := by
  ext x
  rw [LinearMap.mem_fixedSubmodule_iff, Module.End.smulLeft_apply, mem_oddVolumeSubmodule]
  constructor
  · intro hx
    have hvx : (μ • complexVolume Q o) • x = x := by
      rw [← hx, ← mul_smul, mul_halfOneAdd ℂ (smul_complexVolume_mul_self o hQ hμ)]
    rcases hμ with rfl | rfl
    · simpa using hvx
    · rw [neg_one_smul, neg_smul] at hvx
      rw [neg_one_smul]
      exact neg_eq_iff_eq_neg.mp hvx
  · exact halfOneAdd_smul_complexVolume_smul_eq o hμ

include hn in
private theorem halfOneAdd_complexVolume_mul_eq [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (a b : CliffordAlgebra (Q.baseChange ℂ))
    (hab : Algebra.lsmul ℂ ℂ S a = Algebra.lsmul ℂ ℂ S b) :
    halfOneAdd ℂ (μ • complexVolume Q o) * a = halfOneAdd ℂ (μ • complexVolume Q o) * b := by
  have hμ := eq_one_or_eq_neg_one_of_complexVolume_smul o hQ hω
  have hbij := bijective_lsmul_even_of_surjective_lsmul o hQ hsurj hω
  have hfst : (oddSpinorSplitEquiv o hn hQ hμ a).1 = (oddSpinorSplitEquiv o hn hQ hμ b).1 :=
    hbij.1 <| (lsmul_oddSpinorSplitEquiv_fst o hn hQ hμ hω a).trans <|
      hab.trans (lsmul_oddSpinorSplitEquiv_fst o hn hQ hμ hω b).symm
  rw [← halfOneAdd_mul_oddSpinorSplitEquiv_fst o hn hQ hμ a,
    ← halfOneAdd_mul_oddSpinorSplitEquiv_fst o hn hQ hμ b, hfst]

/-- **Exact range of single-factor odd evaluation.** For any nontrivial Clifford module `S` on
which `ω` acts by `μ`, the image of `S ⊗[ℂ] Hom_Cl(S, E) →ₗ[Cℓ] E` is the `μ`-volume submodule
`oddVolumeSubmodule Q o hn μ`. -/
theorem range_isotypicEval_eq_oddVolumeSubmodule [Nontrivial S] {μ : ℂ}
    (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    LinearMap.range (isotypicEval ℂ (A := CliffordAlgebra (Q.baseChange ℂ)) (S := S) (M := E)) =
      oddVolumeSubmodule (E := E) Q o hn μ := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul s f =>
      rw [isotypicEval_tmul]
      exact apply_mem_oddVolumeSubmodule o hn hω f s
    | add _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  · have hμ := ne_zero_of_complexVolume_smul o hQ hω
    let R := even (Q.baseChange ℂ)
    have : IsSimpleRing R := isSimpleRing_even_baseChange hn hQ
    have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
    have : IsSemisimpleRing R := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
    obtain ⟨k, φ, s, hsum⟩ := TauCeti.Module.IsGenerator.exists_sum_eq_one (R := R) (M := S)
    let g (i : Fin k) : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E :=
      (oddVolumeSubmodule (E := E) Q o hn μ).subtype.comp
        ((oddVolumeSubmoduleRestrictEvenEquiv o hn hμ hω).symm ((φ i).smulRight ⟨x, hx⟩))
    refine ⟨∑ i, s i ⊗ₜ g i, ?_⟩
    have hcoe : (∑ i, ((φ i (s i) : R) : CliffordAlgebra (Q.baseChange ℂ))) = 1 := by
      simpa using congrArg R.val hsum
    simp [g, Subalgebra.smul_def, ← Finset.sum_smul, hcoe]

/-- **Single-factor odd Clifford evaluation.** Evaluation `s ⊗ T ↦ T s` is a Clifford-module
isomorphism from `S ⊗[ℂ] Hom_Cl(S, E)` onto the matching volume submodule `E^μ`. -/
def oddVolumeFactorEquiv [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) ≃ₗ[CliffordAlgebra (Q.baseChange ℂ)]
      oddVolumeSubmodule (E := E) Q o hn μ :=
  have := _root_.Module.Finite.of_surjective_end _ hsurj
  have hμ := eq_one_or_eq_neg_one_of_complexVolume_smul o hQ hω
  (isotypicTensorEquivOfCentral (halfOneAdd_complexVolume_mem_center o hn)
      (fun s ↦ halfOneAdd_smul_complexVolume_smul_eq o hμ (hω s)) hsurj
      (halfOneAdd_complexVolume_mul_eq o hn hQ hsurj hω)).trans
    (LinearEquiv.ofEq _ _ (fixedSubmodule_smulLeft_eq_oddVolumeSubmodule o hn hQ hμ _))

/-- Coercing `oddVolumeFactorEquiv` to `E` recovers `isotypicEval ℂ`. -/
@[simp]
theorem coe_oddVolumeFactorEquiv_apply [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (x : S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    (oddVolumeFactorEquiv o hn hQ hsurj hω x : E) = isotypicEval ℂ x := by
  simp [oddVolumeFactorEquiv]

/-- Naturality of the inverse of `oddVolumeFactorEquiv` along any Clifford-linear map
`g : E →ₗ[Cℓ] F`. -/
@[simp]
theorem oddVolumeFactorEquiv_symm_apply_map {F : Type*} [AddCommGroup F] [Module ℂ F]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F] [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s)
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F)
    (x : oddVolumeSubmodule (E := E) Q o hn μ) :
    (oddVolumeFactorEquiv (E := F) o hn hQ hsurj hω).symm
        (g.cliffordVolumeRestrict o hn μ x) =
      TensorProduct.AlgebraTensorModule.map
        (LinearMap.id (R := CliffordAlgebra (Q.baseChange ℂ)) (M := S))
        (LinearMap.compRight (M := S) ℂ g)
        ((oddVolumeFactorEquiv (E := E) o hn hQ hsurj hω).symm x) := by
  apply (oddVolumeFactorEquiv (E := F) o hn hQ hsurj hω).injective
  apply Subtype.ext
  rw [LinearEquiv.apply_symm_apply, coe_oddVolumeFactorEquiv_apply, isotypicEval_map_apply,
    ← coe_oddVolumeFactorEquiv_apply o hn hQ hsurj hω, LinearEquiv.apply_symm_apply,
    LinearMap.coe_cliffordVolumeRestrict_apply]

/-- **Dimension of a volume submodule in odd dimension.** Given a nontrivial odd spinor factor `S`
of label `μ`, the `μ`-volume submodule of any Clifford module `E` has dimension
`2 ^ (n / 2) · dim Hom_Cl(S, E)`. -/
theorem finrank_oddVolumeSubmodule_eq_two_pow_mul_finrank_linearMap [Nontrivial S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    {μ : ℂ} (hω : ∀ s : S, complexVolume Q o • s = μ • s) :
    finrank ℂ (oddVolumeSubmodule (E := E) Q o hn μ) =
      2 ^ (n / 2) * finrank ℂ (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
  rw [← ((oddVolumeFactorEquiv (E := E) o hn hQ hsurj hω).restrictScalars ℂ).finrank_eq,
    Module.finrank_tensorProduct, finrank_eq_two_pow_of_surjective_lsmul hQ hsurj,
    Fact.out (p := finrank ℝ V = n)]

end SingleFactor

/-! ### Two-factor odd evaluation over the full Clifford algebra -/

private theorem complexVolume_smul_eq_one_smul {S : Type*} [AddCommGroup S] [Module ℂ S]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
    (hω : ∀ s : S, complexVolume Q o • s = s) (s : S) :
    complexVolume Q o • s = (1 : ℂ) • s :=
  (hω s).trans (one_smul ℂ s).symm

private theorem complexVolume_smul_eq_neg_one_smul {S : Type*} [AddCommGroup S] [Module ℂ S]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
    (hω : ∀ s : S, complexVolume Q o • s = -s) (s : S) :
    complexVolume Q o • s = (-1 : ℂ) • s :=
  (hω s).trans (neg_one_smul ℂ s).symm

/-- **Opposite-sign volume modules force odd dimension.** Under `Q v = -‖v‖²`, if
`complexVolume Q o` acts as `+1` on a nontrivial module `S₁` and as `-1` on a nontrivial module
`S₂`, then `n` is odd (dimension zero is ruled out because the zero-dimensional Clifford algebra
is `ℂ`, where `ω` is a single scalar). -/
theorem odd_of_complexVolume_smul_eq_self_neg (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {S₁ S₂ : Type*}
    [AddCommGroup S₁] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₁] [Nontrivial S₁]
    [AddCommGroup S₂] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₂] [Nontrivial S₂]
    (hω₁ : ∀ s : S₁, complexVolume Q o • s = s)
    (hω₂ : ∀ s : S₂, complexVolume Q o • s = -s) :
    Odd n := by
  let : Module ℂ S₁ := Module.compHom S₁ (algebraMap ℂ (CliffordAlgebra (Q.baseChange ℂ)))
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₁ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module ℂ S₂ := Module.compHom S₂ (algebraMap ℂ (CliffordAlgebra (Q.baseChange ℂ)))
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₂ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rcases eq_zero_or_odd_of_complexVolume_smul o hQ (complexVolume_smul_eq_one_smul o hω₁) with
    rfl | hn
  · have : Subsingleton V := finrank_zero_iff.mp (Fact.out (p := finrank ℝ V = 0))
    let c : ℂ := equivOfSubsingleton (Q.baseChange ℂ) (complexVolume Q o)
    have hc : complexVolume Q o = algebraMap ℂ (CliffordAlgebra (Q.baseChange ℂ)) c := by
      rw [← equivOfSubsingleton_symm_apply (Q.baseChange ℂ),
        (equivOfSubsingleton (Q.baseChange ℂ)).symm_apply_apply]
    obtain ⟨s₁, hs₁⟩ := exists_ne (0 : S₁)
    obtain ⟨s₂, hs₂⟩ := exists_ne (0 : S₂)
    have hc1 : c = 1 := smul_left_injective ℂ hs₁ (by
      dsimp only
      rw [← algebraMap_smul (CliffordAlgebra (Q.baseChange ℂ)), ← hc, hω₁, one_smul])
    have hc2 : c = -1 := smul_left_injective ℂ hs₂ (by
      dsimp only
      rw [← algebraMap_smul (CliffordAlgebra (Q.baseChange ℂ)), ← hc, hω₂, neg_one_smul])
    norm_num [hc1] at hc2
  · exact hn

section TwoFactor

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  {S₁ S₂ : Type*}
  [AddCommGroup S₁] [Module ℂ S₁] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₁]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₁] [Nontrivial S₁]
  [AddCommGroup S₂] [Module ℂ S₂] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₂]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₂] [Nontrivial S₂]
  (hsurj₁ : Function.Surjective
    (Algebra.lsmul ℂ ℂ S₁ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₁))
  (hsurj₂ : Function.Surjective
    (Algebra.lsmul ℂ ℂ S₂ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₂))
  (hω₁ : ∀ s : S₁, complexVolume Q o • s = s)
  (hω₂ : ∀ s : S₂, complexVolume Q o • s = -s)

include hQ hsurj₁ hsurj₂ hω₁ hω₂ in
/-- **Two opposite-sign spinor factors split the Clifford algebra.** When `ω` acts by `+1` on
`S₁` and by `-1` on `S₂` (which forces `n` to be odd), the combined action
`Cℓ →ₐ[ℂ] End_ℂ S₁ × End_ℂ S₂` is bijective. -/
theorem bijective_lsmul_prod_of_complexVolume_smul :
    Function.Bijective
      ((Algebra.lsmul ℂ ℂ S₁).prod (Algebra.lsmul ℂ ℂ S₂) :
        CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₁ × Module.End ℂ S₂) := by
  have hn := odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂
  have hω₁' := complexVolume_smul_eq_one_smul o hω₁
  have hω₂' := complexVolume_smul_eq_neg_one_smul o hω₂
  have hbij₁ := bijective_lsmul_even_of_surjective_lsmul o hQ hsurj₁ hω₁'
  have hbij₂ := bijective_lsmul_even_of_surjective_lsmul o hQ hsurj₂ hω₂'
  let split := oddSpinorSplitEquiv o hn hQ (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  have hprod : ((Algebra.lsmul ℂ ℂ S₁).prod (Algebra.lsmul ℂ ℂ S₂) :
        CliffordAlgebra (Q.baseChange ℂ) → Module.End ℂ S₁ × Module.End ℂ S₂) =
      (Prod.map (Algebra.lsmul ℂ ℂ S₁ : even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₁)
        (Algebra.lsmul ℂ ℂ S₂ : even (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₂)) ∘ split := by
    ext a : 1
    refine Prod.ext ?_ ?_
    · exact (lsmul_oddSpinorSplitEquiv_fst o hn hQ (Or.inl rfl) hω₁' a).symm
    · have hsnd : ((split a).2 : CliffordAlgebra (Q.baseChange ℂ)) =
          ((oddSpinorSplitEquiv o hn hQ (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) a).1 :
            CliffordAlgebra (Q.baseChange ℂ)) := by
        dsimp only [split]
        rw [coe_oddSpinorSplitEquiv_apply_snd, coe_oddSpinorSplitEquiv_apply_fst, one_smul,
          neg_one_smul, neg_neg]
      exact ((congrArg (Algebra.lsmul ℂ ℂ S₂) hsnd).trans
        (lsmul_oddSpinorSplitEquiv_fst o hn hQ (Or.inr rfl) hω₂' a)).symm
  rw [hprod]
  exact (hbij₁.prodMap hbij₂).comp split.bijective

/-- **Two-factor odd Clifford evaluation.** Given nontrivial spinor factors `S₁` and `S₂` with
volume eigenvalues `+1` and `-1` (which forces `n` to be odd), every Clifford module `E` decomposes
canonically as a `CliffordAlgebra (Q.baseChange ℂ)`-module via
`(S₁ ⊗[ℂ] Hom_Cl(S₁, E)) × (S₂ ⊗[ℂ] Hom_Cl(S₂, E)) ≃ₗ[Cℓ] E`, `(s₁ ⊗ T₁, s₂ ⊗ T₂) ↦ T₁ s₁ + T₂ s₂`.
-/
def oddVolumeTwoFactorEquiv :
    ((S₁ ⊗[ℂ] (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) ×
      (S₂ ⊗[ℂ] (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E))) ≃ₗ[
        CliffordAlgebra (Q.baseChange ℂ)] E :=
  have := _root_.Module.Finite.of_surjective_end _ hsurj₁
  have := _root_.Module.Finite.of_surjective_end _ hsurj₂
  isotypicProdTensorEquivOfBijective
    (bijective_lsmul_prod_of_complexVolume_smul o hQ hsurj₁ hsurj₂ hω₁ hω₂)

/-- Applying `oddVolumeTwoFactorEquiv` sums the two single-factor evaluations. -/
@[simp]
theorem oddVolumeTwoFactorEquiv_apply
    (x : S₁ ⊗[ℂ] (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E))
    (y : S₂ ⊗[ℂ] (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂ (x, y) =
      isotypicEval ℂ x + isotypicEval ℂ y := by
  simp [oddVolumeTwoFactorEquiv]

-- Public theorem types cannot reference `private` helpers under `module`, so the three public
-- inverse signatures spell out the `Prop` conversions as direct `Eq.trans` terms.
/-- The inverse of `oddVolumeTwoFactorEquiv` projects onto `E⁺` and applies the inverse of
`oddVolumeFactorEquiv` on the first factor, and similarly onto `E⁻` on the second factor. -/
theorem oddVolumeTwoFactorEquiv_symm_apply (m : E) :
    (oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm m =
      ((oddVolumeFactorEquiv o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂) hQ hsurj₁
          (fun s ↦ (hω₁ s).trans (one_smul ℂ s).symm)).symm
          ((oddVolumeDecomposition o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂)
              hQ).symm m).1,
       (oddVolumeFactorEquiv o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂) hQ hsurj₂
          (fun s ↦ (hω₂ s).trans (neg_one_smul ℂ s).symm)).symm
          ((oddVolumeDecomposition o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂)
              hQ).symm m).2) := by
  have hn := odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂
  apply (oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).injective
  rw [LinearEquiv.apply_symm_apply, oddVolumeTwoFactorEquiv_apply,
    ← coe_oddVolumeFactorEquiv_apply o hn hQ hsurj₁ (complexVolume_smul_eq_one_smul o hω₁),
    ← coe_oddVolumeFactorEquiv_apply o hn hQ hsurj₂ (complexVolume_smul_eq_neg_one_smul o hω₂),
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    ← oddVolumeDecomposition_apply o hn hQ, LinearEquiv.apply_symm_apply]

/-- First component of the inverse of `oddVolumeTwoFactorEquiv`: project to `E⁺` and apply the
inverse of `oddVolumeFactorEquiv`. -/
@[simp]
theorem oddVolumeTwoFactorEquiv_symm_fst (m : E) :
    ((oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm m).1 =
      (oddVolumeFactorEquiv o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂) hQ hsurj₁
          (fun s ↦ (hω₁ s).trans (one_smul ℂ s).symm)).symm
        ((oddVolumeDecomposition o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂)
            hQ).symm m).1 :=
  congrArg Prod.fst (oddVolumeTwoFactorEquiv_symm_apply o hQ hsurj₁ hsurj₂ hω₁ hω₂ m)

/-- Second component of the inverse of `oddVolumeTwoFactorEquiv`: project to `E⁻` and apply the
inverse of `oddVolumeFactorEquiv`. -/
@[simp]
theorem oddVolumeTwoFactorEquiv_symm_snd (m : E) :
    ((oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm m).2 =
      (oddVolumeFactorEquiv o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂) hQ hsurj₂
          (fun s ↦ (hω₂ s).trans (neg_one_smul ℂ s).symm)).symm
        ((oddVolumeDecomposition o (odd_of_complexVolume_smul_eq_self_neg o hQ hω₁ hω₂)
            hQ).symm m).2 :=
  congrArg Prod.snd (oddVolumeTwoFactorEquiv_symm_apply o hQ hsurj₁ hsurj₂ hω₁ hω₂ m)

/-- Naturality of `oddVolumeTwoFactorEquiv` under any Clifford-linear map `g : E →ₗ[Cℓ] F`. -/
theorem map_oddVolumeTwoFactorEquiv {F : Type*} [AddCommGroup F] [Module ℂ F]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F]
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F)
    (x : S₁ ⊗[ℂ] (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E))
    (y : S₂ ⊗[ℂ] (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    g (oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂ (x, y)) =
      oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂
        (TensorProduct.AlgebraTensorModule.map
            (LinearMap.id (R := CliffordAlgebra (Q.baseChange ℂ)) (M := S₁))
            (LinearMap.compRight (M := S₁) ℂ g) x,
         TensorProduct.AlgebraTensorModule.map
            (LinearMap.id (R := CliffordAlgebra (Q.baseChange ℂ)) (M := S₂))
            (LinearMap.compRight (M := S₂) ℂ g) y) := by
  simp [isotypicEval_map_apply]

/-- Naturality of the inverse of `oddVolumeTwoFactorEquiv` along any Clifford-linear map
`g : E →ₗ[Cℓ] F`. -/
@[simp]
theorem oddVolumeTwoFactorEquiv_symm_apply_map {F : Type*} [AddCommGroup F] [Module ℂ F]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F]
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F) (m : E) :
    (oddVolumeTwoFactorEquiv (E := F) o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm (g m) =
      (TensorProduct.AlgebraTensorModule.map
          (LinearMap.id (R := CliffordAlgebra (Q.baseChange ℂ)) (M := S₁))
          (LinearMap.compRight (M := S₁) ℂ g)
          ((oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm m).1,
       TensorProduct.AlgebraTensorModule.map
          (LinearMap.id (R := CliffordAlgebra (Q.baseChange ℂ)) (M := S₂))
          (LinearMap.compRight (M := S₂) ℂ g)
          ((oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂).symm m).2) := by
  simp [oddVolumeTwoFactorEquiv]

/-- Reversing the orientation interchanges the `+1` and `-1` spinor factors in
`oddVolumeTwoFactorEquiv`. -/
theorem oddVolumeTwoFactorEquiv_neg_orientation
    (x : S₁ ⊗[ℂ] (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E))
    (y : S₂ ⊗[ℂ] (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    oddVolumeTwoFactorEquiv (-o) hQ hsurj₂ hsurj₁
        (fun s ↦ by rw [complexVolume_neg_orientation, neg_smul, hω₂, neg_neg])
        (fun s ↦ by rw [complexVolume_neg_orientation, neg_smul, hω₁]) (y, x) =
      oddVolumeTwoFactorEquiv o hQ hsurj₁ hsurj₂ hω₁ hω₂ (x, y) := by
  simp [add_comm]

include hQ hsurj₁ hsurj₂ hω₁ hω₂ in
/-- **Dimension formula for a finite-dimensional odd Clifford module.** Given nontrivial spinor
factors `S₁` and `S₂` with volume eigenvalues `+1` and `-1` (which forces `n` to be odd), every
finite-dimensional module `E` has dimension
`2 ^ (n / 2) · (dim Hom_Cl(S₁, E) + dim Hom_Cl(S₂, E))`. -/
theorem finrank_eq_two_pow_mul_add_finrank_linearMap [FiniteDimensional ℂ E] :
    finrank ℂ E = 2 ^ (n / 2) *
      (finrank ℂ (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) +
        finrank ℂ (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) := by
  have := _root_.Module.Finite.of_surjective_end _ hsurj₁
  have := _root_.Module.Finite.of_surjective_end _ hsurj₂
  rw [finrank_eq_add_finrank_mul_finrank_linearMap_of_bijective_prod
      (bijective_lsmul_prod_of_complexVolume_smul o hQ hsurj₁ hsurj₂ hω₁ hω₂),
    finrank_eq_two_pow_of_surjective_lsmul hQ hsurj₁,
    finrank_eq_two_pow_of_surjective_lsmul hQ hsurj₂, Fact.out (p := finrank ℝ V = n), mul_add]

end TwoFactor

/-! ### Grading operators in odd dimension -/

section OddGrading

include hn in
/-- **In odd dimension a grading anticommutes with `ω`** (in contrast to
`CliffordAlgebra.apply_complexVolume_smul` in even dimension): an endomorphism `γ` anticommuting
with Clifford multiplication by every vector satisfies `γ (ω • ψ) = -(ω • γ ψ)`. -/
theorem apply_complexVolume_smul_of_odd {γ : E →ₗ[ℂ] E}
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))
    (ψ : E) :
    γ (complexVolume Q o • ψ) = -(complexVolume Q o • γ ψ) := by
  rw [apply_smul_eq_involute_smul hγ, involute_complexVolume, hn.neg_one_pow, neg_one_smul,
    neg_smul]

include hn in
private theorem lsmul_complexVolume_anticommute_of_odd {γ : E →ₗ[ℂ] E}
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ)) :
    Algebra.lsmul ℂ ℂ E (complexVolume Q o) * γ +
      γ * Algebra.lsmul ℂ ℂ E (complexVolume Q o) = 0 := by
  ext ψ
  simp only [LinearMap.add_apply, mul_apply_eq_comp, Algebra.lsmul_coe, LinearMap.zero_apply]
  rw [apply_complexVolume_smul_of_odd o hn hγ, add_neg_cancel]

/-- An invertible grading operator `γ : E ≃ₗ[ℂ] E` anticommuting with Clifford multiplication in
odd dimension exchanges the `μ`- and `-μ`-volume submodules as `ℂ`-vector spaces. -/
def oddVolumeSubmoduleEquivOfAnticommute (γ : E ≃ₗ[ℂ] E)
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))
    (μ : ℂ) :
    oddVolumeSubmodule (E := E) Q o hn μ ≃ₗ[ℂ] oddVolumeSubmodule (E := E) Q o hn (-μ) :=
  Module.End.genEigenspaceEquivOfAnticommute γ
    (lsmul_complexVolume_anticommute_of_odd o hn hγ) μ 1

/-- Coercing `oddVolumeSubmoduleEquivOfAnticommute` to `E` applies `γ`. -/
@[simp]
theorem coe_oddVolumeSubmoduleEquivOfAnticommute_apply (γ : E ≃ₗ[ℂ] E)
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))
    (μ : ℂ) (x : oddVolumeSubmodule (E := E) Q o hn μ) :
    (oddVolumeSubmoduleEquivOfAnticommute o hn γ hγ μ x : E) = γ x :=
  Module.End.coe_genEigenspaceEquivOfAnticommute_apply γ _ μ 1 x

/-- Coercing `(oddVolumeSubmoduleEquivOfAnticommute ...).symm` to `E` applies `γ.symm`. -/
@[simp]
theorem coe_oddVolumeSubmoduleEquivOfAnticommute_symm_apply (γ : E ≃ₗ[ℂ] E)
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))
    (μ : ℂ) (x : oddVolumeSubmodule (E := E) Q o hn (-μ)) :
    ((oddVolumeSubmoduleEquivOfAnticommute o hn γ hγ μ).symm x : E) = γ.symm x :=
  Module.End.coe_genEigenspaceEquivOfAnticommute_symm_apply γ _ μ 1 x

/-- An invertible grading operator in odd dimension forces `E^{-μ}` and `E^μ` to have equal
dimension. -/
theorem finrank_oddVolumeSubmodule_neg_of_anticommute (γ : E ≃ₗ[ℂ] E)
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ))
    (μ : ℂ) :
    finrank ℂ (oddVolumeSubmodule (E := E) Q o hn (-μ)) =
      finrank ℂ (oddVolumeSubmodule (E := E) Q o hn μ) :=
  (oddVolumeSubmoduleEquivOfAnticommute o hn γ hγ μ).symm.finrank_eq

/-- **A graded Clifford module has equal spinor-factor multiplicities.** For `Q v = -‖v‖²`, any two
nontrivial spinor factors `S₁, S₂` onto whose endomorphisms `CliffordAlgebra (Q.baseChange ℂ)`
surjects have equal multiplicity in any module `E` carrying an invertible grading operator
anticommuting with Clifford multiplication by vectors (in particular, no ungraded odd irreducible
factor carries such a grading). -/
theorem finrank_linearMap_eq_of_anticommute (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {S₁ S₂ : Type*}
    [AddCommGroup S₁] [Module ℂ S₁] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₁]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₁] [Nontrivial S₁]
    [AddCommGroup S₂] [Module ℂ S₂] [Module (CliffordAlgebra (Q.baseChange ℂ)) S₂]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S₂] [Nontrivial S₂]
    (hsurj₁ : Function.Surjective
      (Algebra.lsmul ℂ ℂ S₁ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₁))
    (hsurj₂ : Function.Surjective
      (Algebra.lsmul ℂ ℂ S₂ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₂))
    (γ : E ≃ₗ[ℂ] E)
    (hγ : ∀ w (ψ : E), γ (ι (Q.baseChange ℂ) w • ψ) = -(ι (Q.baseChange ℂ) w • γ ψ)) :
    finrank ℂ (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) =
      finrank ℂ (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
  apply Nat.mul_left_cancel (Nat.two_pow_pos (finrank ℝ V / 2))
  rcases Nat.even_or_odd (finrank ℝ V) with heven | hodd
  · have := _root_.Module.Finite.of_surjective_end _ hsurj₁
    have := _root_.Module.Finite.of_surjective_end _ hsurj₂
    have hbij₁ := bijective_lsmul_of_surjective_lsmul_of_even hQ heven hsurj₁
    have hbij₂ := bijective_lsmul_of_surjective_lsmul_of_even hQ heven hsurj₂
    calc
      2 ^ (finrank ℝ V / 2) * finrank ℂ (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)
          = finrank ℂ S₁ * finrank ℂ (S₁ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
        rw [finrank_eq_two_pow_of_surjective_lsmul hQ hsurj₁]
      _ = finrank ℂ E :=
        (finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul (M := E) hbij₁).symm
      _ = finrank ℂ S₂ * finrank ℂ (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) :=
        finrank_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul (M := E) hbij₂
      _ = 2 ^ (finrank ℝ V / 2) * finrank ℂ (S₂ →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
        rw [finrank_eq_two_pow_of_surjective_lsmul hQ hsurj₂]
  · obtain ⟨μ₁, hμ₁, hω₁⟩ := exists_sign_complexVolume_smul_eq_of_surjective_lsmul hQ hodd hsurj₁
    obtain ⟨μ₂, hμ₂, hω₂⟩ := exists_sign_complexVolume_smul_eq_of_surjective_lsmul hQ hodd hsurj₂
    have : Fact (finrank ℝ V = finrank ℝ V) := ⟨rfl⟩
    rw [← finrank_oddVolumeSubmodule_eq_two_pow_mul_finrank_linearMap (E := E) _ hodd hQ hsurj₁
        hω₁,
      ← finrank_oddVolumeSubmodule_eq_two_pow_mul_finrank_linearMap (E := E) _ hodd hQ hsurj₂
        hω₂]
    rcases hμ₁ with rfl | rfl <;> rcases hμ₂ with rfl | rfl
    · rfl
    · exact (finrank_oddVolumeSubmodule_neg_of_anticommute _ hodd γ hγ 1).symm
    · exact finrank_oddVolumeSubmodule_neg_of_anticommute _ hodd γ hγ 1
    · rfl

end OddGrading

end CliffordAlgebra
