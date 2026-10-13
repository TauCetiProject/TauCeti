/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacePermutation.Archimedean
public import TauCeti.NumberTheory.NumberField.Units.LogEmbedding
import TauCeti.Algebra.Module.ZLattice.BaseChange
import TauCeti.RepresentationTheory.Homological.TateCohomology.Lattice

/-!
# The Herbrand quotient of the global units

Let `L/K` be a cyclic extension of number fields with Galois group `G`. The unit group `(𝓞 L)ˣ`,
with its Galois action, is an integral representation of `G`, and its Herbrand quotient is

```text
h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / [L : K] = 2^r / [L : K],
```

where `ℤ[S_∞(L)]` is the permutation lattice on the infinite places of `L` and `r` is the number of
infinite places of `K` ramified in `L` (`TauCeti.ClassFieldTheory.herbrandQuotient_units_eq_div`,
`TauCeti.ClassFieldTheory.herbrandQuotient_units`).

The proof is Dirichlet's unit theorem read equivariantly. The logarithmic embedding has finite
kernel, the roots of unity, and its image, the unit lattice, is a full lattice in the real space
`logSpace L`; the Galois group acts on that space by permuting the coordinates of the sum-zero
hyperplane of `ℝ^{S_∞(L)}` (`TauCeti.NumberField.Units.logSpaceRep`). The sum-zero sublattice of
`ℤ[S_∞(L)]` is a second Galois-stable lattice in the same representation: reading off the
coordinates away from the distinguished place `w₀` identifies it with `ℤ^{S_∞(L) ∖ {w₀}}`. By
Tate's lattice lemma (`TauCeti.TateCohomology.herbrandQuotient_eq_of_isBaseChange`) the two
lattices have the same Herbrand quotient, and that of the sum-zero lattice is
`h(ℤ[S_∞(L)]) / |G|`
(`TauCeti.TateCohomology.herbrandQuotient_augmentationSubrepresentation_eq_div`).

Together with the finite-place permutation lattices this is the unit part of the Herbrand quotient
of the `S`-units, through which the Herbrand quotient of the idele classes of a cyclic extension,
and so the first fundamental inequality, is computed.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_units_eq_div_card`:
  `h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / |Aut(L/K)|`, for `Aut(L/K)` cyclic.
* `TauCeti.ClassFieldTheory.herbrandQuotient_units_eq_div`: `h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / [L : K]`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_units`: `h((𝓞 L)ˣ) = 2^r / [L : K]`, with `r` the
  number of infinite places of `K` ramified in `L`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3 (the Herbrand quotient of the unit group).
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII, §6.
-/

public noncomputable section

open CategoryTheory Limits NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem TauCeti.NumberField.Units

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

/-! ### The sum-zero lattice on the infinite places in `logSpace L` -/

section Augmentation

variable (K L)

/-- The integral sum-zero permutation lattice on the infinite places of `L`. -/
private abbrev augmentationLattice : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.of (augmentationSubrepresentation ℤ (L ≃ₐ[K] L) (InfinitePlace L)).toRepresentation

variable {K L}

/-- The coefficients of a vector of the sum-zero lattice sum to zero. -/
private theorem sum_coeff_augmentationLattice (v : augmentationLattice K L) :
    ∑ w, (v : MonoidAlgebra ℤ (InfinitePlace L)).coeff w = 0 := by
  simpa [Finsupp.sum_fintype] using
    (mem_augmentationSubrepresentation_iff (G := L ≃ₐ[K] L)).1 v.2

variable (K L)

open Classical in
/-- A sum-zero vector of `ℤ[S_∞(L)]` is determined by its coordinates away from `w₀`, and these
can be arbitrary. -/
private def augmentationCoordEquiv :
    augmentationLattice K L ≃ₗ[ℤ] ({w : InfinitePlace L // w ≠ w₀} → ℤ) :=
  LinearEquiv.ofBijective
    (LinearMap.funLeft ℤ ℤ Subtype.val ∘ₗ Finsupp.lcoeFun ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap ∘ₗ
      (augmentationSubrepresentation ℤ (L ≃ₐ[K] L) (InfinitePlace L)).toSubmodule.subtype) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun v hv ↦ ?_, fun y ↦ ?_⟩
    · have hv' (w : InfinitePlace L) (hw : w ≠ w₀) :
          (v : MonoidAlgebra ℤ (InfinitePlace L)).coeff w = 0 := by
        simpa using congrFun hv ⟨w, hw⟩
      have h₀ := sum_coeff_augmentationLattice v
      rw [Fintype.sum_eq_single w₀ hv'] at h₀
      refine Subtype.ext (MonoidAlgebra.coeff_injective (Finsupp.ext fun w ↦ ?_))
      by_cases hw : w = w₀
      · simpa [hw] using h₀
      · simpa using hv' w hw
    -- extend `y` to `w₀` by minus the sum of its coordinates
    · let f : InfinitePlace L → ℤ := fun w ↦ if h : w = w₀ then -∑ i, y i else y ⟨w, h⟩
      have hf : ∑ w, f w = 0 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀,
          Fintype.sum_congr _ _ fun w : {w // w ≠ w₀} ↦ (by simp [f, w.2] : f w = y w)]
        simp [f]
      refine ⟨⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm f), ?_⟩, funext fun w ↦ ?_⟩
      · simpa [Finsupp.sum_fintype] using hf
      · simp [f, w.2]

variable {K L}

private theorem augmentationCoordEquiv_apply (v : augmentationLattice K L)
    (w : {w : InfinitePlace L // w ≠ w₀}) :
    augmentationCoordEquiv K L v w = (v : MonoidAlgebra ℤ (InfinitePlace L)).coeff w.1 := by
  simp only [augmentationCoordEquiv]
  rfl

variable (K L) in
open Classical in
/-- The sum-zero lattice of `ℤ[S_∞(L)]` in `logSpace L`, by its coordinates away from `w₀`. -/
private def augmentationToLogSpace : augmentationLattice K L →ₗ[ℤ] logSpace L :=
  Fintype.linearCombination ℤ (Pi.basisFun ℝ {w : InfinitePlace L // w ≠ w₀}) ∘ₗ
    (augmentationCoordEquiv K L).toLinearMap

private theorem augmentationToLogSpace_apply (v : augmentationLattice K L)
    (w : {w : InfinitePlace L // w ≠ w₀}) :
    augmentationToLogSpace K L v w = (v : MonoidAlgebra ℤ (InfinitePlace L)).coeff w.1 := by
  classical
  simp only [augmentationToLogSpace, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Fintype.linearCombination_apply, Finset.sum_apply]
  simpa [Pi.single_apply] using augmentationCoordEquiv_apply v w

/-- The sum-zero lattice of `ℤ[S_∞(L)]` spans `logSpace L` over `ℝ` as a lattice. -/
private theorem isBaseChange_augmentationToLogSpace :
    IsBaseChange ℝ (augmentationToLogSpace K L) := by
  classical
  exact (IsBaseChange.of_fintype_basis ℤ (Pi.basisFun ℝ _)).comp_equiv (augmentationCoordEquiv K L)

/-- The embedding of the sum-zero lattice in `logSpace L` is Galois-equivariant. -/
private theorem augmentationToLogSpace_rho (σ : L ≃ₐ[K] L) (v : augmentationLattice K L) :
    augmentationToLogSpace K L ((augmentationLattice K L).ρ σ v) =
      logSpaceRep K L σ (augmentationToLogSpace K L v) := by
  have hext : logSpaceExtend L (augmentationToLogSpace K L v) =
      fun t ↦ ((v : MonoidAlgebra ℤ (InfinitePlace L)).coeff t : ℝ) := by
    have hv : augmentationToLogSpace K L v = fun w : {w : InfinitePlace L // w ≠ w₀} ↦
        ((v : MonoidAlgebra ℤ (InfinitePlace L)).coeff w.1 : ℝ) :=
      funext (augmentationToLogSpace_apply v)
    rw [hv]
    exact logSpaceExtend_eq_self
      (f := fun t ↦ ((v : MonoidAlgebra ℤ (InfinitePlace L)).coeff t : ℝ))
      (by exact_mod_cast sum_coeff_augmentationLattice v)
  funext w
  rw [logSpaceRep_apply, hext, augmentationToLogSpace_apply]
  simp [Subrepresentation.toRepresentation_apply]

end Augmentation

/-! ### The unit lattice -/

section UnitLattice

variable (K L)

/-- The unit lattice of `L` as an integral representation of `Aut(L/K)`. -/
private abbrev unitLatticeRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.of (unitLatticeSubrep K L).toRepresentation

private theorem logEmbedding_mem_unitLatticeSubrep (x : Additive (𝓞 L)ˣ) :
    logEmbedding L x ∈ (unitLatticeSubrep K L).toSubmodule := by
  rw [toSubmodule_unitLatticeSubrep]
  exact ⟨x, trivial, rfl⟩

/-- The logarithmic embedding onto the unit lattice, as a morphism of representations. -/
private def unitsToUnitLattice :
    Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ ⟶ unitLatticeRep K L :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((logEmbedding L).toIntLinearMap.codRestrict (unitLatticeSubrep K L).toSubmodule
      (logEmbedding_mem_unitLatticeSubrep K L)) fun σ x ↦
    -- in `logSpace L`, the two sides are `logEmbedding` of `σ • x` and `logSpaceRep K L σ` of
    -- `logEmbedding` of `x`: `codRestrict` and the restricted action have these underlying maps
    Subtype.ext <| (logEmbedding_smul σ x).trans
      (Representation.restrictScalarsInt_apply _ _ _).symm

variable {K L}

private theorem coe_unitsToUnitLattice_hom_apply (x : Additive (𝓞 L)ˣ) :
    ((unitsToUnitLattice K L).hom x : logSpace L) = logEmbedding L x :=
  (rfl)

/-- The logarithmic embedding maps the units onto the unit lattice. -/
private instance : Epi (unitsToUnitLattice K L) := (Rep.epi_iff_surjective _).2 fun y ↦ by
  have hy : (y : logSpace L) ∈ unitLattice L := by
    rw [← toSubmodule_unitLatticeSubrep (K := K)]
    exact y.2
  obtain ⟨x, -, hx⟩ := hy
  exact ⟨x, Subtype.ext <| (coe_unitsToUnitLattice_hom_apply x).trans hx⟩

/-- The kernel of the logarithmic embedding, the roots of unity, is finite. -/
private theorem finite_kernel_unitsToUnitLattice : Finite ↑(kernel (unitsToUnitLattice K L)) := by
  have : Finite (LinearMap.ker
      ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map (unitsToUnitLattice K L)).hom) := by
    have hker (x : LinearMap.ker
        ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map (unitsToUnitLattice K L)).hom) :
        Additive.toMul (α := (𝓞 L)ˣ) x.1 ∈ torsion L := by
      rw [← logEmbedding_eq_zero_iff, ← coe_unitsToUnitLattice_hom_apply (K := K)]
      exact congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
    exact Finite.of_injective
      (fun x ↦ (⟨Additive.toMul (α := (𝓞 L)ˣ) x.1, hker x⟩ : torsion L))
      fun x y hxy ↦ by
        have h : Additive.toMul (α := (𝓞 L)ˣ) x.1 = Additive.toMul (α := (𝓞 L)ˣ) y.1 :=
          congrArg (fun z : torsion L ↦ (z : (𝓞 L)ˣ)) hxy
        exact Subtype.ext h
  -- the kernel is computed in `ModuleCat ℤ`, as the kernel of the underlying linear map
  exact Finite.of_equiv _ (PreservesKernel.iso (forget₂ _ (ModuleCat ℤ)) (unitsToUnitLattice K L) ≪≫
    ModuleCat.kernelIsoKer _).toLinearEquiv.toEquiv.symm

end UnitLattice

/-! ### The Herbrand quotient -/

variable [NumberField K] [IsCyclic (L ≃ₐ[K] L)]

/-- The units and the sum-zero lattice on the infinite places have the same Herbrand quotient. -/
private theorem herbrandQuotient_units_eq_herbrandQuotient_augmentationLattice :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) =
      TateCohomology.herbrandQuotient (augmentationLattice K L) := by
  -- the logarithmic embedding maps the units onto the unit lattice, with finite kernel
  have := finite_kernel_unitsToUnitLattice (K := K) (L := L)
  rw [TateCohomology.herbrandQuotient_eq_of_epi_of_finite_kernel (unitsToUnitLattice K L)]
  -- the unit lattice and the sum-zero lattice are two Galois-stable lattices in `logSpace L`
  have : Module.Free ℤ (augmentationLattice K L) :=
    Module.Free.of_equiv (augmentationCoordEquiv K L).symm
  -- the unit lattice is free of finite rank, by Dirichlet's unit theorem
  classical
  let e : unitLattice L ≃ₗ[ℤ] unitLatticeRep K L :=
    LinearEquiv.ofEq _ _ (toSubmodule_unitLatticeSubrep (K := K) (L := L)).symm
  have : Module.Free ℤ (unitLatticeRep K L) := Module.Free.of_equiv e
  have : Module.Finite ℤ (unitLatticeRep K L) := Module.Finite.equiv e
  have hi : IsBaseChange ℝ (unitLatticeSubrep K L).toSubmodule.subtype := by
    rw [toSubmodule_unitLatticeSubrep]
    exact ZLattice.isBaseChange_subtype ℝ (unitLattice L)
  exact TateCohomology.herbrandQuotient_eq_of_isBaseChange (logSpaceRep K L) hi
    isBaseChange_augmentationToLogSpace
    (fun σ x ↦ by simp [Subrepresentation.toRepresentation_apply]) augmentationToLogSpace_rho

/-- **The Herbrand quotient of the units** of an extension of number fields `L/K` with cyclic
automorphism group is the Herbrand quotient of the permutation lattice on the infinite places of `L`
divided by the order of the automorphism group: `h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / |Aut(L/K)|`. -/
theorem herbrandQuotient_units_eq_div_card :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) =
      TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) /
        Nat.card (L ≃ₐ[K] L) := by
  rw [herbrandQuotient_units_eq_herbrandQuotient_augmentationLattice,
    TateCohomology.herbrandQuotient_augmentationSubrepresentation_eq_div]

variable [IsGalois K L]

/-- **The Herbrand quotient of the units** of a cyclic extension of number fields `L/K` is the
Herbrand quotient of the permutation lattice on the infinite places of `L` divided by the degree:
`h((𝓞 L)ˣ) = h(ℤ[S_∞(L)]) / [L : K]`. -/
theorem herbrandQuotient_units_eq_div :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) =
      TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) /
        Module.finrank K L := by
  rw [herbrandQuotient_units_eq_div_card, IsGalois.card_aut_eq_finrank K L]

open scoped Classical in
/-- **The Herbrand quotient of the units** of a cyclic extension of number fields `L/K` is
`2^r / [L : K]`, where `r` is the number of infinite places of `K` ramified in `L`, that is, the
real places of `K` that become complex in `L`. -/
theorem herbrandQuotient_units :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) =
      (2 : ℚ) ^ (Finset.univ.filter fun v : InfinitePlace K ↦ ¬ v.IsUnramifiedIn L).card /
        Module.finrank K L := by
  rw [herbrandQuotient_units_eq_div, herbrandQuotient_ofMulAction_infinitePlace]

end TauCeti.ClassFieldTheory
