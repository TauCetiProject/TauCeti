/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension
public import TauCeti.Algebra.Module.GradedModule.HomogeneousPart

/-!
# Finite Laurent support of graded Hom spaces

Let `P` be a finitely generated graded module and `M` a finite-dimensional graded module over a
graded algebra over a field. Only finitely many shifts `M{j}` receive a nonzero graded map from
`P`, and each Hom space is finite-dimensional, so the Hom spaces `Hom(P, M{j})` have finite
Laurent support. A surjection from a finite graded free module `⨁ᵢ A{dᵢ}` embeds
`Hom(P, M{j})` into `∏ᵢ M_{dᵢ-j}`. No projectivity of `P` and no finite-dimensionality of the
algebra are needed.

## Main results

* The instance `Module.Finite k (M ⟶ N)`: graded maps between finite-dimensional graded modules
  form a finite-dimensional space.
* `TauCeti.GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj`: graded maps from a finitely
  generated graded module into the shifts of a finite-dimensional one have finite Laurent support.
* `TauCeti.GradedModuleCat.homShiftDirectSumEquiv`: for a finitely generated graded source, the
  direct sum of the graded maps into all shifts is the space of ungraded module maps.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded free
  modules and degree shifts.
-/

public section

open CategoryTheory

namespace TauCeti.GradedModuleCat

universe v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- **Graded maps between finite-dimensional graded modules form a finite-dimensional space**:
forgetting the grading and the `A`-linearity embeds them in the `k`-linear maps. -/
instance (M N : GradedModuleCat.{v} 𝒜) [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (M ⟶ N) :=
  Module.Finite.of_injective
    ({ toFun f := f.hom.restrictScalars k
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : (M ⟶ N) →ₗ[k] (M →ₗ[k] N))
    fun _ _ h ↦ hom_ext (LinearMap.ext fun x ↦ LinearMap.congr_fun h x)

variable [GradedAlgebra 𝒜]

/-! ### Decomposition of an ungraded map into homogeneous parts -/

variable (M N : GradedModuleCat.{uA} 𝒜)

/-- Sum the underlying maps of a finitely supported family of graded maps `M ⟶ N{j}`. -/
private def homShiftDirectSumMap :
    DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j)) →ₗ[k] (M →ₗ[A] N) :=
  DirectSum.toModule k ℤ _ fun _ ↦
    { toFun := fun f ↦ f.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

omit [GradedAlgebra 𝒜] in
@[simp]
private theorem homShiftDirectSumMap_of (j : ℤ) (f : M ⟶ N.shiftObj j) :
    homShiftDirectSumMap M N (DirectSum.of (fun j : ℤ ↦ M ⟶ N.shiftObj j) j f) = f.hom := by
  classical
  rw [← DirectSum.lof_eq_of k, homShiftDirectSumMap, DirectSum.toModule_lof]
  rfl

/-- The degree-`r` homogeneous part of an ungraded map, regarded as a graded map to `N{-r}`. -/
private noncomputable def homogeneousPartToShift (f : M →ₗ[A] N) (r : ℤ) :
    M ⟶ N.shiftObj (-r) :=
  ofHom (M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 f r) <|
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [mem_shiftObj_piece_iff, sub_neg_eq_add]
      simpa only [add_zero] using
        M.grading.isHomogeneous_homogeneousPartOfGradedSMul N.grading 𝒜 f r |>.map_mem hx

private theorem homogeneousPartToShift_hom (f : M →ₗ[A] N) (r : ℤ) :
    (homogeneousPartToShift M N f r).hom =
      M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 f r :=
  rfl

omit [GradedAlgebra 𝒜] in
private theorem isHomogeneous_hom_to_shift {j : ℤ} (f : M ⟶ N.shiftObj j) :
    LinearMap.IsHomogeneous f.hom M.grading.piece N.grading.piece (-j) := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  have h := f.isHomogeneous.map_mem hx
  rw [mem_shiftObj_piece_iff] at h
  simpa only [add_zero, sub_eq_add_neg] using h

/-- The degree-`-j` homogeneous part of a sum of graded maps recovers its `j`-th summand. -/
private theorem homogeneousPartOfGradedSMul_homShiftDirectSumMap
    (y : DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j))) (j : ℤ) :
    M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 (homShiftDirectSumMap M N y) (-j) =
      (y j).hom := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i f =>
      classical
      rw [homShiftDirectSumMap_of]
      by_cases hij : i = j
      · subst i
        simp only [DirectSum.of_apply, dite_true]
        exact M.grading.homogeneousPartOfGradedSMul_eq_self N.grading 𝒜 f.hom (-j)
          (isHomogeneous_hom_to_shift M N f)
      · simp only [DirectSum.of_apply, hij, dite_false, hom_zero]
        exact M.grading.homogeneousPartOfGradedSMul_eq_zero_of_ne N.grading 𝒜 f.hom
          (isHomogeneous_hom_to_shift M N f) (by omega)
  | add x y hx hy =>
      rw [map_add, M.grading.homogeneousPartOfGradedSMul_add, hx, hy, DirectSum.add_apply,
        hom_add]

private theorem homShiftDirectSumMap_injective :
    Function.Injective (homShiftDirectSumMap M N) := by
  intro z z' h
  apply DirectSum.ext
  intro j
  apply hom_ext
  rw [← homogeneousPartOfGradedSMul_homShiftDirectSumMap, h,
    homogeneousPartOfGradedSMul_homShiftDirectSumMap]

private theorem homShiftDirectSumMap_surjective [Module.Finite A M] :
    Function.Surjective (homShiftDirectSumMap M N) := by
  classical
  intro f
  obtain ⟨d, hd⟩ := M.grading.exists_finset_homogeneousPartOfGradedSMul_eq_zero N.grading 𝒜 f
  refine ⟨∑ r ∈ d, DirectSum.of (fun j : ℤ ↦ M ⟶ N.shiftObj j) (-r)
      (homogeneousPartToShift M N f r), M.grading.linearMap_ext fun p x hx ↦ ?_⟩
  simp only [map_sum, homShiftDirectSumMap_of, homogeneousPartToShift_hom, LinearMap.sum_apply,
    M.grading.homogeneousPartOfGradedSMul_apply_of_mem N.grading 𝒜 f _ hx]
  -- Every nonzero component `(f x)_q` is the value of the degree-`(q - p)` part, so `q - p ∈ d`.
  have hsub : (DirectSum.decompose N.grading.piece (f x)).support ⊆ d.image (p + ·) := by
    intro q hq
    refine Finset.mem_image.2 ⟨q - p, ?_, add_sub_cancel p q⟩
    by_contra hqd
    have h := LinearMap.congr_fun (hd (q - p) hqd) x
    rw [M.grading.homogeneousPartOfGradedSMul_apply_of_mem N.grading 𝒜 f _ hx, add_sub_cancel,
      LinearMap.zero_apply] at h
    exact DFinsupp.mem_support_iff.1 hq (Subtype.ext h)
  calc
    ∑ r ∈ d, (DirectSum.decompose N.grading.piece (f x) (p + r) : N) =
        ∑ q ∈ d.image (p + ·), (DirectSum.decompose N.grading.piece (f x) q : N) :=
      (Finset.sum_image (f := fun q ↦ (DirectSum.decompose N.grading.piece (f x) q : N))
        fun _ _ _ _ ↦ add_left_cancel).symm
    _ = ∑ q ∈ (DirectSum.decompose N.grading.piece (f x)).support,
          (DirectSum.decompose N.grading.piece (f x) q : N) :=
      (Finset.sum_subset hsub fun q _ hq ↦ by simp [DFinsupp.notMem_support_iff.1 hq]).symm
    _ = f x := DirectSum.sum_support_decompose N.grading.piece (f x)

/-- **An ungraded map out of a finitely generated graded module is the finite sum of its
homogeneous parts.** Equivalently, the direct sum of the graded morphism spaces `M ⟶ N{j}` over
all internal shifts is linearly equivalent to the space of underlying module maps `M →ₗ[A] N`.
No finiteness is needed on the target.

The shift convention means that a morphism to `N{j}` has underlying homogeneous degree `-j`. -/
noncomputable def homShiftDirectSumEquiv [Module.Finite A M] :
    DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j)) ≃ₗ[k] (M →ₗ[A] N) :=
  LinearEquiv.ofBijective (homShiftDirectSumMap M N)
    ⟨homShiftDirectSumMap_injective M N, homShiftDirectSumMap_surjective M N⟩

/-- On a single homogeneous summand, `homShiftDirectSumEquiv` forgets the grading. -/
@[simp]
theorem homShiftDirectSumEquiv_of [Module.Finite A M] (j : ℤ) (f : M ⟶ N.shiftObj j) :
    homShiftDirectSumEquiv M N
        (DirectSum.of (fun j : ℤ ↦ M ⟶ N.shiftObj j) j f) = f.hom :=
  homShiftDirectSumMap_of M N j f

/-- The `j`-th summand of `homShiftDirectSumEquiv.symm f` is the degree-`-j` homogeneous part of
the ungraded map `f`. -/
@[simp]
theorem homShiftDirectSumEquiv_symm_apply_hom [Module.Finite A M] (f : M →ₗ[A] N) (j : ℤ) :
    ((homShiftDirectSumEquiv M N).symm f j).hom =
      M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 f (-j) := by
  conv_rhs => rw [← (homShiftDirectSumEquiv M N).apply_symm_apply f]
  exact (homogeneousPartOfGradedSMul_homShiftDirectSumMap M N _ j).symm

/-! ### Finite Laurent support -/

/-- **Graded maps into the shifts of a finite-dimensional graded module have finite Laurent
support** when the source is finitely generated. A surjection from a finite graded free module
`⨁ᵢ A{dᵢ}` embeds `Hom(P, M{j})` into `∏ᵢ M_{dᵢ-j}`, and `M` has only finitely many nonzero
pieces. -/
theorem hasFiniteLaurentSupport_hom_shiftObj (P M : GradedModuleCat.{uA} 𝒜)
    [Module.Finite A P] [Module.Finite k M] :
    HasFiniteLaurentSupport k fun j : ℤ ↦ P ⟶ M.shiftObj j := by
  classical
  obtain ⟨I, hI, d, π, hπ⟩ := exists_finite_free_surjection P
  have : Epi π := (epi_iff_surjective π).2 hπ
  let _ : Fintype I := Fintype.ofFinite I
  have hM := M.grading.finite_piece_ne_bot
  -- Maps out of the free module are tuples in the pieces `M_{dᵢ-j}`.
  have hfree : HasFiniteLaurentSupport k fun j : ℤ ↦ ∀ i, (M.shiftObj j).grading.piece (d i) := by
    refine HasFiniteLaurentSupport.of_finset (fun j ↦ inferInstance)
      (Finset.univ.biUnion fun i ↦ hM.toFinset.image fun p ↦ d i - p) fun j hj ↦ ?_
    have (i : I) : Subsingleton ((M.shiftObj j).grading.piece (d i)) := by
      rw [Submodule.subsingleton_iff_eq_bot]
      by_contra hne
      refine hj (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2
        ⟨d i + -j, hM.mem_toFinset.2 ?_, by omega⟩⟩)
      simpa using hne
    infer_instance
  exact (hfree.of_equiv fun j ↦ (freeHomEquiv (M.shiftObj j)).symm).of_injective
    (fun j ↦ Linear.leftComp k _ π) fun j _ _ h ↦ (cancel_epi π).1 h

end TauCeti.GradedModuleCat
