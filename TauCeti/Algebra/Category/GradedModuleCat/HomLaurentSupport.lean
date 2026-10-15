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
* `TauCeti.GradedModuleCat.homShiftDirectSumEquiv`: for finite-dimensional graded modules, the
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

private theorem homogeneousPartOfGradedSMul_eq_zero_of_ne
    (f : M →ₗ[A] N) {r s : ℤ}
    (hf : LinearMap.IsHomogeneous f M.grading.piece N.grading.piece s) (hrs : r ≠ s) :
    M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 f r = 0 := by
  refine M.grading.linearMap_ext fun p x hx ↦ ?_
  rw [M.grading.homogeneousPartOfGradedSMul_apply_of_mem N.grading 𝒜 f r hx,
    LinearMap.zero_apply]
  exact DirectSum.decompose_of_mem_ne N.grading.piece (hf.map_mem hx) fun h ↦
    hrs (add_left_cancel h.symm)

private theorem homShiftDirectSumMap_injective :
    Function.Injective (homShiftDirectSumMap M N) := by
  intro z z' h
  apply DirectSum.ext
  intro j
  apply hom_ext
  change (z j).hom = (z' j).hom
  have hpart := congrArg
    (fun f : M →ₗ[A] N ↦ M.grading.homogeneousPartOfGradedSMul N.grading 𝒜 f (-j)) h
  suffices key : ∀ y : DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j)),
      M.grading.homogeneousPartOfGradedSMul N.grading 𝒜
          (homShiftDirectSumMap M N y) (-j) = (y j).hom by
    simpa only [key] using hpart
  intro y
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i f =>
      classical
      by_cases hij : i = j
      · subst i
        rw [homShiftDirectSumMap_of]
        simp only [DirectSum.of_apply, dite_true]
        exact M.grading.homogeneousPartOfGradedSMul_eq_self N.grading 𝒜 f.hom (-j)
          (isHomogeneous_hom_to_shift M N f)
      · rw [homShiftDirectSumMap_of]
        simp only [DirectSum.of_apply, hij, dite_false]
        rw [homogeneousPartOfGradedSMul_eq_zero_of_ne M N f.hom
          (isHomogeneous_hom_to_shift M N f) (by omega : -j ≠ -i)]
        rfl
  | add x y hx hy =>
      rw [map_add, M.grading.homogeneousPartOfGradedSMul_add, hx, hy, DirectSum.add_apply,
        hom_add]

private theorem homShiftDirectSumMap_surjective [Module.Finite k M] [Module.Finite k N] :
    Function.Surjective (homShiftDirectSumMap M N) := by
  classical
  intro f
  let sM := M.grading.finite_piece_ne_bot.toFinset
  let sN := N.grading.finite_piece_ne_bot.toFinset
  let d : Finset ℤ := (sM ×ˢ sN).image fun pq ↦ pq.2 - pq.1
  let z : DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j)) :=
    ∑ r ∈ d, DirectSum.of (fun j : ℤ ↦ M ⟶ N.shiftObj j) (-r)
      (homogeneousPartToShift M N f r)
  refine ⟨z, LinearMap.ext fun x ↦ ?_⟩
  rw [← M.grading.sum_decompose_toFinset M.grading.finite_piece_ne_bot x]
  rw [map_sum, map_sum]
  conv_rhs => rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : M.grading.piece p ≠ ⊥ := M.grading.finite_piece_ne_bot.mem_toFinset.mp hp
  simp only [homShiftDirectSumMap_of, homogeneousPartToShift_hom, LinearMap.sum_apply,
    M.grading.homogeneousPartOfGradedSMul_apply_of_mem N.grading 𝒜 f _
      (DirectSum.decompose M.grading.piece x p).property]
  let t : Finset ℤ := sN.image fun q ↦ q - p
  calc
    ∑ r ∈ d, (DirectSum.decompose N.grading.piece
        (f (DirectSum.decompose M.grading.piece x p)) (p + r) : N) =
        ∑ r ∈ t, (DirectSum.decompose N.grading.piece
          (f (DirectSum.decompose M.grading.piece x p)) (p + r) : N) := by
      refine (Finset.sum_subset ?_ fun r hr hrt ↦ ?_).symm
      · intro r hr
        change r ∈ sN.image (fun q ↦ q - p) at hr
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
        change q - p ∈ (sM ×ˢ sN).image (fun pq ↦ pq.2 - pq.1)
        exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
      · have hbot : N.grading.piece (p + r) = ⊥ := by
          by_contra hn
          apply hrt
          change r ∈ sN.image (fun q ↦ q - p)
          exact Finset.mem_image.mpr
            ⟨p + r, by simpa [sN] using
              N.grading.finite_piece_ne_bot.mem_toFinset.mpr hn, by omega⟩
        exact (Submodule.eq_bot_iff _).mp hbot _
          (DirectSum.decompose N.grading.piece
            (f (DirectSum.decompose M.grading.piece x p)) (p + r)).property
    _ = ∑ q ∈ sN, (DirectSum.decompose N.grading.piece
          (f (DirectSum.decompose M.grading.piece x p)) q : N) := by
      change (∑ r ∈ sN.image (fun q ↦ q - p), (DirectSum.decompose N.grading.piece
        (f (DirectSum.decompose M.grading.piece x p)) (p + r) : N)) = _
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro q hq
        rw [show p + (q - p) = q by omega]
      · intro q hq q' hq' heq
        exact sub_left_injective heq
    _ = f (DirectSum.decompose M.grading.piece x p) :=
      N.grading.sum_decompose_toFinset N.grading.finite_piece_ne_bot _

/-- **An ungraded map between finite-dimensional graded modules is the finite sum of its
homogeneous parts.** Equivalently, the direct sum of the graded morphism spaces `M ⟶ N{j}` over
all internal shifts is linearly equivalent to the space of underlying module maps `M →ₗ[A] N`.

The shift convention means that a morphism to `N{j}` has underlying homogeneous degree `-j`. -/
noncomputable def homShiftDirectSumEquiv [Module.Finite k M] [Module.Finite k N] :
    DirectSum ℤ (fun j ↦ (M ⟶ N.shiftObj j)) ≃ₗ[k] (M →ₗ[A] N) :=
  LinearEquiv.ofBijective (homShiftDirectSumMap M N)
    ⟨homShiftDirectSumMap_injective M N, homShiftDirectSumMap_surjective M N⟩

/-- On a single homogeneous summand, `homShiftDirectSumEquiv` forgets the grading. -/
@[simp]
theorem homShiftDirectSumEquiv_of [Module.Finite k M] [Module.Finite k N]
    (j : ℤ) (f : M ⟶ N.shiftObj j) :
    homShiftDirectSumEquiv M N
        (DirectSum.of (fun j : ℤ ↦ M ⟶ N.shiftObj j) j f) = f.hom :=
  homShiftDirectSumMap_of M N j f

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
