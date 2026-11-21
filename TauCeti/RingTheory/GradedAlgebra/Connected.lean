/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Degree-zero projection and augmentation of connected nonnegatively `ℤ`-graded algebras

For a `ℤ`-graded `R`-algebra `A` (`𝒜 : ℤ → Submodule R A`) concentrated in nonnegative degrees
(`∀ i < 0, 𝒜 i = ⊥`), `TauCeti.GradedAlgebra.coe_decompose_mul_zero_of_nonneg` shows that taking
the degree-zero component is multiplicative. Bundling `a ↦ decompose 𝒜 a 0` therefore produces an
`R`-algebra homomorphism `projZeroAlgHom : A →ₐ[R] 𝒜 0` whose kernel is the positive-degree part
`⨆ i > 0, 𝒜 i`.

When `A` is moreover connected (`𝒜 0` lies in the image of `algebraMap R A`, with
`FaithfulSMul R A`), `Algebra.ofId R (𝒜 0)` is an `R`-algebra equivalence
`gradeZeroAlgEquiv : R ≃ₐ[R] 𝒜 0`. Composing `projZeroAlgHom` with its inverse defines the
canonical `R`-algebra augmentation `connectedAugmentation : A →ₐ[R] R` annihilating positive
degrees and retracting `algebraMap R A`.

## Main definitions

* `TauCeti.GradedAlgebra.projZeroAlgHom`: degree-zero projection `A →ₐ[R] 𝒜 0` for a nonnegatively
  `ℤ`-graded `R`-algebra.
* `TauCeti.GradedAlgebra.gradeZeroAlgEquiv`: the `R`-algebra equivalence `R ≃ₐ[R] 𝒜 0` for a
  connected graded `R`-algebra.
* `TauCeti.GradedAlgebra.connectedAugmentation`: the canonical augmentation `A →ₐ[R] R` of a
  connected nonnegatively `ℤ`-graded `R`-algebra.

## Main results

* `TauCeti.GradedAlgebra.projZeroAlgHom_eq_zero_iff`: `projZeroAlgHom hneg a = 0` iff
  `a ∈ ⨆ i > 0, 𝒜 i`.
* `TauCeti.GradedAlgebra.mul_mem_positive_of_left`: `⨆ i > 0, 𝒜 i` is closed under right
  multiplication by arbitrary elements of `A`.
* `TauCeti.GradedAlgebra.connectedAugmentation_eq_zero_iff`: the kernel of `connectedAugmentation`
  is `⨆ i > 0, 𝒜 i`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti.GradedAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- Projection onto the degree-zero subalgebra `𝒜 0` of a nonnegatively `ℤ`-graded `R`-algebra.
This is the `ℤ`-graded algebra counterpart of `GradedRing.projZeroRingHom`. -/
def projZeroAlgHom (hneg : ∀ i < 0, 𝒜 i = ⊥) : A →ₐ[R] 𝒜 0 where
  toFun a := decompose 𝒜 a 0
  map_one' := Subtype.ext (decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (coe_decompose_mul_zero_of_nonneg hneg x y)
  commutes' c := Subtype.ext <| by
    simpa using decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 c)

/-- Applying `projZeroAlgHom` extracts the degree-zero component `decompose 𝒜 a 0`. -/
@[simp]
theorem projZeroAlgHom_apply (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : A) :
    projZeroAlgHom hneg a = decompose 𝒜 a 0 :=
  (rfl)

/-- The underlying element of `projZeroAlgHom hneg a` is the degree-zero component of `a`. -/
theorem coe_projZeroAlgHom_apply (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : A) :
    (projZeroAlgHom hneg a : A) = decompose 𝒜 a 0 :=
  (rfl)

/-- `projZeroAlgHom` restricts to the identity on `𝒜 0`. -/
theorem projZeroAlgHom_apply_coe (hneg : ∀ i < 0, 𝒜 i = ⊥) (a : 𝒜 0) :
    projZeroAlgHom hneg (a : A) = a :=
  Subtype.ext (decompose_of_mem_same 𝒜 a.2)

/-- Homogeneous elements of strictly positive degree map to zero under `projZeroAlgHom`. -/
theorem projZeroAlgHom_eq_zero_of_mem_pos (hneg : ∀ i < 0, 𝒜 i = ⊥) {i : ℤ} (hi : 0 < i)
    {a : A} (ha : a ∈ 𝒜 i) : projZeroAlgHom hneg a = 0 :=
  Subtype.ext (decompose_of_mem_ne 𝒜 ha (ne_of_gt hi))

/-- In a nonnegatively graded algebra, an element has vanishing degree-zero projection if and only
if it lies in the positive-degree submodule `⨆ i > 0, 𝒜 i`. -/
theorem projZeroAlgHom_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) {a : A} :
    projZeroAlgHom hneg a = 0 ↔ a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  constructor
  · intro ha0
    classical
    rw [← sum_support_decompose 𝒜 a]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · have hz : (decompose 𝒜 a i : A) = 0 := by
        simpa [hneg i hi] using (decompose 𝒜 a i).2
      simp [hz]
    · rw [← coe_projZeroAlgHom_apply hneg, ha0, ZeroMemClass.coe_zero]
      exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi (decompose 𝒜 a i).2)
  · intro ha
    refine Submodule.iSup_induction _ (motive := fun x ↦ projZeroAlgHom hneg x = 0) ha
      (fun i x hx ↦ ?_) (map_zero _) (fun _ _ hx hy ↦ by rw [map_add, hx, hy, add_zero])
    refine Submodule.iSup_induction _ (motive := fun x ↦ projZeroAlgHom hneg x = 0) hx
      (fun hi x hx ↦ projZeroAlgHom_eq_zero_of_mem_pos hneg hi hx)
      (map_zero _) (fun _ _ hx hy ↦ by rw [map_add, hx, hy, add_zero])

/-- In a nonnegatively graded algebra, the positive-degree part `⨆ i > 0, 𝒜 i` is closed under
right multiplication by arbitrary elements of `A`. -/
theorem mul_mem_positive_of_left (hneg : ∀ i < 0, 𝒜 i = ⊥) {a : A}
    (ha : a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) (b : A) :
    a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  rw [← projZeroAlgHom_eq_zero_iff hneg] at ha ⊢
  simp [map_mul, ha]

/-- The `R`-algebra equivalence `R ≃ₐ[R] 𝒜 0` for a connected graded `R`-algebra. -/
def gradeZeroAlgEquiv [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) : R ≃ₐ[R] 𝒜 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (𝒜 0)) ⟨fun c₁ c₂ h ↦
    FaithfulSMul.algebraMap_injective R A (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨c, hc⟩ := hzero x.1 x.2
      exact ⟨c, Subtype.ext hc⟩⟩

/-- Applying `gradeZeroAlgEquiv` embeds scalars via `algebraMap R A`. -/
@[simp]
theorem coe_gradeZeroAlgEquiv_apply [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (c : R) :
    (gradeZeroAlgEquiv hzero c : A) = algebraMap R A c :=
  congrArg Subtype.val (AlgEquiv.ofBijective_apply (Algebra.ofId R (𝒜 0)) _ c)

/-- `(gradeZeroAlgEquiv hzero).symm` sends the embedded scalar `algebraMap R A c` back to `c`. -/
@[simp]
theorem gradeZeroAlgEquiv_symm_apply [FaithfulSMul R A]
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (c : R) :
    (gradeZeroAlgEquiv hzero).symm ⟨algebraMap R A c, SetLike.algebraMap_mem_graded 𝒜 c⟩ = c :=
  (gradeZeroAlgEquiv hzero).injective <| Subtype.ext <| by
    rw [AlgEquiv.apply_symm_apply, coe_gradeZeroAlgEquiv_apply]

/-- The canonical augmentation `A →ₐ[R] R` of a connected nonnegatively `ℤ`-graded `R`-algebra,
sending positive-degree elements to zero and identifying `𝒜 0` with `R`. -/
def connectedAugmentation [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) : A →ₐ[R] R :=
  (gradeZeroAlgEquiv hzero).symm.toAlgHom.comp (projZeroAlgHom hneg)

/-- `connectedAugmentation` is a retraction of `algebraMap R A`. -/
theorem connectedAugmentation_algebraMap [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (c : R) :
    connectedAugmentation hneg hzero (algebraMap R A c) = c :=
  (connectedAugmentation hneg hzero).commutes c

/-- Embedding `connectedAugmentation hneg hzero a` back into `A` recovers the degree-zero
component `decompose 𝒜 a 0`. -/
theorem algebraMap_connectedAugmentation [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) (a : A) :
    algebraMap R A (connectedAugmentation hneg hzero a) = decompose 𝒜 a 0 := by
  rw [← coe_gradeZeroAlgEquiv_apply hzero, connectedAugmentation, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, coe_projZeroAlgHom_apply]

/-- On degree-zero elements, `connectedAugmentation` inverts `algebraMap R A`. -/
@[simp]
theorem algebraMap_connectedAugmentation_of_mem_zero [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {a : A} (ha : a ∈ 𝒜 0) :
    algebraMap R A (connectedAugmentation hneg hzero a) = a :=
  (algebraMap_connectedAugmentation hneg hzero a).trans (decompose_of_mem_same 𝒜 ha)

/-- Homogeneous elements of strictly positive degree lie in the kernel of `connectedAugmentation`.
-/
theorem connectedAugmentation_eq_zero_of_mem_pos [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {i : ℤ} (hi : 0 < i)
    {a : A} (ha : a ∈ 𝒜 i) : connectedAugmentation hneg hzero a = 0 := by
  rw [connectedAugmentation, AlgHom.comp_apply, projZeroAlgHom_eq_zero_of_mem_pos hneg hi ha,
    map_zero]

/-- The kernel of `connectedAugmentation` is the positive-degree submodule `⨆ i > 0, 𝒜 i`. -/
theorem connectedAugmentation_eq_zero_iff [FaithfulSMul R A] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap R A)) {a : A} :
    connectedAugmentation hneg hzero a = 0 ↔ a ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  unfold connectedAugmentation
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    _root_.map_eq_zero_iff _ (gradeZeroAlgEquiv hzero).symm.injective,
    projZeroAlgHom_eq_zero_iff]

end TauCeti.GradedAlgebra
