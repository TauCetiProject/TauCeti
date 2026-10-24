/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
public import TauCeti.RingTheory.HochschildCohomology.Complex

/-!
# Normalized Hochschild cochains

A normalized Hochschild cochain vanishes whenever any argument other than the zeroth is the
unit. These are the cochains dual to normalized chains `A ⊗ (A / k1) ⊗ ⋯ ⊗ (A / k1)`.
The Hochschild coboundary and Connes' operator preserve this submodule, giving its mixed
complex structure. The underlying cochain complex and its inclusion into the full Hochschild
complex use the native `CochainComplex` API. On normalized cochains the formula for `B` reduces
to the signed cyclic sum of `φ(1, a₀, …, aₙ)`.

Normalization leaves all degree-zero cochains in place. It is different from requiring
vanishing on the scalar subalgebra in every degree, and does not assert that cyclic cochains
are normalized.

## References

* J.-L. Loday, *Cyclic Homology*, §§1.1 and 2.1 (normalized Hochschild mixed complex).
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

namespace TauCeti

section Normalized

variable (R A M : Type*) [CommSemiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommMonoid M] [Module R M]

/-- Hochschild cochains which vanish when a noninitial argument is the unit. -/
def normalizedHochschildCochains (n : ℕ) :
    Submodule R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) where
  carrier := {φ | ∀ (a : Fin (n + 1) → A) (i : Fin (n + 1)), i ≠ 0 → a i = 1 → φ a = 0}
  zero_mem' := by simp
  add_mem' hφ hψ a i hi ha := by simp [hφ a i hi ha, hψ a i hi ha]
  smul_mem' r _ hφ a i hi ha := by simp [hφ a i hi ha]

variable {R A M} {n : ℕ}

/-- Normalization means vanishing if any noninitial argument equals the unit. -/
@[simp]
theorem mem_normalizedHochschildCochains_iff
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ normalizedHochschildCochains R A M n ↔
      ∀ (a : Fin (n + 1) → A) (i : Fin (n + 1)), i ≠ 0 → a i = 1 → φ a = 0 := Iff.rfl

/-- There is no normalization condition in degree zero. -/
@[simp]
theorem normalizedHochschildCochains_zero : normalizedHochschildCochains R A M 0 = ⊤ := by
  ext φ
  simp

/-- Applying a linear map to the values preserves normalization. -/
theorem _root_.LinearMap.compMultilinearMap_mem_normalizedHochschildCochains
    {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M n) :
    f.compMultilinearMap φ ∈ normalizedHochschildCochains R A N n := by
  intro a i hi ha
  simp [hφ a i hi ha]

/-- A normalized cochain also vanishes on scalar multiples of the unit in noninitial slots. -/
theorem apply_update_smul_one_eq_zero_of_mem_normalizedHochschildCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M n) (a : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : i ≠ 0) (r : R) :
    φ (Function.update a i (r • (1 : A))) = 0 := by
  rw [φ.map_update_smul, hφ _ i hi (Function.update_self _ _ _), smul_zero]

/-- Pullback along a linear map preserving the unit preserves normalized cochains. -/
theorem _root_.LinearMap.compLinearMap_mem_normalizedHochschildCochains
    {B : Type*} [AddCommMonoid B] [One B] [Module R B] (f : B →ₗ[R] A) (hf : f 1 = 1)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M n) :
    φ.compLinearMap (fun _ ↦ f) ∈ normalizedHochschildCochains R B M n := by
  intro a i hi ha
  exact hφ _ i hi (by simpa only [ha] using hf)

end Normalized

section Hochschild

variable {R A M : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {n : ℕ}

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem normalized_face_eq_zero
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M n)
    (a : Fin (n + 2) → A) (j : Fin (n + 1)) (ha : a j.succ = 1)
    (i : Fin (n + 2)) (hi : i ≠ j.castSucc ∧ i ≠ j.succ) :
    φ (hochschildFace i a) = 0 := by
  induction i using Fin.lastCases with
  | last =>
    have hj : j.val < n := by
      have := j.isLt
      have := hi.2
      simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_succ] at this
      omega
    apply hφ _ (⟨j.val, hj⟩ : Fin n).succ (Fin.succ_ne_zero _)
    simpa [hochschildFace_last, Fin.cons, Fin.ext_iff] using ha
  | cast i =>
    rw [hochschildFace_castSucc]
    have hi₁ : i.val ≠ j.val := by simpa [Fin.ext_iff] using hi.1
    have hi₂ : i.val ≠ j.val + 1 := by simpa [Fin.ext_iff] using hi.2
    rcases lt_or_gt_of_ne hi₁ with hij | hji
    · apply hφ _ j (by intro h; simp [h] at hij)
      rw [Fin.contractNth_apply_of_gt i.castSucc _ a j hij]
      exact ha
    · have hji' : j.val + 1 < i.val := by omega
      apply hφ _ (⟨j.val, by omega⟩ : Fin n).succ (Fin.succ_ne_zero _)
      rw [Fin.contractNth_apply_of_lt i.castSucc _ a _ hji']
      exact ha

/-- The Hochschild coboundary preserves normalized cochains. -/
theorem hochschildCoboundary_mem_normalizedHochschildCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M n) :
    hochschildCoboundary R A M n φ ∈ normalizedHochschildCochains R A M (n + 1) := by
  -- The two faces adjacent to a unit cancel; every remaining face has a noninitial unit argument.
  intro a k hk ha
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk
  rw [hochschildCoboundary_apply, Finset.sum_eq_add_of_mem j.castSucc j.succ
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp [Fin.ext_iff])
    (fun i _ hi ↦ by rw [normalized_face_eq_zero hφ a j ha i hi, smul_zero]),
    hochschildFace_castSucc_eq_succ_of_apply_succ_eq_one a j ha]
  simp [pow_succ]

end Hochschild

section Connes

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- On normalized cochains Connes' operator is the cyclic norm of unit insertion. -/
theorem connesB_eq_cyclicNorm_barContraction_of_normalized
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M (n + 1)) :
    connesB R A M n φ = cyclicNorm R A M n (barContraction R A M n φ) := by
  have hs : barContraction R A M n (cyclicOperator R A M (n + 1) φ) = 0 := by
    ext a
    rw [barContraction_apply, cyclicOperator_apply]
    rw [hφ _ (0 : Fin (n + 1)).succ (Fin.succ_ne_zero _) (by simp), smul_zero]
    rfl
  rw [connesB_apply, map_sub, hs, sub_zero]

/-- The signed cyclic-sum formula for `B` on normalized cochains, dual to the formula on
normalized Hochschild chains. -/
theorem connesB_apply_of_normalized
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M (n + 1)) (a : Fin (n + 1) → A) :
    connesB R A M n φ a =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n * k) •
        φ (Fin.cons 1 (a ∘ (finRotate (n + 1) ^ k).symm)) := by
  rw [connesB_eq_cyclicNorm_barContraction_of_normalized hφ, cyclicNorm_apply]
  simp only [barContraction_apply]

/-- `B` of a normalized cochain vanishes if any argument is the unit, including the zeroth. -/
theorem connesB_apply_eq_zero_of_normalized
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M (n + 1))
    (a : Fin (n + 1) → A) (i : Fin (n + 1)) (ha : a i = 1) :
    connesB R A M n φ a = 0 := by
  rw [connesB_apply_of_normalized hφ]
  apply Finset.sum_eq_zero
  intro k _
  rw [hφ _ ((finRotate (n + 1) ^ k) i).succ (Fin.succ_ne_zero _) (by simpa using ha),
    smul_zero]

/-- Connes' operator preserves normalized Hochschild cochains. -/
theorem connesB_mem_normalizedHochschildCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ normalizedHochschildCochains R A M (n + 1)) :
    connesB R A M n φ ∈ normalizedHochschildCochains R A M n :=
  fun a i _ ha ↦ connesB_apply_eq_zero_of_normalized hφ a i ha

variable (R A M) in
/-- Connes' operator restricted to normalized cochains. -/
def normalizedConnesB (n : ℕ) :
    normalizedHochschildCochains R A M (n + 1) →ₗ[R]
      normalizedHochschildCochains R A M n :=
  (connesB R A M n).restrict fun _ hφ ↦ connesB_mem_normalizedHochschildCochains hφ

/-- Forgetting normalization intertwines the normalized and full Connes operators. -/
@[simp]
theorem coe_normalizedConnesB (φ : normalizedHochschildCochains R A M (n + 1)) :
    (normalizedConnesB R A M n φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) =
      connesB R A M n φ := (rfl)

/-- The normalized Connes operator squares to zero. -/
@[simp]
theorem normalizedConnesB_normalizedConnesB
    (φ : normalizedHochschildCochains R A M (n + 2)) :
    normalizedConnesB R A M n (normalizedConnesB R A M (n + 1) φ) = 0 := by
  apply Subtype.ext
  simp

end Connes

section Operators

variable (R A M : Type*) [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The Hochschild coboundary restricted to normalized cochains. -/
def normalizedHochschildCoboundary (n : ℕ) :
    normalizedHochschildCochains R A M n →ₗ[R]
      normalizedHochschildCochains R A M (n + 1) :=
  (hochschildCoboundary R A M n).restrict
    fun _ hφ ↦ hochschildCoboundary_mem_normalizedHochschildCochains hφ

variable {R A M} {n : ℕ}

/-- Forgetting normalization intertwines the normalized and full Hochschild coboundaries. -/
@[simp]
theorem coe_normalizedHochschildCoboundary (φ : normalizedHochschildCochains R A M n) :
    (normalizedHochschildCoboundary R A M n φ :
      MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) = hochschildCoboundary R A M n φ := (rfl)

/-- The normalized Hochschild coboundary and Connes operator anticommute in positive degrees. -/
theorem normalizedHochschildCoboundary_normalizedConnesB_add
    (φ : normalizedHochschildCochains R A M (n + 1)) :
    normalizedHochschildCoboundary R A M n (normalizedConnesB R A M n φ) +
      normalizedConnesB R A M (n + 1) (normalizedHochschildCoboundary R A M (n + 1) φ) = 0 := by
  apply Subtype.ext
  simpa only [Submodule.coe_add, Submodule.coe_zero, coe_normalizedHochschildCoboundary,
    coe_normalizedConnesB] using
    hochschildCoboundary_connesB_add_connesB_hochschildCoboundary φ.val

/-- The mixed-complex identity at the bottom degree: `B b = 0` on degree-zero cochains. -/
@[simp]
theorem normalizedConnesB_normalizedHochschildCoboundary_zero
    (φ : normalizedHochschildCochains R A M 0) :
    normalizedConnesB R A M 0 (normalizedHochschildCoboundary R A M 0 φ) = 0 := by
  apply Subtype.ext
  ext a
  rw [coe_normalizedConnesB, coe_normalizedHochschildCoboundary,
    connesB_apply_of_normalized (hochschildCoboundary_mem_normalizedHochschildCochains φ.property)]
  simp only [Nat.zero_add, Finset.sum_range_one, zero_mul, pow_zero, one_smul,
    Equiv.Perm.one_def, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id,
    Submodule.coe_zero, zero_apply]
  rw [hochschildCoboundary_zero_apply]
  simp

end Operators

section Associative

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {n : ℕ}

/-- The normalized Hochschild coboundary squares to zero. -/
@[simp]
theorem normalizedHochschildCoboundary_normalizedHochschildCoboundary
    (φ : normalizedHochschildCochains R A M n) :
    normalizedHochschildCoboundary R A M (n + 1)
      (normalizedHochschildCoboundary R A M n φ) = 0 := by
  apply Subtype.ext
  simp

end Associative

section Complex

open CategoryTheory

variable (R A M : Type*) [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The normalized Hochschild cochain complex, with the restricted Hochschild coboundary. -/
def normalizedHochschildCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (normalizedHochschildCochains R A M n))
    (fun n ↦ ModuleCat.ofHom (normalizedHochschildCoboundary R A M n)) fun n ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun φ ↦
        normalizedHochschildCoboundary_normalizedHochschildCoboundary φ

/-- The degree-`n` term of the normalized complex is the module of normalized cochains. -/
def normalizedHochschildCochainComplexXIso (n : ℕ) :
    (normalizedHochschildCochainComplex R A M).X n ≅
      ModuleCat.of R (normalizedHochschildCochains R A M n) := Iso.refl _

/-- The normalized complex has the restricted Hochschild coboundary as differential. -/
@[reassoc, elementwise]
theorem normalizedHochschildCochainComplex_d (n : ℕ) :
    (normalizedHochschildCochainComplex R A M).d n (n + 1) ≫
        (normalizedHochschildCochainComplexXIso R A M (n + 1)).hom =
      (normalizedHochschildCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (normalizedHochschildCoboundary R A M n) := by
  simp [normalizedHochschildCochainComplex, normalizedHochschildCochainComplexXIso]

/-- Inclusion of normalized cochains into the full Hochschild cochain complex. -/
def normalizedHochschildCochainComplexι :
    normalizedHochschildCochainComplex R A M ⟶ hochschildCochainComplex R A M where
  f n := (normalizedHochschildCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (normalizedHochschildCochains R A M n).subtype ≫
      (hochschildCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hochschildCochainComplex_d_apply,
      Iso.inv_hom_id_apply, normalizedHochschildCochainComplex_d_apply, ModuleCat.hom_ofHom,
      Submodule.subtype_apply, coe_normalizedHochschildCoboundary]

/-- Termwise, the comparison with full Hochschild cochains is the submodule inclusion. -/
@[reassoc, elementwise]
theorem normalizedHochschildCochainComplexι_f (n : ℕ) :
    (normalizedHochschildCochainComplexι R A M).f n ≫ (hochschildCochainComplexXIso R A M n).hom =
      (normalizedHochschildCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (normalizedHochschildCochains R A M n).subtype := by
  simp [normalizedHochschildCochainComplexι]

end Complex

end TauCeti
