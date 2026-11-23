/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The normalized décalage of a cochain complex of abelian groups

Let `p` be a natural number and `M` a `ℤ`-graded cochain complex of abelian groups on whose terms
multiplication by `p` is injective. The *normalized décalage* `E_p(M)` has in degree `n` the
subgroup `{x ∈ Mⁿ | d x ∈ p Mⁿ⁺¹}`, with differential `x ↦ d x / p`. Multiplication by `pⁿ`
identifies it with the subcomplex `η_p M ⊆ M[1/p]` of Berthelot–Ogus décalage,
`(η_p M)ⁿ = {x ∈ pⁿ Mⁿ | d x ∈ pⁿ⁺¹ Mⁿ⁺¹}`; the normalized form avoids the localization and
treats negative degrees in the same way as positive ones. This file works with `E_p(M)` only and
does not construct `η_p M`.

For a prime `p` this is the décalage operator Bhatt–Lurie–Mathew use to define saturated
Dieudonné complexes: a Frobenius on a `p`-torsion-free Dieudonné complex is the same as a
cochain map `M ⟶ E_p(M)`.

## Main definitions

* `CochainComplex.decalageAddSubgroup M p n`: the elements of `Mⁿ` whose differential is
  divisible by `p`.
* `CochainComplex.normalizedDecalage M p hM`: the complex `E_p(M)`.
* `CochainComplex.normalizedDecalageMap`: the cochain map `E_p(M) ⟶ E_p(N)` induced by a
  cochain map `M ⟶ N`.

## Main results

* `CochainComplex.decalageAddSubgroup_eq_ker`: `E_p(M)ⁿ` is the kernel of `d` followed by
  reduction modulo `p`.
* `CochainComplex.smul_normalizedDecalage_d`: `p • d_E x = d_M x`.
* `CochainComplex.normalizedDecalageMap_id`, `CochainComplex.normalizedDecalageMap_comp`:
  functoriality.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Construction 2.1.3 and Remark 2.1.4.
-/

public section

open CategoryTheory

universe u

namespace CochainComplex

section AddSubgroup

variable (M : CochainComplex AddCommGrpCat.{u} ℤ) (p : ℕ)

/-- The elements of `M.X n` whose differential is divisible by `p`: the degree-`n` term of the
normalized décalage `E_p(M)`. -/
def decalageAddSubgroup (n : ℤ) : AddSubgroup (M.X n) :=
  (DistribSMul.toAddMonoidHom (M.X (n + 1)) p).range.comap (M.d n (n + 1)).hom

@[simp]
lemma mem_decalageAddSubgroup_iff {n : ℤ} {x : M.X n} :
    x ∈ M.decalageAddSubgroup p n ↔ ∃ y, p • y = (M.d n (n + 1)).hom x := by
  simp [decalageAddSubgroup]

/-- `E_p(M)ⁿ` is the kernel of the differential followed by reduction modulo `p`. -/
lemma decalageAddSubgroup_eq_ker (n : ℤ) :
    M.decalageAddSubgroup p n = ((QuotientAddGroup.mk' (DistribSMul.toAddMonoidHom
      (M.X (n + 1)) p).range).comp (M.d n (n + 1)).hom).ker := by
  rw [← AddMonoidHom.comap_ker, QuotientAddGroup.ker_mk', decalageAddSubgroup]

/-- Every cocycle lies in `E_p(M)`. -/
lemma mem_decalageAddSubgroup_of_d_eq_zero {n : ℤ} {x : M.X n}
    (hx : (M.d n (n + 1)).hom x = 0) : x ∈ M.decalageAddSubgroup p n :=
  (M.mem_decalageAddSubgroup_iff p).2 ⟨0, by rw [smul_zero, hx]⟩

end AddSubgroup

variable {M : CochainComplex AddCommGrpCat.{u} ℤ} {p : ℕ} (hM : ∀ n, IsSMulRegular (M.X n) p)

/-- The map `x ↦ d x / p` on `E_p(M)ⁿ`, with values in `Mⁿ⁺¹`. -/
private noncomputable def divD (n : ℤ) : M.decalageAddSubgroup p n →+ M.X (n + 1) :=
  ((AddMonoidHom.ofInjective (f := DistribSMul.toAddMonoidHom (M.X (n + 1)) p)
    (hM (n + 1))).symm : _ →+ M.X (n + 1)).comp
      (((M.d n (n + 1)).hom.comp (M.decalageAddSubgroup p n).subtype).codRestrict _
        fun x ↦ AddSubgroup.mem_comap.1 x.property)

private lemma smul_divD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    p • divD hM n x = (M.d n (n + 1)).hom x :=
  AddMonoidHom.apply_ofInjective_symm (f := DistribSMul.toAddMonoidHom (M.X (n + 1)) p)
    (hM (n + 1)) _

private lemma d_divD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    (M.d (n + 1) (n + 1 + 1)).hom (divD hM n x) = 0 := by
  refine hM (n + 1 + 1) ?_
  beta_reduce
  rw [smul_zero, ← map_nsmul, smul_divD, ← AddCommGrpCat.comp_apply, M.d_comp_d]
  simp

/-- The differential `x ↦ d x / p` of the normalized décalage. -/
noncomputable def decalageD (n : ℤ) :
    M.decalageAddSubgroup p n →+ M.decalageAddSubgroup p (n + 1) :=
  (divD hM n).codRestrict _ fun x ↦ M.mem_decalageAddSubgroup_of_d_eq_zero p (d_divD hM n x)

/-- The defining property of `decalageD`: `p • d_E x = d x`. -/
lemma smul_decalageD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    p • (decalageD hM n x : M.X (n + 1)) = (M.d n (n + 1)).hom x :=
  smul_divD hM n x

/-- `decalageD hM n x` is the unique `y` with `p • y = d x`. -/
lemma decalageD_eq_iff {n : ℤ} {x : M.decalageAddSubgroup p n} {y : M.X (n + 1)} :
    (decalageD hM n x : M.X (n + 1)) = y ↔ p • y = (M.d n (n + 1)).hom x :=
  ⟨fun h ↦ h ▸ smul_decalageD hM n x, fun h ↦ hM (n + 1) ((smul_decalageD hM n x).trans h.symm)⟩

/-- The image of the differential of `E_p(M)` consists of cocycles of `M`. -/
@[simp]
lemma d_decalageD (n : ℤ) (x : M.decalageAddSubgroup p n) :
    (M.d (n + 1) (n + 1 + 1)).hom (decalageD hM n x) = 0 :=
  d_divD hM n x

/-- The differential of the normalized décalage squares to zero. -/
lemma decalageD_comp_decalageD (n : ℤ) :
    (decalageD hM (n + 1)).comp (decalageD hM n) = 0 := by
  ext x
  exact (decalageD_eq_iff hM).2 (by simp)

variable (M p) in
/-- The normalized décalage `E_p(M)` of a cochain complex of abelian groups on whose terms
multiplication by `p` is injective: the elements `x` with `d x` divisible by `p`, with
differential `x ↦ d x / p`. -/
noncomputable abbrev normalizedDecalage : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.of (fun n ↦ AddCommGrpCat.of (M.decalageAddSubgroup p n))
    (fun n ↦ AddCommGrpCat.ofHom (decalageD hM n))
    (fun n ↦ by ext1; exact decalageD_comp_decalageD hM n)

lemma normalizedDecalage_d_apply (n : ℤ) (x : M.decalageAddSubgroup p n) :
    ((M.normalizedDecalage p hM).d n (n + 1)).hom x = decalageD hM n x := by
  simp only [normalizedDecalage, CochainComplex.of_d, AddCommGrpCat.hom_ofHom]

/-- The differential of `E_p(M)` multiplied by `p` is the differential of `M`. -/
lemma smul_normalizedDecalage_d (n : ℤ) (x : M.decalageAddSubgroup p n) :
    p • Subtype.val (((M.normalizedDecalage p hM).d n (n + 1)).hom x) =
      (M.d n (n + 1)).hom x := by
  rw [normalizedDecalage_d_apply, smul_decalageD]

section Map

variable {N : CochainComplex AddCommGrpCat.{u} ℤ} (hN : ∀ n, IsSMulRegular (N.X n) p)

/-- A cochain map sends `E_p(M)` into `E_p(N)`. -/
lemma map_mem_decalageAddSubgroup (φ : M ⟶ N) {n : ℤ} {x : M.X n}
    (hx : x ∈ M.decalageAddSubgroup p n) : (φ.f n).hom x ∈ N.decalageAddSubgroup p n := by
  obtain ⟨y, hy⟩ := (M.mem_decalageAddSubgroup_iff p).1 hx
  refine (N.mem_decalageAddSubgroup_iff p).2 ⟨(φ.f (n + 1)).hom y, ?_⟩
  rw [← map_nsmul, hy, ← AddCommGrpCat.comp_apply, ← φ.comm, AddCommGrpCat.comp_apply]

/-- The degree-`n` component of `normalizedDecalageMap`. -/
private noncomputable def normalizedDecalageMapF (φ : M ⟶ N) (n : ℤ) :
    (M.normalizedDecalage p hM).X n ⟶ (N.normalizedDecalage p hN).X n :=
  AddCommGrpCat.ofHom
    (((φ.f n).hom.comp (M.decalageAddSubgroup p n).subtype).codRestrict _
      fun x ↦ map_mem_decalageAddSubgroup φ x.property)

private lemma normalizedDecalageMapF_apply (φ : M ⟶ N) (n : ℤ)
    (x : (M.normalizedDecalage p hM).X n) :
    Subtype.val ((normalizedDecalageMapF hM hN φ n).hom x) = (φ.f n).hom x.val :=
  rfl

/-- The cochain map `E_p(M) ⟶ E_p(N)` induced by a cochain map `M ⟶ N`: it is `φ` on
elements. -/
noncomputable def normalizedDecalageMap (φ : M ⟶ N) :
    M.normalizedDecalage p hM ⟶ N.normalizedDecalage p hN :=
  CochainComplex.ofHom (normalizedDecalageMapF hM hN φ) fun n ↦ by
    ext x
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    rw [normalizedDecalage_d_apply, decalageD_eq_iff, normalizedDecalageMapF_apply,
      normalizedDecalageMapF_apply, ← map_nsmul, smul_normalizedDecalage_d,
      ← AddCommGrpCat.comp_apply, ← φ.comm, AddCommGrpCat.comp_apply]

@[simp]
lemma normalizedDecalageMap_f_apply (φ : M ⟶ N) (n : ℤ) (x : M.decalageAddSubgroup p n) :
    Subtype.val (((normalizedDecalageMap hM hN φ).f n).hom x) = (φ.f n).hom x :=
  (rfl)

@[simp]
lemma normalizedDecalageMap_id : normalizedDecalageMap hM hM (𝟙 M) = 𝟙 _ := by
  ext n x
  rfl

@[simp]
lemma normalizedDecalageMap_comp {K : CochainComplex AddCommGrpCat.{u} ℤ}
    (hK : ∀ n, IsSMulRegular (K.X n) p) (φ : M ⟶ N) (ψ : N ⟶ K) :
    normalizedDecalageMap hM hK (φ ≫ ψ) =
      normalizedDecalageMap hM hN φ ≫ normalizedDecalageMap hN hK ψ := by
  ext n x
  rfl

end Map

end CochainComplex
