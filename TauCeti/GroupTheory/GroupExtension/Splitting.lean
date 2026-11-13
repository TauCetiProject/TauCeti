/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Splittings, their ranges, and semidirect products

The range of a splitting complements the included kernel of an extension, and the range
determines the splitting uniquely. Equivalences of extensions transport splittings in both
directions, and a splitting identifies the middle group with the semidirect product of the kernel
and quotient by multiplying the included kernel factor with the section value. These results allow
splitting criteria to be interpreted as existence criteria for subgroup complements and semidirect
product decompositions.
-/

public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]
  {S : GroupExtension N E G}

@[simp]
theorem Splitting.toMonoidHom_apply (s : S.Splitting) (g : G) :
    s.toMonoidHom g = s g := (rfl)

/-- The equivalence from the semidirect product induced by a splitting multiplies the included
kernel element with the image of the quotient element under the splitting. -/
@[simp]
theorem Splitting.semidirectProductToGroupExtensionEquiv_apply (s : S.Splitting)
    (x : N ⋊[s.conjAct] G) :
    s.semidirectProductToGroupExtensionEquiv x = S.inl x.left * s x.right := (rfl)

/-- The multiplicative equivalence from the semidirect product induced by a splitting multiplies
the included kernel element with the image of the quotient element under the splitting. -/
@[simp]
theorem Splitting.semidirectProductMulEquiv_apply (s : S.Splitting) (x : N ⋊[s.conjAct] G) :
    s.semidirectProductMulEquiv x = S.inl x.left * s x.right := (rfl)

/-- The inverse semidirect-product equivalence sends an included kernel element to the left
factor. -/
@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_inl (s : S.Splitting) (n : N) :
    s.semidirectProductMulEquiv.symm (S.inl n) = SemidirectProduct.inl n := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- The inverse semidirect-product equivalence sends a splitting value to the right factor. -/
@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_splitting (s : S.Splitting) (g : G) :
    s.semidirectProductMulEquiv.symm (s g) = SemidirectProduct.inr g := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- The right component of the inverse semidirect-product equivalence is the extension
projection. -/
@[simp]
theorem Splitting.right_semidirectProductMulEquiv_symm (s : S.Splitting) (e : E) :
    (s.semidirectProductMulEquiv.symm e).right = S.rightHom e := (rfl)

/-- Including the left component of the inverse semidirect-product equivalence gives the kernel
remainder after dividing out the splitting value. -/
@[simp]
theorem Splitting.inl_left_semidirectProductMulEquiv_symm (s : S.Splitting) (e : E) :
    S.inl (s.semidirectProductMulEquiv.symm e).left = e * (s (S.rightHom e))⁻¹ := by
  have he := s.semidirectProductMulEquiv.apply_symm_apply e
  rw [semidirectProductMulEquiv_apply, right_semidirectProductMulEquiv_symm] at he
  exact eq_mul_inv_of_mul_eq he

/-- The range of a splitting is a complement of the included kernel. -/
theorem Splitting.isComplement'_range (s : S.Splitting) :
    S.inl.range.IsComplement' s.toMonoidHom.range := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hx, g, rfl⟩
    have hg : g = 1 := by
      simpa using (S.range_inl_eq_ker_rightHom ▸ hx : s g ∈ S.rightHom.ker)
    simp [hg]
  · apply Set.eq_univ_iff_forall.mpr
    intro e
    refine ⟨e * (s (S.rightHom e))⁻¹, ?_, s (S.rightHom e), ⟨_, rfl⟩, ?_⟩
    · rw [S.range_inl_eq_ker_rightHom]
      simp
    · simp

/-- Two splittings with the same range are equal. -/
theorem Splitting.eq_of_range_eq (s t : S.Splitting)
    (h : s.toMonoidHom.range = t.toMonoidHom.range) : s = t := by
  apply DFunLike.ext
  intro g
  have hg : s g ∈ t.toMonoidHom.range := h ▸ (⟨g, rfl⟩ : s g ∈ s.toMonoidHom.range)
  obtain ⟨g', hg'⟩ := hg
  have : g' = g := by
    simpa using congrArg S.rightHom hg'
  simpa [this] using hg'.symm

variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G}

/-- An equivalence of extensions induces a bijection on their splittings. -/
def Equiv.splittingEquiv (e : S.Equiv S') : S.Splitting ≃ S'.Splitting where
  toFun s :=
    { toMonoidHom := e.toMulEquiv.toMonoidHom.comp s.toMonoidHom
      rightInverse_rightHom g := by simp }
  invFun s :=
    { toMonoidHom := e.symm.toMulEquiv.toMonoidHom.comp s.toMonoidHom
      rightInverse_rightHom g := by simp }
  left_inv s := by
    apply DFunLike.ext
    intro g
    exact e.symm_apply_apply (s g)
  right_inv s := by
    apply DFunLike.ext
    intro g
    exact e.apply_symm_apply (s g)

@[simp]
theorem Equiv.splittingEquiv_apply (e : S.Equiv S') (s : S.Splitting) (g : G) :
    e.splittingEquiv s g = e (s g) := (rfl)

@[simp]
theorem Equiv.splittingEquiv_symm_apply (e : S.Equiv S') (s : S'.Splitting) (g : G) :
    e.splittingEquiv.symm s g = e.symm (s g) := (rfl)

/-- Equivalent extensions split simultaneously. -/
theorem Equiv.nonempty_splitting_iff (e : S.Equiv S') :
    Nonempty S.Splitting ↔ Nonempty S'.Splitting :=
  e.splittingEquiv.nonempty_congr

end GroupExtension
