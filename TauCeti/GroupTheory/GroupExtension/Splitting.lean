/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Splittings, their ranges, and semidirect-product decompositions

The range of a splitting complements the included kernel of an extension, and the range
determines the splitting uniquely. Equivalences of extensions transport splittings in both
directions. This file also supplies the evaluation and inverse formulas for Mathlib's
`GroupExtension.Splitting.semidirectProductMulEquiv`, expressing the semidirect-product components
of an extension element `e` in terms of `S.rightHom e` and `e * (s (S.rightHom e))⁻¹`.
-/

public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]
  {S : GroupExtension N E G}

@[simp]
theorem Splitting.toMonoidHom_apply (s : S.Splitting) (g : G) :
    s.toMonoidHom g = s g := (rfl)

@[simp]
theorem Splitting.conjAct_apply (s : S.Splitting) (g : G) :
    s.conjAct g = S.conjAct (s g) := (rfl)

/-- Including the kernel intertwines `s.conjAct` with conjugation by `s g` in `E`. -/
theorem Splitting.inl_conjAct (s : S.Splitting) (g : G) (n : N) :
    S.inl (s.conjAct g n) = s g * S.inl n * (s g)⁻¹ := by
  rw [s.conjAct_apply, S.inl_conjAct_comm]

@[simp]
theorem Splitting.semidirectProductToGroupExtensionEquiv_apply (s : S.Splitting)
    (x : N ⋊[s.conjAct] G) :
    s.semidirectProductToGroupExtensionEquiv x = S.inl x.left * s x.right := by
  obtain ⟨n, g⟩ := x
  rfl

@[simp]
theorem Splitting.semidirectProductMulEquiv_apply (s : S.Splitting) (x : N ⋊[s.conjAct] G) :
    s.semidirectProductMulEquiv x = S.inl x.left * s x.right :=
  s.semidirectProductToGroupExtensionEquiv_apply x

theorem Splitting.semidirectProductMulEquiv_inl (s : S.Splitting) (n : N) :
    s.semidirectProductMulEquiv (SemidirectProduct.inl n) = S.inl n := by
  simp

theorem Splitting.semidirectProductMulEquiv_inr (s : S.Splitting) (g : G) :
    s.semidirectProductMulEquiv (SemidirectProduct.inr g) = s g := by
  simp

@[simp]
theorem Splitting.semidirectProductMulEquiv_comp_inl (s : S.Splitting) :
    (MonoidHom.ofClass s.semidirectProductMulEquiv).comp SemidirectProduct.inl = S.inl :=
  MonoidHom.ext s.semidirectProductMulEquiv_inl

@[simp]
theorem Splitting.semidirectProductMulEquiv_comp_inr (s : S.Splitting) :
    (MonoidHom.ofClass s.semidirectProductMulEquiv).comp SemidirectProduct.inr = s.toMonoidHom :=
  MonoidHom.ext s.semidirectProductMulEquiv_inr

/-- The right semidirect-product component under `s.semidirectProductMulEquiv.symm` is
`S.rightHom`. -/
@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_right (s : S.Splitting) (e : E) :
    (s.semidirectProductMulEquiv.symm e).right = S.rightHom e := by
  simpa using (congrArg S.rightHom
    (s.semidirectProductMulEquiv_apply (s.semidirectProductMulEquiv.symm e))).symm

@[simp]
theorem Splitting.rightHom_comp_semidirectProductMulEquiv_symm (s : S.Splitting) :
    SemidirectProduct.rightHom.comp (MonoidHom.ofClass s.semidirectProductMulEquiv.symm) =
      S.rightHom :=
  MonoidHom.ext s.semidirectProductMulEquiv_symm_right

/-- Including the left semidirect-product component of `s.semidirectProductMulEquiv.symm e` into
`E` gives `e * (s (S.rightHom e))⁻¹`. -/
@[simp]
theorem Splitting.inl_semidirectProductMulEquiv_symm_left (s : S.Splitting) (e : E) :
    S.inl (s.semidirectProductMulEquiv.symm e).left = e * (s (S.rightHom e))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← s.semidirectProductMulEquiv_symm_right,
    ← s.semidirectProductMulEquiv_apply, MulEquiv.apply_symm_apply]

@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_inl (s : S.Splitting) (n : N) :
    s.semidirectProductMulEquiv.symm (S.inl n) = SemidirectProduct.inl n :=
  (MulEquiv.symm_apply_eq _).mpr (s.semidirectProductMulEquiv_inl n).symm

@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_splitting (s : S.Splitting) (g : G) :
    s.semidirectProductMulEquiv.symm (s g) = SemidirectProduct.inr g :=
  (MulEquiv.symm_apply_eq _).mpr (s.semidirectProductMulEquiv_inr g).symm

@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_comp_inl (s : S.Splitting) :
    (MonoidHom.ofClass s.semidirectProductMulEquiv.symm).comp S.inl = SemidirectProduct.inl :=
  MonoidHom.ext s.semidirectProductMulEquiv_symm_inl

@[simp]
theorem Splitting.semidirectProductMulEquiv_symm_comp_toMonoidHom (s : S.Splitting) :
    (MonoidHom.ofClass s.semidirectProductMulEquiv.symm).comp s.toMonoidHom =
      SemidirectProduct.inr :=
  MonoidHom.ext s.semidirectProductMulEquiv_symm_splitting

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
