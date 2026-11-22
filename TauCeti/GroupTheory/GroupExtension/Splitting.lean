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
determines the splitting uniquely. Equivalences of extensions and compatible multiplicative
equivalences on the middle and quotient groups transport splittings in both directions, as does
relabelling the kernel and quotient (`GroupExtension.splittingRelabelEquiv`,
`GroupExtension.Splitting.relabel`, `GroupExtension.nonempty_splitting_relabel_iff`). These results
allow splitting criteria to be
interpreted as existence criteria for actual subgroup complements. This file also supplies the
evaluation and inverse formulas for Mathlib's `GroupExtension.Splitting.semidirectProductMulEquiv`,
expressing the semidirect-product components of an extension element `e` in terms of
`S.rightHom e` and `e * (s (S.rightHom e))⁻¹`.
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

section MulEquiv

variable (S)

/-- Compatible multiplicative equivalences `(eE, eG)` on the middle and quotient groups of two
group extensions induce a bijection between their splittings, sending `s` to `eE ∘ s ∘ eG.symm`. -/
@[to_additive
  /-- Compatible additive equivalences `(eE, eG)` on the middle and quotient groups of two additive
  group extensions induce a bijection between their splittings, sending `s` to
  `eE ∘ s ∘ eG.symm`. -/]
def splittingEquivOfMulEquiv {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom) :
    S.Splitting ≃ S'.Splitting where
  toFun s :=
    { toMonoidHom := eE.toMonoidHom.comp ((s : G →* E).comp eG.symm.toMonoidHom)
      rightInverse_rightHom g' := by
        have h := DFunLike.congr_fun hright (s (eG.symm g'))
        simpa only [MonoidHom.toFun_eq_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MonoidHom.coe_ofClass, s.rightHom_splitting, eG.apply_symm_apply] using h }
  invFun s' :=
    { toMonoidHom := eE.symm.toMonoidHom.comp ((s' : G' →* E').comp eG.toMonoidHom)
      rightInverse_rightHom g := by
        simp only [MonoidHom.toFun_eq_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MonoidHom.coe_ofClass]
        have h := DFunLike.congr_fun hright (eE.symm (s' (eG g)))
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eE.apply_symm_apply,
          s'.rightHom_splitting] at h
        exact eG.injective h.symm }
  left_inv s := DFunLike.ext _ _ fun _ => by simp
  right_inv s' := DFunLike.ext _ _ fun _ => by simp

@[to_additive (attr := simp)]
theorem splittingEquivOfMulEquiv_apply {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom)
    (s : S.Splitting) (g' : G') :
    S.splittingEquivOfMulEquiv S' eE eG hright s g' = eE (s (eG.symm g')) :=
  (rfl)

@[to_additive (attr := simp)]
theorem splittingEquivOfMulEquiv_symm_apply {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom)
    (s' : S'.Splitting) (g : G) :
    (S.splittingEquivOfMulEquiv S' eE eG hright).symm s' g = eE.symm (s' (eG g)) :=
  (rfl)

end MulEquiv

section Relabel

variable {N' G' : Type*} [Group N'] [Group G']

/-- Relabelling a group extension induces a bijection on splittings, sending `s` to
`s.relabel eN eG`. -/
@[to_additive
  /-- Relabelling an additive group extension induces a bijection on splittings, sending `s` to
  `s.relabel eN eG`. -/]
def splittingRelabelEquiv (S : GroupExtension N E G) (eN : N' ≃* N) (eG : G ≃* G') :
    S.Splitting ≃ (S.relabel eN eG).Splitting :=
  S.splittingEquivOfMulEquiv (S.relabel eN eG) (MulEquiv.refl E) eG
    (DFunLike.ext _ _ fun _ ↦ by
      simp only [GroupExtension.relabel_rightHom, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply])

/-- Evaluating the forward relabelling equivalence on a splitting at `g'` evaluates the original
splitting at `eG.symm g'`. -/
@[to_additive (attr := simp)
  /-- Evaluating the forward relabelling equivalence on an additive splitting at `g'` evaluates the
  original splitting at `eG.symm g'`. -/]
theorem splittingRelabelEquiv_apply (S : GroupExtension N E G) (eN : N' ≃* N) (eG : G ≃* G')
    (s : S.Splitting) (g' : G') :
    S.splittingRelabelEquiv eN eG s g' = s (eG.symm g') := by
  rw [splittingRelabelEquiv, splittingEquivOfMulEquiv_apply, MulEquiv.refl_apply]

/-- Evaluating the inverse relabelling equivalence on a splitting at `g` evaluates the relabelled
splitting at `eG g`. -/
@[to_additive (attr := simp)
  /-- Evaluating the inverse relabelling equivalence on an additive splitting at `g` evaluates the
  relabelled splitting at `eG g`. -/]
theorem splittingRelabelEquiv_symm_apply (S : GroupExtension N E G) (eN : N' ≃* N)
    (eG : G ≃* G') (s' : (S.relabel eN eG).Splitting) (g : G) :
    (S.splittingRelabelEquiv eN eG).symm s' g = s' (eG g) := by
  rw [splittingRelabelEquiv, splittingEquivOfMulEquiv_symm_apply, MulEquiv.refl_symm,
    MulEquiv.refl_apply]

/-- Transport a splitting of `S` to a splitting of `S.relabel eN eG` by precomposing with
`eG.symm`. -/
@[to_additive
  /-- Transport a splitting of an additive extension `S` to a splitting of `S.relabel eN eG` by
  precomposing with `eG.symm`. -/]
def Splitting.relabel (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') :
    (S.relabel eN eG).Splitting :=
  S.splittingRelabelEquiv eN eG s

/-- Evaluating a relabelled splitting at `g'` evaluates the original splitting at `eG.symm g'`. -/
@[to_additive (attr := simp)
  /-- Evaluating a relabelled additive splitting at `g'` evaluates the original splitting at
  `eG.symm g'`. -/]
theorem Splitting.relabel_apply (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') (g' : G') :
    s.relabel eN eG g' = s (eG.symm g') :=
  S.splittingRelabelEquiv_apply eN eG s g'

/-- The underlying section of a relabelled splitting is the relabelled underlying section. -/
@[to_additive (attr := simp)
  /-- The underlying section of a relabelled additive splitting is the relabelled underlying
  section. -/]
theorem Splitting.relabel_toSection (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') :
    (s.relabel eN eG).toSection = s.toSection.relabel eN eG :=
  DFunLike.ext _ _ fun g' ↦
    (Splitting.relabel_apply s eN eG g').trans (Section.relabel_apply s.toSection eN eG g').symm

/-- A relabelled extension splits if and only if the original extension splits. -/
@[to_additive
  /-- A relabelled additive extension splits if and only if the original additive extension
  splits. -/]
theorem nonempty_splitting_relabel_iff (S : GroupExtension N E G) (eN : N' ≃* N) (eG : G ≃* G') :
    Nonempty (S.relabel eN eG).Splitting ↔ Nonempty S.Splitting :=
  (S.splittingRelabelEquiv eN eG).nonempty_congr.symm

end Relabel

end GroupExtension
