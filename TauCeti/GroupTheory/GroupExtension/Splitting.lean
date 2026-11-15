/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Complement

/-!
# Splittings and their ranges

The range of a splitting complements the included kernel of an extension, and the range
determines the splitting uniquely. Equivalences of extensions, relabellings of their outer terms,
and compatible multiplicative equivalences on the middle and quotient groups transport splittings
in both directions. These results allow splitting criteria to be interpreted as existence criteria
for actual subgroup complements.
-/

public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]
  {S : GroupExtension N E G}

@[to_additive (attr := simp)]
theorem Splitting.toMonoidHom_apply (s : S.Splitting) (g : G) :
    s.toMonoidHom g = s g := (rfl)

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
@[to_additive /-- An equivalence of additive extensions induces a bijection on their splittings. -/]
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

@[to_additive (attr := simp)]
theorem Equiv.splittingEquiv_apply (e : S.Equiv S') (s : S.Splitting) (g : G) :
    e.splittingEquiv s g = e (s g) := (rfl)

@[to_additive (attr := simp)]
theorem Equiv.splittingEquiv_symm_apply (e : S.Equiv S') (s : S'.Splitting) (g : G) :
    e.splittingEquiv.symm s g = e.symm (s g) := (rfl)

/-- Equivalent extensions split simultaneously. -/
@[to_additive /-- Equivalent additive extensions split simultaneously. -/]
theorem Equiv.nonempty_splitting_iff (e : S.Equiv S') :
    Nonempty S.Splitting ↔ Nonempty S'.Splitting :=
  e.splittingEquiv.nonempty_congr

section Relabel

variable (S)

/-- Relabelling the kernel does not change the projection, so splittings are unchanged. -/
@[to_additive
  /-- Relabelling the kernel of an additive extension does not change the projection, so splittings
  are unchanged. -/]
def Splitting.relabelKerEquiv {N' : Type*} [Group N'] (e : N' ≃* N) :
    S.Splitting ≃ (S.relabelKer e).Splitting where
  toFun s :=
    { toMonoidHom := s.toMonoidHom
      rightInverse_rightHom g := by simp }
  invFun s :=
    { toMonoidHom := s.toMonoidHom
      rightInverse_rightHom g := by simpa using s.rightHom_splitting g }
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]
theorem Splitting.relabelKerEquiv_apply {N' : Type*} [Group N'] (e : N' ≃* N) (s : S.Splitting)
    (g : G) : Splitting.relabelKerEquiv S e s g = s g :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelKerEquiv_symm_apply {N' : Type*} [Group N'] (e : N' ≃* N)
    (s : (S.relabelKer e).Splitting) (g : G) :
    (Splitting.relabelKerEquiv S e).symm s g = s g :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelKerEquiv_toSection {N' : Type*} [Group N'] (e : N' ≃* N)
    (s : S.Splitting) :
    (Splitting.relabelKerEquiv S e s).toSection = Section.relabelKerEquiv S e s.toSection :=
  DFunLike.ext _ _ fun _ => by simp

/-- Relabelling the quotient along `e : G ≃* G'` transports splittings by precomposition with
`e.symm`. -/
@[to_additive
  /-- Relabelling the quotient of an additive extension along `e : G ≃+ G'` transports splittings
  by precomposition with `e.symm`. -/]
def Splitting.relabelQuotientEquiv {G' : Type*} [Group G'] (e : G ≃* G') :
    S.Splitting ≃ (S.relabelQuotient e).Splitting where
  toFun s :=
    { toMonoidHom := s.toMonoidHom.comp e.symm.toMonoidHom
      rightInverse_rightHom g' := by simp }
  invFun s' :=
    { toMonoidHom := s'.toMonoidHom.comp e.toMonoidHom
      rightInverse_rightHom g := by
        have h := s'.rightHom_splitting (e g)
        rwa [relabelQuotient_rightHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          e.apply_eq_iff_eq] at h }
  left_inv s := DFunLike.ext _ _ fun g => congrArg s (e.symm_apply_apply g)
  right_inv s' := DFunLike.ext _ _ fun g' => congrArg s' (e.apply_symm_apply g')

@[to_additive (attr := simp)]
theorem Splitting.relabelQuotientEquiv_apply {G' : Type*} [Group G'] (e : G ≃* G')
    (s : S.Splitting) (g' : G') :
    Splitting.relabelQuotientEquiv S e s g' = s (e.symm g') :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelQuotientEquiv_symm_apply {G' : Type*} [Group G'] (e : G ≃* G')
    (s' : (S.relabelQuotient e).Splitting) (g : G) :
    (Splitting.relabelQuotientEquiv S e).symm s' g = s' (e g) :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelQuotientEquiv_toSection {G' : Type*} [Group G'] (e : G ≃* G')
    (s : S.Splitting) :
    (Splitting.relabelQuotientEquiv S e s).toSection =
      Section.relabelQuotientEquiv S e s.toSection :=
  DFunLike.ext _ _ fun _ => by simp

/-- Relabelling both outer terms transports splittings by precomposition with the inverse quotient
equivalence. -/
@[to_additive
  /-- Relabelling both outer terms of an additive extension transports splittings by precomposition
  with the inverse quotient equivalence. -/]
def Splitting.relabelEquiv {N' G' : Type*} [Group N'] [Group G'] (eN : N' ≃* N) (eG : G ≃* G') :
    S.Splitting ≃ (S.relabel eN eG).Splitting where
  toFun s :=
    { toMonoidHom := s.toMonoidHom.comp eG.symm.toMonoidHom
      rightInverse_rightHom g' := by simp }
  invFun s' :=
    { toMonoidHom := s'.toMonoidHom.comp eG.toMonoidHom
      rightInverse_rightHom g := by
        have h := s'.rightHom_splitting (eG g)
        rwa [relabel_rightHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          eG.apply_eq_iff_eq] at h }
  left_inv s := DFunLike.ext _ _ fun g => congrArg s (eG.symm_apply_apply g)
  right_inv s' := DFunLike.ext _ _ fun g' => congrArg s' (eG.apply_symm_apply g')

@[to_additive (attr := simp)]
theorem Splitting.relabelEquiv_apply {N' G' : Type*} [Group N'] [Group G'] (eN : N' ≃* N)
    (eG : G ≃* G') (s : S.Splitting) (g' : G') :
    Splitting.relabelEquiv S eN eG s g' = s (eG.symm g') :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelEquiv_symm_apply {N' G' : Type*} [Group N'] [Group G'] (eN : N' ≃* N)
    (eG : G ≃* G') (s' : (S.relabel eN eG).Splitting) (g : G) :
    (Splitting.relabelEquiv S eN eG).symm s' g = s' (eG g) :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.relabelEquiv_toSection {N' G' : Type*} [Group N'] [Group G'] (eN : N' ≃* N)
    (eG : G ≃* G') (s : S.Splitting) :
    (Splitting.relabelEquiv S eN eG s).toSection = Section.relabelEquiv S eN eG s.toSection :=
  DFunLike.ext _ _ fun _ => by simp

/-- Relabelling outer terms preserves existence of a splitting. -/
@[to_additive (attr := simp)
  /-- Relabelling outer terms of an additive extension preserves existence of a splitting. -/]
theorem nonempty_splitting_relabel_iff {N' G' : Type*} [Group N'] [Group G'] (eN : N' ≃* N)
    (eG : G ≃* G') : Nonempty (S.relabel eN eG).Splitting ↔ Nonempty S.Splitting :=
  (Splitting.relabelEquiv S eN eG).symm.nonempty_congr

/-- Compatible multiplicative equivalences `(eE, eG)` on the middle and quotient groups of two
group extensions induce a bijection between their splittings, sending `s` to `eE ∘ s ∘ eG.symm`. -/
@[to_additive
  /-- Compatible additive equivalences `(eE, eG)` on the middle and quotient groups of two additive
  group extensions induce a bijection between their splittings, sending `s` to
  `eE ∘ s ∘ eG.symm`. -/]
def Splitting.equivOfMulEquiv {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom) :
    S.Splitting ≃ S'.Splitting where
  toFun s :=
    { toMonoidHom := eE.toMonoidHom.comp (s.toMonoidHom.comp eG.symm.toMonoidHom)
      rightInverse_rightHom g' := by
        have h := DFunLike.congr_fun hright (s (eG.symm g'))
        simpa only [MonoidHom.toFun_eq_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          Splitting.toMonoidHom_apply, s.rightHom_splitting, eG.apply_symm_apply] using h }
  invFun s' :=
    { toMonoidHom := eE.symm.toMonoidHom.comp (s'.toMonoidHom.comp eG.toMonoidHom)
      rightInverse_rightHom g := by
        simp only [MonoidHom.toFun_eq_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          Splitting.toMonoidHom_apply]
        have h := DFunLike.congr_fun hright (eE.symm (s' (eG g)))
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eE.apply_symm_apply,
          s'.rightHom_splitting] at h
        exact eG.injective h.symm }
  left_inv s := DFunLike.ext _ _ fun _ => by simp
  right_inv s' := DFunLike.ext _ _ fun _ => by simp

@[to_additive (attr := simp)]
theorem Splitting.equivOfMulEquiv_apply {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom)
    (s : S.Splitting) (g' : G') :
    Splitting.equivOfMulEquiv S S' eE eG hright s g' = eE (s (eG.symm g')) :=
  (rfl)

@[to_additive (attr := simp)]
theorem Splitting.equivOfMulEquiv_symm_apply {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom)
    (s' : S'.Splitting) (g : G) :
    (Splitting.equivOfMulEquiv S S' eE eG hright).symm s' g = eE.symm (s' (eG g)) :=
  (rfl)

/-- Group extensions related by compatible multiplicative equivalences on their middle and quotient
groups split simultaneously. -/
@[to_additive
  /-- Additive group extensions related by compatible additive equivalences on their middle and
  quotient groups split simultaneously. -/]
theorem nonempty_splitting_iff_of_mulEquiv {N' E' G' : Type*} [Group N'] [Group E'] [Group G']
    (S' : GroupExtension N' E' G') (eE : E ≃* E') (eG : G ≃* G')
    (hright : S'.rightHom.comp eE.toMonoidHom = eG.toMonoidHom.comp S.rightHom) :
    Nonempty S.Splitting ↔ Nonempty S'.Splitting :=
  (Splitting.equivOfMulEquiv S S' eE eG hright).nonempty_congr

end Relabel

end GroupExtension
