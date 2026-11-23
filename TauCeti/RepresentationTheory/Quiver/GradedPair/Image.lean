/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.GradedPair.Shift
import TauCeti.Algebra.DirectSum.Internal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual image pairs of raising and lowering operators

The image of a raising or lowering pair `P = (V, T)` is the pair obtained by restricting `T` to
its **actual** range `LinearMap.range T`, graded by the intersections `range T ∩ Vₐ`. Since pairs
live on coordinate spaces, an image is recorded by a coordinate model: a
`TauCeti.GradedPair.SubmoduleModel P W` is a pair on a coordinate graded space together with an
injective linear embedding onto the submodule `W` which preserves grade membership in both
directions and intertwines the two operators. An image model `TauCeti.GradedPair.ImageModel P`
is a model of `LinearMap.range P.operator`.

Every graded `T`-stable submodule has a model
(`TauCeti.GradedPair.nonempty_submoduleModel`), and any two models of the same submodule carry
graded-isomorphic pairs (`TauCeti.GradedPair.SubmoduleModel.isomorphic`). The range of `T` is
such a submodule, so every pair has a chosen image model `TauCeti.GradedPair.imageModel`.
Iterating this construction gives `TauCeti.GradedPair.iteratedImage P k`, a model of the actual
range of `T ^ k`: the zeroth one is the pair itself, and the `(k + 1)`-st is the chosen image of
the `k`-th, embedded through it.

## Main definitions

* `TauCeti.GradedPair.SubmoduleModel P W`: a coordinate model of the restriction of `P` to `W`.
* `TauCeti.GradedPair.ImageModel P`: a coordinate model of the actual image of `P`.
* `TauCeti.GradedPair.imageModel P`: a chosen image model.
* `TauCeti.GradedPair.SubmoduleModel.image`: the image model of a model of `W`, embedded onto
  `W.map P.operator`.
* `TauCeti.GradedPair.iteratedImage P k`: the `k`-th iterated image, embedded onto the range of
  `P.operator ^ k`.

## Main results

* `TauCeti.GradedPair.nonempty_submoduleModel`: a submodule spanned by its intersections with the
  grades and stable under the operator has a coordinate model.
* `TauCeti.GradedPair.SubmoduleModel.map_grade`: a model maps each of its grades onto the
  corresponding grade intersection `W ⊓ S.grade a`.
* `TauCeti.GradedPair.SubmoduleModel.isomorphic`: models of the same submodule are
  graded-isomorphic.
* `TauCeti.GradedPair.SubmoduleModel.n_eq_zero_iff`: a model is zero-dimensional exactly when
  its submodule is zero; in particular images of zero operators are zero
  (`TauCeti.GradedPair.ImageModel.n_eq_zero_iff`).
* `TauCeti.GradedPair.exists_iteratedImage_n_eq_zero`: iterated images eventually vanish.
* `TauCeti.GradedPair.isomorphic_shift_imageModel`: the shift of the image of a pair is
  isomorphic to the image of the shifted pair.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1 and Lemma 3.3.
-/

public section

open Module

namespace TauCeti

namespace GradedPair

variable {S : GradedCoordSpace} {d : StepDirection}

/-- A coordinate model of the restriction of the pair `P` to the submodule `W`: a pair on a
coordinate graded space with an injective linear embedding onto `W`, which preserves grade
membership in both directions and intertwines the two operators. -/
structure SubmoduleModel (P : GradedPair S d) (W : Submodule ℂ S.Carrier) where
  /-- The coordinate graded space of the model. -/
  space : GradedCoordSpace
  /-- The restricted operator, as a pair on `space`. -/
  pair : GradedPair space d
  /-- The embedding of the model into the ambient space. -/
  embed : space.Carrier →ₗ[ℂ] S.Carrier
  /-- The embedding is injective. -/
  embed_injective : Function.Injective embed
  /-- The embedding is onto `W`. -/
  range_embed : LinearMap.range embed = W
  /-- The embedding preserves grade membership in both directions. -/
  embed_mem_grade_iff {a : ℤ} {v : space.Carrier} : embed v ∈ S.grade a ↔ v ∈ space.grade a
  /-- The embedding intertwines the operators. -/
  embed_operator (v : space.Carrier) : embed (pair.operator v) = P.operator (embed v)

/-- An image model of a pair: a coordinate model of the actual range of its operator. -/
abbrev ImageModel (P : GradedPair S d) : Type :=
  P.SubmoduleModel (LinearMap.range P.operator)

attribute [simp] SubmoduleModel.embed_mem_grade_iff SubmoduleModel.embed_operator

/-- A pair is a model of its restriction to the whole space, with the identity embedding. -/
@[expose] def topModel (P : GradedPair S d) : P.SubmoduleModel ⊤ where
  space := S
  pair := P
  embed := LinearMap.id
  embed_injective := Function.injective_id
  range_embed := LinearMap.range_id
  embed_mem_grade_iff := Iff.rfl
  embed_operator _ := rfl

namespace SubmoduleModel

variable {P : GradedPair S d} {W W' : Submodule ℂ S.Carrier}

/-- The embedding of a model takes values in its submodule. -/
theorem embed_mem (M : P.SubmoduleModel W) (v : M.space.Carrier) : M.embed v ∈ W :=
  M.range_embed.le (LinearMap.mem_range_self M.embed v)

/-- The submodule of a model consists exactly of the embedded vectors. -/
theorem mem_iff_exists_embed_eq (M : P.SubmoduleModel W) {w : S.Carrier} :
    w ∈ W ↔ ∃ v, M.embed v = w :=
  ⟨fun hw ↦ LinearMap.mem_range.1 (M.range_embed.ge hw), fun ⟨v, hv⟩ ↦ hv ▸ M.embed_mem v⟩

/-- Transport a model along an equality of submodules. -/
@[expose] def congr (M : P.SubmoduleModel W) (h : W = W') : P.SubmoduleModel W' where
  space := M.space
  pair := M.pair
  embed := M.embed
  embed_injective := M.embed_injective
  range_embed := M.range_embed.trans h
  embed_mem_grade_iff := M.embed_mem_grade_iff
  embed_operator := M.embed_operator

/-- The linear equivalence between the carrier of a model and its submodule. -/
noncomputable def equiv (M : P.SubmoduleModel W) : M.space.Carrier ≃ₗ[ℂ] W :=
  (LinearEquiv.ofInjective M.embed M.embed_injective).trans (LinearEquiv.ofEq _ _ M.range_embed)

@[simp]
theorem coe_equiv_apply (M : P.SubmoduleModel W) (v : M.space.Carrier) :
    (M.equiv v : S.Carrier) = M.embed v :=
  (rfl)

@[simp]
theorem embed_equiv_symm_apply (M : P.SubmoduleModel W) (w : W) :
    M.embed (M.equiv.symm w) = w := by
  rw [← coe_equiv_apply, LinearEquiv.apply_symm_apply]

/-- A model maps each of its grades onto the corresponding grade of its submodule. -/
theorem map_grade (M : P.SubmoduleModel W) (a : ℤ) :
    (M.space.grade a).map M.embed = W ⊓ S.grade a := by
  ext w
  refine ⟨?_, fun ⟨hw, hwa⟩ ↦ ?_⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨M.embed_mem v, M.embed_mem_grade_iff.2 hv⟩
  · obtain ⟨v, rfl⟩ := M.mem_iff_exists_embed_eq.1 hw
    exact ⟨v, M.embed_mem_grade_iff.1 hwa, rfl⟩

/-- The grades of a model have the dimensions of the grade intersections of its submodule. -/
theorem finrank_grade (M : P.SubmoduleModel W) (a : ℤ) :
    finrank ℂ (M.space.grade a) = finrank ℂ ↥(W ⊓ S.grade a) := by
  rw [← M.map_grade, (Submodule.equivMapOfInjective _ M.embed_injective _).finrank_eq]

/-- The total dimension of a model is the dimension of its submodule. -/
theorem n_eq_finrank (M : P.SubmoduleModel W) : M.space.n = finrank ℂ W := by
  rw [← M.equiv.finrank_eq, Module.finrank_fin_fun]

/-- A model is zero-dimensional exactly when its submodule is zero. -/
theorem n_eq_zero_iff (M : P.SubmoduleModel W) : M.space.n = 0 ↔ W = ⊥ := by
  rw [n_eq_finrank, Submodule.finrank_eq_zero]

/-- The linear equivalence between two models of the same submodule, through that submodule. -/
noncomputable def linearEquiv (M M' : P.SubmoduleModel W) :
    M.space.Carrier ≃ₗ[ℂ] M'.space.Carrier :=
  M.equiv.trans M'.equiv.symm

@[simp]
theorem embed_linearEquiv_apply (M M' : P.SubmoduleModel W) (v : M.space.Carrier) :
    M'.embed (M.linearEquiv M' v) = M.embed v := by
  simp [linearEquiv]

/-- Two models of the same submodule are related by the graded equivalence of pairs which
matches their embeddings. -/
noncomputable def gradedPairEquiv (M M' : P.SubmoduleModel W) :
    GradedPairEquiv M.pair M'.pair where
  toLinearEquiv := M.linearEquiv M'
  mem_grade_iff' a v := by
    rw [← M.embed_mem_grade_iff, ← M'.embed_mem_grade_iff, embed_linearEquiv_apply]
  map_operator' v := M'.embed_injective (by simp)

@[simp]
theorem embed_gradedPairEquiv_apply (M M' : P.SubmoduleModel W) (v : M.space.Carrier) :
    M'.embed (M.gradedPairEquiv M' v) = M.embed v :=
  M.embed_linearEquiv_apply M' v

/-- Models of the same submodule carry graded-isomorphic pairs. -/
theorem isomorphic (M M' : P.SubmoduleModel W) : M.pair.Isomorphic M'.pair :=
  (M.gradedPairEquiv M').isomorphic

/-- A model of a submodule `W'` of a model `M` of `W` gives a model of the image of `W'` under the
embedding of `M`. -/
@[expose] def comp (M : P.SubmoduleModel W) {W' : Submodule ℂ M.space.Carrier}
    (M' : M.pair.SubmoduleModel W') : P.SubmoduleModel (W'.map M.embed) where
  space := M'.space
  pair := M'.pair
  embed := M.embed ∘ₗ M'.embed
  embed_injective := M.embed_injective.comp M'.embed_injective
  range_embed := by rw [LinearMap.range_comp, M'.range_embed]
  embed_mem_grade_iff := by simp
  embed_operator v := by simp

/-- Shift a model of `W` by `c`: the shifted model pair embeds onto the same submodule for the
shifted pair. -/
@[expose] def shift (M : P.SubmoduleModel W) (c : ℤ) : (P.shift c).SubmoduleModel W where
  space := M.space.shift c
  pair := M.pair.shift c
  embed := M.embed
  embed_injective := M.embed_injective
  range_embed := M.range_embed
  embed_mem_grade_iff := by
    intro a v
    rw [GradedCoordSpace.mem_grade_shift, GradedCoordSpace.mem_grade_shift]
    exact M.embed_mem_grade_iff
  embed_operator v := by
    simp only [operator_shift]
    exact M.embed_operator v

/-- The embedding of a model carries the image of its operator onto the image of `W` under the
ambient operator. -/
theorem map_range_operator (M : P.SubmoduleModel W) :
    (LinearMap.range M.pair.operator).map M.embed = W.map P.operator := by
  have h : M.embed ∘ₗ M.pair.operator = P.operator ∘ₗ M.embed := LinearMap.ext M.embed_operator
  rw [← LinearMap.range_comp, h, LinearMap.range_comp, M.range_embed]

end SubmoduleModel

/-! ### Existence of models -/

/-- A submodule which is spanned by its intersections with the grades and which is stable under
the operator of a pair has a coordinate model. -/
theorem nonempty_submoduleModel (P : GradedPair S d) {W : Submodule ℂ S.Carrier}
    (hW : ⨆ a, W ⊓ S.grade a = W) (hPW : ∀ v ∈ W, P.operator v ∈ W) :
    Nonempty (P.SubmoduleModel W) := by
  classical
  have hint : DirectSum.IsInternal fun a ↦ (W ⊓ S.grade a).comap W.subtype :=
    DirectSum.isInternal_submodule_comap_subtype
      (S.isInternal_grade.submodule_iSupIndep.mono fun _ ↦ inf_le_right) hW
  obtain ⟨T, e, he⟩ := GradedCoordSpace.exists_linearEquiv_of_isInternal hint
  have hmem (a : ℤ) (w : W) : (w : S.Carrier) ∈ S.grade a ↔ e w ∈ T.grade a := by
    rw [← he]
    simp
  let R : Module.End ℂ T.Carrier :=
    e.toLinearMap ∘ₗ P.operator.restrict hPW ∘ₗ e.symm.toLinearMap
  have hR : LinearMap.IsHomogeneous R T.grade T.grade d.step := by
    refine LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_
    have hv' : ((e.symm v : W) : S.Carrier) ∈ S.grade a := by
      rw [hmem, LinearEquiv.apply_symm_apply]
      exact hv
    exact (hmem _ (P.operator.restrict hPW (e.symm v))).1 (P.isHomogeneous.map_mem hv')
  exact ⟨{
    space := T
    pair := ⟨R, hR⟩
    embed := W.subtype ∘ₗ e.symm.toLinearMap
    embed_injective := W.injective_subtype.comp e.symm.injective
    range_embed := by
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
    embed_mem_grade_iff := by
      intro a v
      simp [hmem]
    embed_operator := fun v ↦ by simp [R] }⟩

/-- The actual range of a pair is spanned by its intersections with the grades. -/
theorem iSup_range_inf_grade (P : GradedPair S d) :
    ⨆ a, LinearMap.range P.operator ⊓ S.grade a = LinearMap.range P.operator :=
  P.isHomogeneous.iSup_range_inf_eq S.isInternal_grade.submodule_iSup_eq_top

/-- Every pair has an image model. -/
theorem nonempty_imageModel (P : GradedPair S d) : Nonempty P.ImageModel :=
  P.nonempty_submoduleModel P.iSup_range_inf_grade fun v _ ↦ LinearMap.mem_range_self _ v

/-- A chosen coordinate model of the actual image of a pair. -/
noncomputable def imageModel (P : GradedPair S d) : P.ImageModel :=
  Classical.choice P.nonempty_imageModel

namespace ImageModel

variable {P : GradedPair S d}

/-- An image model is zero-dimensional exactly when the operator is zero. In particular the
image of a zero pair, such as a singleton or the empty pair, is zero. -/
theorem n_eq_zero_iff (M : P.ImageModel) : M.space.n = 0 ↔ P.operator = 0 := by
  rw [SubmoduleModel.n_eq_zero_iff, LinearMap.range_eq_bot]

end ImageModel

/-- The image model of the zero pair is zero-dimensional. -/
@[simp]
theorem imageModel_zero_n : (imageModel (0 : GradedPair S d)).space.n = 0 :=
  (ImageModel.n_eq_zero_iff _).2 rfl

/-- The image of a shifted pair is the shift of the image, up to graded isomorphism. -/
theorem isomorphic_shift_imageModel (P : GradedPair S d) (c : ℤ) :
    (P.imageModel.pair.shift c).Isomorphic (P.shift c).imageModel.pair :=
  SubmoduleModel.isomorphic ((P.imageModel.shift c).congr (by rw [operator_shift]))
    (P.shift c).imageModel

/-! ### Iterated images -/

namespace SubmoduleModel

variable {P : GradedPair S d} {W : Submodule ℂ S.Carrier}

/-- The image of a model of `W`: the chosen image model of its pair, embedded through `M` onto
`W.map P.operator`. -/
@[expose] noncomputable def image (M : P.SubmoduleModel W) : P.SubmoduleModel (W.map P.operator) :=
  (M.comp M.pair.imageModel).congr M.map_range_operator

/-- The image of a model carries the image pair of the model pair. -/
theorem isomorphic_image (M : P.SubmoduleModel W) :
    M.image.pair.Isomorphic M.pair.imageModel.pair :=
  Isomorphic.refl _

end SubmoduleModel

/-- The `k`-th iterated image of a pair: a coordinate model of the actual range of
`P.operator ^ k`. The zeroth one is the pair itself, and each next one is the image of the
previous one. -/
@[expose] noncomputable def iteratedImage (P : GradedPair S d) :
    (k : ℕ) → P.SubmoduleModel (LinearMap.range (P.operator ^ k))
  | 0 => P.topModel.congr (by rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id])
  | k + 1 => (P.iteratedImage k).image.congr (by
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp])

/-- The zeroth iterated image is the pair itself. -/
theorem isomorphic_iteratedImage_zero (P : GradedPair S d) :
    (P.iteratedImage 0).pair.Isomorphic P :=
  Isomorphic.refl _

/-- The `(k + 1)`-st iterated image is the image of the `k`-th. -/
theorem isomorphic_iteratedImage_succ (P : GradedPair S d) (k : ℕ) :
    (P.iteratedImage (k + 1)).pair.Isomorphic (P.iteratedImage k).pair.imageModel.pair :=
  Isomorphic.refl _

/-- The total dimension of the `k`-th iterated image is the rank of `P.operator ^ k`. -/
theorem iteratedImage_n (P : GradedPair S d) (k : ℕ) :
    (P.iteratedImage k).space.n = finrank ℂ (LinearMap.range (P.operator ^ k)) :=
  (P.iteratedImage k).n_eq_finrank

/-- The `k`-th iterated image is zero-dimensional exactly when `P.operator ^ k = 0`. -/
theorem iteratedImage_n_eq_zero_iff (P : GradedPair S d) (k : ℕ) :
    (P.iteratedImage k).space.n = 0 ↔ P.operator ^ k = 0 := by
  rw [SubmoduleModel.n_eq_zero_iff, LinearMap.range_eq_bot]

/-- Iterated images of a pair eventually vanish, since its operator is nilpotent. -/
theorem exists_iteratedImage_n_eq_zero (P : GradedPair S d) :
    ∃ k, (P.iteratedImage k).space.n = 0 := by
  obtain ⟨k, hk⟩ := P.isNilpotent
  exact ⟨k, (P.iteratedImage_n_eq_zero_iff k).2 hk⟩

/-- The `k`-th iterated image of a shifted pair is the shift of the `k`-th iterated image, up to
graded isomorphism. -/
theorem isomorphic_shift_iteratedImage (P : GradedPair S d) (c : ℤ) (k : ℕ) :
    ((P.iteratedImage k).pair.shift c).Isomorphic ((P.shift c).iteratedImage k).pair :=
  SubmoduleModel.isomorphic (((P.iteratedImage k).shift c).congr (by rw [operator_shift]))
    ((P.shift c).iteratedImage k)

end GradedPair

end TauCeti
