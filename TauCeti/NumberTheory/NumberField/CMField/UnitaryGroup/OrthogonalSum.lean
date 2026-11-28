/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.OrthogonalSum
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame

/-!
# Orthogonal sums and reindexing of hermitian spaces with an adelic frame

Let `E` be a CM field. A hermitian space with an adelic frame of signs `s` on a finite index set
`ι` (`TauCeti.FramedHermitianSpace E s`) is a pair `V = (J, x)` of a Gram matrix `J ∈ M_ι(E)` and
an adelic frame `x ∈ GL_ι(E_∞) × GL_ι(𝔸_f)` with `x* J x = diag(s)` at the infinite places and
`x* J x = 1` at the finite places. This file builds new spaces from old ones.

* The **orthogonal sum** `V ⊕ V′` of spaces of signs `s` on `ι` and `s′` on `κ` is the space of
  signs `Sum.elim s s′` on `ι ⊕ κ` with the block-diagonal Gram matrix `diag(J, J′)` and the
  block-diagonal frame `diag(x, x′)`: congruence by a block-diagonal matrix acts blockwise, and
  the concatenated sign matrix is `diag(diag(s), diag(s′))`.
* The **reindexing** of `V` along `e : ι ≃ κ` is the space of signs `s ∘ e.symm` on `κ` whose
  Gram matrix and frame are those of `V` with rows and columns reindexed along `e`.

The adelic unitary groups follow: `(g, g′) ↦ diag(g, g′)` embeds `G(s) × G(s′)` in
`G(Sum.elim s s′)` (`TauCeti.adelicUnitaryGroup.sumHom`), and reindexing identifies `G(s)` with
`G(s ∘ e.symm)` (`TauCeti.adelicUnitaryGroup.reindexEquiv`). Both constructions are compatible
with the moved spaces, the lattices and the rational points:
`V · g ⊕ V′ · g′ = (V ⊕ V′) · diag(g, g′)`, the lattice of `V ⊕ V′` is the product of the lattices,
and `diag(γ, γ′)` is a rational point of `V ⊕ V′` for rational points `γ` of `V` and `γ′` of `V′`;
reindexing carries the lattice and the rational points of `V` onto those of the reindexed space.

Orthogonal sums are how split spaces are assembled from hyperbolic planes and a core, and how the
doubled space `V ⊕ V⁻` of the doubling method is formed; reindexing reorders the coordinates of
such sums.

## Main definitions

* `TauCeti.adelicUnitaryGroup.sumHom E s s'`: the block-diagonal embedding
  `G(s) × G(s′) →* G(Sum.elim s s′)`.
* `TauCeti.adelicUnitaryGroup.reindexEquiv E e s`: the isomorphism `G(s) ≃* G(s ∘ e.symm)`.
* `TauCeti.FramedHermitianSpace.sum V V'`: the orthogonal sum `V ⊕ V′`.
* `TauCeti.FramedHermitianSpace.reindex e V`: the reindexing of `V` along `e`.

## Main results

* `TauCeti.adelicUnitaryGroup.fromBlocksGL_mem_iff`: `(diag(g_∞, g′_∞), diag(g_f, g′_f))` lies in
  `G(Sum.elim s s′)` exactly when `g ∈ G(s)` and `g′ ∈ G(s′)`, and
  `TauCeti.adelicUnitaryGroup.reindexGL_mem_iff`: the reindexing of `g` lies in `G(s ∘ e.symm)`
  exactly when `g ∈ G(s)`.
* `TauCeti.adelicUnitaryGroup.sumHom_injective`: the block-diagonal embedding is injective.
* `TauCeti.FramedHermitianSpace.sum_smul`, `TauCeti.FramedHermitianSpace.reindex_smul`: sums and
  reindexing commute with moving spaces.
* `TauCeti.FramedHermitianSpace.mem_lattice_sum_iff`: `Λ_{V ⊕ V′} = Λ_V × Λ_{V′}`, and
  `TauCeti.FramedHermitianSpace.mem_lattice_reindex_iff`: the lattice of the reindexed space.
* `TauCeti.FramedHermitianSpace.rationalEmbedding_sum`,
  `TauCeti.FramedHermitianSpace.map_sumHom_prod_rationalPoints_le`: the block-diagonal rational
  points of `V ⊕ V′`.
* `TauCeti.FramedHermitianSpace.rationalEmbedding_reindex`,
  `TauCeti.FramedHermitianSpace.rationalPoints_reindex`: the rational points of the reindexed space.

## Attribution

The sum and the reindexing of spaces with an adelic frame are those of `New.Space.sum` and
`New.Space.reindex` in the file `src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι κ : Type*} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Block-diagonal and reindexed elements of the adelic unitary groups -/

namespace adelicUnitaryGroup

/-- **Block-diagonal elements of `G(Sum.elim s s′)`.** A pair of block-diagonal invertible matrices
`(diag(g_∞, g′_∞), diag(g_f, g′_f))` lies in `G(Sum.elim s s′)` exactly when `(g_∞, g_f) ∈ G(s)`
and `(g′_∞, g′_f) ∈ G(s′)`. -/
theorem fromBlocksGL_mem_iff {s : ι → ℤˣ} {s' : κ → ℤˣ}
    {g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]}
    {g' : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]} :
    (fromBlocksGL (g.1, g'.1), fromBlocksGL (g.2, g'.2)) ∈ adelicUnitaryGroup E (Sum.elim s s') ↔
      g ∈ adelicUnitaryGroup E s ∧ g' ∈ adelicUnitaryGroup E s' := by
  simp only [Subgroup.mem_prod, infiniteAdelicUnitaryGroup,
    diagonal_comp_sumElim (fun u : ℤˣ ↦ ((u : ℤ) : InfiniteAdeleRing E)),
    fromBlocksGL_mem_unitaryGroupOf_iff, finiteAdelicUnitaryGroup, ← unitaryGroupOf_one,
    ← fromBlocks_one]
  exact and_and_and_comm

variable (E) in
/-- The **block-diagonal embedding** `(g, g′) ↦ (diag(g_∞, g′_∞), diag(g_f, g′_f))` of
`G(s) × G(s′)` in the adelic unitary group `G(Sum.elim s s′)` of the concatenated signs. -/
def sumHom (s : ι → ℤˣ) (s' : κ → ℤˣ) :
    adelicUnitaryGroup E s × adelicUnitaryGroup E s' →* adelicUnitaryGroup E (Sum.elim s s') :=
  MonoidHom.codRestrict
    ((fromBlocksGL.prodMap fromBlocksGL).comp
      ((MulEquiv.prodProdProdComm (GL ι (InfiniteAdeleRing E)) (GL ι 𝔸ᶠ[E])
        (GL κ (InfiniteAdeleRing E)) (GL κ 𝔸ᶠ[E])).toMonoidHom.comp
        ((adelicUnitaryGroup E s).subtype.prodMap (adelicUnitaryGroup E s').subtype)))
    _ fun g ↦ fromBlocksGL_mem_iff.2 ⟨g.1.property, g.2.property⟩

variable {s : ι → ℤˣ} {s' : κ → ℤˣ}

/-- The block-diagonal embedding is `(g, g′) ↦ (diag(g_∞, g′_∞), diag(g_f, g′_f))`. -/
@[simp]
theorem coe_sumHom (g : adelicUnitaryGroup E s × adelicUnitaryGroup E s') :
    (sumHom E s s' g : GL (ι ⊕ κ) (InfiniteAdeleRing E) × GL (ι ⊕ κ) 𝔸ᶠ[E]) =
      (fromBlocksGL ((g.1 : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1,
          (g.2 : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]).1),
        fromBlocksGL ((g.1 : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2,
          (g.2 : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]).2)) :=
  (rfl)

/-- The block-diagonal embedding `G(s) × G(s′) →* G(Sum.elim s s′)` is injective. -/
theorem sumHom_injective : Function.Injective (sumHom E s s') := by
  intro g h hgh
  rw [Subtype.ext_iff, coe_sumHom, coe_sumHom, Prod.mk.injEq] at hgh
  obtain ⟨h₁₁, h₂₁⟩ := Prod.mk.inj (fromBlocksGL_injective hgh.1)
  obtain ⟨h₁₂, h₂₂⟩ := Prod.mk.inj (fromBlocksGL_injective hgh.2)
  exact Prod.ext (Subtype.ext (Prod.ext h₁₁ h₁₂)) (Subtype.ext (Prod.ext h₂₁ h₂₂))

/-- **Reindexed elements of `G(s ∘ e.symm)`.** Reindexing a pair of invertible matrices along
`e : ι ≃ κ` gives an element of `G(s ∘ e.symm)` exactly when the pair lies in `G(s)`. -/
theorem reindexGL_mem_iff (e : ι ≃ κ) {g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]} :
    (e.reindexGL _ g.1, e.reindexGL _ g.2) ∈ adelicUnitaryGroup E (s ∘ e.symm) ↔
      g ∈ adelicUnitaryGroup E s := by
  -- the sign matrix of `s ∘ e.symm` is the reindexed sign matrix of `s`
  have hs : (diagonal fun i ↦ (((s ∘ e.symm) i : ℤ) : InfiniteAdeleRing E)) =
      reindex e e (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) := by
    simp only [reindex_apply, submatrix_diagonal_equiv, Function.comp_def]
  rw [Subgroup.mem_prod, Subgroup.mem_prod, infiniteAdelicUnitaryGroup, hs,
    Equiv.reindexGL_mem_unitaryGroupOf_iff, finiteAdelicUnitaryGroup,
    ← Equiv.map_reindexGL_unitarySubgroup e, Equiv.mem_map_reindexGL_iff,
    Equiv.reindexGL_symm_apply_reindexGL]

variable (E) in
/-- The isomorphism `G(s) ≃* G(s ∘ e.symm)` reindexing both components of an adelic matrix along
`e : ι ≃ κ`; its inverse reindexes along `e.symm`. -/
def reindexEquiv (e : ι ≃ κ) (s : ι → ℤˣ) :
    adelicUnitaryGroup E s ≃* adelicUnitaryGroup E (s ∘ e.symm) :=
  MonoidHom.toMulEquiv
    ((((e.reindexGL (InfiniteAdeleRing E)).toMonoidHom.prodMap
      (e.reindexGL 𝔸ᶠ[E]).toMonoidHom).comp (adelicUnitaryGroup E s).subtype).codRestrict _
        fun g ↦ (reindexGL_mem_iff e).2 g.property)
    ((((e.symm.reindexGL (InfiniteAdeleRing E)).toMonoidHom.prodMap
      (e.symm.reindexGL 𝔸ᶠ[E]).toMonoidHom).comp
        (adelicUnitaryGroup E (s ∘ e.symm)).subtype).codRestrict _
        fun g ↦ (reindexGL_mem_iff e).1 (by simp))
    (by ext g : 3 <;> simp) (by ext g : 3 <;> simp)

/-- `reindexEquiv E e s` reindexes both components along `e`. -/
@[simp]
theorem coe_reindexEquiv (e : ι ≃ κ) (g : adelicUnitaryGroup E s) :
    (reindexEquiv E e s g : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]) =
      (e.reindexGL _ (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1,
        e.reindexGL _ (g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2) :=
  (rfl)

/-- The inverse of `reindexEquiv E e s` reindexes both components along `e.symm`. -/
@[simp]
theorem coe_reindexEquiv_symm (e : ι ≃ κ) (g : adelicUnitaryGroup E (s ∘ e.symm)) :
    ((reindexEquiv E e s).symm g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]) =
      (e.symm.reindexGL _ (g : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]).1,
        e.symm.reindexGL _ (g : GL κ (InfiniteAdeleRing E) × GL κ 𝔸ᶠ[E]).2) :=
  (rfl)

end adelicUnitaryGroup

/-! ### Orthogonal sums of spaces -/

namespace FramedHermitianSpace

variable {s : ι → ℤˣ} {s' : κ → ℤˣ}

/-- The **orthogonal sum** `V ⊕ V′` of hermitian spaces with an adelic frame of signs `s` on `ι`
and `s′` on `κ`: the space of signs `Sum.elim s s′` on `ι ⊕ κ` with the block-diagonal Gram matrix
`diag(J, J′)` and the block-diagonal frame `diag(x, x′)`. -/
def sum (V : FramedHermitianSpace E s) (V' : FramedHermitianSpace E s') :
    FramedHermitianSpace E (Sum.elim s s') where
  gram := fromBlocks V.gram 0 0 V'.gram
  frame := (fromBlocksGL (V.frame.1, V'.frame.1), fromBlocksGL (V.frame.2, V'.frame.2))
  -- congruence by `diag(x, x′)` is blockwise, and the blocks are the frame equations of `V`, `V′`
  star_mul_gram_mul_fst := by
    simp only [coe_fromBlocksGL, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      star_eq_conjTranspose, conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks]
    rw [← star_eq_conjTranspose, ← star_eq_conjTranspose, V.star_mul_gram_mul_fst,
      V'.star_mul_gram_mul_fst,
      diagonal_comp_sumElim (fun u : ℤˣ ↦ ((u : ℤ) : InfiniteAdeleRing E))]
  star_mul_gram_mul_snd := by
    simp only [coe_fromBlocksGL, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      star_eq_conjTranspose, conjTranspose_fromBlocks_mul_fromBlocks_mul_fromBlocks]
    rw [← star_eq_conjTranspose, ← star_eq_conjTranspose, V.star_mul_gram_mul_snd,
      V'.star_mul_gram_mul_snd, fromBlocks_one]

variable (V : FramedHermitianSpace E s) (V' : FramedHermitianSpace E s')

/-- The Gram matrix of `V ⊕ V′` is `diag(J, J′)`. -/
@[simp]
theorem gram_sum : (V.sum V').gram = fromBlocks V.gram 0 0 V'.gram :=
  (rfl)

/-- The frame of `V ⊕ V′` is `diag(x, x′)`, in both components. -/
@[simp]
theorem frame_sum :
    (V.sum V').frame =
      (fromBlocksGL (V.frame.1, V'.frame.1), fromBlocksGL (V.frame.2, V'.frame.2)) :=
  (rfl)

/-- **Moving an orthogonal sum blockwise**: `(V ⊕ V′) · diag(g, g′) = V · g ⊕ V′ · g′`. -/
theorem sum_smul (g : adelicUnitaryGroup E s) (g' : adelicUnitaryGroup E s') :
    MulOpposite.op (adelicUnitaryGroup.sumHom E s s' (g, g')) • V.sum V' =
      (MulOpposite.op g • V).sum (MulOpposite.op g' • V') := by
  refine FramedHermitianSpace.ext rfl ?_
  simp only [frame_smul, frame_sum, MulOpposite.unop_op, adelicUnitaryGroup.coe_sumHom,
    Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul, ← map_mul]

/-- **The lattice of an orthogonal sum is the product of the lattices**: `y ∈ Λ_{V ⊕ V′}` exactly
when its components on `ι` and on `κ` lie in `Λ_V` and in `Λ_{V′}`. -/
theorem mem_lattice_sum_iff {y : ι ⊕ κ → E} :
    y ∈ (V.sum V').lattice ↔ y ∘ Sum.inl ∈ V.lattice ∧ y ∘ Sum.inr ∈ V'.lattice := by
  simp only [mem_lattice_iff, frame_sum, ← map_inv, Prod.inv_mk, coe_fromBlocksGL,
    fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Function.comp_assoc]

/-- **Block-diagonal rational points of an orthogonal sum**: if `δ ∈ U(diag(J, J′))` is the
block-diagonal matrix `diag(γ, γ′)` of `γ ∈ U(J)` and `γ′ ∈ U(J′)`, its rational embedding in
`G(Sum.elim s s′)` is the block-diagonal element of the rational embeddings of `γ` and `γ′`:
`diag(x, x′)⁻¹ diag(γ, γ′) diag(x, x′) = diag(x⁻¹ γ x, x′⁻¹ γ′ x′)`. -/
theorem rationalEmbedding_sum {δ : unitaryGroupOf (V.sum V').gram} {γ : unitaryGroupOf V.gram}
    {γ' : unitaryGroupOf V'.gram} (hδ : (δ : GL (ι ⊕ κ) E) = fromBlocksGL ((γ : GL ι E), γ')) :
    (V.sum V').rationalEmbedding δ =
      adelicUnitaryGroup.sumHom E s s' (V.rationalEmbedding γ, V'.rationalEmbedding γ') := by
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
  simp only [coe_rationalEmbedding, frame_sum, hδ, RingHom.map_fromBlocksGL,
    adelicUnitaryGroup.coe_sumHom, ← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk]

/-- The block-diagonal elements `diag(γ, γ′)` with `γ ∈ Γ_V` and `γ′ ∈ Γ_{V′}` are rational points
of `V ⊕ V′`. -/
theorem map_sumHom_prod_rationalPoints_le :
    (V.rationalPoints.prod V'.rationalPoints).map (adelicUnitaryGroup.sumHom E s s') ≤
      (V.sum V').rationalPoints := by
  rw [rationalPoints_def, rationalPoints_def, rationalPoints_def]
  rintro _ ⟨⟨_, _⟩, ⟨⟨γ, rfl⟩, ⟨γ', rfl⟩⟩, rfl⟩
  have hδ : fromBlocksGL ((γ : GL ι E), (γ' : GL κ E)) ∈ unitaryGroupOf (V.sum V').gram := by
    rw [gram_sum]
    exact fromBlocksGL_mem_unitaryGroupOf_iff.2 ⟨γ.property, γ'.property⟩
  exact ⟨⟨_, hδ⟩, rationalEmbedding_sum V V' rfl⟩

/-! ### Reindexing spaces -/

/-- The **reindexing** of a hermitian space with an adelic frame along `e : ι ≃ κ`: the space of
signs `s ∘ e.symm` on `κ` whose Gram matrix and frame are those of `V` with rows and columns
reindexed along `e`. -/
def reindex (e : ι ≃ κ) (V : FramedHermitianSpace E s) : FramedHermitianSpace E (s ∘ e.symm) where
  gram := Matrix.reindex e e V.gram
  frame := (e.reindexGL _ V.frame.1, e.reindexGL _ V.frame.2)
  -- congruence commutes with reindexing, and the reindexed frame equations are those of `V`
  star_mul_gram_mul_fst := by
    rw [← reindex_map, Equiv.star_reindexGL_mul_reindex_mul_reindexGL, V.star_mul_gram_mul_fst,
      reindex_apply, submatrix_diagonal_equiv]
    simp only [Function.comp_def]
  star_mul_gram_mul_snd := by
    rw [← reindex_map, Equiv.star_reindexGL_mul_reindex_mul_reindexGL, V.star_mul_gram_mul_snd,
      reindex_apply, submatrix_one_equiv]

variable (e : ι ≃ κ)

/-- The Gram matrix of the reindexed space is the reindexed Gram matrix. -/
@[simp]
theorem gram_reindex : (V.reindex e).gram = Matrix.reindex e e V.gram :=
  (rfl)

/-- The frame of the reindexed space is the reindexed frame, in both components. -/
@[simp]
theorem frame_reindex : (V.reindex e).frame = (e.reindexGL _ V.frame.1, e.reindexGL _ V.frame.2) :=
  (rfl)

/-- **Reindexing commutes with moving spaces**: the reindexing of `V · g` is the reindexing of `V`
moved by the reindexing of `g`. -/
theorem reindex_smul (g : adelicUnitaryGroup E s) :
    MulOpposite.op (adelicUnitaryGroup.reindexEquiv E e s g) • V.reindex e =
      (MulOpposite.op g • V).reindex e := by
  refine FramedHermitianSpace.ext rfl ?_
  simp only [frame_smul, frame_reindex, MulOpposite.unop_op, adelicUnitaryGroup.coe_reindexEquiv,
    Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul, map_mul]

/-- **The lattice of a reindexed space**: `y ∈ Λ_{V.reindex e}` exactly when `y ∘ e ∈ Λ_V`. -/
theorem mem_lattice_reindex_iff {y : κ → E} : y ∈ (V.reindex e).lattice ↔ y ∘ e ∈ V.lattice := by
  simp only [mem_lattice_iff, frame_reindex, ← map_inv, Equiv.coe_reindexGL,
    submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_apply, Function.comp_assoc]
  exact ⟨fun h i ↦ by simpa using h (e i), fun h i ↦ h _⟩

/-- **Rational points of a reindexed space**: if `δ ∈ U(reindex e e J)` is the reindexing of
`γ ∈ U(J)`, its rational embedding is the reindexing of the rational embedding of `γ`. -/
theorem rationalEmbedding_reindex {δ : unitaryGroupOf (V.reindex e).gram}
    {γ : unitaryGroupOf V.gram} (hδ : (δ : GL κ E) = e.reindexGL E γ) :
    (V.reindex e).rationalEmbedding δ =
      adelicUnitaryGroup.reindexEquiv E e s (V.rationalEmbedding γ) := by
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
  simp only [coe_rationalEmbedding, frame_reindex, hδ, Equiv.map_reindexGL,
    adelicUnitaryGroup.coe_reindexEquiv, ← map_inv, ← map_mul]

/-- **The rational points of a reindexed space** are the reindexed rational points:
`Γ_{V.reindex e}` is the image of `Γ_V` under the reindexing `G(s) ≃* G(s ∘ e.symm)`. -/
theorem rationalPoints_reindex :
    (V.reindex e).rationalPoints =
      V.rationalPoints.map (adelicUnitaryGroup.reindexEquiv E e s).toMonoidHom := by
  rw [rationalPoints_def, rationalPoints_def]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨δ, rfl⟩
    -- `δ` is the reindexing of `γ = (e.symm).reindexGL δ ∈ U(J)`
    have hγ : e.symm.reindexGL E δ ∈ unitaryGroupOf V.gram := by
      rw [← Equiv.reindexGL_mem_unitaryGroupOf_iff (e := e), Equiv.reindexGL_apply_symm_reindexGL,
        ← gram_reindex]
      exact δ.property
    exact ⟨V.rationalEmbedding ⟨_, hγ⟩, ⟨_, rfl⟩,
      (V.rationalEmbedding_reindex e (Equiv.reindexGL_apply_symm_reindexGL e E δ).symm).symm⟩
  · rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    have hδ : e.reindexGL E γ ∈ unitaryGroupOf (V.reindex e).gram := by
      rw [gram_reindex, Equiv.reindexGL_mem_unitaryGroupOf_iff]
      exact γ.property
    exact ⟨⟨_, hδ⟩, V.rationalEmbedding_reindex e rfl⟩

end FramedHermitianSpace

end TauCeti
