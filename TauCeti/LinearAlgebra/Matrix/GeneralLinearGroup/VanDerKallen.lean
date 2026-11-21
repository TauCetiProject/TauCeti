/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Van der Kallen's subgroups of the general linear group

For sets `P` and `Q` of indices, `TauCeti.vanDerKallenSubgroup R P Q` is the subgroup
`G^(P,Q)` of `GL n R` of the invertible matrices `g` that fix the standard basis columns `e_j`,
`j ∈ P`, and the standard basis rows `e_i*`, `i ∈ Q`:
`g e_j = e_j` and `e_i* g = e_i*`. Equivalently, the `j`-th column of `g` is that of the
identity matrix for `j ∈ P`, and the `i`-th row of `g` is that of the identity matrix for
`i ∈ Q`. These are the groups through which van der Kallen proves homology stability for the
general linear groups: each `G^(P,Q)` acts on a complex of unimodular frames, the stabiliser of a
standard frame is again a group of the same family, and the spectral sequences of these actions
carry an induction over the whole family. `G^(∅,∅)` is all of `GL n R`, and when `P = Q = T`
the group `G^(T,T)` is the general linear group of the coordinates outside `T`.

This file sets up the family and the facts about it that do not depend on the frame complexes:

* `G^(P,Q)` is antitone in `P` and `Q`, and `G^(P ∪ P', Q ∪ Q') = G^(P,Q) ⊓ G^(P',Q')`; in
  particular the square group `G^(P ∪ Q, P ∪ Q)` lies in `G^(P,Q)`;
* the stabiliser of the standard frame `(e_(f a))_a`, an `n × k` matrix acted on by left
  multiplication, is `G^(range f, ∅)`, and its stabiliser inside `G^(P,Q)` is
  `G^(P ∪ range f, Q)`;
* the inverse transpose `g ↦ (g⁻¹)ᵀ` exchanges `G^(P,Q)` and `G^(Q,P)`, which exchanges the
  frames of columns with the frames of rows;
* the stabilization `g ↦ diag(g, 1)` from `GL_m` to `GL_k` pulls `G_k^(P,Q)` back to the group of
  the same indices in `GL_m`, and so restricts to an injective homomorphism between them;
* `G^(T,T) ≃* GL Tᶜ R`, through the block diagonal matrices `diag(1, g)`.

## Main definitions

* `TauCeti.vanDerKallenSubgroup`: the subgroup `G^(P,Q)` of `GL n R`.
* `TauCeti.stabilizeVanDerKallen`: the upper inclusion `G_m^(P,Q) →* G_k^(P,Q)` along
  `TauCeti.stabilizeGL`, for `m ≤ k`.
* `TauCeti.vanDerKallenSubgroupEquiv`: the isomorphism `G^(T,T) ≃* GL Tᶜ R`.

## Main results

* `TauCeti.mem_vanDerKallenSubgroup_iff_apply`: membership in terms of matrix entries.
* `TauCeti.vanDerKallenSubgroup_union_union`: `G^(P ∪ P', Q ∪ Q') = G^(P,Q) ⊓ G^(P',Q')`.
* `TauCeti.stabilizer_submatrix_one`: the stabiliser in `GL n R` of a standard frame.
* `TauCeti.stabilizer_vanDerKallenSubgroup_submatrix_one`: the stabiliser of a standard frame
  in `G^(P,Q)` is `G^(P ∪ range f, Q)`.
* `TauCeti.map_inverseTranspose_vanDerKallenSubgroup`: the inverse transpose maps `G^(P,Q)`
  onto `G^(Q,P)`.
* `TauCeti.comap_stabilizeGL_vanDerKallenSubgroup`: the preimage of `G_k^(P,Q)` under the
  stabilization from `GL_m`.
* `TauCeti.range_blockComplGL`: the block diagonal matrices `diag(1, g)` form `G^(T,T)`.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  §3.2 (the groups `G_n(P,Q)`) and Examples 3.5 (their actions on frames and the stabilisers of
  standard frames).
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable (R : Type*) {n : Type*} [Fintype n] [DecidableEq n]

section Semiring

variable [Semiring R]

/-- **Van der Kallen's subgroup** `G^(P,Q)` of `GL n R`: the invertible matrices `g` fixing the
standard basis columns `e_j` for `j ∈ P` and the standard basis rows `e_i*` for `i ∈ Q`, that is,
`g e_j = e_j` and `e_i* g = e_i*`. -/
def vanDerKallenSubgroup (P Q : Set n) : Subgroup (GL n R) where
  carrier := {g | (∀ j ∈ P, (g : Matrix n n R) *ᵥ Pi.single j 1 = Pi.single j 1) ∧
    ∀ i ∈ Q, Pi.single i 1 ᵥ* (g : Matrix n n R) = Pi.single i 1}
  mul_mem' {g h} hg hh := by
    refine ⟨fun j hj ↦ ?_, fun i hi ↦ ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hh.1 j hj, hg.1 j hj]
    · rw [Units.val_mul, ← vecMul_vecMul, hg.2 i hi, hh.2 i hi]
  one_mem' := ⟨fun _ _ ↦ one_mulVec _, fun _ _ ↦ vecMul_one _⟩
  inv_mem' {g} hg := by
    refine ⟨fun j hj ↦ ?_, fun i hi ↦ ?_⟩
    · conv_lhs => rw [← hg.1 j hj, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mulVec]
    · conv_lhs => rw [← hg.2 i hi, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        vecMul_one]

variable {R}

/-- Membership in `G^(P,Q)`: `g e_j = e_j` for `j ∈ P` and `e_i* g = e_i*` for `i ∈ Q`. -/
@[simp]
theorem mem_vanDerKallenSubgroup_iff {P Q : Set n} {g : GL n R} :
    g ∈ vanDerKallenSubgroup R P Q ↔
      (∀ j ∈ P, (g : Matrix n n R) *ᵥ Pi.single j 1 = Pi.single j 1) ∧
        ∀ i ∈ Q, Pi.single i 1 ᵥ* (g : Matrix n n R) = Pi.single i 1 :=
  Iff.rfl

/-- Membership in `G^(P,Q)` in terms of entries: the columns indexed by `P` and the rows indexed
by `Q` are those of the identity matrix. -/
theorem mem_vanDerKallenSubgroup_iff_apply {P Q : Set n} {g : GL n R} :
    g ∈ vanDerKallenSubgroup R P Q ↔
      (∀ j ∈ P, ∀ i, (g : Matrix n n R) i j = (1 : Matrix n n R) i j) ∧
        ∀ i ∈ Q, ∀ j, (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  simp only [mem_vanDerKallenSubgroup_iff, mulVec_single_one, single_one_vecMul, funext_iff,
    col_apply, row_apply, Pi.single_apply, Matrix.one_apply]
  exact and_congr Iff.rfl <| forall₂_congr fun i _ ↦ forall_congr' fun j ↦ by
    simp only [@eq_comm _ j i]

/-- `G^(∅,∅)` is all of `GL n R`. -/
@[simp]
theorem vanDerKallenSubgroup_empty_empty : vanDerKallenSubgroup R (∅ : Set n) ∅ = ⊤ := by
  ext g
  simp

/-- `G^(P,Q)` is antitone in `P` and in `Q`. -/
@[gcongr]
theorem vanDerKallenSubgroup_anti {P P' Q Q' : Set n} (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    vanDerKallenSubgroup R P' Q' ≤ vanDerKallenSubgroup R P Q :=
  fun _ hg ↦ ⟨fun j hj ↦ hg.1 j (hP hj), fun i hi ↦ hg.2 i (hQ hi)⟩

/-- Fixing the columns of `P ∪ P'` and the rows of `Q ∪ Q'` is fixing those of `P` and `Q` and
those of `P'` and `Q'`. -/
theorem vanDerKallenSubgroup_union_union (P P' Q Q' : Set n) :
    vanDerKallenSubgroup R (P ∪ P') (Q ∪ Q') =
      vanDerKallenSubgroup R P Q ⊓ vanDerKallenSubgroup R P' Q' := by
  ext g
  simp only [Subgroup.mem_inf, mem_vanDerKallenSubgroup_iff, Set.mem_union, or_imp,
    forall_and]
  tauto

/-- The square group `G^(P ∪ Q, P ∪ Q)` lies in `G^(P,Q)`. -/
theorem vanDerKallenSubgroup_union_le (P Q : Set n) :
    vanDerKallenSubgroup R (P ∪ Q) (P ∪ Q) ≤ vanDerKallenSubgroup R P Q :=
  vanDerKallenSubgroup_anti Set.subset_union_left Set.subset_union_right

/-- A matrix fixing every standard basis column is the identity: `G^(univ, Q) = 1`. -/
@[simp]
theorem vanDerKallenSubgroup_univ_left (Q : Set n) :
    vanDerKallenSubgroup R Set.univ Q = ⊥ := by
  refine eq_bot_iff.2 fun g hg ↦ Subgroup.mem_bot.2 <| Units.ext <| Matrix.ext fun i j ↦ ?_
  exact (mem_vanDerKallenSubgroup_iff_apply.1 hg).1 j trivial i

/-- A matrix fixing every standard basis row is the identity: `G^(P, univ) = 1`. -/
@[simp]
theorem vanDerKallenSubgroup_univ_right (P : Set n) :
    vanDerKallenSubgroup R P Set.univ = ⊥ := by
  refine eq_bot_iff.2 fun g hg ↦ Subgroup.mem_bot.2 <| Units.ext <| Matrix.ext fun i j ↦ ?_
  exact (mem_vanDerKallenSubgroup_iff_apply.1 hg).2 i trivial j

end Semiring

/-! ## Stabilisers of standard frames -/

section CommRing

variable [CommRing R]

/-- The stabiliser in `GL n R` of the standard frame `(e_(f a))_a`, the `n × k` matrix whose
`a`-th column is the standard basis column `e_(f a)`, is the group `G^(range f, ∅)` fixing these
columns. -/
theorem stabilizer_submatrix_one {k : Type*} (f : k → n) :
    MulAction.stabilizer (GL n R) ((1 : Matrix n n R).submatrix id f) =
      vanDerKallenSubgroup R (Set.range f) ∅ := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, GeneralLinearGroup.smul_def,
    mem_vanDerKallenSubgroup_iff_apply, Set.forall_mem_range, Set.mem_empty_iff_false,
    IsEmpty.forall_iff, implies_true, and_true, ← Matrix.ext_iff]
  simp only [Matrix.mul_apply, submatrix_apply, id_eq, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact forall_comm

/-- Adding the columns `e_(f a)` to `P` cuts `G^(P,Q)` down to the stabiliser of the standard
frame `(e_(f a))_a`: `G^(P ∪ range f, Q) = G^(P,Q) ∩ Stab(e_(f a))_a`. -/
theorem vanDerKallenSubgroup_union_range {k : Type*} (P Q : Set n) (f : k → n) :
    vanDerKallenSubgroup R (P ∪ Set.range f) Q =
      vanDerKallenSubgroup R P Q ⊓
        MulAction.stabilizer (GL n R) ((1 : Matrix n n R).submatrix id f) := by
  rw [stabilizer_submatrix_one, ← vanDerKallenSubgroup_union_union, Set.union_empty]

/-- The stabiliser of the standard frame `(e_(f a))_a` in `G^(P,Q)` is `G^(P ∪ range f, Q)`,
as a subgroup of `G^(P,Q)`. -/
theorem stabilizer_vanDerKallenSubgroup_submatrix_one {k : Type*} (P Q : Set n) (f : k → n) :
    MulAction.stabilizer (vanDerKallenSubgroup R P Q) ((1 : Matrix n n R).submatrix id f) =
      (vanDerKallenSubgroup R (P ∪ Set.range f) Q).subgroupOf (vanDerKallenSubgroup R P Q) := by
  rw [vanDerKallenSubgroup_union_range, Subgroup.inf_subgroupOf_left,
    MulAction.stabilizer_subgroupOf]

end CommRing

/-! ## The inverse transpose: columns and rows -/

section CommSemiring

variable [CommSemiring R]

open GeneralLinearGroup in
/-- The inverse transpose `g ↦ (g⁻¹)ᵀ` carries `G^(P,Q)` into `G^(Q,P)`: the columns fixed by
`g` become rows fixed by `(g⁻¹)ᵀ`, and the rows fixed by `g` become columns. -/
theorem inverseTranspose_mem_vanDerKallenSubgroup_iff {P Q : Set n} {g : GL n R} :
    inverseTranspose g ∈ vanDerKallenSubgroup R Q P ↔ g ∈ vanDerKallenSubgroup R P Q := by
  rw [← inv_mem_iff (x := g)]
  simp only [mem_vanDerKallenSubgroup_iff, coe_inverseTranspose, mulVec_transpose,
    vecMul_transpose]
  exact and_comm

open GeneralLinearGroup in
/-- The inverse transpose `g ↦ (g⁻¹)ᵀ` maps `G^(P,Q)` onto `G^(Q,P)`. -/
theorem map_inverseTranspose_vanDerKallenSubgroup (P Q : Set n) :
    (vanDerKallenSubgroup R P Q).map (inverseTranspose : GL n R ≃* GL n R).toMonoidHom =
      vanDerKallenSubgroup R Q P := by
  ext g
  rw [Subgroup.mem_map_equiv, inverseTranspose_symm,
    ← inverseTranspose_mem_vanDerKallenSubgroup_iff, inverseTranspose_inverseTranspose]

end CommSemiring

/-! ## The upper inclusion along the stabilization -/

section Stabilize

variable [Ring R]

/-- The stabilization `g ↦ diag(g, 1)` from `GL_m` to `GL_k` pulls `G_k^(P,Q)` back to the group
`G_m` of the same indices: a matrix `g` fixes the columns and rows of `diag(g, 1)` indexed by `P`
and `Q` exactly when it fixes those of its own indexed by the indices in `P` and `Q` below `m`,
the remaining columns and rows of `diag(g, 1)` being those of the identity anyway. -/
theorem comap_stabilizeGL_vanDerKallenSubgroup {m k : ℕ} (h : m ≤ k) (P Q : Set (Fin k)) :
    (vanDerKallenSubgroup R P Q).comap (stabilizeGL R h) =
      vanDerKallenSubgroup R (Fin.castLE h ⁻¹' P) (Fin.castLE h ⁻¹' Q) := by
  ext g
  simp only [Subgroup.mem_comap, mem_vanDerKallenSubgroup_iff_apply, coe_stabilizeGL_apply,
    Set.mem_preimage]
  constructor
  · rintro ⟨hP, hQ⟩
    refine ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩
    · simpa [Matrix.one_apply, Fin.ext_iff] using hP _ hj (Fin.castLE h i)
    · simpa [Matrix.one_apply, Fin.ext_iff] using hQ _ hi (Fin.castLE h j)
  · rintro ⟨hP, hQ⟩
    refine ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;> split_ifs with hij
    · simpa [Matrix.one_apply, Fin.ext_iff] using hP ⟨j, hij.2⟩ hj ⟨i, hij.1⟩
    · rfl
    · simpa [Matrix.one_apply, Fin.ext_iff] using hQ ⟨i, hij.1⟩ hi ⟨j, hij.2⟩
    · rfl

/-- The **upper inclusion** `G_m^(P,Q) →* G_k^(P,Q)`, the restriction of the stabilization
`g ↦ diag(g, 1)`, where the indices of `G_m` are those of `G_k` below `m`. -/
def stabilizeVanDerKallen {m k : ℕ} (h : m ≤ k) (P Q : Set (Fin k)) :
    vanDerKallenSubgroup R (Fin.castLE h ⁻¹' P) (Fin.castLE h ⁻¹' Q) →*
      vanDerKallenSubgroup R P Q :=
  ((stabilizeGL R h).comp (Subgroup.subtype _)).codRestrict _ fun g ↦
    Subgroup.mem_comap.1 <| (comap_stabilizeGL_vanDerKallenSubgroup R h P Q).ge g.property

variable {R}

/-- The upper inclusion is the stabilization `g ↦ diag(g, 1)` on underlying matrices. -/
@[simp]
theorem coe_stabilizeVanDerKallen_apply {m k : ℕ} (h : m ≤ k) (P Q : Set (Fin k))
    (g : vanDerKallenSubgroup R (Fin.castLE h ⁻¹' P) (Fin.castLE h ⁻¹' Q)) :
    (stabilizeVanDerKallen R h P Q g : GL (Fin k) R) = stabilizeGL R h g :=
  (rfl)

/-- The upper inclusion is injective. -/
theorem stabilizeVanDerKallen_injective {m k : ℕ} (h : m ≤ k) (P Q : Set (Fin k)) :
    Function.Injective (stabilizeVanDerKallen R h P Q) := fun g g' hgg' ↦
  Subtype.ext <| stabilizeGL_injective h <| by
    simpa using congrArg Subtype.val hgg'

end Stabilize

/-! ## The square groups -/

section Square

variable [Ring R] (T : Set n) [DecidablePred (· ∈ T)]

/-- A matrix of the square group `G^(T,T)`, decomposed into blocks along `T` and its complement,
has the identity matrix as its three blocks touching `T`. -/
private theorem exists_reindexGL_eq_fromBlocks_of_mem {g : GL n R}
    (hg : g ∈ vanDerKallenSubgroup R T T) :
    ∃ D : Matrix (Tᶜ : Set n) (Tᶜ : Set n) R,
      ↑((Equiv.Set.sumCompl T).symm.reindexGL R g) = fromBlocks (1 : Matrix T T R) 0 0 D := by
  set g' : Matrix (T ⊕ (Tᶜ : Set n)) (T ⊕ (Tᶜ : Set n)) R :=
    ↑((Equiv.Set.sumCompl T).symm.reindexGL R g)
  obtain ⟨hP, hQ⟩ := mem_vanDerKallenSubgroup_iff_apply.1 hg
  refine ⟨g'.toBlocks₂₂, ?_⟩
  conv_lhs => rw [← fromBlocks_toBlocks g']
  congr 1 <;> ext i j
  · simpa [g', toBlocks₁₁, Matrix.one_apply, Subtype.ext_iff] using hQ i i.property j
  · simpa [g', toBlocks₁₂, Matrix.one_apply, ne_of_mem_of_not_mem i.property j.property] using
      hQ i i.property j
  · simpa [g', toBlocks₂₁, Matrix.one_apply, (ne_of_mem_of_not_mem j.property i.property).symm]
      using hP j j.property i

/-- The block diagonal matrices `diag(1, g)` are exactly the square group `G^(T,T)`. -/
theorem range_blockComplGL : (blockComplGL R T).range = vanDerKallenSubgroup R T T := by
  ext g
  constructor
  · rintro ⟨g', rfl⟩
    exact mem_vanDerKallenSubgroup_iff_apply.2
      ⟨fun j hj i ↦ by simp [coe_blockComplGL_apply, hj],
        fun i hi j ↦ by simp [coe_blockComplGL_apply, hi]⟩
  · intro hg
    obtain ⟨D, hD⟩ := exists_reindexGL_eq_fromBlocks_of_mem (R := R) (T := T) hg
    obtain ⟨u, -, hu⟩ := exists_fromBlocksGL_one_eq hD
    refine ⟨u, ((Equiv.Set.sumCompl T).symm.reindexGL R).injective ?_⟩
    rw [reindexGL_symm_blockComplGL, hu]

/-- The square group `G^(T,T)`, the invertible matrices fixing the standard basis columns and
rows indexed by `T`, is the general linear group of the coordinates outside `T`: its elements
are the block diagonal matrices `diag(1, g)`. -/
def vanDerKallenSubgroupEquiv : vanDerKallenSubgroup R T T ≃* GL (Tᶜ : Set n) R :=
  ((MonoidHom.ofInjective (blockComplGL_injective R T)).trans
    (MulEquiv.subgroupCongr (range_blockComplGL R T))).symm

variable {R T}

/-- The inverse of `vanDerKallenSubgroupEquiv` is the block diagonal embedding
`g ↦ diag(1, g)`. -/
@[simp]
theorem coe_vanDerKallenSubgroupEquiv_symm (g : GL (Tᶜ : Set n) R) :
    ((vanDerKallenSubgroupEquiv R T).symm g : GL n R) = blockComplGL R T g := by
  simp [vanDerKallenSubgroupEquiv, MonoidHom.ofInjective_apply]

/-- The inverse of `vanDerKallenSubgroupEquiv` places `g` in the block of the coordinates
outside `T` and fills the rest with the identity matrix. -/
theorem coe_vanDerKallenSubgroupEquiv_symm_apply (g : GL (Tᶜ : Set n) R) (i j : n) :
    (((vanDerKallenSubgroupEquiv R T).symm g : GL n R) : Matrix n n R) i j =
      if hij : i ∉ T ∧ j ∉ T then (g : Matrix (Tᶜ : Set n) (Tᶜ : Set n) R) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix n n R) i j := by
  rw [coe_vanDerKallenSubgroupEquiv_symm, coe_blockComplGL_apply]

/-- `vanDerKallenSubgroupEquiv` sends a matrix of `G^(T,T)` to its block of the coordinates
outside `T`. -/
@[simp]
theorem coe_vanDerKallenSubgroupEquiv_apply (g : vanDerKallenSubgroup R T T) :
    (vanDerKallenSubgroupEquiv R T g : Matrix (Tᶜ : Set n) (Tᶜ : Set n) R) =
      ((g : GL n R) : Matrix n n R).submatrix Subtype.val Subtype.val := by
  ext i j
  have h := coe_vanDerKallenSubgroupEquiv_symm_apply (vanDerKallenSubgroupEquiv R T g) i j
  simp only [MulEquiv.symm_apply_apply, Set.notMem_of_mem_compl i.property,
    Set.notMem_of_mem_compl j.property, not_false_eq_true, and_self, dite_true] at h
  exact h.symm

end Square

end TauCeti
