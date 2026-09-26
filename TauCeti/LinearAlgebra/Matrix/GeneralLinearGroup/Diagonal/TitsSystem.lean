/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat

import TauCeti.Data.Fin.Basic

/-!
# The standard Tits systems of the general linear groups

Let `B` be the upper-triangular subgroup of `GLₙ₊₁(k)` and let `N` be the normalizer of its
diagonal torus `T`. Over a field whose unit group is nontrivial, these subgroups form a Tits
system whose simple reflections are the classes of the permutation matrices of the adjacent
transpositions `(i i+1)`.

In every rank, the Weyl group is the symmetric group on the coordinates, and
its simple reflections are the adjacent transpositions. The multiplication step of the Tits
system holds over every field, so the Bruhat decomposition, covering `GLₘ(k)` by the double cosets
`B τ B` of permutation matrices, is proved without the assumption on the unit group; over `𝔽₂`
it holds even though, in dimension `m ≥ 2`, `B` and the torus normalizer do not form a Tits
system.

## Main results

* `TauCeti.glTitsSystem`: the standard Tits system of `GLₙ₊₁(k)`, including `GL₂(k)` when `n = 1`.
* `TauCeti.glTitsSystemWeylGroupMulEquivPerm`: identifies its Weyl group with coordinate
  permutations.
* `TauCeti.glTitsSystemSimpleRep` and `TauCeti.glTitsSystem_simple`: its simple reflections are
  represented by the permutation matrices of the adjacent transpositions.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 26.2–26.3, 28.1 and 29.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Sections 8.3–8.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter IV, §2, no. 2, Example 1.
-/

public section

open Matrix
open scoped Pointwise

namespace TauCeti

universe u

noncomputable section

section TitsSystem

variable (k : Type u) [Field k] [Nontrivial kˣ]

/-- The normalizer of the diagonal torus, abbreviated within the construction. -/
private abbrev GLDiagonalNormalizer (m : ℕ) : Subgroup (GL (Fin m) k) :=
  Subgroup.normalizer (diagonalTorus k m : Set (GL (Fin m) k))

/-- Permutation matrices as elements of the diagonal-torus normalizer. -/
private def permutationNormalizer (m : ℕ) : Equiv.Perm (Fin m) →* GLDiagonalNormalizer k m :=
  (permutationGL (k := k)).codRestrict _ permutationGL_mem_normalizer

private theorem upperTriangularGroup_subgroupOf_normalizer (m : ℕ) :
    (upperTriangularGroup (Fin m) k).subgroupOf (GLDiagonalNormalizer k m) =
      (diagonalTorus k m).subgroupOf (GLDiagonalNormalizer k m) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact ⟨UpperTriangularGroup.mem_diagonalTorus_of_mem g,
    fun hg ↦ UpperTriangularGroup.diagonalTorus_le hg⟩

/-- The intersection `B ∩ N` is normal in `N`: it is the diagonal torus, which is normal in its
own normalizer. Stated as an instance because the Weyl quotient `N ⧸ (B ∩ N)` is only a group once
it is available. -/
private instance (m : ℕ) :
    ((upperTriangularGroup (Fin m) k).subgroupOf (GLDiagonalNormalizer k m)).Normal := by
  rw [upperTriangularGroup_subgroupOf_normalizer]
  exact Subgroup.normal_in_normalizer

/-- Every class in the Weyl quotient `N ⧸ (B ∩ N)` is represented by a permutation matrix. -/
private theorem mk_permutationNormalizer_surjective (m : ℕ) :
    Function.Surjective ((QuotientGroup.mk'
      ((upperTriangularGroup (Fin m) k).subgroupOf (GLDiagonalNormalizer k m))).comp
        (permutationNormalizer k m)) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨diagonalNormalizerPerm (k := k) (n := m) g, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    upperTriangularGroup_subgroupOf_normalizer, Subgroup.mem_subgroupOf,
    ← diagonalNormalizerPerm_eq_one_iff, map_mul, map_inv]
  have hperm : diagonalNormalizerPerm (k := k) (n := m)
      (permutationNormalizer k m (diagonalNormalizerPerm (k := k) (n := m) g)) =
        diagonalNormalizerPerm (k := k) (n := m) g :=
    diagonalNormalizerPerm_permutationGL _
  rw [hperm, inv_mul_cancel]

omit [Nontrivial kˣ] in
/-- A diagonal left factor does not change a double coset of the upper-triangular subgroup. -/
private theorem doubleCoset_diagGL_mul {m : ℕ} (d : Fin m → kˣ) (g : GL (Fin m) k) :
    DoubleCoset.doubleCoset (diagGL d * g)
        (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) =
      DoubleCoset.doubleCoset g
        (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) :=
  DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨diagGL d, UpperTriangularGroup.diagonalTorus_le
      (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩), 1, one_mem _, (mul_one _).symm⟩)

/-- The Tits multiplication axiom for an adjacent transposition `s`:
`B s B w B ⊆ B s w B ∪ B w B` for every `w` in the diagonal-torus normalizer. -/
private theorem doubleCoset_mul_doubleCoset_subset {m : ℕ} {a b : Fin m}
    (hab : a.val + 1 = b.val) (w : GLDiagonalNormalizer k m) :
    DoubleCoset.doubleCoset (permutationGL (k := k) (Equiv.swap a b))
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) *
        DoubleCoset.doubleCoset (w : GL (Fin m) k)
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) ⊆
      DoubleCoset.doubleCoset (permutationGL (k := k) (Equiv.swap a b) * w)
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) ∪
        DoubleCoset.doubleCoset (w : GL (Fin m) k)
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) := by
  intro z hz
  obtain ⟨_, hz₁, _, hz₂, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₁
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz₂
  obtain ⟨d, τ, hw⟩ := mem_normalizer_diagonalTorus_iff_exists.mp w.property
  have hd : diagGL d ∈ upperTriangularGroup (Fin m) k :=
    UpperTriangularGroup.diagonalTorus_le (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩)
  -- Replace `w = d τ` by the permutation matrix `τ` in both target double cosets.
  have hsw : permutationGL (k := k) (Equiv.swap a b) * w =
      diagGL (fun i ↦ d ((Equiv.swap a b)⁻¹ i)) *
        (permutationGL (k := k) (Equiv.swap a b) * permutationGL (k := k) τ) := by
    rw [hw, ← permutationGL_mul_diagGL_mul_inv]
    group
  rw [hsw, doubleCoset_diagGL_mul, hw, doubleCoset_diagGL_mul]
  have hfactor : b₁ * permutationGL (k := k) (Equiv.swap a b) * b₂ *
      (b₃ * (diagGL d * permutationGL (k := k) τ) * b₄) =
      b₁ * (permutationGL (k := k) (Equiv.swap a b) * (b₂ * b₃ * diagGL d) *
        permutationGL (k := k) τ) * b₄ := by
    group
  rw [hfactor]
  rcases permutationGL_swap_mul_mul_permutationGL_mem hab
      (mul_mem (mul_mem hb₂ hb₃) hd) τ with h | h
  · exact Or.inl (DoubleCoset.doubleCoset_eq_of_mem h ▸
      DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, b₄, hb₄, rfl⟩)
  · exact Or.inr (DoubleCoset.doubleCoset_eq_of_mem h ▸
      DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, b₄, hb₄, rfl⟩)

omit [Nontrivial kˣ] in
/-- Conjugating the upper transvection `x_{ab}(1)` by the transposition of `a` and `b` leaves the
upper-triangular subgroup. -/
private theorem permutationGL_swap_mul_transvectionUnit_mul_inv_notMem {m : ℕ} {a b : Fin m}
    (hab : a < b) :
    permutationGL (k := k) (Equiv.swap a b) * transvectionUnit hab.ne (1 : k) *
        (permutationGL (k := k) (Equiv.swap a b))⁻¹ ∉ upperTriangularGroup (Fin m) k := by
  have hconj : permutationGL (k := k) (Equiv.swap a b) * transvectionUnit hab.ne (1 : k) *
      (permutationGL (k := k) (Equiv.swap a b))⁻¹ =
        (permutationGL (k := k) (Equiv.swap a b))⁻¹ * transvectionUnit hab.ne (1 : k) *
          permutationGL (k := k) (Equiv.swap a b) := by
    rw [← map_inv, Equiv.swap_inv]
  intro hmem
  have hentry := UpperTriangularGroup.mem_iff.mp hmem (i := b) (j := a) hab
  rw [hconj, coe_permutationGL_inv_mul_mul_permutationGL_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, coe_transvectionUnit, Matrix.transvection] at hentry
  simp [hab.ne] at hentry

/-- The permutation matrix of the transposition of `i` and `i + 1`, as an element of the
diagonal-torus normalizer. -/
private def glSimpleRep (n : ℕ) (i : Fin n) : GLDiagonalNormalizer k (n + 1) :=
  permutationNormalizer k (n + 1) (Equiv.swap i.castSucc i.succ)

/-- The classes of the adjacent transpositions generate the Weyl quotient `N ⧸ (B ∩ N)`. -/
private theorem closure_range_mk_glSimpleRep (n : ℕ) :
    Subgroup.closure (Set.range fun i : Fin n ↦ (QuotientGroup.mk (glSimpleRep k n i) :
      GLDiagonalNormalizer k (n + 1) ⧸
        (upperTriangularGroup (Fin (n + 1)) k).subgroupOf (GLDiagonalNormalizer k (n + 1)))) =
      ⊤ := by
  apply Subgroup.closure_eq_top_of_mclosure_eq_top
  have hrange : (Set.range fun i : Fin n ↦ (QuotientGroup.mk (glSimpleRep k n i) :
      GLDiagonalNormalizer k (n + 1) ⧸
        (upperTriangularGroup (Fin (n + 1)) k).subgroupOf (GLDiagonalNormalizer k (n + 1)))) =
      ((QuotientGroup.mk' _).comp (permutationNormalizer k (n + 1))) ''
        Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← MonoidHom.map_mclosure, Equiv.Perm.mclosure_swap_castSucc_succ,
    ← MonoidHom.mrange_eq_map, MonoidHom.mrange_eq_top]
  exact mk_permutationNormalizer_surjective k (n + 1)

/-- The standard Tits system of `GLₙ₊₁(k)`: `B` is the upper-triangular subgroup, `N` is the
normalizer of the diagonal torus, and the simple reflections are the classes of the permutation
matrices of the adjacent transpositions `(i i+1)`. -/
def glTitsSystem (n : ℕ) : TitsSystem (GL (Fin (n + 1)) k) where
  subgroupB := upperTriangularGroup (Fin (n + 1)) k
  subgroupN := GLDiagonalNormalizer k (n + 1)
  closure_subgroupB_union_subgroupN := top_unique <|
    (closure_upperTriangularGroup_union_range_permutationGL k (n + 1)).ge.trans <|
      Subgroup.closure_mono <| Set.union_subset_union_right _ <|
        Set.range_subset_iff.mpr permutationGL_mem_normalizer
  intersection_normal := inferInstance
  simple := Set.range fun i : Fin n ↦ QuotientGroup.mk (glSimpleRep k n i)
  closure_simple := closure_range_mk_glSimpleRep k n
  exists_simpleRep_sq_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    refine ⟨glSimpleRep k n i, rfl, ?_⟩
    rw [glSimpleRep, ← map_mul, Equiv.swap_mul_self, map_one]
    exact one_mem _
  mul_doubleCoset_subset s hs := by
    obtain ⟨i, rfl⟩ := hs
    exact ⟨glSimpleRep k n i, rfl,
      doubleCoset_mul_doubleCoset_subset k (by simp)⟩
  exists_conj_not_mem s hs := by
    obtain ⟨i, rfl⟩ := hs
    exact ⟨glSimpleRep k n i, rfl,
      ⟨_, transvectionUnit_mem_upperTriangularGroup (Fin.castSucc_lt_succ (i := i)) 1⟩,
      permutationGL_swap_mul_transvectionUnit_mul_inv_notMem k (Fin.castSucc_lt_succ (i := i))⟩

variable (n : ℕ)

/-- The `B` subgroup of the standard `GLₙ₊₁` Tits system is the upper-triangular subgroup. -/
@[simp]
theorem glTitsSystem_subgroupB :
    (glTitsSystem k n).subgroupB = upperTriangularGroup (Fin (n + 1)) k := by
  rw [glTitsSystem]

/-- The `N` subgroup of the standard `GLₙ₊₁` Tits system is the diagonal-torus normalizer. -/
@[simp]
theorem glTitsSystem_subgroupN :
    (glTitsSystem k n).subgroupN =
      Subgroup.normalizer (diagonalTorus k (n + 1) : Set (GL (Fin (n + 1)) k)) := by
  rw [glTitsSystem]

/-- In the standard `GLₙ₊₁` Tits system, `B ∩ N` is the diagonal torus inside the
normalizer. -/
theorem glTitsSystem_mem_intersection (g : (glTitsSystem k n).subgroupN) :
    g ∈ (glTitsSystem k n).intersection ↔
      (g : GL (Fin (n + 1)) k) ∈ diagonalTorus k (n + 1) := by
  rw [TitsSystem.mem_intersection, glTitsSystem_subgroupB]
  let g' : GLDiagonalNormalizer k (n + 1) :=
    ⟨g, by simpa only [GLDiagonalNormalizer, glTitsSystem_subgroupN] using g.property⟩
  have h := SetLike.ext_iff.mp (upperTriangularGroup_subgroupOf_normalizer k (n + 1)) g'
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
  simpa only [g'] using h

/-- The standard representative of the `i`-th simple reflection of the `GLₙ₊₁` Tits system. -/
def glTitsSystemSimpleRep (i : Fin n) : (glTitsSystem k n).subgroupN :=
  glSimpleRep k n i

/-- The `i`-th simple representative is the permutation matrix of the transposition of `i` and
`i + 1`. -/
@[simp]
theorem coe_glTitsSystemSimpleRep (i : Fin n) :
    (glTitsSystemSimpleRep k n i : GL (Fin (n + 1)) k) =
      permutationGL (k := k) (Equiv.swap i.castSucc i.succ) :=
  (rfl)

/-- The simple reflections of the standard `GLₙ₊₁` Tits system are the classes of the adjacent
transpositions. -/
@[simp]
theorem glTitsSystem_simple :
    (glTitsSystem k n).simple =
      Set.range fun i : Fin n ↦
        (QuotientGroup.mk (glTitsSystemSimpleRep k n i) : (glTitsSystem k n).WeylGroup) :=
  (rfl)

/-- The Weyl group of the standard `GLₙ₊₁` Tits system is the permutation group of its
coordinates. -/
noncomputable def glTitsSystemWeylGroupMulEquivPerm :
    (glTitsSystem k n).WeylGroup ≃* Equiv.Perm (Fin (n + 1)) := by
  -- `WeylGroup` unfolds through `glTitsSystem` to this normalizer quotient.
  change (GLDiagonalNormalizer k (n + 1) ⧸
    (upperTriangularGroup (Fin (n + 1)) k).subgroupOf (GLDiagonalNormalizer k (n + 1))) ≃* _
  exact (QuotientGroup.quotientMulEquivOfEq
    (upperTriangularGroup_subgroupOf_normalizer k (n + 1))).trans
      (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n + 1))

/-- The `i`-th simple reflection acts by swapping coordinates `i` and `i + 1`. -/
@[simp]
theorem glTitsSystemWeylGroupMulEquivPerm_simpleRep (i : Fin n) :
    glTitsSystemWeylGroupMulEquivPerm k n
      (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) =
        Equiv.swap i.castSucc i.succ := by
  -- This exposes the normalizer quotient to which the equivalence was defined.
  change ((QuotientGroup.quotientMulEquivOfEq
      (upperTriangularGroup_subgroupOf_normalizer k (n + 1))).trans
      (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n + 1)))
        (QuotientGroup.mk (glSimpleRep k n i)) = _
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    diagonalNormalizerQuotientMulEquivPerm_mk]
  exact diagonalNormalizerPerm_permutationGL (Equiv.swap i.castSucc i.succ)

/-- The Weyl-group equivalence sends the class of a permutation matrix to that permutation. -/
@[simp]
theorem glTitsSystemWeylGroupMulEquivPerm_mk_permutationGL (σ : Equiv.Perm (Fin (n + 1))) :
    glTitsSystemWeylGroupMulEquivPerm k n
      (QuotientGroup.mk ⟨permutationGL (k := k) σ,
        by simpa only [glTitsSystem_subgroupN] using permutationGL_mem_normalizer σ⟩) = σ := by
  -- This exposes the normalizer quotient to which the equivalence was defined.
  change ((QuotientGroup.quotientMulEquivOfEq
      (upperTriangularGroup_subgroupOf_normalizer k (n + 1))).trans
      (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n + 1)))
        (QuotientGroup.mk (permutationNormalizer k (n + 1) σ)) = _
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    diagonalNormalizerQuotientMulEquivPerm_mk]
  exact diagonalNormalizerPerm_permutationGL σ

/-- The inverse Weyl-group equivalence sends a coordinate permutation to the class of its
permutation matrix. -/
@[simp]
theorem glTitsSystemWeylGroupMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin (n + 1))) :
    (glTitsSystemWeylGroupMulEquivPerm k n).symm σ =
      QuotientGroup.mk ⟨permutationGL (k := k) σ,
        by simpa only [glTitsSystem_subgroupN] using permutationGL_mem_normalizer σ⟩ := by
  apply (glTitsSystemWeylGroupMulEquivPerm k n).injective
  simp

end TitsSystem

end

end TauCeti
