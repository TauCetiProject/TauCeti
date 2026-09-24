/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Transvection

import TauCeti.Data.Fin.Basic

/-!
# The standard Tits systems of the general linear groups

Let `B` be the upper-triangular subgroup of `GLₙ₊₁(k)` and let `N` be the normalizer of its
diagonal torus `T`. Over a field whose unit group is nontrivial, these subgroups form a Tits
system whose simple reflections are the classes of the permutation matrices of the adjacent
transpositions `(i i+1)`.

The rank-one construction identifies the Weyl group of `GL₂` with the two permutations of its
coordinate lines. In every rank, the Weyl group is the symmetric group on the coordinates, and
its simple reflections are the adjacent transpositions. The multiplication step of the Tits
system holds over every field, so the Bruhat decomposition, covering `GLₘ(k)` by the double cosets
`B τ B` of permutation matrices, is proved without the assumption on the unit group; over `𝔽₂`
it holds even though, in dimension `m ≥ 2`, `B` and the torus normalizer do not form a Tits
system.

## Main results

* `TauCeti.gl2TitsSystem`: the standard Tits system of `GL₂(k)`.
* `TauCeti.gl2TitsSystem_mem_intersection`: its subgroup `B ∩ N` is the diagonal torus inside
  `N`.
* `TauCeti.gl2TitsSystemSimpleRep` and `TauCeti.gl2TitsSystem_simple`: its Weyl group has the
  single simple reflection represented by `GL2WeylElement k`.
* `TauCeti.glTitsSystem`: the standard Tits system of `GLₙ₊₁(k)`, and `TauCeti.glTitsSystem_one`:
  in rank one it is `TauCeti.gl2TitsSystem`.
* `TauCeti.glTitsSystemWeylGroupMulEquivPerm`: identifies its Weyl group with coordinate
  permutations.
* `TauCeti.glTitsSystemSimpleRep` and `TauCeti.glTitsSystem_simple`: its simple reflections are
  represented by the permutation matrices of the adjacent transpositions.
* `TauCeti.exists_mem_doubleCoset_permutationGL`: the Bruhat decomposition of `GLₘ(k)` over any
  field, every element lies in `B τ B` for a permutation `τ`.

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

variable (k : Type u) [Field k] [Nontrivial kˣ]

/-- The normalizer of the diagonal torus, abbreviated within the construction. -/
private abbrev GL2DiagonalNormalizer : Subgroup (GL (Fin 2) k) :=
  Subgroup.normalizer (diagonalTorus k 2 : Set (GL (Fin 2) k))

/-- The Weyl permutation matrix as an element of the diagonal-torus normalizer. -/
private def gl2WeylNormalizer : GL2DiagonalNormalizer k :=
  ⟨GL2WeylElement k, gl2WeylElement_mem_normalizer_diagonalTorus (R := k)⟩

private theorem gl2_borel_comap_normalizer_eq_diagonal :
    (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype =
      (diagonalTorus k 2).subgroupOf (GL2DiagonalNormalizer k) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hmem : (g : GL (Fin 2) k) ∈
        GL2Borel k ⊓ GL2DiagonalNormalizer k := ⟨hg, g.property⟩
    rw [UpperTriangularGroup.inf_normalizer_diagonalTorus_eq] at hmem
    exact hmem
  · intro hg
    exact UpperTriangularGroup.diagonalTorus_le (R := k) (n := 2) hg

private theorem gl2_mem_borel_iff_normalizerPerm_eq_one (g : GL2DiagonalNormalizer k) :
    (g : GL (Fin 2) k) ∈ GL2Borel k ↔
      diagonalNormalizerPerm (k := k) (n := 2) g = 1 := by
  have hinter := SetLike.ext_iff.mp (gl2_borel_comap_normalizer_eq_diagonal k) g
  constructor
  · exact fun hg ↦ (diagonalNormalizerPerm_eq_one_iff g).mpr (hinter.mp hg)
  · exact fun hg ↦ hinter.mpr ((diagonalNormalizerPerm_eq_one_iff g).mp hg)

private theorem gl2_normalizer_closure :
    Subgroup.closure
        (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
            Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k}) = ⊤ := by
  apply top_unique
  intro g _
  let C : Subgroup (GL2DiagonalNormalizer k) :=
    Subgroup.closure
      (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
          Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k})
  have hinter_le :
      (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype ≤ C := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl hx)
  have hweyl : gl2WeylNormalizer k ∈ C :=
    Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  let φ := diagonalNormalizerPerm (k := k) (n := 2)
  have hφweyl : φ (gl2WeylNormalizer k) = Equiv.swap 0 1 :=
    diagonalNormalizerPerm_gl2WeylElement (k := k)
  rcases perm_fin_two_eq_one_or_swap (φ g) with hg | hg
  · exact hinter_le ((gl2_mem_borel_iff_normalizerPerm_eq_one k g).mpr hg)
  · have hker : g * (gl2WeylNormalizer k)⁻¹ ∈
        (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype := by
      rw [Subgroup.mem_comap, Subgroup.subtype_apply]
      apply (gl2_mem_borel_iff_normalizerPerm_eq_one k _).mpr
      rw [map_mul, map_inv, hg, hφweyl, mul_inv_cancel]
    have hfactor : g = (g * (gl2WeylNormalizer k)⁻¹) * gl2WeylNormalizer k := by
      simp
    rw [hfactor]
    exact C.mul_mem (hinter_le hker) hweyl

omit [Nontrivial kˣ] in
private theorem gl2_borel_normalizer_closure :
    Subgroup.closure
        ((GL2Borel k : Set (GL (Fin 2) k)) ∪ GL2DiagonalNormalizer k) = ⊤ := by
  have hle :
      Subgroup.closure (insert (GL2WeylElement k) (GL2Borel k : Set (GL (Fin 2) k))) ≤
        Subgroup.closure ((GL2Borel k : Set (GL (Fin 2) k)) ∪ GL2DiagonalNormalizer k) :=
    Subgroup.closure_mono (by
      intro g hg
      rcases hg with (rfl | hg)
      · exact Or.inr (gl2WeylNormalizer k).property
      · exact Or.inl hg)
  rw [GL2Borel.closure_insert_gl2WeylElement_eq_top] at hle
  exact top_unique hle

private theorem gl2_doubleCoset_weyl_mul_union_eq_univ (g : GL2DiagonalNormalizer k) :
    DoubleCoset.doubleCoset
          ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) : GL (Fin 2) k)
          (GL2Borel k) (GL2Borel k) ∪
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) =
      Set.univ := by
  let φ := diagonalNormalizerPerm (k := k) (n := 2)
  have hφweyl : φ (gl2WeylNormalizer k) = Equiv.swap 0 1 :=
    diagonalNormalizerPerm_gl2WeylElement (k := k)
  rcases perm_fin_two_eq_one_or_swap (φ g) with hg | hg
  · have hgB : (g : GL (Fin 2) k) ∈ GL2Borel k :=
      (gl2_mem_borel_iff_normalizerPerm_eq_one k g).mpr hg
    have hwg : ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∉ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      simp [φ, hφweyl, hg]
    have hwgCoset := DoubleCoset.doubleCoset_eq_of_mem
      (GL2Borel.mem_doubleCoset_weyl_of_notMem hwg)
    have hgCoset :
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) =
          DoubleCoset.doubleCoset (1 : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) :=
      DoubleCoset.doubleCoset_eq_of_mem (by
        rw [GL2Borel.doubleCoset_one_eq]
        exact hgB)
    rw [hwgCoset, hgCoset, GL2Borel.doubleCoset_one_eq, Set.union_comm,
      GL2Borel.union_doubleCoset_weyl_eq_univ]
  · have hgB : (g : GL (Fin 2) k) ∉ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      exact hg.trans_ne (Equiv.swap_eq_one_iff.not.mpr Fin.zero_ne_one)
    have hwg : ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∈ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      simp [φ, hφweyl, hg]
    have hwgCoset :
        DoubleCoset.doubleCoset
            ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) : GL (Fin 2) k)
            (GL2Borel k) (GL2Borel k) =
          DoubleCoset.doubleCoset (1 : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) :=
      DoubleCoset.doubleCoset_eq_of_mem (by
        rw [GL2Borel.doubleCoset_one_eq]
        exact hwg)
    have hgCoset := DoubleCoset.doubleCoset_eq_of_mem
      (GL2Borel.mem_doubleCoset_weyl_of_notMem hgB)
    rw [hwgCoset, GL2Borel.doubleCoset_one_eq, hgCoset,
      GL2Borel.union_doubleCoset_weyl_eq_univ]

omit [Nontrivial kˣ] in
private theorem gl2_tits_exists_conj_not_mem
    (s : GL2DiagonalNormalizer k)
    (hs : s ∈ ({gl2WeylNormalizer k} : Set (GL2DiagonalNormalizer k))) :
    ∃ b : GL2Borel k,
      (s : GL (Fin 2) k) * (b : GL (Fin 2) k) * (s : GL (Fin 2) k)⁻¹ ∉ GL2Borel k := by
  rw [Set.mem_singleton_iff.mp hs]
  refine ⟨⟨GL2Borel.mk 1 1 1, GL2Borel.mk_mem 1 1 1⟩, ?_⟩
  rw [GL2Borel.mem_iff]
  simp [gl2WeylNormalizer, Units.val_mul, GL2Borel.coe_mk, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The intersection `B ∩ N` is normal in `N`: under `gl2_borel_comap_normalizer_eq_diagonal` it
is the diagonal torus, which is normal in its own normalizer. Stated as an instance because the
Weyl quotient `N ⧸ (B ∩ N)` is only a group once it is available. -/
private instance :
    ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype).Normal := by
  rw [gl2_borel_comap_normalizer_eq_diagonal]
  exact Subgroup.normal_in_normalizer

/-- The class of the Weyl permutation matrix generates the Weyl quotient `N ⧸ (B ∩ N)` of `GL₂`. -/
private theorem gl2_closure_simple : Subgroup.closure ({QuotientGroup.mk (gl2WeylNormalizer k)} :
    Set (GL2DiagonalNormalizer k ⧸ (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype)) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) s
  have hg : g ∈ Subgroup.closure
      (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
          Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k}) := by
    rw [gl2_normalizer_closure]
    exact Subgroup.mem_top g
  have hmap : QuotientGroup.mk'
        ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) g ∈
      (Subgroup.closure
        (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
            Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k})).map
          (QuotientGroup.mk'
            ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype)) :=
    ⟨g, hg, rfl⟩
  rw [MonoidHom.map_closure] at hmap
  exact ((Subgroup.closure_le
    (Subgroup.closure
      ({QuotientGroup.mk (gl2WeylNormalizer k)} :
        Set (GL2DiagonalNormalizer k ⧸
          (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype)))).mpr (fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hy with hy | hy
    · have hqy : QuotientGroup.mk'
          ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) y = 1 :=
        (QuotientGroup.eq_one_iff y).mpr hy
      rw [hqy]
      exact (Subgroup.closure
        ({QuotientGroup.mk (gl2WeylNormalizer k)} :
          Set (GL2DiagonalNormalizer k ⧸
            (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype))).one_mem
    · rw [Set.mem_singleton_iff] at hy
      subst y
      exact Subgroup.subset_closure (Set.mem_singleton _))) hmap

/-- The standard rank-one Tits system of `GL₂(k)`: `B` is the upper-triangular subgroup,
`N` is the diagonal-torus normalizer, and its unique simple reflection is represented by the
Weyl permutation matrix. -/
def gl2TitsSystem : TitsSystem (GL (Fin 2) k) where
  subgroupB := GL2Borel k
  subgroupN := GL2DiagonalNormalizer k
  closure_subgroupB_union_subgroupN := gl2_borel_normalizer_closure k
  intersection_normal := by
    rw [← Subgroup.comap_subtype]
    infer_instance
  simple := {QuotientGroup.mk (gl2WeylNormalizer k)}
  closure_simple := gl2_closure_simple k
  exists_simpleRep_sq_mem s hs := by
    rw [Set.mem_singleton_iff] at hs
    refine ⟨gl2WeylNormalizer k, hs.symm, ?_⟩
    rw [← Subgroup.comap_subtype, Subgroup.mem_comap, map_mul]
    simp only [Subgroup.subtype_apply, gl2WeylNormalizer]
    rw [gl2WeylElement_mul_self]
    exact (GL2Borel k).one_mem
  mul_doubleCoset_subset s hs := by
    rw [Set.mem_singleton_iff] at hs
    refine ⟨gl2WeylNormalizer k, hs.symm, fun g ↦ ?_⟩
    rw [gl2_doubleCoset_weyl_mul_union_eq_univ]
    exact Set.subset_univ _
  exists_conj_not_mem s hs := by
    rw [Set.mem_singleton_iff] at hs
    obtain ⟨b, hb⟩ := gl2_tits_exists_conj_not_mem k
      (gl2WeylNormalizer k) (Set.mem_singleton _)
    exact ⟨gl2WeylNormalizer k, hs.symm, b, hb⟩

/-- The `B` subgroup of the standard `GL₂` Tits system is the upper-triangular subgroup. -/
@[simp]
theorem gl2TitsSystem_subgroupB : (gl2TitsSystem k).subgroupB = GL2Borel k :=
  by rw [gl2TitsSystem]

/-- The `N` subgroup of the standard `GL₂` Tits system is the diagonal-torus normalizer. -/
@[simp]
theorem gl2TitsSystem_subgroupN :
    (gl2TitsSystem k).subgroupN =
      Subgroup.normalizer (diagonalTorus k 2 : Set (GL (Fin 2) k)) :=
  by rw [gl2TitsSystem]

/-- The standard representative of the simple reflection in the `GL₂` Tits system. -/
def gl2TitsSystemSimpleRep : (gl2TitsSystem k).subgroupN :=
  gl2WeylNormalizer k

/-- The standard simple representative is the Weyl permutation matrix after forgetting the
normalizer subtype. -/
@[simp]
theorem coe_gl2TitsSystemSimpleRep :
    (gl2TitsSystemSimpleRep k : GL (Fin 2) k) = GL2WeylElement k :=
  (rfl)

/-- In the standard `GL₂` Tits system, membership in `B ∩ N` is exactly membership in the
diagonal torus after forgetting the normalizer subtype. -/
theorem gl2TitsSystem_mem_intersection (n : (gl2TitsSystem k).subgroupN) :
    n ∈ (gl2TitsSystem k).intersection ↔
      (n : GL (Fin 2) k) ∈ diagonalTorus k 2 := by
  rw [TitsSystem.mem_intersection]
  let n' : GL2DiagonalNormalizer k :=
    ⟨n, by simpa only [gl2TitsSystem] using n.property⟩
  have hinter := SetLike.ext_iff.mp (gl2_borel_comap_normalizer_eq_diagonal k)
    n'
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.subtype_apply] at hinter
  simpa only [n', gl2TitsSystem] using hinter

/-- The simple set of the standard `GL₂` Tits system is the singleton represented by the Weyl
permutation matrix. -/
theorem gl2TitsSystem_simple :
    (gl2TitsSystem k).simple =
      {(QuotientGroup.mk (gl2TitsSystemSimpleRep k) : (gl2TitsSystem k).WeylGroup)} := by
  ext s
  simp only [gl2TitsSystem, gl2TitsSystemSimpleRep]
  rfl

end

noncomputable section

section Adjacent

variable {k : Type u} [Field k] {m : ℕ} {a b : Fin m}

/-- The adjacent transposition `(a b)` reverses the order of exactly one pair. -/
private theorem swap_lt_swap_of_lt (hab : a.val + 1 = b.val) {i j : Fin m} (hji : j < i)
    (hne : ¬ (j = a ∧ i = b)) : Equiv.swap a b j < Equiv.swap a b i := by
  simp only [Equiv.swap_apply_def]
  simp only [Fin.lt_def, Fin.ext_iff] at hji hne ⊢
  split_ifs <;> simp_all <;> omega

private theorem permutationGL_swap_inv :
    (permutationGL (k := k) (Equiv.swap a b))⁻¹ = permutationGL (k := k) (Equiv.swap a b) := by
  rw [← map_inv, Equiv.swap_inv]

private theorem permutationGL_swap_mul_self :
    permutationGL (k := k) (Equiv.swap a b) * permutationGL (k := k) (Equiv.swap a b) = 1 := by
  rw [← map_mul, Equiv.swap_mul_self, map_one]

/-- Conjugating by an adjacent transposition keeps an upper-triangular matrix upper triangular when
the entry in the swapped position vanishes. -/
private theorem conj_swap_mem_of_apply_eq_zero (hab : a.val + 1 = b.val) {x : GL (Fin m) k}
    (hx : x ∈ upperTriangularGroup (Fin m) k) (hx0 : (x : Matrix (Fin m) (Fin m) k) a b = 0) :
    (permutationGL (k := k) (Equiv.swap a b))⁻¹ * x * permutationGL (k := k) (Equiv.swap a b) ∈
      upperTriangularGroup (Fin m) k := by
  rw [UpperTriangularGroup.permutationGL_inv_mul_mul_permutationGL_mem_iff]
  intro i j hji
  by_cases h : j = a ∧ i = b
  · obtain ⟨rfl, rfl⟩ := h
    simpa using hx0
  · exact (UpperTriangularGroup.mem_iff.mp hx) (swap_lt_swap_of_lt hab hji h)

/-- An upper-triangular matrix is a product of one whose `(a, b)` entry vanishes and a
transvection at `(a, b)`. -/
private theorem exists_mul_transvectionUnit (hab : a < b) {x : GL (Fin m) k}
    (hx : x ∈ upperTriangularGroup (Fin m) k) :
    ∃ y ∈ upperTriangularGroup (Fin m) k, (y : Matrix (Fin m) (Fin m) k) a b = 0 ∧
      ∃ c : k, x = y * transvectionUnit hab.ne c := by
  let t := UpperTriangularGroup.diag ⟨x, hx⟩ a
  have ht : (t : k) = (x : Matrix (Fin m) (Fin m) k) a a := UpperTriangularGroup.diag_apply_val _ _
  let c := (t : k)⁻¹ * (x : Matrix (Fin m) (Fin m) k) a b
  refine ⟨x * transvectionUnit hab.ne (-c), (upperTriangularGroup (Fin m) k).mul_mem hx
    (transvectionUnit_mem_upperTriangularGroup hab _), ?_, c, ?_⟩
  · rw [Units.val_mul, coe_transvectionUnit, Matrix.mul_transvection_apply_same, ← ht]
    simp only [c]
    field_simp
    ring
  · rw [mul_assoc, ← transvectionUnit_add, neg_add_cancel, transvectionUnit_zero, mul_one]

/-- Conjugating the transvection at `(a, b)` by the transposition of `a` and `b` gives the
transvection at `(b, a)`. -/
private theorem permutationGL_swap_mul_transvectionUnit_mul_permutationGL_swap (hab : a ≠ b)
    (c : k) :
    permutationGL (k := k) (Equiv.swap a b) * transvectionUnit hab c *
        permutationGL (k := k) (Equiv.swap a b) = transvectionUnit hab.symm c := by
  have h := permutationGL_inv_mul_transvectionUnit_mul_permutationGL (A := k)
    (Equiv.swap a b) hab c
  rw [permutationGL_swap_inv] at h
  rw [h]
  ext i j
  simp [Matrix.transvection, Matrix.single_apply]

/-- The rank-one Bruhat factorization: for `c ≠ 0`, the lower transvection `x_{ba}(c)` lies in
`B s x_{ab}(c⁻¹)`, where `s` is the transposition of `a` and `b`. -/
private theorem transvectionUnit_mul_transvectionUnit_mul_permutationGL_mem (hab : a < b)
    {c : k} (hc : c ≠ 0) :
    transvectionUnit hab.ne.symm c * transvectionUnit hab.ne (-c⁻¹) *
        permutationGL (k := k) (Equiv.swap a b) ∈ upperTriangularGroup (Fin m) k := by
  rw [UpperTriangularGroup.mem_iff]
  intro i j hji
  have h₁ : a.val < b.val := hab
  have h₂ : j.val < i.val := hji
  rw [coe_mul_permutationGL_apply, Units.val_mul, coe_transvectionUnit, coe_transvectionUnit]
  -- Row `b` of `x_{ba}(c) M` is row `b` plus `c` times row `a` of `M`; other rows are unchanged.
  rcases eq_or_ne i b with rfl | hib
  on_goal 1 => rw [Matrix.transvection_mul_apply_same]
  on_goal 2 => rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hib]
  all_goals
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Equiv.swap_apply_def]
    split_ifs <;> simp only [Fin.ext_iff, not_true_eq_false, and_true, true_and] at * <;>
      first | omega | simp [hc]

/-- The Tits multiplication step for an adjacent transposition `s`: for `x ∈ B` and a
permutation `τ`, the product `s x τ` lies in `B s τ B ∪ B τ B`. -/
private theorem permutationGL_swap_mul_mul_permutationGL_mem (hab : a.val + 1 = b.val)
    {x : GL (Fin m) k} (hx : x ∈ upperTriangularGroup (Fin m) k) (τ : Equiv.Perm (Fin m)) :
    permutationGL (k := k) (Equiv.swap a b) * x * permutationGL (k := k) τ ∈
      DoubleCoset.doubleCoset
          (permutationGL (k := k) (Equiv.swap a b) * permutationGL (k := k) τ)
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) ∪
        DoubleCoset.doubleCoset (permutationGL (k := k) τ)
          (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) := by
  have hlt : a < b := Fin.lt_def.mpr (by omega)
  obtain ⟨y, hy, hy0, c, rfl⟩ := exists_mul_transvectionUnit hlt hx
  have hsys := conj_swap_mem_of_apply_eq_zero hab hy hy0
  rw [permutationGL_swap_inv] at hsys
  set s := permutationGL (k := k) (Equiv.swap a b) with hs
  set P := permutationGL (k := k) τ with hP
  set u := transvectionUnit hlt.ne c with hu
  have hsinv : s⁻¹ = s := permutationGL_swap_inv
  have hss (z : GL (Fin m) k) : s * (s * z) = z := by
    rw [← mul_assoc, permutationGL_swap_mul_self, one_mul]
  rcases lt_or_gt_of_ne (τ.symm.injective.ne hlt.ne) with hτ | hτ
  · -- `τ` keeps `a` before `b`, so `u` moves past `τ` into `B`.
    left
    have huP : P⁻¹ * u * P ∈ upperTriangularGroup (Fin m) k := by
      rw [hP, hu, permutationGL_inv_mul_transvectionUnit_mul_permutationGL]
      exact transvectionUnit_mem_upperTriangularGroup hτ c
    refine DoubleCoset.mem_doubleCoset.mpr ⟨s * y * s, hsys, P⁻¹ * u * P, huP, ?_⟩
    simp only [mul_assoc, hss, mul_inv_cancel_left]
  · by_cases hc : c = 0
    · left
      refine DoubleCoset.mem_doubleCoset.mpr ⟨s * y * s, hsys, 1, one_mem _, ?_⟩
      simp only [hu, hc, transvectionUnit_zero, mul_one, mul_assoc, hss]
    · -- `τ` reverses `a` and `b`: factor `s u s` through the rank-one Bruhat cell.
      right
      set v := transvectionUnit hlt.ne c⁻¹ with hv
      have hℓ : s * u * s = transvectionUnit hlt.ne.symm c :=
        permutationGL_swap_mul_transvectionUnit_mul_permutationGL_swap hlt.ne c
      have hℓv : s * u * s * v⁻¹ * s ∈ upperTriangularGroup (Fin m) k := by
        rw [hℓ, hv, transvectionUnit_inv]
        exact transvectionUnit_mul_transvectionUnit_mul_permutationGL_mem hlt hc
      have hvP : (s * P)⁻¹ * v * (s * P) ∈ upperTriangularGroup (Fin m) k := by
        rw [hs, hP, hv, ← map_mul, permutationGL_inv_mul_transvectionUnit_mul_permutationGL]
        exact transvectionUnit_mem_upperTriangularGroup (by simpa [Equiv.Perm.mul_def] using hτ) _
      refine DoubleCoset.mem_doubleCoset.mpr ⟨s * y * s * (s * u * s * v⁻¹ * s),
        mul_mem hsys hℓv, (s * P)⁻¹ * v * (s * P), hvP, ?_⟩
      simp only [_root_.mul_inv_rev, hsinv, mul_assoc, hss, mul_inv_cancel_left,
        inv_mul_cancel_left]

/-- The upper-triangular subgroup and the permutation matrices generate `GLₘ(k)`. -/
private theorem closure_upperTriangularGroup_union_range_permutationGL (k : Type u) [Field k]
    (m : ℕ) :
    Subgroup.closure ((upperTriangularGroup (Fin m) k : Set (GL (Fin m) k)) ∪
      Set.range (permutationGL (k := k))) = ⊤ := by
  set C := Subgroup.closure ((upperTriangularGroup (Fin m) k : Set (GL (Fin m) k)) ∪
    Set.range (permutationGL (k := k)))
  have hB : upperTriangularGroup (Fin m) k ≤ C := fun x hx ↦ Subgroup.subset_closure (Or.inl hx)
  have hN (σ : Equiv.Perm (Fin m)) : permutationGL (k := k) σ ∈ C :=
    Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)
  refine top_unique fun g _ ↦ ?_
  obtain ⟨h, hC, hh⟩ : ∃ h ∈ C, (h : Matrix (Fin m) (Fin m) k) = g := by
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M ↦ ∃ h ∈ C, (h : Matrix (Fin m) (Fin m) k) = M) g
      (Matrix.isUnits_det_units g).ne_zero ?_ ?_ ?_
    · intro D hD
      have hD' (i : Fin m) : D i ≠ 0 := by
        rw [Matrix.det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      refine ⟨diagGL fun i ↦ Units.mk0 (D i) (hD' i), hB (UpperTriangularGroup.diagonalTorus_le
        (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩)), ?_⟩
      simp [diagGL_coe]
    · intro t
      refine ⟨transvectionUnit t.hij t.c, ?_, by
        rw [coe_transvectionUnit, Matrix.TransvectionStruct.toMatrix]⟩
      rcases lt_or_gt_of_ne t.hij with hlt | hgt
      · exact hB (transvectionUnit_mem_upperTriangularGroup hlt t.c)
      · -- A lower transvection is an upper one conjugated by the transposition of its indices.
        have hconj := permutationGL_inv_mul_transvectionUnit_mul_permutationGL (A := k)
          (Equiv.swap t.i t.j) t.hij.symm t.c
        have heq : transvectionUnit t.hij t.c =
            (permutationGL (k := k) (Equiv.swap t.i t.j))⁻¹ * transvectionUnit t.hij.symm t.c *
              permutationGL (k := k) (Equiv.swap t.i t.j) := by
          rw [hconj]
          ext
          simp [Matrix.transvection, Matrix.single_apply]
        rw [heq]
        exact mul_mem (mul_mem (inv_mem (hN _))
          (hB (transvectionUnit_mem_upperTriangularGroup hgt t.c))) (hN _)
    · rintro A B - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x * y, mul_mem hx hy, rfl⟩
  rwa [← Units.ext hh]

/-- Left multiplication by an adjacent transposition maps a Bruhat cell `B τ B` into the Bruhat
cell of another permutation matrix. -/
private theorem exists_permutationGL_swap_mul_mem_doubleCoset (hab : a.val + 1 = b.val)
    {g : GL (Fin m) k} {τ : Equiv.Perm (Fin m)}
    (hg : g ∈ DoubleCoset.doubleCoset (permutationGL (k := k) τ)
      (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k)) :
    ∃ τ' : Equiv.Perm (Fin m), permutationGL (k := k) (Equiv.swap a b) * g ∈
      DoubleCoset.doubleCoset (permutationGL (k := k) τ')
        (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  have hmem : permutationGL (k := k) (Equiv.swap a b) * (x * permutationGL (k := k) τ * y) ∈
      DoubleCoset.doubleCoset (permutationGL (k := k) (Equiv.swap a b) * x *
        permutationGL (k := k) τ) (upperTriangularGroup (Fin m) k)
        (upperTriangularGroup (Fin m) k) :=
    DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, y, hy, by group⟩
  rcases permutationGL_swap_mul_mul_permutationGL_mem hab hx τ with h | h
  · refine ⟨Equiv.swap a b * τ, ?_⟩
    rw [map_mul, ← DoubleCoset.doubleCoset_eq_of_mem h]
    exact hmem
  · refine ⟨τ, ?_⟩
    rw [← DoubleCoset.doubleCoset_eq_of_mem h]
    exact hmem

/-- **Bruhat decomposition** of `GLₘ(k)` over any field: every invertible matrix lies in a
double coset `B τ B` of the upper-triangular subgroup represented by a permutation matrix. -/
theorem exists_mem_doubleCoset_permutationGL (g : GL (Fin m) k) :
    ∃ τ : Equiv.Perm (Fin m), g ∈ DoubleCoset.doubleCoset (permutationGL (k := k) τ)
      (upperTriangularGroup (Fin m) k) (upperTriangularGroup (Fin m) k) := by
  obtain _ | n := m
  · exact ⟨1, DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩⟩
  -- The union of the cells `B τ B` is stable under left multiplication by `B` and by
  -- permutation matrices, which together generate `GLₙ₊₁(k)`.
  set B := upperTriangularGroup (Fin (n + 1)) k
  have hB {x h : GL (Fin (n + 1)) k} (hx : x ∈ B) :
      (∃ τ, h ∈ DoubleCoset.doubleCoset (permutationGL (k := k) τ) B B) →
        ∃ τ, x * h ∈ DoubleCoset.doubleCoset (permutationGL (k := k) τ) B B := by
    rintro ⟨τ, hτ⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hτ
    exact ⟨τ, DoubleCoset.mem_doubleCoset.mpr ⟨x * y, mul_mem hx hy, z, hz, by group⟩⟩
  have hperm (σ : Equiv.Perm (Fin (n + 1))) {h : GL (Fin (n + 1)) k} :
      (∃ τ, h ∈ DoubleCoset.doubleCoset (permutationGL (k := k) τ) B B) →
        ∃ τ, permutationGL (k := k) σ * h ∈
          DoubleCoset.doubleCoset (permutationGL (k := k) τ) B B := by
    induction (Equiv.Perm.mclosure_swap_castSucc_succ n).ge (Submonoid.mem_top σ) using
      Submonoid.closure_induction_left generalizing h with
    | one => simpa only [map_one, one_mul] using id
    | mul_left x hx y _ ih =>
      obtain ⟨i, rfl⟩ := hx
      rintro ⟨τ, hτ⟩
      rw [map_mul, mul_assoc]
      obtain ⟨τ', hτ'⟩ := ih ⟨τ, hτ⟩
      exact exists_permutationGL_swap_mul_mem_doubleCoset (by simp) hτ'
  have hg : g ∈ Subgroup.closure ((B : Set (GL (Fin (n + 1)) k)) ∪
      Set.range (permutationGL (k := k))) := by
    rw [closure_upperTriangularGroup_union_range_permutationGL]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _, 1, one_mem _, by simp⟩⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨σ, rfl⟩
    · exact hB hx ih
    · exact hperm σ ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨σ, rfl⟩
    · exact hB (inv_mem hx) ih
    · rw [← map_inv]
      exact hperm σ⁻¹ ih

end Adjacent

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
    rw [permutationGL_swap_inv]
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

/-- In rank one the standard Tits system is the one of `GL₂` built from its Bruhat
decomposition. -/
theorem glTitsSystem_one : glTitsSystem k 1 = gl2TitsSystem k := by
  have hw : glTitsSystemSimpleRep k 1 0 = gl2TitsSystemSimpleRep k := by
    apply Subtype.ext
    rw [coe_glTitsSystemSimpleRep, coe_gl2TitsSystemSimpleRep,
      gl2WeylElement_eq_permutationGL_swap]
    -- In `Fin 2`, `Fin.castSucc 0` and `Fin.succ 0` are `0` and `1`.
    rfl
  -- `GL2Borel k` is the abbreviation `upperTriangularGroup (Fin 2) k`, and both systems use the
  -- diagonal-torus normalizer.
  ext1
  · rfl
  · rfl
  · rw [glTitsSystem_simple, gl2TitsSystem_simple, Set.range_unique, Fin.default_eq_zero, hw]
    -- The two Weyl quotients are the same type, `N ⧸ (B ∩ N)` for `GL₂ = GL (Fin (1 + 1))`.
    exact HEq.rfl

end TitsSystem

end

end TauCeti
