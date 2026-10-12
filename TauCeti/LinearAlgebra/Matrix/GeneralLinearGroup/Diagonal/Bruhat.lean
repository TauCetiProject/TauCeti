/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The Bruhat Weyl element and the Borel subgroup are compared with the diagonal normalizer below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
-- The monomial description of the diagonal normalizer supplies its permutation quotient.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Transvection

/-!
# The diagonal normalizer and the Bruhat data of `GL₂`

This file aligns upper-triangular Bruhat data with the diagonal normalizer. For `GLₙ`, an
upper-triangular monomial matrix is diagonal, and hence

`Bₙ ⊓ N(Tₙ) = Tₙ`.

Specializing to `GL₂`, the Weyl element used in the Bruhat decomposition is the permutation
matrix of the transposition, so it lies in `N(T)` and induces the nontrivial element of its
permutation quotient. In particular,

`B ⊓ N(T) = T`,

where `B` is the standard Borel subgroup. This is the kernel identification in the
rank-one `(B, N)`-pair: the already-established quotient `N(T) / T ≃ S₂` can equivalently be
written with `B ⊓ N(T)` as its denominator.

The assumption `Nontrivial kˣ` in the intersection theorems is necessary for the full
group-theoretic normalizer. For example, over `𝔽₂` the diagonal torus of `GL₂` is trivial, so
its normalizer is all of `GL₂` and the displayed rank-one intersection would instead be `B`.

## Main results

* `TauCeti.gl2WeylElement_eq_permutationGL_swap`: the Bruhat Weyl element is the permutation
  matrix of the transposition.
* `TauCeti.gl2WeylElement_mem_normalizer_diagonalTorus`: the Weyl element normalizes the diagonal
  torus.
* `TauCeti.diagonalNormalizerPerm_gl2WeylElement`: the Weyl element induces the transposition on
  the coordinate lines.
* `TauCeti.UpperTriangularGroup.inf_normalizer_diagonalTorus_eq`: in every dimension, the
  intersection of the upper-triangular subgroup with the diagonal normalizer is the diagonal
  torus.
* `TauCeti.UpperTriangularGroup.permutationGL_inv_mul_mul_permutationGL_mem_iff`: when a
  conjugate by a permutation matrix is upper triangular.
* `TauCeti.closure_upperTriangularGroup_union_range_permutationGL`: the upper-triangular
  subgroup and permutation matrices generate `GLₘ(k)`.
* `TauCeti.exists_mem_doubleCoset_permutationGL`: the Bruhat decomposition of `GLₘ(k)` over any
  field, every element lies in `B τ B` for a permutation `τ`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 26.2–26.3 and 28.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Sections 8.3–8.4.

This advances Layer 7, "Bruhat decomposition and BN-pairs / Tits systems", of the
ReductiveGroups roadmap by identifying the intersection subgroup, including in the rank-one
`GL₂` example.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

section WeylElement

variable (R : Type u) [Semiring R]

/-- The Weyl element in the Bruhat decomposition of `GL₂` is the permutation matrix of the
transposition of the two coordinate lines. -/
theorem gl2WeylElement_eq_permutationGL_swap :
    GL2WeylElement R = permutationGL (k := R) (Equiv.swap 0 1) := by
  apply Units.ext
  rw [permutationGL_coe, coe_gl2WeylElement]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Equiv.Perm.permMatrix]

/-- The Bruhat Weyl element normalizes the diagonal torus. -/
theorem gl2WeylElement_mem_normalizer_diagonalTorus :
    GL2WeylElement R ∈
      Subgroup.normalizer (diagonalTorus R 2 : Set (GL (Fin 2) R)) := by
  rw [gl2WeylElement_eq_permutationGL_swap]
  exact permutationGL_mem_normalizer (Equiv.swap 0 1)

end WeylElement

section Field

variable {k : Type u} [Field k]

variable [Nontrivial kˣ]

/-- The coordinate permutation induced by the Bruhat Weyl element is the transposition. -/
theorem diagonalNormalizerPerm_gl2WeylElement :
    diagonalNormalizerPerm (k := k) (n := 2)
        ⟨GL2WeylElement k,
          gl2WeylElement_mem_normalizer_diagonalTorus (R := k)⟩ =
      Equiv.swap 0 1 := by
  simpa only [gl2WeylElement_eq_permutationGL_swap] using
    diagonalNormalizerPerm_permutationGL (k := k) (n := 2) (Equiv.swap 0 1)

end Field

section UpperTriangular

section CommRing

variable {R : Type u} [CommRing R] {n : ℕ}

namespace UpperTriangularGroup

/-- Every diagonal matrix is upper triangular, so the diagonal torus lies in the standard
upper-triangular subgroup. -/
theorem diagonalTorus_le :
    diagonalTorus R n ≤ upperTriangularGroup (Fin n) R := by
  intro g hg
  obtain ⟨d, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
  rw [mem_iff]
  intro i j hji
  rw [diagGL_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

/-- Conjugating by the permutation matrix of `σ` gives an upper-triangular matrix exactly when
the entries of `g` at `(σ i, σ j)` vanish for all `j < i`. -/
theorem permutationGL_inv_mul_mul_permutationGL_mem_iff {ι : Type*} [Fintype ι]
    [LinearOrder ι] (σ : Equiv.Perm ι) (g : GL ι R) :
    (permutationGL (k := R) σ)⁻¹ * g * permutationGL (k := R) σ ∈ upperTriangularGroup ι R ↔
      ∀ ⦃i j : ι⦄, j < i → (g : Matrix ι ι R) (σ i) (σ j) = 0 := by
  rw [mem_iff, Matrix.IsUpperTriangular, Matrix.BlockTriangular]
  simp only [id, coe_permutationGL_inv_mul_mul_permutationGL_apply]

end UpperTriangularGroup

end CommRing

section Field

variable {k : Type u} [Field k] [Nontrivial kˣ] {n : ℕ}

namespace UpperTriangularGroup

/-- A diagonal-normalizer element that is upper triangular is diagonal. Equivalently, an
upper-triangular monomial matrix cannot carry a nontrivial coordinate permutation. -/
theorem mem_diagonalTorus_of_mem
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (hg : (g : GL (Fin n) k) ∈ upperTriangularGroup (Fin n) k) :
    (g : GL (Fin n) k) ∈ diagonalTorus k n := by
  obtain ⟨d, σ, hfactor⟩ := mem_normalizer_diagonalTorus_iff_exists.mp g.property
  have hupper := mem_iff.mp hg
  have hle (ι : Fin n) : σ ι ≤ ι := by
    by_contra h
    have hzero := hupper (lt_of_not_ge h)
    have hentry := congrArg
      (fun x : GL (Fin n) k ↦ (x : Matrix (Fin n) (Fin n) k) (σ ι) ι) hfactor
    rw [hzero] at hentry
    simp only [Units.val_mul, diagGL_coe, permutationGL_coe, Matrix.diagonal_mul] at hentry
    have hperm : (σ⁻¹.permMatrix k) (σ ι) ι = 1 := by
      simp [Equiv.Perm.permMatrix]
    rw [hperm, mul_one] at hentry
    exact Units.ne_zero (d (σ ι)) hentry.symm
  have hσ : σ = 1 := by
    by_contra hne
    have hstrict : ∃ ι ∈ Finset.univ, (σ ι).val < ι.val := by
      have hnot : ¬ ∀ ι, σ ι = ι := by
        intro h
        apply hne
        apply Equiv.ext
        intro ι
        simpa using h ι
      obtain ⟨ι, hι⟩ := not_forall.mp hnot
      exact ⟨ι, Finset.mem_univ _,
        lt_of_le_of_ne (hle ι) fun hval ↦ hι (Fin.ext hval)⟩
    have hsum : (∑ ι : Fin n, (σ ι).val) = ∑ ι : Fin n, ι.val :=
      Equiv.sum_comp σ fun ι : Fin n ↦ ι.val
    have hsumlt : (∑ ι : Fin n, (σ ι).val) < ∑ ι : Fin n, ι.val :=
      Finset.sum_lt_sum (fun ι _ ↦ hle ι) hstrict
    exact hsumlt.ne hsum
  rw [hσ, map_one, mul_one] at hfactor
  exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, hfactor.symm⟩

/-- Over a field with at least two units, the intersection of the upper-triangular subgroup of
`GLₙ` with the normalizer of the diagonal torus is exactly the diagonal torus. -/
theorem inf_normalizer_diagonalTorus_eq :
    upperTriangularGroup (Fin n) k ⊓
        Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) =
      diagonalTorus k n := by
  apply le_antisymm
  · intro g hg
    exact mem_diagonalTorus_of_mem ⟨g, hg.2⟩ hg.1
  · intro g hg
    exact ⟨diagonalTorus_le hg, Subgroup.le_normalizer hg⟩

end UpperTriangularGroup

end Field

end UpperTriangular

end

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
theorem permutationGL_swap_mul_mul_permutationGL_mem (hab : a.val + 1 = b.val)
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
theorem closure_upperTriangularGroup_union_range_permutationGL (k : Type u) [Field k]
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

/-- Each element of a Bruhat cell `B τ B`, after left multiplication by an adjacent
transposition, belongs to a permutation double coset. -/
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

end TauCeti
