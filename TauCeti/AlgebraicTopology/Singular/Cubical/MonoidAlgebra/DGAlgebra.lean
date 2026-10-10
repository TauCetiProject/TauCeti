/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Graded
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The DG algebra of normalized cubical chains of a topological monoid

For a topological monoid `G`, the graded algebra `⨁ n, C^□_n(G; R)` of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Graded` is a differential graded algebra,
with the boundary as differential and `C^□_n` in cohomological degree `-n` (the convention
`C^{-n} = C_n`).

## Main definitions

* `TauCeti.cubicalChainGrading G R`: the `ℤ`-grading of `normalizedCubicalChainAlgebra G R`, with
  `C^□_n` in degree `-n`.
* `TauCeti.cubicalChainDifferential G R`: the boundary as an `R`-linear endomorphism.
* The `GradedAlgebra` instance on `cubicalChainGrading G R`, and the `Ring` instance on
  `normalizedCubicalChainAlgebra G R`.

## Main results

* `TauCeti.cubicalChain_isDGAlgebra`: `normalizedCubicalChainAlgebra G R` with this grading and
  differential is a differential graded algebra.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open DirectSum

namespace TauCeti

section Grading

variable (G : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G] (R : Type*) [CommRing R]

/-- The inclusion of the chains of dimension `n` into the graded algebra. -/
abbrev cubicalChainLof (n : ℕ) :
    NormalizedCubicalChain G R n →ₗ[R] normalizedCubicalChainAlgebra G R :=
  DirectSum.lof R ℕ (fun n ↦ NormalizedCubicalChain G R n) n

/-- The graded piece of cohomological degree `i` of the algebra of cubical chains: the chains of
dimension `-i` when `i ≤ 0`, and zero otherwise. -/
def cubicalChainGrading (i : ℤ) : Submodule R (normalizedCubicalChainAlgebra G R) :=
  if 0 ≤ -i then LinearMap.range (cubicalChainLof G R (-i).toNat) else ⊥

/-- Membership in a graded piece: zero, or a chain of the dimension `-i`. -/
theorem mem_cubicalChainGrading_iff {i : ℤ} {x : normalizedCubicalChainAlgebra G R} :
    x ∈ cubicalChainGrading G R i ↔
      x = 0 ∨ ∃ (n : ℕ) (y : NormalizedCubicalChain G R n), (n : ℤ) = -i ∧
        cubicalChainLof G R n y = x := by
  constructor
  · intro hx
    by_cases h : 0 ≤ -i
    · simp only [cubicalChainGrading, h, ↓reduceIte] at hx
      obtain ⟨y, rfl⟩ := hx
      exact Or.inr ⟨_, y, Int.toNat_of_nonneg h, rfl⟩
    · simp only [cubicalChainGrading, h, ↓reduceIte, Submodule.mem_bot] at hx
      exact Or.inl hx
  · rintro (rfl | ⟨n, y, hn, rfl⟩)
    · exact zero_mem _
    · have h : 0 ≤ -i := by omega
      have hn' : (-i).toNat = n := by omega
      simp only [cubicalChainGrading, h, ↓reduceIte]
      have key : ∀ k : ℕ, k = n → cubicalChainLof G R n y ∈
          LinearMap.range (cubicalChainLof G R k) := by
        rintro k rfl
        exact ⟨y, rfl⟩
      exact key _ hn'

/-- A chain of dimension `n` lies in cohomological degree `-n`. -/
theorem cubicalChainLof_mem {n : ℕ} (y : NormalizedCubicalChain G R n) :
    cubicalChainLof G R n y ∈ cubicalChainGrading G R (-(n : ℤ)) :=
  (mem_cubicalChainGrading_iff G R).2 (Or.inr ⟨n, y, by simp, rfl⟩)

/-- The Pontryagin product adds cohomological degrees. -/
instance : SetLike.GradedMonoid (cubicalChainGrading G R) where
  one_mem := (mem_cubicalChainGrading_iff G R).2
    (Or.inr ⟨0, NormalizedCubicalChain.one G R, by simp, by
      rw [DirectSum.lof_eq_of]
      rfl⟩)
  mul_mem := fun i j a b ha hb ↦ by
    rw [mem_cubicalChainGrading_iff] at ha hb ⊢
    rcases ha with rfl | ⟨m, y, hm, rfl⟩
    · left
      simp
    rcases hb with rfl | ⟨n, z, hn, rfl⟩
    · left
      simp
    right
    refine ⟨m + n, NormalizedCubicalChain.mul G R m n y z, by push_cast; omega, ?_⟩
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of,
      NormalizedCubicalChain.gMul_mul]

/-- The decomposition of the algebra of cubical chains along its `ℤ`-grading. -/
def cubicalChainDecompose :
    normalizedCubicalChainAlgebra G R →+ ⨁ i : ℤ, cubicalChainGrading G R i :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun i : ℤ ↦ cubicalChainGrading G R i) (-(n : ℤ))).comp
      ((cubicalChainLof G R n).codRestrict (cubicalChainGrading G R (-(n : ℤ)))
        (cubicalChainLof_mem G R)).toAddMonoidHom

/-- The algebra of cubical chains is the internal direct sum of its graded pieces. -/
instance : DirectSum.Decomposition (cubicalChainGrading G R) :=
  DirectSum.Decomposition.ofAddHom (ℳ := cubicalChainGrading G R) (cubicalChainDecompose G R)
    (by
      refine DirectSum.addHom_ext fun n y ↦ ?_
      simp [cubicalChainDecompose, DirectSum.lof_eq_of])
    (by
      refine DirectSum.addHom_ext fun i x ↦ ?_
      obtain ⟨x, hx⟩ := x
      rcases (mem_cubicalChainGrading_iff G R).1 hx with rfl | ⟨n, y, hn, rfl⟩
      · simp only [cubicalChainDecompose, DirectSum.coeAddMonoidHom_of, AddMonoidHom.comp_apply,
          AddMonoidHom.id_apply, map_zero]
        exact (map_zero (DirectSum.of (fun i : ℤ ↦ cubicalChainGrading G R i) i)).symm
      · obtain rfl : i = -(n : ℤ) := by omega
        simp [cubicalChainDecompose, DirectSum.lof_eq_of]
        rfl)

/-- The algebra of cubical chains is a `ℤ`-graded algebra. -/
instance :
    GradedAlgebra (R := R) (A := normalizedCubicalChainAlgebra G R) (cubicalChainGrading G R) :=
  { }


end Grading

section Differential

variable (G : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G] (R : Type*) [CommRing R]

open NormalizedCubicalChain

/-- The ring structure of the algebra of cubical chains. -/
instance : Ring (normalizedCubicalChainAlgebra G R) :=
  DirectSum.ring (fun n : ℕ ↦ NormalizedCubicalChain G R n)

omit [Monoid G] [ContinuousMul G] in
/-- Reindexing a chain does not change its image in the graded algebra. -/
theorem cubicalChainLof_cast {n m : ℕ} (h : n = m) (x : NormalizedCubicalChain G R n) :
    cubicalChainLof G R m (cast R h x) = cubicalChainLof G R n x := by
  subst h
  rw [cast_rfl]

/-- The product of homogeneous chains in the graded algebra. -/
theorem cubicalChainLof_mul {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (b : NormalizedCubicalChain G R q) :
    cubicalChainLof G R p a * cubicalChainLof G R q b =
      cubicalChainLof G R (p + q) (mul G R p q a b) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    NormalizedCubicalChain.gMul_mul]

/-- The boundary of the chains of dimension `n`, as a map into the graded algebra; it vanishes in
dimension `0`. -/
def cubicalChainBoundaryLof :
    ∀ n : ℕ, NormalizedCubicalChain G R n →ₗ[R] normalizedCubicalChainAlgebra G R
  | 0 => 0
  | k + 1 => (cubicalChainLof G R k).comp (boundary G R k)

/-- The differential of the algebra of cubical chains: the boundary, of cohomological degree
`+1`. -/
def cubicalChainDifferential :
    normalizedCubicalChainAlgebra G R →ₗ[R] normalizedCubicalChainAlgebra G R :=
  DirectSum.toModule R ℕ _ (cubicalChainBoundaryLof G R)

omit [Monoid G] [ContinuousMul G] in
/-- The differential on the chains of a given dimension. -/
theorem cubicalChainDifferential_lof (n : ℕ) (y : NormalizedCubicalChain G R n) :
    cubicalChainDifferential G R (cubicalChainLof G R n y) = cubicalChainBoundaryLof G R n y :=
  DirectSum.toModule_lof R n y

/-- The differential vanishes on `0`-chains. -/
@[simp]
theorem cubicalChainDifferential_lof_zero (y : NormalizedCubicalChain G R 0) :
    cubicalChainDifferential G R (cubicalChainLof G R 0 y) = 0 := by
  rw [cubicalChainDifferential_lof]
  rfl

omit [Monoid G] [ContinuousMul G] in
/-- The differential on `(k + 1)`-chains is the boundary. -/
@[simp]
theorem cubicalChainDifferential_lof_succ (k : ℕ) (y : NormalizedCubicalChain G R (k + 1)) :
    cubicalChainDifferential G R (cubicalChainLof G R (k + 1) y) =
      cubicalChainLof G R k (boundary G R k y) := by
  rw [cubicalChainDifferential_lof]
  rfl

/-- The sign `(-1) ^ (-n)` acts on the graded algebra as `(-1) ^ n ∈ R`. -/
theorem negOnePow_neg_natCast_smul (n : ℕ) (x : normalizedCubicalChainAlgebra G R) :
    (-(n : ℤ)).negOnePow • x = (-1 : R) ^ n • x := by
  have h : (((-(n : ℤ)).negOnePow : ℤ) : R) = (-1 : R) ^ n := by
    rw [Int.negOnePow_neg]
    exact Int.cast_negOnePow_natCast R n
  calc (-(n : ℤ)).negOnePow • x = ((-(n : ℤ)).negOnePow : ℤ) • x := Units.smul_def _ _
    _ = (((-(n : ℤ)).negOnePow : ℤ) : R) • x := (Int.cast_smul_eq_zsmul R _ x).symm
    _ = (-1 : R) ^ n • x := congrArg (· • x) h

/-- The graded Leibniz rule on homogeneous chains. -/
theorem cubicalChainDifferential_lof_mul_lof {m q : ℕ} (y : NormalizedCubicalChain G R m)
    (z : NormalizedCubicalChain G R q) :
    cubicalChainDifferential G R (cubicalChainLof G R m y * cubicalChainLof G R q z) =
      cubicalChainDifferential G R (cubicalChainLof G R m y) * cubicalChainLof G R q z +
        (-(m : ℤ)).negOnePow •
          (cubicalChainLof G R m y * cubicalChainDifferential G R (cubicalChainLof G R q z)) := by
  rw [cubicalChainLof_mul, negOnePow_neg_natCast_smul]
  rcases m with _ | k <;> rcases q with _ | j
  · rw [cubicalChainDifferential_lof G R (0 + 0)]
    change (0 : normalizedCubicalChainAlgebra G R) = _
    rw [cubicalChainDifferential_lof_zero, cubicalChainDifferential_lof_zero, zero_mul, mul_zero,
      zero_add]
    exact (smul_zero (M := R) (A := normalizedCubicalChainAlgebra G R) ((-1 : R) ^ 0)).symm
  · have hL : cubicalChainDifferential G R
        (cubicalChainLof G R (0 + (j + 1)) (mul G R 0 (j + 1) y z)) =
          cubicalChainLof G R (0 + j) (mul G R 0 j y (boundary G R j z)) := by
      rw [cubicalChainDifferential_lof G R (0 + (j + 1))]
      change cubicalChainLof G R (0 + j) (boundary G R (0 + j) (mul G R 0 (j + 1) y z)) = _
      congr 1
      apply cast_injective R (Nat.zero_add j)
      exact (boundary_cast R (Nat.zero_add j) (mul G R 0 (j + 1) y z)).symm.trans
        (boundary_mul_zero_left y z)
    rw [hL, cubicalChainDifferential_lof_zero, cubicalChainDifferential_lof_succ,
      cubicalChainLof_mul, zero_mul, zero_add (M := normalizedCubicalChainAlgebra G R), pow_zero]
    exact (one_smul R
      (cubicalChainLof G R (0 + j) (mul G R 0 j y (boundary G R j z)))).symm
  · rw [cubicalChainDifferential_lof G R (k + 1 + 0)]
    change cubicalChainLof G R k (boundary G R k (mul G R (k + 1) 0 y z)) = _
    rw [boundary_mul_zero_right, cubicalChainDifferential_lof_succ,
      cubicalChainDifferential_lof_zero, mul_zero, cubicalChainLof_mul,
      show ((-1 : R) ^ (k + 1)) • (0 : normalizedCubicalChainAlgebra G R) = 0 from
        smul_zero (M := R) (A := normalizedCubicalChainAlgebra G R) _,
      add_zero (M := normalizedCubicalChainAlgebra G R)]
    rfl
  · rw [cubicalChainDifferential_lof G R (k + 1 + (j + 1))]
    change cubicalChainLof G R (k + 1 + j) (boundary G R (k + 1 + j)
      (mul G R (k + 1) (j + 1) y z)) = _
    have h' : k + 1 + j = k + j + 1 := by omega
    have e : cast R h' (boundary G R (k + 1 + j) (mul G R (k + 1) (j + 1) y z)) =
        mul G R k (j + 1) (boundary G R k y) z +
          (-1 : R) ^ (k + 1) • cast R h' (mul G R (k + 1) j y (boundary G R j z)) :=
      (boundary_cast R h' (mul G R (k + 1) (j + 1) y z)).symm.trans (boundary_mul y z)
    rw [cubicalChainDifferential_lof_succ, cubicalChainDifferential_lof_succ, cubicalChainLof_mul,
      cubicalChainLof_mul, ← cubicalChainLof_cast G R h', e, map_add, map_smul,
      cubicalChainLof_cast]
    rfl

/-- **The normalized cubical chains of a topological monoid form a differential graded algebra**:
`⨁ n, C^□_n(G; R)` with the Pontryagin product, `C^□_n` in cohomological degree `-n`, and the
boundary as differential. -/
theorem cubicalChain_isDGAlgebra :
    IsDGAlgebra (R := R) (A := normalizedCubicalChainAlgebra G R) (cubicalChainGrading G R)
      (cubicalChainDifferential G R) where
  map_mem := fun {p} {a} ha ↦ by
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨n, y, hn, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    rcases n with _ | k
    · rw [cubicalChainDifferential_lof_zero]
      exact zero_mem _
    · rw [cubicalChainDifferential_lof_succ]
      exact (mem_cubicalChainGrading_iff G R).2 (Or.inr ⟨k, _, by push_cast at hn; omega, rfl⟩)
  sq_zero := fun a ↦ by
    induction a using DirectSum.induction_on with
    | zero => simp
    | of n y =>
      rw [← DirectSum.lof_eq_of R]
      rcases n with _ | k
      · rw [cubicalChainDifferential_lof_zero, map_zero]
      rw [cubicalChainDifferential_lof_succ]
      rcases k with _ | j
      · rw [cubicalChainDifferential_lof_zero]
      · rw [cubicalChainDifferential_lof_succ, ← LinearMap.comp_apply (boundary G R j),
          boundary_boundary, LinearMap.zero_apply, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  leibniz := fun {p} {a} ha b ↦ by
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨m, y, hm, rfl⟩
    · simp
    obtain rfl : p = -(m : ℤ) := by omega
    induction b using DirectSum.induction_on with
    | zero => simp
    | of q z =>
      rw [← DirectSum.lof_eq_of R]
      exact cubicalChainDifferential_lof_mul_lof G R y z
    | add b b' hb hb' =>
      rw [mul_add, map_add, hb, hb', map_add, mul_add, mul_add, smul_add]
      abel

end Differential

end TauCeti

end
