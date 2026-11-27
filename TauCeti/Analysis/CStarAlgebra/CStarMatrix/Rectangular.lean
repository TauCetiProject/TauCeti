/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Rectangular C⋆-matrix algebra, amplifications, and operator norms

Additional algebraic identities for rectangular `CStarMatrix` operations (`1 * M`, `M * 1`,
negation, subtraction, conjugate transpose linearity, `map` homomorphic laws, and proper-star
cancellation), functorial non-unital (`CStarMatrix.mapₙₐ`) and unital (`CStarMatrix.mapₐ`)
entrywise amplifications, and rectangular operator norm properties.

## Main declarations

* `CStarMatrix.mapₙₐ_id`, `CStarMatrix.mapₙₐ_comp`, `CStarMatrix.mapₐ`,
  `CStarMatrix.mapₐ_apply`, `CStarMatrix.mapₐ_id`, `CStarMatrix.mapₐ_comp`: functorial non-unital
  and unital entrywise matrix amplifications.
* `CStarMatrix.ofMatrix_one`, `CStarMatrix.ofMatrix_mul`, `CStarMatrix.ofMatrix_conjTranspose`,
  `CStarMatrix.conjTranspose_mul_self_eq_zero`, `CStarMatrix.self_mul_conjTranspose_eq_zero`:
  conversion and proper-star cancellation for rectangular matrices.
* `CStarMatrix.toCLM_mul`, `CStarMatrix.norm_mul_le_rectangular`, `CStarMatrix.norm_mapₙₐ`,
  `CStarMatrix.norm_reindexₐ`: rectangular operator-norm submultiplicativity and isometry of
  amplification and reindexing.
* `CStarMatrix.compress_one_apply`, `CStarMatrix.star_compress_one_mul_self`,
  `CStarMatrix.compress_one_mul_star_self`, `CStarMatrix.compress_self_nonneg`: compression by
  `1` on the left, conjugation identities, and preservation of positivity.
-/

public section

open Matrix

namespace CStarMatrix

section MapNA

variable {R n A B C : Type*} [Fintype n] [Semiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
  [NonUnitalNonAssocSemiring C] [Module R C] [Star C]

/-- Entrywise amplification of the identity non-unital ⋆-algebra homomorphism is the identity. -/
@[simp] theorem mapₙₐ_id :
    mapₙₐ (n := n) (NonUnitalStarAlgHom.id R A) =
      NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by ext; rfl

/-- Entrywise non-unital matrix amplification preserves composition. -/
theorem mapₙₐ_comp (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (n := n) (g.comp f) = (mapₙₐ (n := n) g).comp (mapₙₐ (n := n) f) := by ext; rfl

end MapNA

section MapA

variable {R n A B C : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Entrywise amplification of a unital ⋆-algebra homomorphism to square C⋆-matrices. -/
def mapₐ (f : A →⋆ₐ[R] B) : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B :=
  let g := mapₙₐ (n := n) f.toNonUnitalStarAlgHom
  { toFun := g
    map_one' := by
      ext i j; by_cases h : i = j <;> simp [g, one_apply, h]
    map_mul' := _root_.map_mul g
    map_zero' := _root_.map_zero g
    map_add' := _root_.map_add g
    commutes' := fun _ => by
      ext i j
      by_cases h : i = j <;> simp [g, algebraMap_apply, h, AlgHomClass.commutes]
    map_star' := map_star g }

/-- Evaluating entrywise unital matrix amplification at an entry `(i, j)`. -/
@[simp] theorem mapₐ_apply (f : A →⋆ₐ[R] B) (M : CStarMatrix n n A) (i j : n) :
    mapₐ f M i j = f (M i j) := (rfl)

/-- Entrywise amplification of the identity unital ⋆-algebra homomorphism is the identity. -/
@[simp] theorem mapₐ_id :
    mapₐ (n := n) (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by ext; rfl

/-- Entrywise unital matrix amplification preserves composition. -/
theorem mapₐ_comp (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapₐ (n := n) (g.comp f) = (mapₐ (n := n) g).comp (mapₐ (n := n) f) := by ext; rfl

end MapA

section RectangularAlgebra

variable {l m n o R A B : Type*}

@[simp] theorem ofMatrix_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix (1 : Matrix n n A) = (1 : CStarMatrix n n A) := (rfl)

@[simp] theorem ofMatrix_mul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix (M * N) = ofMatrix M * ofMatrix N := (rfl)

@[simp] theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := (rfl)

@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  Matrix.one_mul (ofMatrix.symm M)

@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  Matrix.mul_one (ofMatrix.symm M)

@[simp] protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (-M) * N = -(M * N) :=
  Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : M * (-N) = -(M * N) :=
  Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) : (L - M) * N = L * N - M * N :=
  Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) : L * (M - N) = L * M - L * N :=
  Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  Matrix.conjTranspose_add (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose :=
  Matrix.conjTranspose_neg (ofMatrix.symm M)

@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  Matrix.conjTranspose_sub (ofMatrix.symm M) (ofMatrix.symm N)

@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (r : R) (M : CStarMatrix m n A) :
    (r • M).conjTranspose = star r • M.conjTranspose :=
  Matrix.conjTranspose_smul r (ofMatrix.symm M)

@[simp] theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 := Matrix.conjTranspose_one

@[simp] protected theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := ext fun _ _ => hf

@[simp] protected theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B] {f : A → B}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) : (1 : CStarMatrix n n A).map f = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h, hf0, hf1]

protected theorem map_add [Add A] [Add B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a + b) = f a + f b) : (M + N).map f = M.map f + N.map f :=
  ext fun i j => hf (M i j) (N i j)

protected theorem map_sub [Sub A] [Sub B] (M N : CStarMatrix m n A) {f : A → B}
    (hf : ∀ a b, f (a - b) = f a - f b) : (M - N).map f = M.map f - N.map f :=
  ext fun i j => hf (M i j) (N i j)

protected theorem map_mul [Fintype m] [AddCommMonoid A] [Mul A] [AddCommMonoid B] [Mul B]
    {F : Type*} [FunLike F A B] [AddMonoidHomClass F A B] [MulHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i j; simp [mul_apply, map_sum, _root_.map_mul]

theorem map_conjTranspose [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map f = (M.map f).conjTranspose := by
  ext i j; simp [map_star]

/-- In a proper star-ordered ring, `Mᴴ * M = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp] theorem conjTranspose_mul_self_eq_zero [Fintype m] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero (A := ofMatrix.symm M)

/-- In a proper star-ordered ring, `M * Mᴴ = 0` iff `M = 0` for rectangular C⋆-matrices. -/
@[simp] theorem self_mul_conjTranspose_eq_zero [Fintype n] [PartialOrder A] [NonUnitalRing A]
    [StarRing A] [StarOrderedRing A] [IsProperStar A] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 :=
  Matrix.self_mul_conjTranspose_eq_zero (A := ofMatrix.symm M)

end RectangularAlgebra

section RectangularNorms

/-- `toCLM` reverses rectangular matrix multiplication. -/
theorem toCLM_mul {l m n A : Type*} [Fintype l] [Fintype m] [NonUnitalCStarAlgebra A]
    (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    toCLM (V * W) = (toCLM W).comp (toCLM V) := by
  ext x j
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply, WithCStarModule.equiv_symm_pi_apply]
  exact congrFun (Matrix.vecMul_vecMul x (ofMatrix.symm V) (ofMatrix.symm W)).symm j

/-- Submultiplicativity of the operator norm for rectangular C⋆-matrices. -/
theorem norm_mul_le_rectangular {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (V : CStarMatrix l m A) (W : CStarMatrix m n A) :
    ‖V * W‖ ≤ ‖V‖ * ‖W‖ := by
  rw [norm_def, toCLM_mul, mul_comm ‖V‖ ‖W‖]
  exact (toCLM W).opNorm_comp_le (toCLM V)

/-- Matrix amplification of an injective non-unital ⋆-algebra homomorphism is isometric. -/
theorem norm_mapₙₐ {n A B : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {f : A →⋆ₙₐ[ℂ] B} (hf : Function.Injective f) (M : CStarMatrix n n A) :
    ‖mapₙₐ f M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map (mapₙₐ f) (CStarMatrix.map_injective hf) M

/-- Reindexing a square C⋆-matrix preserves its norm. -/
@[simp] theorem norm_reindexₐ {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ ℂ A e M‖ = ‖M‖ := StarAlgEquiv.norm_map (reindexₐ ℂ A e) M

end RectangularNorms

section Compression

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Compressing by the standard basis on the left multiplies by `f⋆` on the right:
`compress 1 f x = x f⋆`. -/
theorem compress_one_apply [DecidableEq m] {ι' : Type*} (f : ι' → n → ℂ) (x : CStarMatrix m n A)
    (k : m) (t' : ι') : compress (1 : CStarMatrix m m ℂ) f x k t' = ∑ l, star (f t' l) • x k l := by
  simp [compress_apply (1 : CStarMatrix m m ℂ) f, one_apply, ite_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- For `R ∈ M_n(A)` and `u ∈ M_n(ℂ)`, the product `z = R u⋆ = compress 1 u R` satisfies
`z⋆z = u (R⋆R) u⋆ = compress u u (R⋆R)`. -/
theorem star_compress_one_mul_self [DecidableEq n] (u : CStarMatrix n n ℂ)
    (R : CStarMatrix n n A) :
    star (compress (1 : CStarMatrix n n ℂ) u R) * compress (1 : CStarMatrix n n ℂ) u R =
      compress u u (star R * R) := by
  ext t t'
  simp only [mul_apply, star_apply, compress_one_apply u, compress_apply u u, star_sum, star_smul,
    star_star, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum]
  -- Reorder `∑ k, ∑ l, ∑ j` to `∑ j, ∑ l, ∑ k`.
  exact Finset.sum_comm_cycle.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

omit [PartialOrder A] [StarOrderedRing A] in
/-- For `R ∈ M_n(A)` and `u ∈ M_n(ℂ)` with `u⋆u = 1`, the product `z = R u⋆ = compress 1 u R`
satisfies `zz⋆ = RR⋆`. -/
theorem compress_one_mul_star_self [DecidableEq n] {u : CStarMatrix n n ℂ} (hu : star u * u = 1)
    (R : CStarMatrix n n A) :
    compress (1 : CStarMatrix n n ℂ) u R * star (compress (1 : CStarMatrix n n ℂ) u R) =
      R * star R := by
  have h (k l : n) : ∑ t, star (u t k) * u t l = if k = l then 1 else 0 := by
    simpa [mul_apply, star_apply, one_apply] using CStarMatrix.ext_iff.mpr hu k l
  ext i j
  simp only [mul_apply, star_apply, compress_one_apply u, star_sum, star_smul, star_star,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  -- Reorder `∑ t, ∑ k, ∑ l` to `∑ l, ∑ k, ∑ t` and use `u⋆u = 1`.
  rw [← Finset.sum_comm_cycle]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Compression preserves positivity**: `0 ≤ x` gives `0 ≤ compress e e x` for any scalar
vectors `e t ∈ ℂⁿ`, i.e. `0 ≤ e x e⋆`. -/
theorem compress_self_nonneg {ι : Type*} [Fintype ι] (e : ι → n → ℂ) {x : CStarMatrix n n A}
    (hx : 0 ≤ x) : 0 ≤ compress e e x := by
  refine nonneg_iff_forall_sum_nonneg.mpr fun y => ?_
  -- The quadratic form at `y` is that of `x` at `w l = ∑ t, star (e t l) • y t`.
  convert nonneg_iff_forall_sum_nonneg.mp hx fun l => ∑ t, star (e t l) • y t using 1
  simp only [compress_apply, star_sum, star_smul, star_star, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul, ← Fintype.sum_prod_type']
  -- reindex `(t, t', k, l) ↦ (k, l, t', t)`
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1), fun q => (q.2.2.2, q.2.2.1, q.1, q.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => by
    dsimp only [Equiv.coe_fn_mk]
    rw [mul_comm (e _ _)]

end Compression

end CStarMatrix
