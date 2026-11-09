/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Kronecker products of operators on finite coordinates

For continuous linear maps `f : (Fin m → R) →L[R] (Fin m' → R)` and
`g : (Fin n → R) →L[R] (Fin n' → R)` over a commutative semiring `R` with a topology,
`ContinuousLinearMap.kronecker f g` is their tensor product acting on `Fin (m * n) → R`, where
the coordinate pair `(i, j)` is the index `finProdFinEquiv (i, j)`. Viewing a vector as an
`m × n` array, it applies `g` to every row and then `f` to every column. Its matrix is the
reindexed Kronecker product of the matrices of `f` and `g`
(`ContinuousLinearMap.toMatrix'_kronecker`).

The product is functorial (`ContinuousLinearMap.kronecker_comp_kronecker`,
`ContinuousLinearMap.id_kronecker_id`) and additive and homogeneous in each factor. These are
the transition maps and morphisms of tensor products of vector bundles presented by finite
coordinate charts. The norm bound and continuity in the two factors are in
`TauCeti.Analysis.Normed.Operator.Kronecker`.

The coordinate isomorphisms `ContinuousLinearEquiv.kroneckerAssoc`, `kroneckerComm`,
`kroneckerLid` and `kroneckerRid` reindex `Fin ((m * n) * p)`, `Fin (m * n)`, `Fin (1 * n)` and
`Fin (n * 1)` along the associativity, symmetry and unit equivalences of index pairs. They
intertwine Kronecker products (`ContinuousLinearMap.kroneckerAssoc_comp_kronecker`,
`kroneckerComm_comp_kronecker`, `kroneckerLid_comp_kronecker`, `kroneckerRid_comp_kronecker`)
and satisfy the pentagon, triangle and hexagon identities. These are the structure maps of the
symmetric monoidal structure on bundles presented by finite coordinate charts.

The matrix comparison uses Mathlib's `Matrix.kronecker` and `LinearMap.toMatrix'`; through it
the mixed-product law is Mathlib's `Matrix.mul_kronecker_mul`.
-/

public section

open scoped Kronecker

namespace ContinuousLinearMap

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]
  {m n m' n' m'' n'' : ℕ}

/-- The Kronecker (tensor) product of two operators on finite coordinates, with the coordinate
pair `(i, j)` stored at index `finProdFinEquiv (i, j)`. -/
def kronecker (f : (Fin m → R) →L[R] (Fin m' → R)) (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (Fin (m * n) → R) →L[R] (Fin (m' * n') → R) :=
  pi fun k ↦ (proj (finProdFinEquiv.symm k).1).comp <| f.comp <| pi fun i ↦
    (proj (finProdFinEquiv.symm k).2).comp <| g.comp <| pi fun j ↦ proj (finProdFinEquiv (i, j))

section Apply

variable (f f₂ : (Fin m → R) →L[R] (Fin m' → R)) (g g₂ : (Fin n → R) →L[R] (Fin n' → R))

/-- The Kronecker product applies `g` to the rows and then `f` to the columns. -/
@[simp] theorem kronecker_apply (v : Fin (m * n) → R) (i : Fin m') (j : Fin n') :
    f.kronecker g v (finProdFinEquiv (i, j)) =
      f (fun i' ↦ g (fun j' ↦ v (finProdFinEquiv (i', j'))) j) i := by
  simp only [kronecker, coe_pi', coe_comp, Function.comp_apply, proj_apply,
    Equiv.symm_apply_apply]

/-- The matrix of a Kronecker product is the reindexed Kronecker product of the matrices. -/
theorem toMatrix'_kronecker :
    LinearMap.toMatrix' (f.kronecker g : (Fin (m * n) → R) →ₗ[R] Fin (m' * n') → R) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (LinearMap.toMatrix' (f : (Fin m → R) →ₗ[R] Fin m' → R) ⊗ₖ
          LinearMap.toMatrix' (g : (Fin n → R) →ₗ[R] Fin n' → R)) := by
  ext k l
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective l
  -- The columns of a basis array are zero except for the basis column of `g`.
  have h : (fun i'' ↦ g (fun j'' ↦ Pi.single (M := fun _ ↦ R) (finProdFinEquiv (i', j')) 1
      (finProdFinEquiv (i'', j''))) j) = g (Pi.single j' 1) j • Pi.single i' 1 := by
    ext i''
    have hrow : (fun j'' ↦ Pi.single (M := fun _ ↦ R) (finProdFinEquiv (i', j')) 1
        (finProdFinEquiv (i'', j''))) = if i'' = i' then Pi.single j' 1 else 0 := by
      ext j''
      by_cases hi : i'' = i' <;> simp [Pi.single_apply, hi]
    rw [hrow]
    by_cases hi : i'' = i' <;> simp [hi]
  simp only [LinearMap.toMatrix'_apply, coe_coe, kronecker_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kronecker_apply, h, map_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

@[simp] theorem id_kronecker_id :
    (ContinuousLinearMap.id R (Fin m → R)).kronecker (ContinuousLinearMap.id R (Fin n → R)) =
      ContinuousLinearMap.id R _ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem add_kronecker [ContinuousAdd R] :
    (f + f₂).kronecker g = f.kronecker g + f₂.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem kronecker_add [ContinuousAdd R] :
    f.kronecker (g + g₂) = f.kronecker g + f.kronecker g₂ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, _root_.add_apply, Pi.add_apply]
  rw [← Pi.add_def, map_add, Pi.add_apply]

theorem smul_kronecker [ContinuousConstSMul R R] (c : R) :
    (c • f).kronecker g = c • f.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

theorem kronecker_smul [ContinuousConstSMul R R] (c : R) :
    f.kronecker (c • g) = c • f.kronecker g := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, _root_.smul_apply, Pi.smul_apply]
  rw [← Pi.smul_def, map_smul, Pi.smul_apply]

end Apply

/-- The mixed-product law: Kronecker products compose factorwise. This is
`Matrix.mul_kronecker_mul` for the matrices of the operators. -/
theorem kronecker_comp_kronecker (f : (Fin m' → R) →L[R] (Fin m'' → R))
    (g : (Fin n' → R) →L[R] (Fin n'' → R)) (f' : (Fin m → R) →L[R] (Fin m' → R))
    (g' : (Fin n → R) →L[R] (Fin n' → R)) :
    (f.kronecker g).comp (f'.kronecker g') = (f.comp f').kronecker (g.comp g') := by
  refine coe_injective <| LinearMap.toMatrix'.injective ?_
  -- Pass to the reindexed Kronecker products of the matrices of the operators.
  simp only [toLinearMap_comp, LinearMap.toMatrix'_comp, toMatrix'_kronecker]
  -- Reindexing along the shared middle index commutes with matrix multiplication.
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  -- What remains is the mixed-product law for matrices.
  rw [Matrix.mul_kronecker_mul]

@[simp] theorem zero_kronecker (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (0 : (Fin m → R) →L[R] (Fin m' → R)).kronecker g = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

@[simp] theorem kronecker_zero (f : (Fin m → R) →L[R] (Fin m' → R)) :
    f.kronecker (0 : (Fin n → R) →L[R] (Fin n' → R)) = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [kronecker_apply, zero_apply, Pi.zero_apply]
  rw [← Pi.zero_def, map_zero, Pi.zero_apply]

end ContinuousLinearMap

/-! ### Coherence isomorphisms of Kronecker coordinates -/

namespace ContinuousLinearEquiv

variable (R : Type*) [CommSemiring R] [TopologicalSpace R]

/-- The associativity isomorphism of Kronecker coordinates, moving the entry at
`((i, j), k)` to `(i, (j, k))`. Since `finProdFinEquiv` lists pairs lexicographically, both
positions are the same natural number, so this only casts the index type. -/
def kroneckerAssoc (m n p : ℕ) : (Fin (m * n * p) → R) ≃L[R] (Fin (m * (n * p)) → R) :=
  (piCongrLeft R (fun _ ↦ R) (finCongr (Nat.mul_assoc m n p).symm)).symm

/-- The symmetry isomorphism of Kronecker coordinates, moving the entry at `(i, j)` to
`(j, i)`. -/
def kroneckerComm (m n : ℕ) : (Fin (m * n) → R) ≃L[R] (Fin (n * m) → R) :=
  (piCongrLeft R (fun _ ↦ R)
    (finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv))).symm

/-- The left unit isomorphism of Kronecker coordinates, reading the entry at `(0, j)` as the
`j`th coordinate. -/
def kroneckerLid (n : ℕ) : (Fin (1 * n) → R) ≃L[R] (Fin n → R) :=
  (piCongrLeft R (fun _ ↦ R) (finCongr (Nat.one_mul n).symm)).symm

/-- The right unit isomorphism of Kronecker coordinates, reading the entry at `(i, 0)` as the
`i`th coordinate. -/
def kroneckerRid (n : ℕ) : (Fin (n * 1) → R) ≃L[R] (Fin n → R) :=
  (piCongrLeft R (fun _ ↦ R) (finCongr (Nat.mul_one n).symm)).symm

variable {R} {m n p : ℕ}

@[simp] theorem kroneckerAssoc_apply (v : Fin (m * n * p) → R) (i : Fin m) (j : Fin n)
    (k : Fin p) :
    kroneckerAssoc R m n p v (finProdFinEquiv (i, finProdFinEquiv (j, k))) =
      v (finProdFinEquiv (finProdFinEquiv (i, j), k)) := by
  -- Both pairs sit at the position `k + p * j + p * n * i`.
  have h : finCongr (Nat.mul_assoc m n p).symm (finProdFinEquiv (i, finProdFinEquiv (j, k))) =
      finProdFinEquiv (finProdFinEquiv (i, j), k) := by
    ext
    simp only [finProdFinEquiv, Equiv.coe_fn_mk, finCongr_apply, Fin.val_cast]
    ring
  exact congrArg v h

@[simp] theorem kroneckerComm_apply (v : Fin (m * n) → R) (i : Fin m) (j : Fin n) :
    kroneckerComm R m n v (finProdFinEquiv (j, i)) = v (finProdFinEquiv (i, j)) :=
  congrArg v (by simp)

@[simp] theorem kroneckerLid_apply (v : Fin (1 * n) → R) (j : Fin n) :
    kroneckerLid R n v j = v (finProdFinEquiv (0, j)) :=
  congrArg v (by ext; simp [finProdFinEquiv])

@[simp] theorem kroneckerRid_apply (v : Fin (n * 1) → R) (i : Fin n) :
    kroneckerRid R n v i = v (finProdFinEquiv (i, 0)) :=
  congrArg v (by ext; simp [finProdFinEquiv])

@[simp] theorem kroneckerAssoc_symm_apply (v : Fin (m * (n * p)) → R) (i : Fin m) (j : Fin n)
    (k : Fin p) :
    (kroneckerAssoc R m n p).symm v (finProdFinEquiv (finProdFinEquiv (i, j), k)) =
      v (finProdFinEquiv (i, finProdFinEquiv (j, k))) := by
  have h := kroneckerAssoc_apply ((kroneckerAssoc R m n p).symm v) i j k
  rw [apply_symm_apply] at h
  exact h.symm

@[simp] theorem kroneckerLid_symm_apply (v : Fin n → R) (j : Fin n) :
    (kroneckerLid R n).symm v (finProdFinEquiv (0, j)) = v j := by
  have h := kroneckerLid_apply ((kroneckerLid R n).symm v) j
  rw [apply_symm_apply] at h
  exact h.symm

@[simp] theorem kroneckerRid_symm_apply (v : Fin n → R) (i : Fin n) :
    (kroneckerRid R n).symm v (finProdFinEquiv (i, 0)) = v i := by
  have h := kroneckerRid_apply ((kroneckerRid R n).symm v) i
  rw [apply_symm_apply] at h
  exact h.symm

/-- Swapping Kronecker coordinates twice is the identity. -/
@[simp] theorem kroneckerComm_symm (m n : ℕ) :
    (kroneckerComm R m n).symm = kroneckerComm R n m := by
  refine ContinuousLinearEquiv.ext <| funext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  have h := kroneckerComm_apply ((kroneckerComm R m n).symm v) i j
  rw [apply_symm_apply] at h
  rw [kroneckerComm_apply, ← h]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open ContinuousLinearEquiv

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] {m n p m' n' p' : ℕ}

/-- Kronecker products are associative up to the coordinate isomorphism `kroneckerAssoc`. This is
the operator form, on `finProdFinEquiv` coordinates, of Mathlib's `Matrix.kronecker_assoc`. -/
theorem kroneckerAssoc_comp_kronecker (f : (Fin m → R) →L[R] (Fin m' → R))
    (g : (Fin n → R) →L[R] (Fin n' → R)) (h : (Fin p → R) →L[R] (Fin p' → R)) :
    (kroneckerAssoc R m' n' p' : (Fin (m' * n' * p') → R) →L[R] _).comp
        ((f.kronecker g).kronecker h) =
      (f.kronecker (g.kronecker h)).comp
        (kroneckerAssoc R m n p : (Fin (m * n * p) → R) →L[R] _) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- The Kronecker product with the identity of the one-dimensional space on the left is the
original operator, up to `kroneckerLid`. -/
theorem kroneckerLid_comp_kronecker (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (kroneckerLid R n' : (Fin (1 * n') → R) →L[R] _).comp
        ((ContinuousLinearMap.id R (Fin 1 → R)).kronecker g) =
      g.comp (kroneckerLid R n : (Fin (1 * n) → R) →L[R] _) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun j ↦ ?_
  have hv : kroneckerLid R n v = fun j' ↦ v (finProdFinEquiv (0, j')) :=
    funext (kroneckerLid_apply v)
  simp [hv]

/-- The Kronecker product with the identity of the one-dimensional space on the right is the
original operator, up to `kroneckerRid`. -/
theorem kroneckerRid_comp_kronecker (f : (Fin m → R) →L[R] (Fin m' → R)) :
    (kroneckerRid R m' : (Fin (m' * 1) → R) →L[R] _).comp
        (f.kronecker (ContinuousLinearMap.id R (Fin 1 → R))) =
      f.comp (kroneckerRid R m : (Fin (m * 1) → R) →L[R] _) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun i ↦ ?_
  have hv : kroneckerRid R m v = fun i' ↦ v (finProdFinEquiv (i', 0)) :=
    funext (kroneckerRid_apply v)
  simp [hv]

/-- Kronecker products are commutative up to the coordinate isomorphism `kroneckerComm`. -/
theorem kroneckerComm_comp_kronecker (f : (Fin m → R) →L[R] (Fin m' → R))
    (g : (Fin n → R) →L[R] (Fin n' → R)) :
    (kroneckerComm R m' n' : (Fin (m' * n') → R) →L[R] _).comp (f.kronecker g) =
      (g.kronecker f).comp (kroneckerComm R m n : (Fin (m * n) → R) →L[R] _) := by
  -- A Kronecker product with an identity factor visibly commutes with the coordinate swap;
  -- the general case factors as `(f ⊗ 1) ∘ (1 ⊗ g)` and `(1 ⊗ f) ∘ (g ⊗ 1)`.
  have hf : (kroneckerComm R m' n' : (Fin (m' * n') → R) →L[R] _).comp
      (f.kronecker (ContinuousLinearMap.id R (Fin n' → R))) =
        ((ContinuousLinearMap.id R (Fin n' → R)).kronecker f).comp
          (kroneckerComm R m n' : (Fin (m * n') → R) →L[R] _) := by
    refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp
  have hg : (kroneckerComm R m n' : (Fin (m * n') → R) →L[R] _).comp
      ((ContinuousLinearMap.id R (Fin m → R)).kronecker g) =
        (g.kronecker (ContinuousLinearMap.id R (Fin m → R))).comp
          (kroneckerComm R m n : (Fin (m * n) → R) →L[R] _) := by
    refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp
  calc (kroneckerComm R m' n' : (Fin (m' * n') → R) →L[R] _).comp (f.kronecker g)
      = ((kroneckerComm R m' n' : (Fin (m' * n') → R) →L[R] _).comp
          (f.kronecker (ContinuousLinearMap.id R (Fin n' → R)))).comp
          ((ContinuousLinearMap.id R (Fin m → R)).kronecker g) := by
        rw [comp_assoc, kronecker_comp_kronecker, comp_id, id_comp]
    _ = ((ContinuousLinearMap.id R (Fin n' → R)).kronecker f).comp
          ((g.kronecker (ContinuousLinearMap.id R (Fin m → R))).comp
            (kroneckerComm R m n : (Fin (m * n) → R) →L[R] _)) := by
        rw [hf, comp_assoc, hg]
    _ = (g.kronecker f).comp (kroneckerComm R m n : (Fin (m * n) → R) →L[R] _) := by
        rw [← comp_assoc, kronecker_comp_kronecker, comp_id, id_comp]

/-! The coherence laws of the Kronecker structure isomorphisms: Mac Lane's pentagon and
triangle, and the two hexagons of a braiding. They are identities between coordinate
permutations. -/

/-- The pentagon identity for `kroneckerAssoc`: the two ways of reassociating
`((i, j), k), l` to `(i, (j, (k, l)))` agree. -/
theorem kroneckerAssoc_pentagon (m n p q : ℕ) :
    ((ContinuousLinearMap.id R (Fin m → R)).kronecker
        (kroneckerAssoc R n p q : (Fin (n * p * q) → R) →L[R] _)).comp
      ((kroneckerAssoc R m (n * p) q : (Fin (m * (n * p) * q) → R) →L[R] _).comp
        ((kroneckerAssoc R m n p : (Fin (m * n * p) → R) →L[R] _).kronecker
          (ContinuousLinearMap.id R (Fin q → R)))) =
      (kroneckerAssoc R m n (p * q) :
          (Fin (m * n * (p * q)) → R) →L[R] (Fin (m * (n * (p * q))) → R)).comp
        (kroneckerAssoc R (m * n) p q : (Fin (m * n * p * q) → R) →L[R] _) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨l, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- The triangle identity relating `kroneckerAssoc` with the unit isomorphisms. -/
theorem kroneckerAssoc_triangle (m n : ℕ) :
    ((ContinuousLinearMap.id R (Fin m → R)).kronecker
        (kroneckerLid R n : (Fin (1 * n) → R) →L[R] _)).comp
      (kroneckerAssoc R m 1 n : (Fin (m * 1 * n) → R) →L[R] _) =
      (kroneckerRid R m : (Fin (m * 1) → R) →L[R] _).kronecker
        (ContinuousLinearMap.id R (Fin n → R)) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- The first hexagon identity for the coordinate swap `kroneckerComm`. -/
theorem kroneckerComm_hexagon_forward (m n p : ℕ) :
    (kroneckerAssoc R n p m : (Fin (n * p * m) → R) →L[R] _).comp
      ((kroneckerComm R m (n * p) : (Fin (m * (n * p)) → R) →L[R] _).comp
        (kroneckerAssoc R m n p : (Fin (m * n * p) → R) →L[R] _)) =
      ((ContinuousLinearMap.id R (Fin n → R)).kronecker
          (kroneckerComm R m p : (Fin (m * p) → R) →L[R] (Fin (p * m) → R))).comp
        ((kroneckerAssoc R n m p : (Fin (n * m * p) → R) →L[R] _).comp
          ((kroneckerComm R m n : (Fin (m * n) → R) →L[R] _).kronecker
            (ContinuousLinearMap.id R (Fin p → R)))) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨l, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- The second hexagon identity for the coordinate swap `kroneckerComm`, stated with the inverse
associativity isomorphisms. -/
theorem kroneckerComm_hexagon_reverse (m n p : ℕ) :
    ((kroneckerAssoc R p m n).symm : (Fin (p * (m * n)) → R) →L[R] _).comp
      ((kroneckerComm R (m * n) p : (Fin (m * n * p) → R) →L[R] _).comp
        ((kroneckerAssoc R m n p).symm : (Fin (m * (n * p)) → R) →L[R] _)) =
      ((kroneckerComm R m p : (Fin (m * p) → R) →L[R] (Fin (p * m) → R)).kronecker
          (ContinuousLinearMap.id R (Fin n → R))).comp
        (((kroneckerAssoc R m p n).symm : (Fin (m * (p * n)) → R) →L[R] _).comp
          ((ContinuousLinearMap.id R (Fin m → R)).kronecker
            (kroneckerComm R n p : (Fin (n * p) → R) →L[R] _))) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k ↦ ?_
  obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨l, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

end ContinuousLinearMap
