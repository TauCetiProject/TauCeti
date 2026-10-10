/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import Mathlib.Data.Matrix.Mul
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Continuation cocycles and the chain maps they induce

A **continuation cocycle** from a twisting cocycle `mP` on `(P, ind)` to a twisting cocycle
`mQ` on `(Q, indQ)`, over a differential graded algebra `(𝒜, d)`, is a matrix
`ν x y ∈ 𝒜 (indQ y - ind x)` with
`d (ν x y) = Σ_z mP x z * ν z y + Σ_z (-1) ^ (ind x - indQ z - 1) • (ν x z * mQ z y)`
(the source's Definition 1.10, transcribed to the cohomological grading `C^{-n} = C_n` of
`TauCeti.Algebra.Homology.DG.Twisted.Cocycle`).  It induces, for every differential graded right
module `(ℳ, dM)`, the degree-zero map `continuationMap ν : ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨Q⟩`,
`Ψ (α ⊗ x) = Σ_y (α · ν x y) ⊗ y`, which preserves the total grading and commutes with the
twisted differentials: this is the **continuation map**.

The Kronecker matrix is a continuation cocycle from `m` to itself, inducing the identity, and the
matrix product of continuation cocycles `m¹ → m²` and `m² → m³` is a continuation cocycle
`m¹ → m³`, inducing the composite of the continuation maps.

As in `TauCeti.Algebra.Homology.DG.Twisted.Complex`, the map is defined for any matrix `ν`, the
theorems take the degree and continuation equations as hypotheses, and the bundled
`ContinuationCocycle` comes last.

## Main definitions

* `TauCeti.continuationMap R M ν`: the map `(P → M) →ₗ[R] (Q → M)` of a matrix `ν`.
* `TauCeti.ContinuationCocycle mP mQ`: continuation cocycles between twisting cocycles, with
  `refl` and `comp`.

## Main results

* `TauCeti.continuationMap_mem_twistedTotalGrading`: the continuation map has total degree zero.
* `TauCeti.continuationMap_twistedDifferential`: the continuation map is a chain map,
  `Ψ ∘ D_P = D_Q ∘ Ψ`, for a differential graded right module.
* `TauCeti.continuationMap_kronecker`, `TauCeti.continuationMap_matMul`: the Kronecker matrix
  induces the identity and the matrix product induces the composite.
* `TauCeti.continuation_kronecker`, `TauCeti.continuation_matMul`: the Kronecker matrix and the
  matrix product satisfy the continuation equation.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definition 1.10.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP uQ uS uT

section Map

variable (R : Type uR) {A : Type uA} (M : Type uM) [CommSemiring R] [Semiring A]
  {P : Type uP} {Q : Type uQ} [Fintype P]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The map `ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨Q⟩` of a matrix `ν : P → Q → A`, on the models `P → M` and
`Q → M`: its `y`-component is `(Ψ f) y = Σ_x op (ν x y) • f x`, so that on an elementary tensor
`Ψ (α ⊗ x) = Σ_y (α · ν x y) ⊗ y` (`continuationMap_single`), with no Koszul sign. -/
noncomputable def continuationMap (ν : P → Q → A) : (P → M) →ₗ[R] (Q → M) where
  toFun f y := ∑ x, op (ν x y) • f x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_comm r]

variable {R M} (ν : P → Q → A)

/-- The `y`-component of the continuation map; not `@[simp]`, so that the elementary-tensor
normal form `continuationMap_single_apply` is reached first. -/
theorem continuationMap_apply (f : P → M) (y : Q) :
    continuationMap R M ν f y = ∑ x, op (ν x y) • f x :=
  (rfl)

/-- The `y`-component of the continuation map of an elementary tensor `α ⊗ x`. -/
@[simp]
theorem continuationMap_single_apply [DecidableEq P] (x : P) (α : M) (y : Q) :
    continuationMap R M ν (Pi.single x α) y = op (ν x y) • α := by
  simp only [continuationMap_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The continuation map of an elementary tensor: `Ψ (α ⊗ x) = Σ_y (α · ν x y) ⊗ y`. -/
theorem continuationMap_single [Fintype Q] [DecidableEq P] [DecidableEq Q] (x : P) (α : M) :
    continuationMap R M ν (Pi.single x α) = ∑ y, Pi.single y (op (ν x y) • α) := by
  funext y'
  rw [continuationMap_single_apply, Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Map

/-! ### The maps of the Kronecker matrix and of a matrix product -/

section MapMatrix

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommSemiring R] [Semiring A]
  {P : Type uP} {Q : Type uQ} {S : Type uS} [Fintype P] [Fintype Q]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The Kronecker matrix induces the identity. -/
@[simp]
theorem continuationMap_kronecker [DecidableEq P] :
    continuationMap R M (1 : Matrix P P A) = LinearMap.id := by
  refine LinearMap.ext fun f ↦ funext fun y ↦ (continuationMap_apply _ f y).trans ?_
  rw [LinearMap.id_apply]
  simp only [Matrix.one_apply, apply_ite op, op_one, op_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The matrix product induces the composite of the continuation maps. -/
theorem continuationMap_matMul (ν₁ : P → Q → A) (ν₂ : Q → S → A) :
    continuationMap R M (Matrix.of ν₁ * Matrix.of ν₂) =
      (continuationMap R M ν₂).comp (continuationMap R M ν₁) := by
  refine LinearMap.ext fun f ↦ funext fun z ↦ (continuationMap_apply _ f z).trans ?_
  rw [LinearMap.comp_apply, continuationMap_apply]
  simp only [continuationMap_apply, Matrix.mul_apply, Matrix.of_apply, Finset.op_sum,
    Finset.sum_smul, Finset.smul_sum, op_mul, mul_smul]
  exact Finset.sum_comm

end MapMatrix

section Properties

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P : Type uP} {Q : Type uQ} {ind : P → ℤ} {indQ : Q → ℤ}
  [Fintype P] [Fintype Q] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  (ν : P → Q → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype P]
  [Fintype Q] in
/-- A homogeneous element `α` of degree `q`, acted on by a homogeneous `a` of degree `e`, has
degree `q + e`. -/
theorem op_smul_mem_of_mem_graded {e : ℤ} {a : A} (ha : a ∈ 𝒜 e) {q : ℤ} {α : M}
    (hα : α ∈ ℳ q) : op a • α ∈ ℳ (q + e) := by
  have hop : op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece e := by
    rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
    exact ha
  have := SetLike.GradedSMul.smul_mem hop hα
  rwa [vadd_eq_add, add_comm] at this

omit [IsScalarTower R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype Q] in
/-- The continuation map of a matrix with homogeneous entries of degree `indQ y - ind x`
preserves the total degree. -/
theorem continuationMap_mem_twistedTotalGrading (hν : ∀ x y, ν x y ∈ 𝒜 (indQ y - ind x))
    {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    continuationMap R M ν f ∈ twistedTotalGrading ℳ indQ n := by
  rw [mem_twistedTotalGrading_iff] at hf ⊢
  intro y
  rw [continuationMap_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have := op_smul_mem_of_mem_graded (hν x y) (hf x)
  convert this using 2
  ring

variable (mP : P → P → A) (mQ : Q → Q → A) (dM : M →ₗ[R] M)

/-- **The continuation map is a chain map**: for a matrix `ν` with homogeneous entries which
satisfies the continuation equation between `mP` and `mQ`, and a differential graded right module
`(ℳ, dM)`, `Ψ ∘ D_P = D_Q ∘ Ψ`. -/
theorem continuationMap_twistedDifferential (hν : ∀ x y, ν x y ∈ 𝒜 (indQ y - ind x))
    (hc : ∀ x y, d (ν x y) =
      ∑ z, mP x z * ν z y + ∑ z, (ind x - indQ z - 1).negOnePow • (ν x z * mQ z y))
    (hM : IsDGRightModule h ℳ dM) (f : P → M) :
    continuationMap R M ν (twistedDifferential mP ℳ dM f) =
      twistedDifferential mQ ℳ dM (continuationMap R M ν f) := by
  classical
  -- Reduce to a homogeneous elementary tensor `α ⊗ x`.
  suffices key : ∀ (x : P) {q : ℤ} {α : M}, α ∈ ℳ q →
      continuationMap R M ν (twistedDifferential mP ℳ dM (Pi.single x α)) =
        twistedDifferential mQ ℳ dM (continuationMap R M ν (Pi.single x α)) by
    rw [← Finset.univ_sum_single f, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    generalize f x = α
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous i α => exact key x α.2
    | add a b ha hb => rw [Pi.single_add, map_add, map_add, map_add, map_add, ha, hb]
  intro x q α hα
  funext w
  -- Left-hand side: `Ψ` of `D_P (α ⊗ x) = dM α ⊗ x + (-1) ^ q Σ_z (α · mP x z) ⊗ z`.
  have hL : continuationMap R M ν (twistedDifferential mP ℳ dM (Pi.single x α)) w =
      op (ν x w) • dM α + ∑ z, op (ν z w) • (q.negOnePow • (op (mP x z) • α)) := by
    rw [twistedDifferential_single mP dM x hα, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
      continuationMap_single_apply]
    simp only [continuationMap_single_apply]
  -- Right-hand side: `D_Q` of `Ψ (α ⊗ x) = Σ_y (α · ν x y) ⊗ y`, through the Leibniz rule.
  have hR : twistedDifferential mQ ℳ dM (continuationMap R M ν (Pi.single x α)) w =
      (op (ν x w) • dM α + q.negOnePow • (op (d (ν x w)) • α)) +
        ∑ y, (q + (indQ y - ind x)).negOnePow • (op (mQ y w) • (op (ν x y) • α)) := by
    rw [continuationMap_single, map_sum, Finset.sum_apply]
    simp only [twistedDifferential_single_apply mQ dM _ w (op_smul_mem_of_mem_graded (hν x _) hα)]
    rw [Finset.sum_add_distrib, ← hM.leibniz hα]
    congr 1
    simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hL, hR, hc x w, op_add, add_smul, smul_add, add_assoc]
  congr 1
  -- The `mP` terms agree.
  have h₁ : q.negOnePow • (op (∑ z, mP x z * ν z w) • α) =
      ∑ z, op (ν z w) • (q.negOnePow • (op (mP x z) • α)) := by
    rw [Finset.op_sum, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [op_mul, mul_smul, smul_comm q.negOnePow (op (ν z w))]
  -- The two `mQ` sums cancel through the sign identity
  -- `(-1) ^ q (-1) ^ (ind x - indQ z - 1) = -(-1) ^ (q + indQ z - ind x)`.
  have h₂ : q.negOnePow • (op (∑ z, (ind x - indQ z - 1).negOnePow • (ν x z * mQ z w)) • α) +
      ∑ y, (q + (indQ y - ind x)).negOnePow • (op (mQ y w) • (op (ν x y) • α)) = 0 := by
    rw [Finset.op_sum, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    have hsign : q.negOnePow * (ind x - indQ z - 1).negOnePow =
        -(q + (indQ z - ind x)).negOnePow := by
      rw [← Int.negOnePow_succ]
      exact negOnePow_mul_negOnePow_of_even ⟨ind x - indQ z - 1, by ring⟩
    rw [op_smul, smul_assoc, smul_smul, hsign, op_mul, mul_smul, Units.neg_smul, neg_add_cancel]
  rw [h₁, add_assoc, h₂, add_zero]

/-! ### The Kronecker matrix and the matrix product -/

section Kronecker

variable [DecidableEq P] (m : P → P → A)

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype P]
  [Fintype Q] in
/-- The Kronecker matrix has entries of degree `ind y - ind x`. -/
theorem kronecker_mem_graded (x y : P) : (1 : Matrix P P A) x y ∈ 𝒜 (ind y - ind x) := by
  rw [Matrix.one_apply]
  split_ifs with hxy
  · subst hxy
    rw [sub_self]
    exact SetLike.one_mem_graded 𝒜
  · exact zero_mem _

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype Q] in
/-- The Kronecker matrix satisfies the continuation equation from `m` to `m`, for any matrix `m`,
as soon as `d 1 = 0`. -/
theorem continuation_kronecker (hd : d 1 = 0) (x y : P) :
    d ((1 : Matrix P P A) x y) = ∑ z, m x z * (1 : Matrix P P A) z y +
      ∑ z, (ind x - ind z - 1).negOnePow • ((1 : Matrix P P A) x z * m z y) := by
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sub_self, zero_sub, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    add_neg_cancel]
  split_ifs with hxy
  · exact hd
  · exact map_zero d

end Kronecker

section MatMul

variable {S : Type uS} {indS : S → ℤ} [Fintype S] (ν₁ : P → Q → A) (ν₂ : Q → S → A)

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype P]
  [Fintype S] in
/-- The matrix product of matrices with entries of degrees `indQ y - ind x` and `indS z - indQ y`
has entries of degree `indS z - ind x`. -/
theorem matMul_mem_graded (hν₁ : ∀ x y, ν₁ x y ∈ 𝒜 (indQ y - ind x))
    (hν₂ : ∀ y z, ν₂ y z ∈ 𝒜 (indS z - indQ y)) (x : P) (z : S) :
    (Matrix.of ν₁ * Matrix.of ν₂) x z ∈ 𝒜 (indS z - ind x) := by
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun y _ ↦ ?_
  simp only [Matrix.of_apply]
  have := SetLike.mul_mem_graded (hν₁ x y) (hν₂ y z)
  convert this using 2
  ring

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] in
/-- The matrix product of continuation cocycles `m₁ → m₂` and `m₂ → m₃` satisfies the
continuation equation from `m₁` to `m₃`. -/
theorem continuation_matMul (h : IsDGAlgebra 𝒜 d) (m₁ : P → P → A) (m₂ : Q → Q → A)
    (m₃ : S → S → A) (hν₁ : ∀ x y, ν₁ x y ∈ 𝒜 (indQ y - ind x))
    (hc₁ : ∀ x y, d (ν₁ x y) =
      ∑ z, m₁ x z * ν₁ z y + ∑ z, (ind x - indQ z - 1).negOnePow • (ν₁ x z * m₂ z y))
    (hc₂ : ∀ y w, d (ν₂ y w) =
      ∑ z, m₂ y z * ν₂ z w + ∑ z, (indQ y - indS z - 1).negOnePow • (ν₂ y z * m₃ z w))
    (x : P) (y : S) :
    d ((Matrix.of ν₁ * Matrix.of ν₂) x y) =
      ∑ w, m₁ x w * (Matrix.of ν₁ * Matrix.of ν₂) w y +
        ∑ w, (ind x - indS w - 1).negOnePow • ((Matrix.of ν₁ * Matrix.of ν₂) x w * m₃ w y) := by
  simp only [Matrix.mul_apply, Matrix.of_apply, map_sum]
  have hL : ∀ z, d (ν₁ x z * ν₂ z y) =
      d (ν₁ x z) * ν₂ z y + (indQ z - ind x).negOnePow • (ν₁ x z * d (ν₂ z y)) :=
    fun z ↦ h.leibniz (hν₁ x z) _
  simp only [hL, hc₁, hc₂, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, Finset.sum_add_distrib, mul_assoc]
  simp only [smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  -- The `m₁` terms agree after exchanging the two sums.
  have hA : (∑ x₁ : Q, ∑ x₂ : P, m₁ x x₂ * (ν₁ x₂ x₁ * ν₂ x₁ y)) =
      ∑ x₁ : P, ∑ i : Q, m₁ x x₁ * (ν₁ x₁ i * ν₂ i y) :=
    Finset.sum_comm
  -- The two `m₂` sums cancel: `(-1) ^ (ind x - indQ z - 1) = -(-1) ^ (indQ z - ind x)`.
  have hBC : (∑ x₁ : Q, ∑ x₂ : Q,
        (ind x - indQ x₂ - 1).negOnePow • (ν₁ x x₂ * (m₂ x₂ x₁ * ν₂ x₁ y))) +
      ∑ x₁ : Q, ∑ i : Q, (indQ x₁ - ind x).negOnePow • (ν₁ x x₁ * (m₂ x₁ i * ν₂ i y)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun w _ ↦ ?_
    rw [Int.negOnePow_sub_sub_one, Units.neg_smul, neg_add_cancel]
  -- The `m₃` terms agree: `(-1) ^ (indQ z - ind x) (-1) ^ (indQ z - indS w - 1)` is
  -- `(-1) ^ (ind x - indS w - 1)`.
  have hD : (∑ x₁ : Q, ∑ x₂ : S, ((indQ x₁ - ind x).negOnePow * (indQ x₁ - indS x₂ - 1).negOnePow) •
        (ν₁ x x₁ * (ν₂ x₁ x₂ * m₃ x₂ y))) =
      ∑ x₁ : S, ∑ x₂ : Q, (ind x - indS x₁ - 1).negOnePow • (ν₁ x x₂ * (ν₂ x₂ x₁ * m₃ x₁ y)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    rw [negOnePow_mul_negOnePow_of_even (c := ind x - indS w - 1) ⟨indQ z - ind x, by ring⟩]
  rw [hA, hD, add_assoc, ← add_assoc _ _ (∑ x₁ : S, ∑ x₂ : Q,
    (ind x - indS x₁ - 1).negOnePow • (ν₁ x x₂ * (ν₂ x₂ x₁ * m₃ x₁ y))), hBC, zero_add]

end MatMul

end Properties

/-! ### Continuation cocycles -/

section Cocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {Q : Type uQ} {S : Type uS} {ind : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}
  [Fintype P] [Fintype Q] [Fintype S]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- A **continuation cocycle** from the twisting cocycle `mP` on `(P, ind)` to the twisting cocycle
`mQ` on `(Q, indQ)` (the source's Definition 1.10): a matrix `ν x y ∈ 𝒜 (indQ y - ind x)` with
`d (ν x y) = Σ_z mP x z * ν z y + Σ_z (-1) ^ (ind x - indQ z - 1) • (ν x z * mQ z y)`. -/
structure ContinuationCocycle (mP : TwistingCocycle 𝒜 d P ind) (mQ : TwistingCocycle 𝒜 d Q indQ)
    where
  /-- The entries of the continuation cocycle. -/
  ν : P → Q → A
  /-- The entry `ν x y` has cohomological degree `indQ y - ind x`. -/
  mem_graded : ∀ x y, ν x y ∈ 𝒜 (indQ y - ind x)
  /-- The continuation equation. -/
  continuation : ∀ x y, d (ν x y) =
    ∑ z, mP.m x z * ν z y + ∑ z, (ind x - indQ z - 1).negOnePow • (ν x z * mQ.m z y)

namespace ContinuationCocycle

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mS : TwistingCocycle 𝒜 d S indS}

omit [GradedAlgebra 𝒜] in
@[ext]
theorem ext {ν₁ ν₂ : ContinuationCocycle mP mQ} (h : ∀ x y, ν₁.ν x y = ν₂.ν x y) : ν₁ = ν₂ := by
  obtain ⟨ν₁, _, _⟩ := ν₁
  obtain ⟨ν₂, _, _⟩ := ν₂
  obtain rfl : ν₁ = ν₂ := funext fun x ↦ funext fun y ↦ h x y
  rfl

/-- The Kronecker matrix, as a continuation cocycle from `m` to itself, for a differential with
`d 1 = 0`. -/
def refl [DecidableEq P] (hd : d 1 = 0) (m : TwistingCocycle 𝒜 d P ind) :
    ContinuationCocycle m m where
  ν := (1 : Matrix P P A)
  mem_graded := kronecker_mem_graded
  continuation := continuation_kronecker m.m hd

@[simp]
theorem refl_ν [DecidableEq P] (hd : d 1 = 0) (m : TwistingCocycle 𝒜 d P ind) :
    (refl hd m).ν = (1 : Matrix P P A) :=
  (rfl)

/-- The matrix product of continuation cocycles `mP → mQ` and `mQ → mS`, a continuation cocycle
`mP → mS`. -/
def comp (h : IsDGAlgebra 𝒜 d) (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mS) :
    ContinuationCocycle mP mS where
  ν := Matrix.of ν₁.ν * Matrix.of ν₂.ν
  mem_graded := matMul_mem_graded ν₁.ν ν₂.ν ν₁.mem_graded ν₂.mem_graded
  continuation := continuation_matMul ν₁.ν ν₂.ν h mP.m mQ.m mS.m ν₁.mem_graded ν₁.continuation
    ν₂.continuation

@[simp]
theorem comp_ν (h : IsDGAlgebra 𝒜 d) (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mS) : (ν₁.comp h ν₂).ν = Matrix.of ν₁.ν * Matrix.of ν₂.ν :=
  (rfl)

/-- The Kronecker continuation cocycle is a left identity for the composition. -/
@[simp]
theorem refl_comp [DecidableEq P] (h : IsDGAlgebra 𝒜 d) (ν : ContinuationCocycle mP mQ) :
    (refl h.map_one_eq_zero mP).comp h ν = ν := by
  ext x y
  rw [comp_ν, refl_ν]
  exact congrFun (congrFun (Matrix.one_mul (Matrix.of ν.ν)) x) y

/-- The Kronecker continuation cocycle is a right identity for the composition. -/
@[simp]
theorem comp_refl [DecidableEq Q] (h : IsDGAlgebra 𝒜 d) (ν : ContinuationCocycle mP mQ) :
    ν.comp h (refl h.map_one_eq_zero mQ) = ν := by
  ext x y
  rw [comp_ν, refl_ν]
  exact congrFun (congrFun (Matrix.mul_one (Matrix.of ν.ν)) x) y

/-- The composition of continuation cocycles is associative. -/
theorem comp_assoc {T : Type uT} {indT : T → ℤ} [Fintype T] {mT : TwistingCocycle 𝒜 d T indT}
    (h : IsDGAlgebra 𝒜 d) (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mS)
    (ν₃ : ContinuationCocycle mS mT) :
    (ν₁.comp h ν₂).comp h ν₃ = ν₁.comp h (ν₂.comp h ν₃) := by
  ext x y
  rw [comp_ν, comp_ν, comp_ν, comp_ν]
  exact congrFun (congrFun
    (Matrix.mul_assoc (Matrix.of ν₁.ν) (Matrix.of ν₂.ν) (Matrix.of ν₃.ν)) x) y

variable [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [SMulCommClass R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {h : IsDGAlgebra 𝒜 d}

omit [IsScalarTower R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype S] in
/-- The continuation map of a continuation cocycle preserves the total degree. -/
theorem continuationMap_mem_twistedTotalGrading (ν : ContinuationCocycle mP mQ) {n : ℤ}
    {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    continuationMap R M ν.ν f ∈ twistedTotalGrading ℳ indQ n :=
  TauCeti.continuationMap_mem_twistedTotalGrading ν.ν ν.mem_graded hf

omit [Fintype S] in
/-- **The continuation map of a continuation cocycle is a chain map** between the twisted
complexes of a differential graded right module. -/
theorem continuationMap_twistedDifferential (ν : ContinuationCocycle mP mQ)
    (hM : IsDGRightModule h ℳ dM) (f : P → M) :
    continuationMap R M ν.ν (twistedDifferential mP.m ℳ dM f) =
      twistedDifferential mQ.m ℳ dM (continuationMap R M ν.ν f) :=
  TauCeti.continuationMap_twistedDifferential ν.ν mP.m mQ.m dM ν.mem_graded ν.continuation hM f

omit [IsScalarTower R Aᵐᵒᵖ M] [Fintype Q] [Fintype S] in
/-- The Kronecker continuation cocycle induces the identity. -/
theorem continuationMap_refl [DecidableEq P] (hd : d 1 = 0) (m : TwistingCocycle 𝒜 d P ind) :
    continuationMap R M (refl hd m).ν = LinearMap.id :=
  continuationMap_kronecker

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- The composite continuation cocycle induces the composite of the continuation maps. -/
theorem continuationMap_comp (h : IsDGAlgebra 𝒜 d) (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mS) :
    continuationMap R M (ν₁.comp h ν₂).ν =
      (continuationMap R M ν₂.ν).comp (continuationMap R M ν₁.ν) :=
  continuationMap_matMul ν₁.ν ν₂.ν

end ContinuationCocycle

end Cocycle

end TauCeti
