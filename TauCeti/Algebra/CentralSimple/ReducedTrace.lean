/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Imported publicly: `Matrix.trace` and `LinearMap.trace` occur in exported statements, the matrix
-- simplicity instance is needed to state `TauCeti.Algebra.reducedTrace_matrix`, and the base-change
-- module supplies `TauCeti.Algebra.deg` together with the instances making `L ⊗[K] A` central
-- simple over `L` (used in the statement of `TauCeti.Algebra.reducedTrace_tmul`).
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.SimpleRing.Matrix
public import TauCeti.Algebra.CentralSimple.BaseChange
-- Used only in proofs: the separable and algebraic closures and infinite Galois descent, the
-- Skolem-Noether theorem, splitting over a separably closed field, the Galois twist of a splitting
-- and tower base change, the trace of a reindexed matrix and of left multiplication on matrices.
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.Algebra.CentralSimple.SkolemNoether
import TauCeti.Algebra.CentralSimple.Splitting
import TauCeti.Algebra.CrossedProduct.Splitting.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.LinearMap
-- Used only by the worked examples: the real numbers and the real quaternions, with their
-- centrality and the trace of left multiplication by a quaternion.
import Mathlib.Basic.Real.Basic
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.Quaternion.AlgEquiv

/-!
# The reduced trace of a central simple algebra

Let `A` be a finite-dimensional central simple algebra over a field `K`. This file defines its
**reduced trace** `TauCeti.Algebra.reducedTrace K A : A →ₗ[K] K`: after extending scalars to any
field `L` over which `A` splits, `L ⊗[K] A ≃ₐ[L] Matrix m m L`, the reduced trace of `a` is the
matrix trace of the image of `1 ⊗ a`. It is the trace form of a central simple algebra: for a
semisimple algebra over `ℚ` the reduced trace is assembled from those of its simple factors over
their centres, and it is the form whose positivity on `x * star x` defines a positive involution
and whose Gram determinants are the discriminants of orders.

The regular trace of left multiplication is `deg K A` times the reduced trace
(`TauCeti.Algebra.trace_mulLeft_eq_deg_mul_reducedTrace`), so in characteristic zero either
determines the other; in characteristic dividing the degree the regular trace vanishes
identically, while the reduced trace is still nondegenerate.

## The construction

The definition uses the separable closure `SeparableClosure K`, which splits `A`
(`TauCeti.Algebra.isSplittingField_of_isSepClosed`), and a chosen splitting over it. The choice
does not matter: two splittings over the same field differ by an automorphism of a matrix
algebra, which is inner by Skolem-Noether, and the matrix trace is invariant under conjugation.
Twisting a splitting by a Galois automorphism `σ` gives another splitting, so the trace is
`σ`-invariant, and infinite Galois theory (`InfiniteGalois.mem_range_algebraMap_iff_fixed`) puts
it in `K`. An arbitrary splitting field `L` is compared with the separable closure inside an
algebraic closure of `L`, which receives a copy of the separable closure of `K`; this gives the
characterization `TauCeti.Algebra.algebraMap_reducedTrace`, from which every other property is
derived without unfolding the definition.

## Main results

* `TauCeti.Algebra.reducedTrace`: the reduced trace, a `K`-linear map `A →ₗ[K] K`.
* `TauCeti.Algebra.algebraMap_reducedTrace`: for every field extension `L / K` and every splitting
  `e : L ⊗[K] A ≃ₐ[L] Matrix m m L`, the reduced trace of `a` is the trace of `e (1 ⊗ a)`.
* `TauCeti.Algebra.reducedTrace_eq_trace`, `TauCeti.Algebra.reducedTrace_matrix`: on a matrix
  algebra over `K` the reduced trace is the matrix trace.
* `TauCeti.Algebra.reducedTrace_one`, `TauCeti.Algebra.reducedTrace_algebraMap`: the reduced
  trace of a scalar `c` is `deg K A * c`.
* `TauCeti.Algebra.reducedTrace_mul_comm`: `Trd (a * b) = Trd (b * a)`.
* `TauCeti.Algebra.eq_zero_of_forall_reducedTrace_mul_eq_zero`: the pairing
  `(a, b) ↦ Trd (a * b)` is nondegenerate.
* `TauCeti.Algebra.reducedTrace_algEquiv`, `TauCeti.Algebra.reducedTrace_op`,
  `TauCeti.Algebra.reducedTrace_star`: invariance under algebra isomorphisms, passage to the
  opposite algebra, and invariance under a `K`-linear involution.
* `TauCeti.Algebra.reducedTrace_tmul`: compatibility with base change to a field extension.
* `TauCeti.Algebra.trace_mulLeft_eq_deg_mul_reducedTrace`: the regular trace of left
  multiplication is `deg K A` times the reduced trace.

## References

* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Cambridge Studies in
  Advanced Mathematics 101, Section 2.6 (reduced norms and traces).
* I. Reiner, *Maximal Orders*, London Mathematical Society Monographs 5, Section 9 (reduced norms
  and traces).
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra

section Splitting

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Two splittings of `A` over the same field have the same trace: they differ by an automorphism
of a matrix algebra, which is inner by Skolem-Noether. -/
private theorem trace_splitting_eq [IsSimpleRing A] [FiniteDimensional K A]
    {L : Type*} [Field L] [Algebra K L]
    {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (e : L ⊗[K] A ≃ₐ[L] Matrix m m L) (e' : L ⊗[K] A ≃ₐ[L] Matrix m' m' L) (x : L ⊗[K] A) :
    (e x).trace = (e' x).trace := by
  -- Both matrix sizes square to `finrank K A`, which is positive.
  have hm := finrank_eq_sq_of_algEquiv_matrix K A L
    (e.trans (Matrix.reindexAlgEquiv L L (Fintype.equivFin m)))
  have hm' := finrank_eq_sq_of_algEquiv_matrix K A L
    (e'.trans (Matrix.reindexAlgEquiv L L (Fintype.equivFin m')))
  have hcard : Fintype.card m' = Fintype.card m :=
    Nat.pow_left_injective two_ne_zero (hm'.symm.trans hm)
  have : Nonempty m := by
    rw [← Fintype.card_pos_iff, Nat.pos_iff_ne_zero]
    intro h0
    exact Module.finrank_pos.ne' (by rw [hm, h0, zero_pow two_ne_zero])
  let r : m' ≃ m := Fintype.equivOfCardEq hcard
  obtain ⟨u, hu⟩ := exists_unit_conj_of_algEquiv L
    (e.symm.trans (e'.trans (Matrix.reindexAlgEquiv L L r)))
  have h := hu (e x)
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    Matrix.coe_reindexAlgEquiv] at h
  rw [← Matrix.trace_units_conj u (e x), ← h]
  exact Matrix.trace_reindex_self r (e' x)

/-- A splitting over `L` extends to a splitting over any field `Ω` above `L`, and the trace
moves along `L → Ω`. -/
private theorem exists_splitting_trace_eq_algebraMap {L : Type*} [Field L] [Algebra K L]
    {m : Type*} [Fintype m] [DecidableEq m] (e : L ⊗[K] A ≃ₐ[L] Matrix m m L)
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] :
    ∃ e' : Ω ⊗[K] A ≃ₐ[Ω] Matrix m m Ω, ∀ a : A,
      (e' (1 ⊗ₜ a)).trace = algebraMap L Ω (e (1 ⊗ₜ a)).trace := by
  refine ⟨(TensorProduct.baseChangeTowerAlgEquiv K L A Ω).symm.trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans (matrixBaseChangeAlgEquiv L Ω m)),
    fun a ↦ ?_⟩
  simp [AddMonoidHom.map_trace]

end Splitting

section Galois

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  [IsSimpleRing A] [FiniteDimensional K A]

/-- The trace of a splitting over a Galois extension, evaluated on `1 ⊗ a`, is fixed by the Galois
group: twisting the splitting by `σ` is another splitting, whose trace is the `σ`-image. -/
private theorem galois_trace_splitting {L : Type*} [Field L] [Algebra K L]
    {m : Type*} [Fintype m] [DecidableEq m] (e : L ⊗[K] A ≃ₐ[L] Matrix m m L)
    (σ : L ≃ₐ[K] L) (a : A) :
    σ (e (1 ⊗ₜ a)).trace = (e (1 ⊗ₜ a)).trace := by
  -- The `σ`-twist of `e` by the `L`-algebra automorphism `splittingAut e σ` is again a splitting.
  have h : (e.trans (splittingAut e σ).symm) (1 ⊗ₜ a) = (e (1 ⊗ₜ a)).map σ := by
    rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq, splittingAut_map, AlgEquiv.symm_apply_apply]
    simp
  rw [AddMonoidHom.map_trace, ← h]
  exact trace_splitting_eq _ e _

end Galois

section Def

variable (K A : Type*) [Field K] [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- A fixed splitting of `A` over the separable closure of `K`. -/
private noncomputable def sepClosureSplitting :
    SeparableClosure K ⊗[K] A ≃ₐ[SeparableClosure K]
      Matrix (Fin (deg K A)) (Fin (deg K A)) (SeparableClosure K) :=
  (isSplittingField_of_isSepClosed K A (SeparableClosure K)).nonempty_algEquiv_matrix_deg.some

/-- The trace through `sepClosureSplitting`, as a `K`-linear map into the separable closure. -/
private noncomputable def sepClosureTrace : A →ₗ[K] SeparableClosure K :=
  ((Matrix.traceLinearMap _ (SeparableClosure K) (SeparableClosure K)).restrictScalars K).comp
    (((sepClosureSplitting K A).toLinearMap.restrictScalars K).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := SeparableClosure K)).toLinearMap)

private theorem sepClosureTrace_apply (a : A) :
    sepClosureTrace K A a = (sepClosureSplitting K A (1 ⊗ₜ a)).trace :=
  (rfl)

private theorem sepClosureTrace_mem_range (a : A) :
    sepClosureTrace K A a ∈ LinearMap.range (Algebra.linearMap K (SeparableClosure K)) := by
  rw [LinearMap.mem_range, sepClosureTrace_apply]
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ ↦
    galois_trace_splitting _ σ a

/-- **The reduced trace** `Trd : A → K` of a finite-dimensional central simple algebra `A` over a
field `K`. -/
noncomputable def reducedTrace : A →ₗ[K] K :=
  (LinearEquiv.ofInjective (Algebra.linearMap K (SeparableClosure K))
      (by rw [Algebra.coe_linearMap]; exact (algebraMap K (SeparableClosure K)).injective)).symm
      |>.toLinearMap.comp
    ((sepClosureTrace K A).codRestrict _ (sepClosureTrace_mem_range K A))

private theorem algebraMap_reducedTrace_sepClosure (a : A) :
    algebraMap K (SeparableClosure K) (reducedTrace K A a) = sepClosureTrace K A a := by
  rw [reducedTrace, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  exact LinearEquiv.ofInjective_symm_apply (f := Algebra.linearMap K (SeparableClosure K)) _

variable {K A}

/-- **The reduced trace is the trace of any splitting.** For every field extension `L / K` and every
`L`-algebra isomorphism `e : L ⊗[K] A ≃ₐ[L] Matrix m m L`, the trace of `e (1 ⊗ a)` is the reduced
trace of `a`, viewed in `L`. -/
theorem algebraMap_reducedTrace {L : Type*} [Field L] [Algebra K L]
    {m : Type*} [Fintype m] [DecidableEq m] (e : L ⊗[K] A ≃ₐ[L] Matrix m m L) (a : A) :
    algebraMap K L (reducedTrace K A a) = (e (1 ⊗ₜ a)).trace := by
  -- Compare `e` with the separable-closure splitting in an algebraically closed field `Ω`
  -- containing both `L` and a copy of the separable closure of `K`.
  let Ω := AlgebraicClosure L
  let φ : SeparableClosure K →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra (SeparableClosure K) Ω := φ.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) Ω :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  obtain ⟨e₁, he₁⟩ := exists_splitting_trace_eq_algebraMap e Ω
  obtain ⟨e₂, he₂⟩ := exists_splitting_trace_eq_algebraMap (sepClosureSplitting K A) Ω
  apply (algebraMap L Ω).injective
  rw [← he₁, trace_splitting_eq e₁ e₂, he₂, ← sepClosureTrace_apply,
    ← algebraMap_reducedTrace_sepClosure, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- Over the base field itself: if `f : A ≃ₐ[K] Matrix m m K` presents `A` as a matrix algebra, the
reduced trace is the matrix trace. -/
theorem reducedTrace_eq_trace {m : Type*} [Fintype m] [DecidableEq m]
    (f : A ≃ₐ[K] Matrix m m K) (a : A) : reducedTrace K A a = (f a).trace := by
  simpa using algebraMap_reducedTrace ((Algebra.TensorProduct.lid K A).trans f) a

/-- The reduced trace of the identity is the degree. -/
@[simp]
theorem reducedTrace_one : reducedTrace K A 1 = deg K A := by
  apply (algebraMap K (SeparableClosure K)).injective
  rw [algebraMap_reducedTrace (sepClosureSplitting K A), ← Algebra.TensorProduct.one_def, map_one,
    Matrix.trace_one, Fintype.card_fin, map_natCast]

/-- The reduced trace of a scalar `c` is `deg K A * c`. -/
@[simp]
theorem reducedTrace_algebraMap (c : K) : reducedTrace K A (algebraMap K A c) = deg K A * c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, reducedTrace_one, smul_eq_mul, mul_comm]

/-- The reduced trace is a trace: it vanishes on commutators. -/
theorem reducedTrace_mul_comm (a b : A) : reducedTrace K A (a * b) = reducedTrace K A (b * a) := by
  apply (algebraMap K (SeparableClosure K)).injective
  have h (x y : A) : (1 : SeparableClosure K) ⊗ₜ[K] (x * y) = (1 ⊗ₜ x) * (1 ⊗ₜ y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [algebraMap_reducedTrace (sepClosureSplitting K A), algebraMap_reducedTrace
    (sepClosureSplitting K A), h, h, map_mul, map_mul, Matrix.trace_mul_comm]

/-- **The reduced trace pairing is nondegenerate**: an element `a` with `Trd (a * b) = 0` for every
`b` is zero. -/
theorem eq_zero_of_forall_reducedTrace_mul_eq_zero {a : A}
    (h : ∀ b, reducedTrace K A (a * b) = 0) : a = 0 := by
  let e := sepClosureSplitting K A
  -- `X ↦ trace (e (1 ⊗ a) * X)` vanishes on the image of every pure tensor, hence everywhere.
  have hzero (t : SeparableClosure K ⊗[K] A) : (e (1 ⊗ₜ a) * e t).trace = 0 := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu => rw [map_add, mul_add, Matrix.trace_add, ht, hu, add_zero]
    | tmul l b =>
      rw [TensorProduct.tmul_eq_smul_one_tmul l b, map_smul, mul_smul_comm, Matrix.trace_smul,
        ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← algebraMap_reducedTrace e, h,
        map_zero, smul_zero]
  have hX : e (1 ⊗ₜ a) = 0 :=
    Matrix.ext_iff_trace_mul_right.2 fun X ↦ by simpa using hzero (e.symm X)
  apply Algebra.TensorProduct.includeRight_injective (A := SeparableClosure K)
    (algebraMap K (SeparableClosure K)).injective
  simpa using hX

/-- The reduced trace is invariant under `K`-algebra isomorphisms. -/
@[simp]
theorem reducedTrace_algEquiv {B : Type*} [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] [FiniteDimensional K B] (f : A ≃ₐ[K] B) (a : A) :
    reducedTrace K B (f a) = reducedTrace K A a := by
  apply (algebraMap K (SeparableClosure K)).injective
  rw [algebraMap_reducedTrace (sepClosureSplitting K B),
    algebraMap_reducedTrace
      ((Algebra.TensorProduct.congr AlgEquiv.refl f).trans (sepClosureSplitting K B))]
  simp

/-- The reduced trace of the opposite algebra is the reduced trace: `Trd (op a) = Trd a`. -/
@[simp]
theorem reducedTrace_op (a : A) :
    reducedTrace K Aᵐᵒᵖ (MulOpposite.op a) = reducedTrace K A a := by
  let e := sepClosureSplitting K A
  -- Transposition turns the opposite of the matrix algebra back into the matrix algebra.
  let eop : SeparableClosure K ⊗[K] Aᵐᵒᵖ ≃ₐ[SeparableClosure K]
      Matrix (Fin (deg K A)) (Fin (deg K A)) (SeparableClosure K) :=
    (TensorProduct.baseChangeOpAlgEquiv K (SeparableClosure K) A).trans
      ((AlgEquiv.op e).trans (Matrix.transposeAlgEquiv _ _ _).symm)
  apply (algebraMap K (SeparableClosure K)).injective
  rw [algebraMap_reducedTrace eop, algebraMap_reducedTrace e]
  simp [eop]

/-- **A `K`-linear involution preserves the reduced trace**: `Trd (star a) = Trd a`. -/
@[simp]
theorem reducedTrace_star [StarRing K] [TrivialStar K] [StarRing A] [StarModule K A] (a : A) :
    reducedTrace K A (star a) = reducedTrace K A a := by
  -- The involution is a `K`-algebra isomorphism `A ≃ₐ[K] Aᵐᵒᵖ`.
  let f : A ≃ₐ[K] Aᵐᵒᵖ :=
    { starRingEquiv with commutes' := fun c ↦ by simp [← algebraMap_star_comm] }
  -- `f` is `starRingEquiv` with the commutation proof attached, so it evaluates through
  -- `starRingEquiv_apply`.
  have hf : f a = MulOpposite.op (star a) := starRingEquiv_apply a
  rw [← reducedTrace_op, ← hf, reducedTrace_algEquiv]

/-- **The reduced trace is compatible with base change**: on `L ⊗[K] A`, central simple over `L`,
the reduced trace of `l ⊗ a` is `l` times the reduced trace of `a`. -/
@[simp]
theorem reducedTrace_tmul (L : Type*) [Field L] [Algebra K L] (l : L) (a : A) :
    reducedTrace L (L ⊗[K] A) (l ⊗ₜ a) = l * algebraMap K L (reducedTrace K A a) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul l a, map_smul, smul_eq_mul]
  congr 1
  let Ω := AlgebraicClosure L
  obtain ⟨e⟩ := (isSplittingField_of_isSepClosed L (L ⊗[K] A) Ω).nonempty_algEquiv_matrix_deg
  apply (algebraMap L Ω).injective
  rw [algebraMap_reducedTrace e, ← IsScalarTower.algebraMap_apply,
    algebraMap_reducedTrace ((TensorProduct.baseChangeTowerAlgEquiv K L A Ω).symm.trans e)]
  simp

/-- **The regular trace is `deg` times the reduced trace**: the trace of left multiplication by
`a` on `A` is `deg K A * Trd a`. -/
theorem trace_mulLeft_eq_deg_mul_reducedTrace (a : A) :
    LinearMap.trace K A (LinearMap.mulLeft K a) = deg K A * reducedTrace K A a := by
  let e := sepClosureSplitting K A
  apply (algebraMap K (SeparableClosure K)).injective
  -- `Algebra.baseChange_lmul` is stated with `Algebra.lmul R B f`, whose underlying map is
  -- `LinearMap.mulLeft R f` by definition, so the `show` restates it in the `LinearMap.mulLeft`
  -- form in which `LinearMap.trace_baseChange` leaves the goal and which
  -- `AlgEquiv.linearEquivConj_mulLeft` rewrites.
  rw [map_mul, map_natCast, algebraMap_reducedTrace e, ← LinearMap.trace_baseChange,
    show (LinearMap.mulLeft K a).baseChange (SeparableClosure K) =
      LinearMap.mulLeft (SeparableClosure K) (1 ⊗ₜ a) from Algebra.baseChange_lmul a,
    ← LinearMap.trace_conj' _ e.toLinearEquiv, AlgEquiv.linearEquivConj_mulLeft,
    Matrix.trace_mulLeft, Fintype.card_fin]

end Def

section Matrix

variable (K : Type*) [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The reduced trace of a full matrix algebra is the matrix trace. -/
@[simp]
theorem reducedTrace_matrix [Nonempty n] (M : Matrix n n K) :
    reducedTrace K (Matrix n n K) M = M.trace :=
  reducedTrace_eq_trace AlgEquiv.refl M

end Matrix

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- On `M₂(ℚ)` the reduced trace is the matrix trace. -/
example : reducedTrace ℚ (Matrix (Fin 2) (Fin 2) ℚ) !![1, 2; 3, 4] = 5 := by
  rw [reducedTrace_matrix, Matrix.trace_fin_two_of]
  norm_num

/-- On `M₂(ℚ)` the regular trace is twice the reduced trace, so the two traces differ already for
a split algebra. -/
example (x : Matrix (Fin 2) (Fin 2) ℚ) :
    LinearMap.trace ℚ _ (LinearMap.mulLeft ℚ x) = 2 * reducedTrace ℚ _ x := by
  rw [trace_mulLeft_eq_deg_mul_reducedTrace, deg_matrix, deg_self]
  norm_num

/-- The real quaternions do not split over `ℝ`, yet their reduced trace is the familiar `2 re`. -/
example (x : ℍ[ℝ]) : reducedTrace ℝ ℍ[ℝ] x = 2 * x.re := by
  have hdeg : deg ℝ ℍ[ℝ] = 2 :=
    deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  have h := trace_mulLeft_eq_deg_mul_reducedTrace (K := ℝ) x
  rw [QuaternionAlgebra.trace_mulLeft, hdeg] at h
  norm_num at h
  linarith

end Examples

end Algebra

end TauCeti
