/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Diagonal

/-!
# Maximal minors and kernel lengths over discrete valuation rings

Let `A` be a matrix over a discrete valuation ring `O` with columns indexed by a finite type `k`,
and let `a ≠ 0` in `O`. The length of the kernel of `A` acting on `(O ⧸ Ideal.span {a}) ^ k`
equals the least additive valuation of a maximal minor of the matrix formed by stacking the rows
of `A` and of `a • 1`.

The proof has two steps:
1. The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` is isomorphic to the module of `O`-linear maps
   from `(k → O) ⧸ rowLattice A a` to `O ⧸ Ideal.span {a}`. Over a principal ideal domain, any
   finitely generated module annihilated by `a ≠ 0` has the same length as its module of linear
   maps into `O ⧸ Ideal.span {a}` (by the structure theorem for finitely generated torsion
   modules).
2. The quotient `(k → O) ⧸ rowLattice A a` has length equal to the least valuation of a maximal
   minor of `A.fromRows (a • 1)`: every choice of `k` rows spans a sublattice whose colength is
   the valuation of the corresponding minor (via diagonalization over a PID), while `rowLattice A a`
   is free of rank `card k` and the determinant of a basis matrix is a linear combination of these
   minors by multilinearity of the determinant.

## Main definitions and results

* `Matrix.maximalMinors`: the set of `card k`-by-`card k` minors of `A.fromRows (a • 1)`.
* `Matrix.matrixKernel`: the kernel of `A` acting on `k → B`.
* `Matrix.rowLattice`: the submodule of `k → O` spanned by the rows of `A` and `a • 1`.
* `Matrix.length_quotient_span_row`: over a discrete valuation ring `O`, the quotient of `k → O`
  by the rows of a square matrix `N` has length `IsDiscreteValuationRing.addVal O N.det`.
* `Matrix.isLeast_length_quotient_rowLattice`: the length of `(k → O) ⧸ A.rowLattice a` is the
  least valuation of a maximal minor in `A.maximalMinors a`.
* `Matrix.isLeast_length_matrixKernel`: for a ring homomorphism `ev : Λ →+* O` into a discrete
  valuation ring with `ev a ≠ 0`, the length of `(A.map ev).matrixKernel (O ⧸ Ideal.span {ev a})`
  is the least `addVal O (ev P)` for `P ∈ A.maximalMinors a`.

## References

* N. Bourbaki, *Algebra*, Chapter VII, §4 (Elementary divisors).
* S. Lang, *Algebra*, Chapter III, §7 (Modules over principal ideal domains).
* Adapted from `grh-lean`, `src/Lib/General/Algebra/SharpMinors.lean`
  (Copyright 2026 Anthropic, PBC, Apache 2.0).
-/

public section

noncomputable section

open Matrix Module Submodule IsDiscreteValuationRing

namespace Matrix

section CommSemiring

variable {O r k : Type*} [CommSemiring O] [Fintype k]

/-- The kernel of `A` on `k → B`, for an `O`-module `B`: the vectors `w` such that
`∑ j, A i j • w j = 0` for every row index `i`. -/
def matrixKernel (A : Matrix r k O) (B : Type*) [AddCommMonoid B] [Module O B] :
    Submodule O (k → B) :=
  ⨅ i : r, LinearMap.ker (∑ j : k, A i j • LinearMap.proj j : (k → B) →ₗ[O] B)

/-- A vector lies in `A.matrixKernel B` exactly when every row of `A` sends it to `0`. -/
@[simp]
theorem mem_matrixKernel {A : Matrix r k O} {B : Type*} [AddCommMonoid B] [Module O B]
    {w : k → B} :
    w ∈ A.matrixKernel B ↔ ∀ i : r, ∑ j : k, A i j • w j = 0 := by
  simp [matrixKernel]

/-- The submodule of `k → O` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

omit [Fintype k] in
/-- Every multiple of `a` lies in `A.rowLattice a`. -/
theorem smul_mem_rowLattice [Finite k] [DecidableEq k] (A : Matrix r k O) (a : O) (v : k → O) :
    a • v ∈ A.rowLattice a := by
  have := Fintype.ofFinite k
  rw [pi_eq_sum_univ' v, Finset.smul_sum]
  refine sum_mem fun j _ ↦ ?_
  rw [smul_comm]
  exact smul_mem _ _
    (subset_span ⟨.inr j, by ext i; simp [Matrix.one_apply, Pi.single_apply, eq_comm]⟩)

end CommSemiring

section CommRing

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [Fintype k] [DecidableEq k]

/-- The minors of size `card k` of the matrix formed by the rows of `A` and of `a • 1`, where `k`
indexes the columns. The family of rows of `A` may be infinite. A choice of rows with a repetition
is allowed; it contributes the minor `0`. -/
def maximalMinors (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- A ring homomorphism `ev` maps the maximal minors of the rows of `A` and `a • 1` onto those of
the rows of `A.map ev` and `ev a • 1`. -/
theorem image_maximalMinors (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' A.maximalMinors a = (A.map ev).maximalMinors (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [Matrix.one_apply, apply_ite ev]
  simp [maximalMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

/-- The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` has the length of the module of `O`-linear maps
from `(k → O) ⧸ A.rowLattice a` to `O ⧸ Ideal.span {a}`, since a map corresponds to its values on
the standard basis. -/
theorem length_matrixKernel_eq_length_linearMap (A : Matrix r k O) (a : O) :
    length O (A.matrixKernel (O ⧸ Ideal.span {a})) =
      length O (((k → O) ⧸ A.rowLattice a) →ₗ[O] O ⧸ Ideal.span {a}) := by
  let val : (((k → O) ⧸ A.rowLattice a) →ₗ[O] O ⧸ Ideal.span {a}) →ₗ[O]
      k → O ⧸ Ideal.span {a} :=
    LinearMap.pi fun j ↦ LinearMap.applyₗ ((A.rowLattice a).mkQ (Pi.single j 1))
  have h_inj : Function.Injective val := fun g g' h_val ↦
    linearMap_qext _ ((Pi.basisFun O k).ext fun j ↦ by simpa [val] using congrFun h_val j)
  have h_range : LinearMap.range val = A.matrixKernel (O ⧸ Ideal.span {a}) := by
    ext w
    rw [mem_matrixKernel]
    refine ⟨?_, fun hw ↦ ?_⟩
    · rintro ⟨g, rfl⟩ i
      have h_row : (A.rowLattice a).mkQ (A i) = 0 :=
        (Quotient.mk_eq_zero _).2 (subset_span ⟨.inl i, rfl⟩)
      calc ∑ j, A i j • val g j
        _ = g ((A.rowLattice a).mkQ (∑ j, A i j • Pi.single j 1)) := by simp [val]
        _ = 0 := by rw [← pi_eq_sum_univ', h_row, map_zero]
    · have h_kill : A.rowLattice a ≤ LinearMap.ker (Fintype.linearCombination O w) :=
        span_le.2 <| by
          rintro _ ⟨i | i, rfl⟩
          · exact hw i
          · simp only [SetLike.mem_coe, LinearMap.mem_ker, Fintype.linearCombination_apply,
              Matrix.row_apply, Matrix.fromRows_apply_inr, Matrix.smul_apply, smul_eq_mul]
            refine Finset.sum_eq_zero fun j _ ↦ ?_
            simp [Algebra.smul_def, (Ideal.Quotient.eq_zero_iff_dvd a _).2 (dvd_mul_right a _)]
      exact ⟨liftQ _ _ h_kill, funext fun j : k ↦ by simp [val]⟩
  rw [← h_range, (LinearEquiv.ofInjective val h_inj).length_eq]

end CommRing

end Matrix

namespace TauCeti

/-- In an integral domain `O`, if `d ∣ a` with `a ≠ 0`, then the module of `O`-linear maps
`(O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})` has the same length as `O ⧸ Ideal.span {d}`. -/
theorem length_linearMap_quotient_span_of_dvd {O : Type*} [CommRing O] [IsDomain O]
    {a d : O} (ha : a ≠ 0) (hd : d ∣ a) :
    length O ((O ⧸ Ideal.span {d}) →ₗ[O] O ⧸ Ideal.span {a}) =
      length O (O ⧸ Ideal.span {d}) := by
  -- The linear maps `O / d → O / a` are the multiples of multiplication by `a / d`.
  obtain ⟨c, rfl⟩ := hd
  have h_mul_le :
      Ideal.span {d} ≤ Submodule.comap (LinearMap.lsmul O O c) (Ideal.span {d * c}) :=
    (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 (by simp [mul_comm]))
  let mulC : (O ⧸ Ideal.span {d}) →ₗ[O] O ⧸ Ideal.span {d * c} :=
    mapQ _ _ (LinearMap.lsmul O O c) h_mul_le
  let φ : O →ₗ[O] (O ⧸ Ideal.span {d}) →ₗ[O] O ⧸ Ideal.span {d * c} :=
    LinearMap.toSpanSingleton O _ mulC
  have hφ (t : O) : φ t 1 = Ideal.Quotient.mk _ (t * c) :=
    congrArg (Ideal.Quotient.mk _) (by simp)
  have h_ext {g g' : (O ⧸ Ideal.span {d}) →ₗ[O] O ⧸ Ideal.span {d * c}}
      (h_one : g 1 = g' 1) : g = g' :=
    linearMap_qext _ (LinearMap.ext_ring h_one)
  have h_ker : LinearMap.ker φ = Ideal.span {d} := by
    ext t
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton,
      ← mul_dvd_mul_iff_right (right_ne_zero_of_mul ha),
      ← Ideal.Quotient.eq_zero_iff_dvd, ← hφ]
    exact ⟨fun h ↦ by rw [h, LinearMap.zero_apply], fun h ↦ h_ext h⟩
  have h_surj : Function.Surjective φ := fun g ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g 1)
    have h_zero : Ideal.Quotient.mk (Ideal.span {d * c}) (d * y) = 0 := by
      have h_smul : Ideal.Quotient.mk (Ideal.span {d * c}) (d * y) =
          d • Ideal.Quotient.mk (Ideal.span {d * c}) y := by
        simp [Algebra.smul_def]
      rw [h_smul, hy, ← map_smul]
      have h_kill : d • (1 : O ⧸ Ideal.span {d}) = 0 := by
        simp [Algebra.smul_def, (Ideal.Quotient.eq_zero_iff_dvd d d).2 dvd_rfl]
      rw [h_kill, map_zero]
    obtain ⟨t, rfl⟩ : c ∣ y := by
      rwa [Ideal.Quotient.eq_zero_iff_dvd,
        mul_dvd_mul_iff_left (left_ne_zero_of_mul ha)] at h_zero
    exact ⟨t, h_ext (by rw [hφ, mul_comm t, hy])⟩
  exact ((quotEquivOfEq _ _ h_ker.symm).trans
    (φ.quotKerEquivOfSurjective h_surj)).length_eq.symm

/-- Over a principal ideal domain `O`, a finitely generated module `Q` annihilated by `a ≠ 0` has
the same length as its module of `O`-linear maps into `O ⧸ Ideal.span {a}`. -/
theorem length_linearMap_quotient_span {O Q : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    {a : O} (ha : a ≠ 0) (h_kill : ∀ x : Q, a • x = 0) :
    length O (Q →ₗ[O] O ⧸ Ideal.span {a}) = length O Q := by
  classical
  have h_torsion : IsTorsion O Q := fun x ↦ ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h_kill x⟩
  obtain ⟨ι, _, p, -, n, ⟨e⟩⟩ := equiv_directSum_of_isTorsion h_torsion
  let d (i : ι) : O := p i ^ n i
  let e' : Q ≃ₗ[O] ∀ i, O ⧸ Ideal.span {d i} := e.trans DFinsupp.linearEquivFunOnFintype
  have h_dvd (i : ι) : d i ∣ a := by
    have h_one : a • (1 : O ⧸ Ideal.span {d i}) = 0 := by
      simpa using congrFun (congrArg e' (h_kill (e'.symm (Pi.single i 1)))) i
    simpa [← Ideal.Quotient.eq_zero_iff_dvd, Algebra.smul_def] using h_one
  calc length O (Q →ₗ[O] O ⧸ Ideal.span {a})
    _ = length O (∀ i, (O ⧸ Ideal.span {d i}) →ₗ[O] O ⧸ Ideal.span {a}) :=
        ((LinearMap.lsum O _ O).trans (e'.symm.congrLeft _ O)).length_eq.symm
    _ = length O Q := by
        simp [e'.length_eq, length_pi_of_fintype,
          length_linearMap_quotient_span_of_dvd ha (h_dvd _)]

/-- A vector lies in the row span of `U * diagonal d * V`, with `U` and `V` invertible matrices,
if and only if `d i` divides the `i`-th coordinate of `v ᵥ* V⁻¹` for every `i`. -/
theorem mem_span_row_mul_diagonal_mul_iff {O k : Type*} [CommRing O] [Fintype k] [DecidableEq k]
    {U V : (Matrix k k O)ˣ} {d v : k → O} :
    v ∈ span O (Set.range (U.val * diagonal d * V.val).row) ↔
      ∀ i : k, d i ∣ (v ᵥ* (V⁻¹).val) i := by
  simp only [← range_vecMulLinear, LinearMap.mem_range, vecMulLinear_apply]
  constructor
  · rintro ⟨u, rfl⟩ i
    rw [vecMul_vecMul, V.mul_inv_cancel_right, ← vecMul_vecMul, vecMul_diagonal]
    exact dvd_mul_left _ _
  · intro h_dvd
    choose u hu using h_dvd
    have h_diag : u ᵥ* diagonal d = v ᵥ* (V⁻¹).val := funext fun i ↦ by
      rw [vecMul_diagonal, mul_comm, hu i]
    refine ⟨u ᵥ* (U⁻¹).val, ?_⟩
    calc u ᵥ* (U⁻¹).val ᵥ* (U.val * diagonal d * V.val) = u ᵥ* diagonal d ᵥ* V.val := by
          rw [vecMul_vecMul, ← mul_assoc, ← mul_assoc, U.inv_mul, one_mul, ← vecMul_vecMul]
      _ = v := by rw [h_diag, vecMul_vecMul, V.inv_mul, vecMul_one]

/-- If every row of a square matrix `N` lies in the row span of a matrix `M`, then `det N` is an
`O`-linear combination of maximal minors of `M`, so any common divisor `x` of those minors divides
`det N`. -/
theorem dvd_det_of_forall_row_mem_span {O m k : Type*} [CommRing O] [Fintype k] [DecidableEq k]
    {M : Matrix m k O} {N : Matrix k k O} {x : O}
    (h_minor : ∀ f : k → m, x ∣ (M.submatrix f id).det)
    (h_row : ∀ i : k, N.row i ∈ span O (Set.range M.row)) : x ∣ N.det := by
  choose c hc using fun i : k ↦ Finsupp.mem_span_range_iff_exists_finsupp.1 (h_row i)
  have h_det : N.det =
      detRowAlternating.toMultilinearMap fun i ↦ ∑ t ∈ (c i).support, c i t • M.row t :=
    congrArg det (funext fun i ↦ (hc i).symm)
  simp only [h_det, MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  exact Finset.dvd_sum fun f _ ↦ (h_minor f).mul_left _

end TauCeti

namespace Matrix

section PID

variable {O r k : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [Finite k] [DecidableEq k]

/-- Over a principal ideal domain, for `a ≠ 0`, the row lattice `A.rowLattice a` is free of full
rank, hence spanned by the rows of a square matrix. -/
theorem exists_span_row_eq_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    ∃ N : Matrix k k O, span O (Set.range N.row) = A.rowLattice a := by
  have := Fintype.ofFinite k
  let g : (k → O) →ₗ[O] A.rowLattice a :=
    (LinearMap.lsmul O _ a).codRestrict _ (A.smul_mem_rowLattice a)
  have h_inj : Function.Injective g := (LinearMap.lsmul_injective ha).codRestrict _
  have h_rank : finrank O (k → O) = finrank O (A.rowLattice a) :=
    (g.finrank_le_finrank_of_injective h_inj).antisymm (finrank_le _)
  let b : Basis k O (A.rowLattice a) := (Pi.basisFun O k).map (.ofFinrankEq _ _ h_rank)
  refine ⟨of fun i ↦ (b i : k → O), ?_⟩
  have h_row : Set.range (of fun i ↦ (b i : k → O)).row =
      Set.range ((A.rowLattice a).subtype ∘ b) := rfl
  rw [h_row, Set.range_comp, ← Submodule.map_span, b.span_eq, map_subtype_top]

end PID

section DVR

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Fintype k] [DecidableEq k]

/-- Over a discrete valuation ring `O`, the quotient of `k → O` by the rows of a square matrix `N`
has length equal to the additive valuation of `N.det`. -/
theorem length_quotient_span_row (N : Matrix k k O) :
    length O ((k → O) ⧸ span O (Set.range N.row)) = addVal O N.det := by
  obtain ⟨L, Q, d, hL, hQ, hdiag⟩ := N.exists_mul_mul_eq_diagonal
  obtain ⟨uL, rfl⟩ := (isUnit_iff_isUnit_det L).2 hL
  obtain ⟨uQ, rfl⟩ := (isUnit_iff_isUnit_det Q).2 hQ
  have hN : N = (uL⁻¹).val * diagonal d * (uQ⁻¹).val := by
    calc N = (uL⁻¹).val * (uL.val * N * uQ.val) * (uQ⁻¹).val := by
          simp [mul_assoc]
      _ = (uL⁻¹).val * diagonal d * (uQ⁻¹).val := by rw [hdiag]
  let π : (k → O) →ₗ[O] ∀ i, O ⧸ Ideal.span {d i} :=
    LinearMap.piMap (fun i ↦ (Ideal.span {d i}).mkQ) ∘ₗ uQ.val.vecMulLinear
  have h_surj : Function.Surjective π :=
    (Function.Surjective.piMap fun _ ↦ mkQ_surjective _).comp
      fun v ↦ ⟨v ᵥ* (uQ⁻¹).val, by simp⟩
  have h_ker : LinearMap.ker π = span O (Set.range N.row) := by
    ext v
    rw [hN, TauCeti.mem_span_row_mul_diagonal_mul_iff, inv_inv, LinearMap.mem_ker, funext_iff]
    exact forall_congr' fun i ↦ Ideal.Quotient.eq_zero_iff_dvd (d i) _
  have h_unit (U : (Matrix k k O)ˣ) : addVal O U.val.det = 0 :=
    addVal_eq_zero_iff.2 ((isUnit_iff_isUnit_det _).1 U.isUnit)
  have h_ord (x : O) : length O (O ⧸ Ideal.span {x}) = addVal O x := Ring.ord_eq_addVal x
  have h_prod : addVal O (∏ i, d i) = ∑ i, addVal O (d i) := by
    induction (Finset.univ : Finset k) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.prod_insert ha, Finset.sum_insert ha, ih]
  calc length O ((k → O) ⧸ span O (Set.range N.row))
    _ = length O (∀ i, O ⧸ Ideal.span {d i}) := by
        rw [← h_ker, (π.quotKerEquivOfSurjective h_surj).length_eq]
    _ = addVal O (∏ i, d i) := by
        rw [length_pi_of_fintype, h_prod]
        simp only [h_ord]
    _ = addVal O N.det := by
        rw [hN, det_mul, det_mul, det_diagonal, addVal_mul, addVal_mul,
          h_unit uL⁻¹, h_unit uQ⁻¹, zero_add, add_zero]

/-- Over a discrete valuation ring `O` and for `a ≠ 0`, the quotient of `k → O` by `A.rowLattice a`
has length equal to the least valuation of a maximal minor in `A.maximalMinors a`. -/
theorem isLeast_length_quotient_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    IsLeast (addVal O '' A.maximalMinors a) (length O ((k → O) ⧸ A.rowLattice a)) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) : ℕ∞ := addVal O (M.submatrix f id).det
  have h_lower (f : k → r ⊕ k) : length O ((k → O) ⧸ A.rowLattice a) ≤ v f := by
    have h_le : span O (Set.range (M.submatrix f id).row) ≤ A.rowLattice a :=
      span_mono (Set.range_comp_subset_range f M.row)
    simpa only [length_quotient_span_row] using length_le_of_surjective _ (factor_surjective h_le)
  obtain ⟨N, hN⟩ := A.exists_span_row_eq_rowLattice ha
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  let f₀ : k → r ⊕ k := Function.argmin v
  have h_dvd : (M.submatrix f₀ id).det ∣ N.det :=
    TauCeti.dvd_det_of_forall_row_mem_span
      (fun f ↦ addVal_le_iff_dvd.1 (Function.argmin_le v f))
      fun i ↦ hN.le (subset_span ⟨i, rfl⟩)
  have h_upper : v f₀ ≤ length O ((k → O) ⧸ A.rowLattice a) :=
    (addVal_le_iff_dvd.2 h_dvd).trans_eq (by rw [← hN, length_quotient_span_row])
  exact ⟨⟨(M.submatrix f₀ id).det, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩,
    Set.forall_mem_image.2 (Set.forall_mem_range.2 h_lower)⟩

/-- For a matrix `A` over a commutative ring `Λ` with columns indexed by a finite type `k`, and a
ring homomorphism `ev : Λ →+* O` into a discrete valuation ring with `ev a ≠ 0`, the length of
`(A.map ev).matrixKernel (O ⧸ Ideal.span {ev a})` is the least `addVal O (ev P)` as `P` ranges
over `A.maximalMinors a`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' A.maximalMinors a)
      (length O ((A.map ev).matrixKernel (O ⧸ Ideal.span {ev a}))) := by
  have h_kill (x : (k → O) ⧸ (A.map ev).rowLattice (ev a)) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    simpa [← Quotient.mk_smul] using (A.map ev).smul_mem_rowLattice (ev a) v
  rw [length_matrixKernel_eq_length_linearMap, TauCeti.length_linearMap_quotient_span ha h_kill,
    ← Set.image_image (addVal O) ev, image_maximalMinors]
  exact (A.map ev).isLeast_length_quotient_rowLattice ha

end DVR

end Matrix

end
