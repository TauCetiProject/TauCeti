/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Basis.SMul
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Finite-dimensional frame functions

A frame function is real-valued on the unit sphere and has a prescribed sum over
orthonormal bases. Hermitian quadratic forms supply examples, with weight their trace,
and are determined by their values on the sphere. The zero- and one-dimensional cases
and nonnegative functions of weight zero need no Gleason theorem.

Multiplying a unit vector by a complex scalar of norm one leaves every frame function
unchanged. Positive operators give nonnegative quadratic frame functions; the diagonal
operator with entries two, one, and zero gives an example of weight three.

## References

* A. M. Gleason, Measures on the closed subspaces of a Hilbert space,
  Journal of Mathematics and Mechanics 6 (1957), 885–893.
-/

public section

open scoped InnerProductSpace BigOperators ComplexOrder

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A frame function on a finite-dimensional space, with real values and basis sum `w`. -/
def IsFrameFunction (f : {v : E // ‖v‖ = 1} → ℝ) (w : ℝ) : Prop :=
  FiniteDimensional ℂ E ∧
    ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∑ i, f ⟨b i, b.norm_eq_one i⟩ = w

/-- The defining orthonormal-basis equation, as a public introduction and elimination rule. -/
theorem isFrameFunction_iff [FiniteDimensional ℂ E] (f : {v : E // ‖v‖ = 1} → ℝ) (w : ℝ) :
    IsFrameFunction f w ↔
      ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
        ∑ i, f ⟨b i, b.norm_eq_one i⟩ = w :=
  ⟨And.right, fun h => ⟨inferInstance, h⟩⟩

/-- Constant functions have weight the dimension times their value. -/
theorem isFrameFunction_const [FiniteDimensional ℂ E] (c : ℝ) :
    IsFrameFunction (fun _ : {v : E // ‖v‖ = 1} => c) (Module.finrank ℂ E * c) := by
  refine ⟨inferInstance, fun b => ?_⟩
  simp

namespace IsFrameFunction

variable {f : {v : E // ‖v‖ = 1} → ℝ} {w : ℝ}

/-- A frame function carries finiteness of its underlying space. -/
theorem finiteDimensional (hf : IsFrameFunction f w) : FiniteDimensional ℂ E := hf.1

/-- The frame equation holds for any finite indexing type. -/
theorem sum_eq (hf : IsFrameFunction f w) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) : ∑ i, f ⟨b i, b.norm_eq_one i⟩ = w := by
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b.toBasis).symm
  calc
    ∑ i, f ⟨b i, b.norm_eq_one i⟩ =
        ∑ j, f ⟨(b.reindex e) j, (b.reindex e).norm_eq_one j⟩ :=
      Fintype.sum_equiv e _ _ (fun i => by simp [OrthonormalBasis.reindex_apply])
    _ = w := hf.2 (b.reindex e)

/-- A frame function depends only on the ray of a unit vector. -/
theorem apply_smul_of_norm_eq_one (hf : IsFrameFunction f w) (c : ℂ) (hc : ‖c‖ = 1)
    (v : {v : E // ‖v‖ = 1}) :
    f ⟨c • v.val, by simp [norm_smul, hc, v.property]⟩ = f v := by
  classical
  let := hf.finiteDimensional
  have ho : Orthonormal ℂ ((↑) : ({v.val} : Set E) → E) := by
    rw [orthonormal_subsingleton_iff]
    rintro ⟨x, hx⟩
    simpa [Set.mem_singleton_iff.mp hx] using v.property
  obtain ⟨s, b, hs, hb⟩ := ho.exists_orthonormalBasis_extension
  let i : s := ⟨v.val, hs (by simp)⟩
  have hi : b i = v.val := congrFun hb i
  let a : s → ℂ := Function.update (fun _ => 1) i c
  have ha (j : s) : ‖a j‖ = 1 := by
    by_cases hj : j = i <;> simp [a, hj, hc]
  let d := b.toBasis.isUnitSMul (fun j => isUnit_iff_ne_zero.mpr
    (norm_ne_zero_iff.mp (by rw [ha j]; exact one_ne_zero)))
  have hd (j : s) : d j = a j • b j := Module.Basis.isUnitSMul_apply _ j
  have hon : Orthonormal ℂ d := by
    constructor
    · intro j
      simp [hd, norm_smul, ha, b.norm_eq_one]
    · intro j k hjk
      simp [hd, inner_smul_left, inner_smul_right, b.orthonormal.inner_eq_zero hjk]
  let b' := d.toOrthonormalBasis hon
  have hb' (j : s) : b' j = a j • b j := by
    simpa only [b', Module.Basis.coe_toOrthonormalBasis] using hd j
  have he : ∑ j ∈ Finset.univ.erase i, f ⟨b' j, b'.norm_eq_one j⟩ =
      ∑ j ∈ Finset.univ.erase i, f ⟨b j, b.norm_eq_one j⟩ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    congr 1
    apply Subtype.ext
    simp [hb', a, hji]
  have hsum := (hf.sum_eq b').trans (hf.sum_eq b).symm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i), he] at hsum
  have h := add_left_cancel hsum
  simpa [hb', a, hi] using h

/-- Adding frame functions adds their weights. -/
theorem add (hf : IsFrameFunction f w) {g : {v : E // ‖v‖ = 1} → ℝ} {w' : ℝ}
    (hg : IsFrameFunction g w') : IsFrameFunction (f + g) (w + w') := by
  refine ⟨hf.finiteDimensional, fun b => ?_⟩
  simp only [Pi.add_apply, Finset.sum_add_distrib, hf.2 b, hg.2 b]

/-- Multiplying a frame function by a real scalar multiplies its weight. -/
theorem smul (hf : IsFrameFunction f w) (c : ℝ) :
    IsFrameFunction (c • f) (c * w) := by
  refine ⟨hf.finiteDimensional, fun b => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf.2 b]

/-- The weight is determined by the function. -/
theorem weight_unique (hf : IsFrameFunction f w) {w' : ℝ}
    (hf' : IsFrameFunction f w') : w = w' := by
  let := hf.finiteDimensional
  exact (hf.2 (stdOrthonormalBasis ℂ E)).symm.trans (hf'.2 (stdOrthonormalBasis ℂ E))

/-- Nonnegative frame functions have nonnegative weight, including in dimension zero. -/
theorem weight_nonneg (hf : IsFrameFunction f w) (hn : ∀ v, 0 ≤ f v) : 0 ≤ w := by
  let := hf.finiteDimensional
  rw [← hf.2 (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg fun _ _ => hn _

/-- A nonnegative frame function of weight zero vanishes on the entire unit sphere. -/
theorem eq_zero_of_nonneg (hf : IsFrameFunction f 0) (hn : ∀ v, 0 ≤ f v) : f = 0 := by
  classical
  let := hf.finiteDimensional
  funext v
  have ho : Orthonormal ℂ ((↑) : ({v.val} : Set E) → E) := by
    rw [orthonormal_subsingleton_iff]
    rintro ⟨x, hx⟩
    simpa [Set.mem_singleton_iff.mp hx] using v.property
  obtain ⟨s, b, hs, hb⟩ := ho.exists_orthonormalBasis_extension
  have hv : v.val ∈ s := hs (by simp)
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn ⟨b i, b.norm_eq_one i⟩)).mp
    (hf.sum_eq b) ⟨v.val, hv⟩ (Finset.mem_univ _)
  simpa [hb] using h

/-- In dimension one each unit vector is itself an orthonormal basis. -/
theorem apply_eq_weight_of_finrank_one (hf : IsFrameFunction f w)
    (hd : Module.finrank ℂ E = 1) (v : {v : E // ‖v‖ = 1}) : f v = w := by
  let := hf.finiteDimensional
  simpa using hf.sum_eq
    (FiniteDimensional.orthonormalBasisSingleton Unit ℂ hd v.val v.property)

end IsFrameFunction

/-- In dimension zero the empty orthonormal basis forces exactly weight zero. -/
theorem isFrameFunction_iff_of_finrank_zero [FiniteDimensional ℂ E]
    (f : {v : E // ‖v‖ = 1} → ℝ) (w : ℝ)
    (hd : Module.finrank ℂ E = 0) : IsFrameFunction f w ↔ w = 0 := by
  constructor
  · intro hf
    have h := hf.2 (stdOrthonormalBasis ℂ E)
    have hz : ∑ i, f ⟨stdOrthonormalBasis ℂ E i, (stdOrthonormalBasis ℂ E).norm_eq_one i⟩ = 0 :=
      Finset.sum_eq_zero fun i _ => Fin.elim0 (Fin.cast hd i)
    exact h.symm.trans hz
  · rintro rfl
    refine ⟨inferInstance, fun b => ?_⟩
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 (Fin.cast hd i)

/-- The real quadratic function of an operator, restricted to unit vectors. -/
noncomputable def _root_.LinearMap.quadraticFrameFunction (T : E →ₗ[ℂ] E)
    (v : {v : E // ‖v‖ = 1}) : ℝ :=
  RCLike.re ⟪v.val, T v.val⟫_ℂ

/-- Evaluation of the real quadratic function on a unit vector. -/
@[simp]
theorem _root_.LinearMap.quadraticFrameFunction_apply (T : E →ₗ[ℂ] E)
    (v : {v : E // ‖v‖ = 1}) :
    T.quadraticFrameFunction v = RCLike.re ⟪v.val, T v.val⟫_ℂ := (rfl)

open _root_.LinearMap (quadraticFrameFunction)

/-- The real quadratic function has weight the real part of the trace.
For Hermitian operators the inner product and trace are real. -/
theorem _root_.LinearMap.isFrameFunction_quadratic [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    IsFrameFunction (quadraticFrameFunction T) (Complex.re (T.trace ℂ E)) := by
  refine ⟨inferInstance, fun b => ?_⟩
  simpa [quadraticFrameFunction, map_sum] using
    congrArg Complex.re (T.trace_eq_sum_inner b).symm

/-- A positive operator has a nonnegative quadratic function on the unit sphere. -/
theorem _root_.LinearMap.IsPositive.quadraticFrameFunction_nonneg {T : E →ₗ[ℂ] E}
    (hT : T.IsPositive) (v : {v : E // ‖v‖ = 1}) :
    0 ≤ T.quadraticFrameFunction v :=
  hT.re_inner_nonneg_right v.val

open _root_.LinearMap (isFrameFunction_quadratic)

/-- A Hermitian operator is uniquely determined by its quadratic function on unit vectors. -/
theorem _root_.LinearMap.IsSymmetric.ext_quadraticFrameFunction {S T : E →ₗ[ℂ] E}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (h : quadraticFrameFunction S = quadraticFrameFunction T) : S = T := by
  apply (ext_inner_map S T).mp
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let a : ℂ := (‖x‖ : ℂ)⁻¹
  have ha : a ≠ 0 := by simp [a, hx]
  have hv : ‖a • x‖ = 1 := by simp [a, norm_smul, hx]
  have hs : (quadraticFrameFunction S ⟨a • x, hv⟩ : ℂ) = ⟪a • x, S (a • x)⟫_ℂ := by
    simpa [quadraticFrameFunction] using hS.coe_re_inner_self_apply (a • x)
  have ht : (quadraticFrameFunction T ⟨a • x, hv⟩ : ℂ) = ⟪a • x, T (a • x)⟫_ℂ := by
    simpa [quadraticFrameFunction] using hT.coe_re_inner_self_apply (a • x)
  have he : ⟪a • x, S (a • x)⟫_ℂ = ⟪a • x, T (a • x)⟫_ℂ := by
    rw [← hs, ← ht, h]
  simp only [map_smul, inner_smul_left, inner_smul_right] at he
  have he' : ⟪x, S x⟫_ℂ = ⟪x, T x⟫_ℂ :=
    mul_left_cancel₀ (by simpa using ha) (mul_left_cancel₀ ha he)
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) he'

/-- The Hermitian operator of a nonnegative weight-zero quadratic frame function is zero. -/
theorem IsFrameFunction.operator_eq_zero {T : E →ₗ[ℂ] E}
    (hf : IsFrameFunction (quadraticFrameFunction T) 0) (hT : T.IsSymmetric)
    (hn : ∀ v, 0 ≤ quadraticFrameFunction T v) : T = 0 := by
  apply hT.ext_quadraticFrameFunction (by intro x y; simp)
  rw [hf.eq_zero_of_nonneg hn]
  funext v
  simp [quadraticFrameFunction]

/-- In dimension one a frame function is induced by multiplication by its weight. -/
theorem IsFrameFunction.eq_quadratic_of_finrank_one
    {f : {v : E // ‖v‖ = 1} → ℝ} {w : ℝ} (hf : IsFrameFunction f w)
    (hd : Module.finrank ℂ E = 1) :
    f = quadraticFrameFunction ((w : ℂ) • LinearMap.id) := by
  funext v
  rw [hf.apply_eq_weight_of_finrank_one hd v]
  simp only [quadraticFrameFunction, LinearMap.smul_apply, LinearMap.id_apply,
    inner_smul_right, inner_self_eq_norm_sq_to_K, v.property]
  norm_num

/-- The weight of a Hermitian quadratic frame function is its complex trace. -/
theorem IsFrameFunction.trace_eq {T : E →ₗ[ℂ] E} {w : ℝ}
    (hf : IsFrameFunction (quadraticFrameFunction T) w) (hT : T.IsSymmetric) :
    T.trace ℂ E = (w : ℂ) := by
  let := hf.finiteDimensional
  let b := stdOrthonormalBasis ℂ E
  rw [T.trace_eq_sum_inner b]
  calc
    ∑ i, ⟪b i, T (b i)⟫_ℂ = ∑ i, (quadraticFrameFunction T ⟨b i, b.norm_eq_one i⟩ : ℂ) :=
      Finset.sum_congr rfl fun i _ =>
        (hT.coe_re_inner_self_apply (b i)).symm
    _ = (w : ℂ) := by exact_mod_cast hf.2 b

/-- In dimension one the frame condition says exactly that the function is constant. -/
theorem isFrameFunction_iff_of_finrank_one [FiniteDimensional ℂ E]
    (f : {v : E // ‖v‖ = 1} → ℝ) (w : ℝ)
    (hd : Module.finrank ℂ E = 1) : IsFrameFunction f w ↔ ∀ v, f v = w := by
  refine ⟨fun hf v => hf.apply_eq_weight_of_finrank_one hd v,
    fun hf => ⟨inferInstance, fun b => ?_⟩⟩
  simp only [hf]
  simp [hd]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- The weight-three function is induced by the Hermitian matrix `diag(2, 1, 0)`. -/
theorem quadraticFrameFunction_diagonal_two_one_zero
    (v : {v : EuclideanSpace ℂ (Fin 3) // ‖v‖ = 1}) :
    quadraticFrameFunction (Matrix.diagonal (![2, 1, 0] : Fin 3 → ℂ)).toEuclideanLin v =
      2 * ‖v.val 0‖ ^ 2 + ‖v.val 1‖ ^ 2 := by
  have hd : (fun i : Fin 3 => ((![2, 1, 0] : Fin 3 → ℝ) i : ℂ)) = ![2, 1, 0] := by
    funext i
    fin_cases i <;> norm_num
  simpa [quadraticFrameFunction, hd, Fin.sum_univ_succ, inner_re_symm, mul_comm] using
    Matrix.re_inner_toEuclideanLin_diagonal_apply_self
      (![2, 1, 0] : Fin 3 → ℝ) v.val

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- The matrix inducing the weight-three example is positive semidefinite. -/
theorem diagonal_two_one_zero_posSemidef :
    (Matrix.diagonal (![2, 1, 0] : Fin 3 → ℂ)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- The operator inducing the weight-three example has trace three. -/
theorem trace_diagonal_two_one_zero :
    (Matrix.diagonal (![2, 1, 0] : Fin 3 → ℂ)).toEuclideanLin.trace
      ℂ (EuclideanSpace ℂ (Fin 3)) = 3 := by
  norm_num [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_diagonal,
    Fin.sum_univ_succ]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- The unnormalized weight-three frame function on complex three-space. -/
theorem isFrameFunction_weight_three :
    IsFrameFunction (fun v : {v : EuclideanSpace ℂ (Fin 3) // ‖v‖ = 1} =>
      2 * ‖v.val 0‖ ^ 2 + ‖v.val 1‖ ^ 2) 3 := by
  simpa only [isFrameFunction_iff, trace_diagonal_two_one_zero, Complex.re_ofNat,
    quadraticFrameFunction_diagonal_two_one_zero] using
    isFrameFunction_quadratic (Matrix.diagonal (![2, 1, 0] : Fin 3 → ℂ)).toEuclideanLin

end TauCeti
