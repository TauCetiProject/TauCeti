/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Sign
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
public import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Basic.Real.Sign
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import TauCeti.Topology.Circle.Degree

import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.Topology.Instances.Matrix

/-!
# The Maslov index of a path of Lagrangian frames

A unitary matrix `U ∈ U(n)` is a frame of the Lagrangian subspace `Λ = U ℝⁿ` of `ℂⁿ`, for the
standard symplectic form `Im ⟪·, ·⟫`. Two frames of the same Lagrangian differ by a real orthogonal
matrix, so the **Souriau map** `W = U Uᵀ` (`Matrix.UnitaryGroup.souriau`) depends only on `Λ`
(`Matrix.UnitaryGroup.souriau_mul_of_mul_transpose_eq_one`,
`Matrix.UnitaryGroup.souriau_eq_of_realImage_eq`). It is a symmetric unitary matrix,
and `Λ ∩ ℝⁿ` is the real part of the eigenspace of `W` at the eigenvalue `1`.

The **Maslov index** of a path `U : [0, 1] → U(n)` of frames (`Matrix.UnitaryGroup.maslovIndex`)
is defined by Souriau's spectral formula for the Robbin–Salamon index of the path of Lagrangians
`U t ℝⁿ` relative to the fixed Lagrangian `ℝⁿ`: it counts, with sign, the eigenvalues of `W t`
that cross `1`, a crossing at an endpoint counting one half. Write `θ` for a continuous angle of
`det (W t) = det (U t) ^ 2`, and `s(W)` (`Matrix.spectralAngleSum`) for the sum, over the
eigenvalues `λ ≠ 1` of `W` counted with algebraic multiplicity, of `arg (-λ) / (2π)`. If
`λ = e^{iφ}` with `0 < φ < 2π` then `arg (-λ) / (2π) = φ / (2π) - 1/2`, so `s(W)` records the
positions of the eigenvalues relative to `1`. Then
`μ(U) = (θ 1 - θ 0) / (2π) - (s(W 1) - s(W 0))`.
While no eigenvalue passes through `1`, the changes of `θ / (2π)` and of `s` cancel. An
eigenvalue moving counterclockwise through `1` makes `s` jump by `-1`, so it adds `1` to the
index; an eigenvalue that starts or ends at `1` contributes one half.

The index has the formal properties of the Robbin–Salamon Maslov index for paths:

* it depends only on the path of Lagrangians, not on the frames
  (`Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq`);
* it is invariant under homotopies fixing the endpoints
  (`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic`);
* it is additive under catenation (`Matrix.UnitaryGroup.maslovIndex_trans`) and changes sign under
  reversal (`Matrix.UnitaryGroup.maslovIndex_symm`);
* it is additive under direct sums (`Matrix.UnitaryGroup.maslovIndex_sum`), also when they are
  read in the regrouped coordinates of symplectic direct sums
  (`Matrix.UnitaryGroup.maslovIndex_eq_add_of_coe_eq_symplecticSum`);
* it changes sign under complex conjugation of the frames
  (`Matrix.UnitaryGroup.maslovIndex_map_map_star`), which reflects the Lagrangians by the
  anti-symplectic involution `z ↦ conj z` fixing `ℝⁿ`: conjugation inverts `det (W t)` and
  negates `s(W t)` (`Matrix.spectralAngleSum_map_star`);
* on a path whose Lagrangians close up, it is the degree of the loop `t ↦ det (U t) ^ 2`, the
  Maslov index of the loop of Lagrangians (`Matrix.UnitaryGroup.maslovIndex_eq_degree`), and on a
  loop of frames it is twice the degree of `t ↦ det (U t)`
  (`Matrix.UnitaryGroup.maslovIndex_eq_two_mul_degree`).

For a diagonal path of frames `U t = diag (e^{i φ_j t})` it is computed explicitly
(`Matrix.UnitaryGroup.maslovIndex_eq_sum_of_diagonal`): each `φ_j` contributes
`c(φ_j 1) - c(φ_j 0)`, where `c(x) = (⌊x / π⌋ + ⌈x / π⌉) / 2` is the half-integer step function
with `c(kπ) = k` and `c = k + 1/2` on `(kπ, (k + 1)π)`. So `c(φ_j 1) - c(φ_j 0)` counts, with
sign, the multiples of `π` crossed by `φ_j`, endpoints counting one half. This gives the
normalization: the half-turn `t ↦ e^{iπt} ℝⁿ` has Maslov index `n`
(`Matrix.UnitaryGroup.maslovIndex_eq_card_of_halfTurn`).
It also gives the localization axiom of Robbin and Salamon for diagonal symmetric matrices
`A t = diag (a_j t)` (`Matrix.UnitaryGroup.maslovIndex_eq_sum_sign_of_diagonal_arctan`): the
graph `{x + i A x}` of `A t` has the frame `diag (e^{i arctan (a_j t)})`, and the index of the path
of graphs is `∑ j, (sign (a_j 1) - sign (a_j 0)) / 2`, half the change of the signature of `A`.

The index is natural under the real orthogonal group, which preserves `ℝⁿ`: moving a path of
frames by a fixed real orthogonal matrix does not change it
(`Matrix.UnitaryGroup.maslovIndex_map_mul_left`). The localization axiom for nondiagonal `A` is
deduced from the diagonal case in `TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization`.
For paths of graphs, the comparison with the definition of the index by crossing forms is in
`TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing`.

The index also satisfies the zero axiom of Robbin and Salamon: it vanishes on a path along which
the eigenvalue `1` of the Souriau maps keeps the same multiplicity, which is the dimension of
`U t ℝⁿ ∩ ℝⁿ` (`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq`). The determinant
of a unitary matrix `W` is `(-1) ^ (n - k) e^{2πi s(W)}`, where `k` is that multiplicity
(`Matrix.det_eq_neg_one_pow_mul_exp_spectralAngleSum`), and `s` is continuous along a family of
unitary matrices in which `k` is constant (`Matrix.continuousAt_spectralAngleSum`), since no other
eigenvalue can then reach `1`. So `2π s(W t) + (n - k) π` is a continuous angle of `det (W t)`, and
the two terms of the index cancel. With invariance under homotopies fixing the endpoints, the zero
axiom gives invariance under homotopies whose endpoints move through Lagrangians whose
intersections with `ℝⁿ` keep their dimensions, the stratum homotopy property of Robbin and Salamon
(`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq`).

The index modulo `2` depends only on the endpoint frames: `e^{πi μ(γ)}` is the quotient of the
values of `U ↦ det U e^{-πi s(U Uᵀ)}` at the two ends
(`Matrix.UnitaryGroup.exp_maslovIndex_mul_det_mul_exp_spectralAngleSum`), because `t ↦ det (γ t)`
is a continuous square root of `det (γ t γ tᵀ)`. For a unitary `W`, `e^{-πi s(W)} det (1 - W)` is a
nonnegative real number (`Matrix.exp_neg_spectralAngleSum_mul_det_one_sub_nonneg`), and
`det (1 - U Uᵀ) = det U det (conj U - U)` (`Matrix.UnitaryGroup.det_one_sub_souriau`). So at a
frame `U` of a Lagrangian transverse to `ℝⁿ`, `det U e^{-πi s(U Uᵀ)}` is a positive multiple of
`det (conj U - U)⁻¹`. This is how `TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Parity`
computes the parity of the Conley–Zehnder index.

## Main declarations

* `Matrix.spectralAngleSum`: the sum of `arg (-λ) / (2π)` over the eigenvalues `λ ≠ 1`.
* `Matrix.UnitaryGroup.souriau`: the Souriau map `U ↦ U Uᵀ`.
* `Matrix.UnitaryGroup.maslovIndex`: the Maslov index of a path of Lagrangian frames.
* `Matrix.det_eq_neg_one_pow_mul_exp_spectralAngleSum`: the determinant of a unitary matrix through
  its spectral angle sum.
* `Matrix.continuousAt_spectralAngleSum`: the spectral angle sum is continuous where the
  multiplicity of the eigenvalue `1` is locally constant.
* `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq`: the zero axiom.
* `Matrix.UnitaryGroup.exp_maslovIndex_mul_det_mul_exp_spectralAngleSum`: the index modulo `2`
  from the endpoint frames.
* `Matrix.UnitaryGroup.maslovIndex_map_map_star`: complex conjugation negates the index.
* `Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq`: the homotopy axiom,
  with endpoints along which the eigenvalue `1` of the Souriau map keeps its multiplicity.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the axioms of the Maslov index for paths).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148 (the map `U ↦ U Uᵀ` and the
  index through the eigenvalues of `U Uᵀ`).
* S. Cappell, R. Lee and E. Miller, *On the Maslov index*, Comm. Pure Appl. Math. **47** (1994),
  121--186, §1 (the Maslov index of a pair of Lagrangian paths through the eigenvalues of a
  unitary matrix, with half weights at the endpoints).
-/

public section

open Complex Filter Polynomial
open scoped ComplexOrder Topology unitInterval

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The position of a complex number `z ≠ 1` on the unit circle relative to `1`, as
`arg (-z) / (2π)`; it is `0` at `z = 1`. For `z = e^{iφ}` with `0 < φ < 2π` it is
`φ / (2π) - 1/2`. -/
private noncomputable def angleOffset (z : ℂ) : ℝ :=
  if z = 1 then 0 else arg (-z) / (2 * Real.pi)

/-- The **spectral angle sum** of a square complex matrix: the sum, over its eigenvalues `λ ≠ 1`
counted with algebraic multiplicity, of `arg (-λ) / (2π)`. For a unitary matrix with eigenvalues
`e^{iφ_j}`, `0 ≤ φ_j < 2π`, it is the sum of `φ_j / (2π) - 1/2` over the `j` with `φ_j ≠ 0`. -/
noncomputable def spectralAngleSum (A : Matrix n n ℂ) : ℝ :=
  (A.charpoly.roots.map angleOffset).sum

/-- The spectral angle sum of a diagonal matrix. -/
theorem spectralAngleSum_diagonal (d : n → ℂ) :
    spectralAngleSum (diagonal d) =
      ∑ i, if d i = 1 then 0 else arg (-d i) / (2 * Real.pi) := by
  rw [spectralAngleSum, charpoly_diagonal, Finset.prod_eq_multiset_prod,
    ← Function.comp_def (fun a : ℂ => X - C a) d, ← Multiset.map_map,
    roots_multiset_prod_X_sub_C, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp only [angleOffset, Function.comp_def]

/-- The spectral angle sum is additive under block upper-triangular, in particular
block-diagonal, sums. -/
@[simp]
theorem spectralAngleSum_fromBlocks_zero₂₁ (A : Matrix n n ℂ) (B : Matrix n m ℂ)
    (D : Matrix m m ℂ) :
    spectralAngleSum (fromBlocks A B 0 D) = spectralAngleSum A + spectralAngleSum D := by
  rw [spectralAngleSum, charpoly_fromBlocks_zero₂₁,
    roots_mul (mul_ne_zero (charpoly_monic A).ne_zero (charpoly_monic D).ne_zero),
    Multiset.map_add, Multiset.sum_add, spectralAngleSum, spectralAngleSum]

/-- The spectral angle sum is additive under symplectic direct sums, which are block-diagonal sums
read in regrouped coordinates. -/
@[simp]
theorem spectralAngleSum_symplecticSum (A : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    spectralAngleSum (symplecticSum A B) = spectralAngleSum A + spectralAngleSum B := by
  have h : symplecticSum A B = reindex (Equiv.sumSumSumComm n m n m).symm
      (Equiv.sumSumSumComm n m n m).symm (fromBlocks A 0 0 B) := by
    rw [symplecticSum_def, reindex_apply, Equiv.symm_symm]
  rw [h, spectralAngleSum, charpoly_reindex, ← spectralAngleSum, spectralAngleSum_fromBlocks_zero₂₁]

/-- The spectral angle sum is invariant under conjugation by an invertible matrix `P` with
inverse `Q`. -/
theorem spectralAngleSum_conj {P Q : Matrix n n ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (W : Matrix n n ℂ) : spectralAngleSum (P * W * Q) = spectralAngleSum W := by
  have h := charpoly_units_conj (⟨P, Q, hPQ, hQP⟩ : (Matrix n n ℂ)ˣ) W
  rw [Units.val_mk, inv_eq_left_inv hQP] at h
  rw [spectralAngleSum, spectralAngleSum, h]

/-- On the unit circle, complex conjugation negates the angle offset: away from `1`, the number
`-z` lies in the slit plane, where conjugation negates the argument. -/
private theorem angleOffset_conj {z : ℂ} (hz : ‖z‖ = 1) :
    angleOffset (starRingEnd ℂ z) = -angleOffset z := by
  by_cases h1 : z = 1
  · simp [angleOffset, h1]
  have h1' : starRingEnd ℂ z ≠ 1 := fun h ↦ h1 (by simpa using congrArg (starRingEnd ℂ) h)
  have hpi := slitPlane_arg_ne_pi (neg_mem_slitPlane_of_norm_eq_one hz h1)
  simp only [angleOffset, h1, h1', ↓reduceIte, ← map_neg, arg_conj, hpi, neg_div]

open scoped Matrix.Norms.L2Operator in
/-- **Complex conjugation negates the spectral angle sum** of a unitary matrix: the eigenvalues of
the conjugate matrix are the conjugates of those of `W`, with the same multiplicities, and
conjugation negates the angle offset of every point of the unit circle. -/
theorem spectralAngleSum_map_star {W : Matrix n n ℂ} (hW : W ∈ unitaryGroup n ℂ) :
    spectralAngleSum (W.map star) = -spectralAngleSum W := by
  have hroots : (W.map star).charpoly.roots = W.charpoly.roots.map (starRingEnd ℂ) := by
    rw [map_star_eq_map_starRingEnd, charpoly_map]
    exact ((charpoly_monic W).roots_map_of_card_eq_natDegree _
      IsAlgClosed.card_roots_eq_natDegree).symm
  rw [spectralAngleSum, spectralAngleSum, hroots, Multiset.map_map, ← Multiset.sum_map_neg]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun z hz ↦ ?_)
  exact angleOffset_conj (spectrum.norm_eq_one_of_unitary hW
    (mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots hz)))

/-- Away from `1`, on the unit circle, the angle offset is continuous: there `-z` lies in the slit
plane, where the argument is continuous. -/
private theorem continuousAt_angleOffset {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ContinuousAt angleOffset z := by
  refine ContinuousAt.congr (((continuousAt_arg (neg_mem_slitPlane_of_norm_eq_one hz hz1)).comp
    continuous_neg.continuousAt).div_const (2 * Real.pi)) ?_
  filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
  simp [angleOffset, hw]

/-- A product of complex numbers of modulus one is `(-1) ^ m e^{2πi s}`, where `s` is the sum of
their angle offsets and `m` the number of factors different from `1`: each factor `z ≠ 1` is
`-e^{i arg (-z)}`. -/
private theorem multiset_prod_eq_neg_one_pow_mul_exp {s : Multiset ℂ} (hs : ∀ z ∈ s, ‖z‖ = 1) :
    s.prod = (-1) ^ (Multiset.card s - s.count 1) *
      exp (↑(2 * Real.pi * (s.map angleOffset).sum) * Complex.I) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, ih fun z hz => hs z (Multiset.mem_cons_of_mem hz), Multiset.map_cons,
      Multiset.sum_cons, mul_add, ofReal_add, add_mul, exp_add, Multiset.card_cons]
    by_cases ha : a = 1
    · rw [ha, Multiset.count_cons_self]
      simp [angleOffset]
    · have h := norm_mul_exp_arg_mul_I (-a)
      rw [norm_neg, hs a (Multiset.mem_cons_self a s), ofReal_one, one_mul] at h
      rw [Multiset.count_cons_of_ne (Ne.symm ha), Nat.sub_add_comm (Multiset.count_le_card 1 s),
        pow_succ, angleOffset, ite_eq_right ha, mul_div_cancel₀ _ (by positivity), h]
      ring

open scoped Matrix.Norms.L2Operator in
/-- The determinant of a unitary matrix `W` through its spectral angle sum:
`det W = (-1) ^ (n - k) e^{2πi s(W)}`, where `k` is the multiplicity of the eigenvalue `1`.
Equivalently, `e^{2πi s(W)}` is the product of `-λ` over the eigenvalues `λ ≠ 1` of `W`, counted
with multiplicity. -/
theorem det_eq_neg_one_pow_mul_exp_spectralAngleSum {W : Matrix n n ℂ}
    (hW : W ∈ unitaryGroup n ℂ) :
    W.det = (-1) ^ (Fintype.card n - W.charpoly.rootMultiplicity 1) *
      exp (↑(2 * Real.pi * spectralAngleSum W) * Complex.I) := by
  rw [det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _), ← count_roots,
    ← charpoly_natDegree_eq_dim W, ← IsAlgClosed.card_roots_eq_natDegree, spectralAngleSum]
  exact multiset_prod_eq_neg_one_pow_mul_exp fun z hz =>
    spectrum.norm_eq_one_of_unitary hW (mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots hz))

/-- For `z` on the unit circle, `e^{-πi o(z)} (1 - z)` is a nonnegative real number, where `o` is
the angle offset: writing `-z = e^{iα}` with `-π < α ≤ π`, it is `e^{-iα/2} (1 + e^{iα}) =
2 cos (α / 2)`. -/
private theorem exp_angleOffset_mul_one_sub_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ exp (-(↑(Real.pi * angleOffset z) * Complex.I)) * (1 - z) := by
  by_cases h1 : z = 1
  · simp [h1]
  have hz' : z = -exp (↑(arg (-z)) * Complex.I) := by
    have h := norm_mul_exp_arg_mul_I (-z)
    rw [norm_neg, hz, ofReal_one, one_mul] at h
    rw [h, neg_neg]
  have hπ : Real.pi * angleOffset z = arg (-z) / 2 := by
    rw [angleOffset, ite_eq_right h1]
    field_simp
  have key : exp (-(↑(arg (-z) / 2) * Complex.I)) * (1 + exp (↑(arg (-z)) * Complex.I)) =
      ↑(2 * Real.cos (arg (-z) / 2)) := by
    rw [mul_add, mul_one, ← exp_add, ofReal_mul, ofReal_cos, ofReal_ofNat, two_cos, add_comm]
    congr 2 <;> push_cast <;> ring
  rw [hπ]
  nth_rw 2 [hz']
  rw [sub_neg_eq_add, key]
  refine zero_le_real.2 (mul_nonneg zero_le_two (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩))
  · linarith [neg_pi_lt_arg (-z)]
  · linarith [arg_le_pi (-z)]

/-- The multiset form of `Matrix.exp_neg_spectralAngleSum_mul_det_one_sub_nonneg`. -/
private theorem exp_sum_angleOffset_mul_prod_one_sub_nonneg {s : Multiset ℂ}
    (hs : ∀ z ∈ s, ‖z‖ = 1) :
    0 ≤ exp (-(↑(Real.pi * (s.map angleOffset).sum) * Complex.I)) * (s.map (1 - ·)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h := mul_nonneg (exp_angleOffset_mul_one_sub_nonneg (hs a (Multiset.mem_cons_self a s)))
      (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, mul_add,
      ofReal_add, add_mul, neg_add, exp_add]
    convert h using 1
    ring

open scoped Matrix.Norms.L2Operator in
/-- For a unitary matrix `W`, the number `e^{-πi s(W)} det (1 - W)` is a nonnegative real number:
it is the product, over the eigenvalues `λ = -e^{iα} ≠ 1` of `W` with `-π < α < π`, of
`e^{-iα/2} (1 - λ) = 2 cos (α / 2)`. Thus `e^{-πi s(W)}` is a positive multiple of
`det (1 - W)⁻¹` when `1` is not an eigenvalue of `W`. -/
theorem exp_neg_spectralAngleSum_mul_det_one_sub_nonneg {W : Matrix n n ℂ}
    (hW : W ∈ unitaryGroup n ℂ) :
    0 ≤ exp (-(↑(Real.pi * spectralAngleSum W) * Complex.I)) * (1 - W).det := by
  rw [← diagonal_one, ← scalar_apply, ← eval_charpoly,
    (IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (charpoly_monic W), spectralAngleSum]
  exact exp_sum_angleOffset_mul_prod_one_sub_nonneg fun z hz =>
    spectrum.norm_eq_one_of_unitary hW (mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots hz))

open scoped Matrix.Norms.L2Operator in
/-- The spectral angle sum is continuous at a unitary matrix `W x₀` along a continuous family of
matrices `W x` in which the multiplicity of the eigenvalue `1` is locally constant. Without that
hypothesis it jumps by an integer whenever an eigenvalue passes through `1`. -/
theorem continuousAt_spectralAngleSum {X : Type*} [TopologicalSpace X] {W : X → Matrix n n ℂ}
    {x₀ : X} (hW : ContinuousAt W x₀) (hu : W x₀ ∈ unitaryGroup n ℂ)
    (h1 : ∀ᶠ x in 𝓝 x₀, (W x).charpoly.rootMultiplicity 1 = (W x₀).charpoly.rootMultiplicity 1) :
    ContinuousAt (fun x => spectralAngleSum (W x)) x₀ :=
  continuousAt_sum_map_roots (d := Fintype.card n)
    (fun i _ => (continuous_charpoly_coeff i).continuousAt.comp hW)
    (Eventually.of_forall fun x => charpoly_degree_eq_dim (W x))
    (fun _ hz hz1 => continuousAt_angleOffset (spectrum.norm_eq_one_of_unitary hu
      (mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots hz))) hz1) h1

namespace UnitaryGroup

variable {α : Type*} [CommRing α] [StarRing α]

/-- The **Souriau map** `U ↦ U Uᵀ` of a unitary matrix. It depends only on the Lagrangian
subspace `U ℝⁿ` framed by `U`. -/
def souriau (U : unitaryGroup n α) : unitaryGroup n α :=
  U * transpose U

@[simp]
theorem coe_souriau (U : unitaryGroup n α) :
    (souriau U : Matrix n n α) = (U : Matrix n n α) * (U : Matrix n n α)ᵀ :=
  (rfl)

/-- The Souriau map is continuous. -/
theorem continuous_souriau [TopologicalSpace α] [IsTopologicalRing α] :
    Continuous (souriau : unitaryGroup n α → unitaryGroup n α) :=
  Continuous.subtype_mk (continuous_subtypeVal.matrix_mul continuous_subtypeVal.matrix_transpose)
    _

/-- Changing the frame `U` by a matrix `O` with `O Oᵀ = 1`, for instance a real orthogonal
matrix, does not change its Souriau map. -/
theorem souriau_mul_of_mul_transpose_eq_one (U O : unitaryGroup n α)
    (hO : (O : Matrix n n α) * (O : Matrix n n α)ᵀ = 1) : souriau (U * O) = souriau U := by
  refine Subtype.ext ?_
  simp only [coe_souriau, Submonoid.coe_mul, transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (O : Matrix n n α), hO, Matrix.one_mul]

/-- **The Souriau map depends only on the Lagrangian.** Two unitary frames `U` and `V` of the same
subspace `U ℝⁿ = V ℝⁿ` differ by a real orthogonal matrix, so they have the same Souriau map. -/
theorem souriau_eq_of_realImage_eq {U V : unitaryGroup n ℂ}
    (h : (U : Matrix n n ℂ).realImage = (V : Matrix n n ℂ).realImage) : souriau U = souriau V := by
  have hgram (W : unitaryGroup n ℂ) : ((W : Matrix n n ℂ)ᴴ * W).map Complex.re = 1 := by
    rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem W.property,
      Matrix.map_one _ Complex.zero_re Complex.one_re]
  obtain ⟨O, hO, hVO⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal
    (M := Unitary.toUnits U) (M' := Unitary.toUnits V) h (hgram U) (hgram V)
  have hOu := map_ofReal_mem_unitaryGroup hO
  rw [show V = U * ⟨_, hOu⟩ from Subtype.ext hVO,
    souriau_mul_of_mul_transpose_eq_one U _ (map_ofReal_mul_transpose_map_ofReal_eq_one hO)]

/-- Moving a frame by `O` conjugates its Souriau map: `(O U) (O U)ᵀ = O (U Uᵀ) Oᵀ`. -/
theorem coe_souriau_mul_left (O U : unitaryGroup n α) :
    (souriau (O * U) : Matrix n n α) = (O : Matrix n n α) * souriau U * (O : Matrix n n α)ᵀ := by
  simp [Matrix.mul_assoc, transpose_mul]

/-- The Souriau map of the complex conjugate frame is the complex conjugate of the Souriau map. -/
@[simp]
theorem souriau_map_star (U : unitaryGroup n α) : souriau (map_star U) = map_star (souriau U) := by
  refine Subtype.ext ?_
  rw [coe_souriau, map_star_coe, map_star_coe, coe_souriau, ← transpose_map]
  simp only [map_star_eq_map_starRingEnd, Matrix.map_mul]

/-- The Souriau map of a block-diagonal sum is the block-diagonal sum of the Souriau maps. -/
@[simp]
theorem souriau_sum (p : unitaryGroup n α × unitaryGroup m α) :
    souriau (sum p) = sum (souriau p.1, souriau p.2) := by
  refine Subtype.ext ?_
  simp [fromBlocks_transpose, fromBlocks_multiply]

/-- The Souriau map of a diagonal unitary matrix squares its entries. -/
theorem coe_souriau_of_coe_eq_diagonal {U : unitaryGroup n α} {d : n → α}
    (hU : (U : Matrix n n α) = diagonal d) :
    (souriau U : Matrix n n α) = diagonal fun i => d i ^ 2 := by
  rw [coe_souriau, hU, diagonal_transpose, diagonal_mul_diagonal]
  simp [sq]

/-- The determinant of the Souriau map is the square of the determinant. -/
@[simp]
theorem detCircle_souriau (U : unitaryGroup n ℂ) : detCircle (souriau U) = detCircle U ^ 2 := by
  refine Circle.ext ?_
  rw [coe_detCircle, coe_souriau, det_mul, det_transpose, Circle.coe_pow, coe_detCircle, sq]

/-- The determinant of `1 - U Uᵀ` for a unitary `U`: since `U Uᴴ = 1`, it factors as
`1 - U Uᵀ = U (conj U - U)ᵀ`. Over `ℂ`, `conj U - U = -2i Im U`, so `1` is an eigenvalue of the
Souriau map exactly when the imaginary part of the frame is singular. -/
theorem det_one_sub_souriau (U : unitaryGroup n α) :
    (1 - (souriau U : Matrix n n α)).det =
      (U : Matrix n n α).det * ((U : Matrix n n α).map star - (U : Matrix n n α)).det := by
  have h : (1 : Matrix n n α) - (U : Matrix n n α) * (U : Matrix n n α)ᵀ =
      (U : Matrix n n α) * ((U : Matrix n n α).map star - (U : Matrix n n α))ᵀ := by
    rw [transpose_sub, Matrix.mul_sub, ← transpose_map, ← conjTranspose, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.1 U.property]
  rw [coe_souriau, h, det_mul, det_transpose]

/-- The path of determinants `t ↦ det (γ t γ tᵀ) = det (γ t) ^ 2` of the Souriau maps along a
path `γ` of frames: the Maslov phases of the Lagrangians `γ t ℝⁿ` relative to `ℝⁿ`. -/
noncomputable def detSouriauPath {U V : unitaryGroup n ℂ} (γ : Path U V) :
    Path (detCircle (souriau U)) (detCircle (souriau V)) :=
  γ.map (continuous_detCircle.comp continuous_souriau)

@[simp]
theorem detSouriauPath_apply {U V : unitaryGroup n ℂ} (γ : Path U V) (t : I) :
    detSouriauPath γ t = detCircle (souriau (γ t)) :=
  (rfl)

/-- The **Maslov index** of a path `γ` of unitary frames, relative to `ℝⁿ`: Souriau's spectral
formula `angleChange (det ∘ W ∘ γ) / (2π) - (s(W V) - s(W U))` for the Robbin–Salamon index of the
path of Lagrangians `γ t ℝⁿ`, with `W` the Souriau map and `s` the spectral angle sum. -/
noncomputable def maslovIndex {U V : unitaryGroup n ℂ} (γ : Path U V) : ℝ :=
  Circle.angleChange (detSouriauPath γ) / (2 * Real.pi) -
    (spectralAngleSum (souriau V : Matrix n n ℂ) - spectralAngleSum (souriau U : Matrix n n ℂ))

/-- Souriau's spectral formula for the Maslov index of a path of frames. -/
theorem maslovIndex_def {U V : unitaryGroup n ℂ} (γ : Path U V) :
    maslovIndex γ = Circle.angleChange (detSouriauPath γ) / (2 * Real.pi) -
      (spectralAngleSum (souriau V : Matrix n n ℂ) - spectralAngleSum (souriau U : Matrix n n ℂ)) :=
  (rfl)

/-- **Independence of the frames.** Two paths of frames with the same Souriau maps, that is,
framing the same path of Lagrangians, have the same Maslov index. -/
theorem maslovIndex_eq_of_souriau_eq {U V U' V' : unitaryGroup n ℂ} (γ : Path U V)
    (γ' : Path U' V') (h : ∀ t, souriau (γ t) = souriau (γ' t)) :
    maslovIndex γ = maslovIndex γ' := by
  have h0 : souriau U = souriau U' := by simpa using h 0
  have h1 : souriau V = souriau V' := by simpa using h 1
  rw [maslovIndex, maslovIndex,
    Circle.angleChange_congr (detSouriauPath γ) (detSouriauPath γ') fun t => by simp [h t], h0, h1]

/-- **The Maslov index modulo `2` from the endpoints.** Along a path `γ` of frames from `U` to `V`,
`e^{πi μ(γ)}` is the quotient of the endpoint values of `U ↦ det U e^{-πi s(U Uᵀ)}`. Indeed
`t ↦ det (γ t)` is a continuous square root of the determinants `det (γ t γ tᵀ)` whose angle
change enters the index. Unlike `μ(γ)` itself, this depends only on the endpoints of the path of
frames, but on the frames, not only on the Lagrangians they span. -/
theorem exp_maslovIndex_mul_det_mul_exp_spectralAngleSum {U V : unitaryGroup n ℂ}
    (γ : Path U V) :
    exp (↑(Real.pi * maslovIndex γ) * Complex.I) * ((U : Matrix n n ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum (souriau U : Matrix n n ℂ)) * Complex.I))) =
      (V : Matrix n n ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum (souriau V : Matrix n n ℂ)) * Complex.I)) := by
  set δ := γ.map continuous_detCircle
  set sU := spectralAngleSum (souriau U : Matrix n n ℂ) with hsU
  set sV := spectralAngleSum (souriau V : Matrix n n ℂ) with hsV
  have hδ : Circle.angleChange (detSouriauPath γ) = 2 * Circle.angleChange δ := by
    rw [Circle.angleChange_congr (detSouriauPath γ) (δ.mul δ) fun t => by
      simp [δ, detCircle_souriau, sq], Circle.angleChange_mul, two_mul]
  -- The angle change of `t ↦ det (γ t)` is an angle of `det V / det U`.
  have hexp : exp (↑(Circle.angleChange δ) * Complex.I) * (U : Matrix n n ℂ).det =
      (V : Matrix n n ℂ).det := by
    have h := congrArg ((↑) : Circle → ℂ) (Circle.exp_angleChange δ)
    rw [Circle.coe_exp, Circle.coe_div, coe_detCircle, coe_detCircle] at h
    rw [h, div_mul_cancel₀ _ (UnitaryGroup.det_isUnit U).ne_zero]
  have hμ : Real.pi * maslovIndex γ = Circle.angleChange δ - Real.pi * (sV - sU) := by
    rw [maslovIndex, hδ, ← hsU, ← hsV]
    field_simp
  -- Both sides are `det U` times one exponential, whose exponents agree by `hμ`.
  rw [← hexp, hμ]
  simp only [mul_assoc, mul_left_comm _ (U : Matrix n n ℂ).det, ← exp_add]
  congr 2
  push_cast
  ring

/-- **Homotopy invariance.** Paths of frames that are homotopic relative to their endpoints have
the same Maslov index. -/
theorem maslovIndex_eq_of_homotopic {U V : unitaryGroup n ℂ} {γ₀ γ₁ : Path U V}
    (h : γ₀.Homotopic γ₁) : maslovIndex γ₀ = maslovIndex γ₁ := by
  rw [maslovIndex, maslovIndex, detSouriauPath, detSouriauPath, Circle.angleChange_eq_of_homotopic
    (h.map ⟨_, continuous_detCircle.comp continuous_souriau⟩)]

/-- The constant path has Maslov index zero. -/
@[simp]
theorem maslovIndex_refl (U : unitaryGroup n ℂ) : maslovIndex (Path.refl U) = 0 := by
  rw [maslovIndex, Circle.angleChange_congr (detSouriauPath (Path.refl U))
      (Path.refl (detCircle (souriau U))) fun _ => by simp,
    Circle.angleChange_refl]
  ring

/-- **Catenation.** The Maslov index of a concatenation of paths is the sum of their indices. -/
@[simp]
theorem maslovIndex_trans {U V W : unitaryGroup n ℂ} (γ₁ : Path U V) (γ₂ : Path V W) :
    maslovIndex (γ₁.trans γ₂) = maslovIndex γ₁ + maslovIndex γ₂ := by
  rw [maslovIndex, maslovIndex, maslovIndex, Circle.angleChange_congr (detSouriauPath (γ₁.trans γ₂))
    ((detSouriauPath γ₁).trans (detSouriauPath γ₂)) fun t => by
      simp only [detSouriauPath, ← Path.map_trans], Circle.angleChange_trans]
  ring

/-- Reversing a path negates its Maslov index. -/
@[simp]
theorem maslovIndex_symm {U V : unitaryGroup n ℂ} (γ : Path U V) :
    maslovIndex γ.symm = -maslovIndex γ := by
  rw [maslovIndex, maslovIndex,
    Circle.angleChange_congr (detSouriauPath γ.symm) (detSouriauPath γ).symm fun t => by
      simp only [detSouriauPath, Path.map_symm],
    Circle.angleChange_symm]
  ring

/-- **The direct-sum axiom.** The block-diagonal sum of two paths of frames has the sum of their
Maslov indices. -/
theorem maslovIndex_sum {U V : unitaryGroup n ℂ} {U' V' : unitaryGroup m ℂ} (γ₁ : Path U V)
    (γ₂ : Path U' V') :
    maslovIndex ((γ₁.prod γ₂).map continuous_sum) = maslovIndex γ₁ + maslovIndex γ₂ := by
  have hpath : Circle.angleChange (detSouriauPath ((γ₁.prod γ₂).map continuous_sum)) =
      Circle.angleChange ((detSouriauPath γ₁).mul (detSouriauPath γ₂)) :=
    Circle.angleChange_congr _ _ fun t => by simp
  rw [maslovIndex, hpath, Circle.angleChange_mul, maslovIndex, maslovIndex]
  simp only [souriau_sum, coe_sum, spectralAngleSum_fromBlocks_zero₂₁]
  ring

/-- **The direct-sum axiom for symplectic direct sums.** A path of frames that is pointwise the
symplectic direct sum `Matrix.symplecticSum` of two paths of frames, the block-diagonal sum read in
the coordinates `(n ⊕ m) ⊕ (n ⊕ m)`, has the sum of their Maslov indices. -/
theorem maslovIndex_eq_add_of_coe_eq_symplecticSum {U V : unitaryGroup (n ⊕ n) ℂ}
    {U' V' : unitaryGroup (m ⊕ m) ℂ} {W W' : unitaryGroup ((n ⊕ m) ⊕ (n ⊕ m)) ℂ}
    (γ₁ : Path U V) (γ₂ : Path U' V') (δ : Path W W')
    (h : ∀ t, (δ t : Matrix ((n ⊕ m) ⊕ (n ⊕ m)) ((n ⊕ m) ⊕ (n ⊕ m)) ℂ) =
      symplecticSum (γ₁ t : Matrix (n ⊕ n) (n ⊕ n) ℂ) (γ₂ t : Matrix (m ⊕ m) (m ⊕ m) ℂ)) :
    maslovIndex δ = maslovIndex γ₁ + maslovIndex γ₂ := by
  have hs (t : I) : (souriau (δ t) : Matrix ((n ⊕ m) ⊕ (n ⊕ m)) ((n ⊕ m) ⊕ (n ⊕ m)) ℂ) =
      symplecticSum (souriau (γ₁ t) : Matrix (n ⊕ n) (n ⊕ n) ℂ)
        (souriau (γ₂ t) : Matrix (m ⊕ m) (m ⊕ m) ℂ) := by
    rw [coe_souriau, h t, symplecticSum_transpose, ← symplecticSum_mul, coe_souriau, coe_souriau]
  have hpath : Circle.angleChange (detSouriauPath δ) =
      Circle.angleChange ((detSouriauPath γ₁).mul (detSouriauPath γ₂)) :=
    Circle.angleChange_congr _ _ fun t => Circle.ext (by simp [h t, mul_pow])
  have h₀ := hs 0
  have h₁ := hs 1
  simp only [Path.source, Path.target] at h₀ h₁
  rw [maslovIndex, hpath, Circle.angleChange_mul, maslovIndex, maslovIndex, h₀, h₁,
    spectralAngleSum_symplecticSum, spectralAngleSum_symplecticSum]
  ring

/-- **Naturality under the real orthogonal group.** Moving a path of frames by a fixed unitary
matrix `O` with `O Oᵀ = 1`, that is, a real orthogonal matrix, which preserves `ℝⁿ`, does not
change its Maslov index: the Souriau maps are conjugated by `O`, which preserves their
determinants and spectra. -/
theorem maslovIndex_map_mul_left {U V : unitaryGroup n ℂ} (O : unitaryGroup n ℂ)
    (hO : (O : Matrix n n ℂ) * (O : Matrix n n ℂ)ᵀ = 1) (γ : Path U V) :
    maslovIndex (γ.map (continuous_const_mul O)) = maslovIndex γ := by
  have hO' : (O : Matrix n n ℂ)ᵀ * O = 1 := mul_eq_one_comm.1 hO
  have hdet (W : unitaryGroup n ℂ) : detCircle (souriau (O * W)) = detCircle (souriau W) := by
    refine Circle.ext ?_
    rw [coe_detCircle, coe_detCircle, coe_souriau_mul_left, det_mul, det_mul, mul_right_comm,
      ← det_mul, hO, det_one, one_mul]
  have hs (W : unitaryGroup n ℂ) : spectralAngleSum (souriau (O * W) : Matrix n n ℂ) =
      spectralAngleSum (souriau W : Matrix n n ℂ) := by
    rw [coe_souriau_mul_left, spectralAngleSum_conj hO hO']
  rw [maslovIndex, maslovIndex, Circle.angleChange_congr (detSouriauPath (γ.map _))
    (detSouriauPath γ) fun t => by simp [hdet], hs, hs]

/-- **Complex conjugation negates the Maslov index.** Conjugating a path of frames reflects the path
of Lagrangians `γ t ℝⁿ` by the anti-symplectic involution `z ↦ conj z` of `ℂⁿ`, which fixes `ℝⁿ`.
The Souriau maps are conjugated, which inverts their determinants and negates their spectral angle
sums. -/
@[simp]
theorem maslovIndex_map_map_star {U V : unitaryGroup n ℂ} (γ : Path U V) :
    maslovIndex (γ.map continuous_map_star) = -maslovIndex γ := by
  have hs (W : unitaryGroup n ℂ) : spectralAngleSum (souriau (map_star W) : Matrix n n ℂ) =
      -spectralAngleSum (souriau W : Matrix n n ℂ) := by
    rw [souriau_map_star, map_star_coe, spectralAngleSum_map_star (souriau W).property]
  rw [maslovIndex, maslovIndex, Circle.angleChange_congr (detSouriauPath (γ.map _))
    (detSouriauPath γ).inv fun t => by simp, Circle.angleChange_inv, hs, hs]
  ring

/-- **The loop case.** If the path of Lagrangians closes up, that is, the frames at the endpoints
have the same Souriau map, the Maslov index is the degree of the loop of determinants
`t ↦ det (γ t γ tᵀ) = det (γ t) ^ 2`, the Maslov index of the loop of Lagrangians. -/
theorem maslovIndex_eq_degree {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) :
    maslovIndex γ = Circle.degree ((detSouriauPath γ).cast rfl (congrArg detCircle h)) := by
  have hs : spectralAngleSum (souriau V : Matrix n n ℂ) =
      spectralAngleSum (souriau U : Matrix n n ℂ) := by
    rw [h]
  rw [maslovIndex, hs, sub_self, sub_zero, Circle.angleChange_congr (detSouriauPath γ)
      ((detSouriauPath γ).cast rfl (congrArg detCircle h)) fun _ => by simp,
    Circle.angleChange_eq_degree_mul]
  field_simp

/-- On a loop of frames, the Maslov index is twice the degree of the loop of determinants. -/
theorem maslovIndex_eq_two_mul_degree {U : unitaryGroup n ℂ} (γ : Path U U) :
    maslovIndex γ = 2 * Circle.degree (γ.map continuous_detCircle) := by
  rw [maslovIndex_eq_degree γ rfl, Circle.degree_congr _
      ((γ.map continuous_detCircle).map (continuous_pow 2)) fun t => by simp [detCircle_souriau],
    Circle.degree_map_pow]
  push_cast
  ring

/-- **The zero axiom.** If the eigenvalue `1` of the Souriau maps `γ t γ tᵀ` keeps the same
multiplicity `k` along a path of frames, the Maslov index of the path vanishes. For a symmetric
unitary matrix this multiplicity is the dimension of the intersection of the Lagrangian with `ℝⁿ`,
so this is the zero axiom of Robbin and Salamon, stated through the Souriau maps: a path of
Lagrangians `γ t ℝⁿ` whose intersections with `ℝⁿ` keep the same dimension has index zero. -/
theorem maslovIndex_eq_zero_of_rootMultiplicity_eq {U V : unitaryGroup n ℂ} (γ : Path U V) {k : ℕ}
    (h : ∀ t, (souriau (γ t) : Matrix n n ℂ).charpoly.rootMultiplicity 1 = k) :
    maslovIndex γ = 0 := by
  have hW : Continuous fun t => (souriau (γ t) : Matrix n n ℂ) :=
    continuous_subtypeVal.comp (continuous_souriau.comp γ.continuous)
  have hs : Continuous fun t => spectralAngleSum (souriau (γ t) : Matrix n n ℂ) :=
    continuous_iff_continuousAt.2 fun t => continuousAt_spectralAngleSum hW.continuousAt
      (souriau (γ t)).property (Eventually.of_forall fun t' => (h t').trans (h t).symm)
  -- A continuous angle `θ` of the determinants `det (W t)` of the Souriau maps and the angle
  -- `2π s(W t) + (n - k) π` are continuous lifts of the same path in the circle, so they differ
  -- by a constant and the change of `θ / (2π)` cancels the change of `s`.
  obtain ⟨θ, hθ⟩ := Circle.exists_lift (detSouriauPath γ)
  obtain ⟨m, hm⟩ := Circle.exists_int_forall_eq_add_of_exp_eq (G' := fun t =>
      2 * Real.pi * spectralAngleSum (souriau (γ t) : Matrix n n ℂ) +
        (Fintype.card n - k : ℕ) * Real.pi) θ.continuous
      ((continuous_const.mul hs).add continuous_const) fun t => by
    refine Circle.ext ?_
    rw [hθ, detSouriauPath_apply, coe_detCircle,
      det_eq_neg_one_pow_mul_exp_spectralAngleSum (souriau (γ t)).property, h t, Circle.coe_exp]
    push_cast
    have hsign : exp (((Fintype.card n - k : ℕ) : ℂ) * Real.pi * Complex.I) =
        (-1) ^ (Fintype.card n - k) := by
      rw [mul_assoc, exp_natCast_mul, exp_pi_mul_I]
    rw [add_mul, exp_add, hsign, mul_comm]
  rw [maslovIndex, Circle.angleChange_eq_sub _ θ.continuous hθ, hm 1, hm 0, γ.source, γ.target]
  field_simp
  ring

/-- **The homotopy axiom.** Let `F` be a homotopy from the path `γ₀` to the path `γ₁` of unitary
frames, with moving endpoints, such that the eigenvalue `1` of the Souriau map of `F (s, 0)` has
the same multiplicity for every `s`, and so does that of `F (s, 1)`. Then `γ₀` and `γ₁` have the
same Maslov index. -/
theorem maslovIndex_eq_of_homotopy_of_rootMultiplicity_eq {U₀ V₀ U₁ V₁ : unitaryGroup n ℂ}
    (γ₀ : Path U₀ V₀) (γ₁ : Path U₁ V₁) (F : C(I × I, unitaryGroup n ℂ))
    (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t) {k₀ k₁ : ℕ}
    (hk₀ : ∀ s, (souriau (F (s, 0)) : Matrix n n ℂ).charpoly.rootMultiplicity 1 = k₀)
    (hk₁ : ∀ s, (souriau (F (s, 1)) : Matrix n n ℂ).charpoly.rootMultiplicity 1 = k₁) :
    maslovIndex γ₀ = maslovIndex γ₁ := by
  let G : ContinuousMap.Homotopy γ₀.toContinuousMap γ₁.toContinuousMap :=
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := h₀
      map_one_left := h₁ }
  -- The edge `G.evalAt x` traces `s ↦ F (s, x)`; this holds by definition of `G` and `evalAt`.
  have hG : ∀ x s, G.evalAt x s = F (s, x) := fun _ _ ↦ rfl
  -- `γ₀` followed by the final edge is homotopic to the initial edge followed by `γ₁`, and the
  -- two edges have index zero by the zero axiom.
  have h := maslovIndex_eq_of_homotopic (Path.Homotopic.map_trans_evalAt G Path.id)
  rw [maslovIndex_trans, maslovIndex_trans,
    maslovIndex_eq_zero_of_rootMultiplicity_eq (G.evalAt 0) fun s ↦ by rw [hG]; exact hk₀ s,
    maslovIndex_eq_zero_of_rootMultiplicity_eq (G.evalAt 1) fun s ↦ by rw [hG]; exact hk₁ s,
    add_zero, zero_add] at h
  rw [maslovIndex_eq_of_souriau_eq γ₀ (Path.id.map (map_continuous γ₀.toContinuousMap))
    fun t ↦ by simp, h]
  exact maslovIndex_eq_of_souriau_eq _ _ fun t ↦ by simp

/-- A path of frames whose Souriau maps never have the eigenvalue `1`, that is, a path of
Lagrangians transverse to `ℝⁿ`, has Maslov index zero. -/
theorem maslovIndex_eq_zero_of_forall_not_isRoot {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : ∀ t, ¬(souriau (γ t) : Matrix n n ℂ).charpoly.IsRoot 1) : maslovIndex γ = 0 :=
  maslovIndex_eq_zero_of_rootMultiplicity_eq γ fun t => rootMultiplicity_eq_zero (h t)

/-- For `x = φ / π`, the difference `x - angleOffset (e^{2iφ})` is the half-integer
`(⌊x⌋ + ⌈x⌉) / 2`: it is `⌊x⌋ + 1/2` if `x` is not an integer and `x` if it is. -/
private theorem div_pi_sub_angleOffset (φ : ℝ) :
    φ / Real.pi - angleOffset (Complex.exp (↑(2 * φ) * Complex.I)) =
      ((⌊φ / Real.pi⌋ + ⌈φ / Real.pi⌉ : ℤ) : ℝ) / 2 := by
  -- If `φ / π` is an integer then `e^{2iφ} = 1` and the offset vanishes; otherwise
  -- `⌈φ / π⌉ = ⌊φ / π⌋ + 1` and the offset comes from `Complex.arg_neg_exp_of_div_pi_ne`.
  by_cases hφ : ∃ k : ℤ, φ / Real.pi = k
  · obtain ⟨k, hk⟩ := hφ
    have hexp : Complex.exp (↑(2 * φ) * Complex.I) = 1 := by
      rw [Complex.exp_eq_one_iff]
      refine ⟨k, ?_⟩
      have : φ = k * Real.pi := by field_simp at hk; linarith
      rw [this]
      push_cast
      ring
    rw [hk, Int.floor_intCast, Int.ceil_intCast]
    simp only [angleOffset, hexp, ↓reduceIte]
    push_cast
    ring
  · simp only [not_exists] at hφ
    have harg := arg_neg_exp_of_div_pi_ne hφ
    have hceil : ⌈φ / Real.pi⌉ = ⌊φ / Real.pi⌋ + 1 :=
      (Int.ceil_eq_floor_add_one_iff_notMem _).2 fun ⟨k, hk⟩ => hφ k hk.symm
    have hne : Complex.exp (↑(2 * φ) * Complex.I) ≠ 1 := fun h1 => by
      rw [h1, Complex.arg_neg_one] at harg
      refine hφ (⌊φ / Real.pi⌋ + 1) ?_
      rw [div_eq_iff Real.pi_ne_zero]
      push_cast
      linarith
    simp only [angleOffset, hne, ↓reduceIte]
    rw [harg, hceil]
    set x := φ / Real.pi with hx
    have hφx : φ = x * Real.pi := by rw [hx]; field_simp
    rw [hφx]
    push_cast
    field_simp
    ring

/-- **The diagonal case.** For a path of diagonal frames `γ t = diag (e^{i φ_j t})` with continuous
angles `φ_j`, the Maslov index is `∑ j, (c(φ_j 1) - c(φ_j 0))`, where `c(x)` is the half-integer
`(⌊x / π⌋ + ⌈x / π⌉) / 2`: each angle counts the multiples of `π` it crosses, with half weight at
the endpoints. -/
theorem maslovIndex_eq_sum_of_diagonal {U V : unitaryGroup n ℂ} (γ : Path U V) {φ : n → I → ℝ}
    (hφ : ∀ j, Continuous (φ j))
    (hγ : ∀ t, (γ t : Matrix n n ℂ) = diagonal fun j => Complex.exp (φ j t * Complex.I)) :
    maslovIndex γ = ∑ j, (((⌊φ j 1 / Real.pi⌋ + ⌈φ j 1 / Real.pi⌉ : ℤ) : ℝ) / 2 -
      ((⌊φ j 0 / Real.pi⌋ + ⌈φ j 0 / Real.pi⌉ : ℤ) : ℝ) / 2) := by
  have hW (t : I) : (souriau (γ t) : Matrix n n ℂ) =
      diagonal fun j => Complex.exp (↑(2 * φ j t) * Complex.I) := by
    rw [coe_souriau_of_coe_eq_diagonal (hγ t)]
    congr 1
    funext j
    rw [← Complex.exp_natCast_mul]
    push_cast
    ring_nf
  -- `t ↦ 2 ∑ j, φ_j t` is a continuous angle of `det (γ t γ tᵀ)`.
  have hangle : Circle.angleChange (detSouriauPath γ) =
      (2 * ∑ j, φ j 1) - 2 * ∑ j, φ j 0 := by
    refine Circle.angleChange_eq_sub _ (θ := fun t => 2 * ∑ j, φ j t)
      (continuous_const.mul (continuous_finsetSum _ fun j _ => hφ j)) fun t => Circle.ext ?_
    rw [Circle.coe_exp]
    simp only [detSouriauPath, Path.map_coe, Function.comp_apply, coe_detCircle, hW t,
      det_diagonal]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have h0 := hW 0
  have h1 := hW 1
  rw [Path.source] at h0
  rw [Path.target] at h1
  rw [maslovIndex, hangle, h0, h1, spectralAngleSum_diagonal, spectralAngleSum_diagonal]
  have hsplit : ((2 * ∑ j, φ j 1) - 2 * ∑ j, φ j 0) / (2 * Real.pi) =
      ∑ j, (φ j 1 / Real.pi - φ j 0 / Real.pi) := by
    rw [Finset.sum_sub_distrib]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    field_simp
  rw [hsplit, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← div_pi_sub_angleOffset (φ j 1), ← div_pi_sub_angleOffset (φ j 0)]
  simp only [angleOffset]
  ring

/-- **Normalization.** The half-turn `t ↦ e^{iπt} ℝⁿ`, framed by `t ↦ e^{iπt} I`, has Maslov
index `n`. -/
theorem maslovIndex_eq_card_of_halfTurn {U V : unitaryGroup n ℂ} (γ : Path U V)
    (hγ : ∀ t, (γ t : Matrix n n ℂ) = Complex.exp (↑(Real.pi * t) * Complex.I) • 1) :
    maslovIndex γ = Fintype.card n := by
  rw [maslovIndex_eq_sum_of_diagonal γ (φ := fun _ t => Real.pi * t)
    (fun _ => continuous_const.mul continuous_subtypeVal) fun t => by
      rw [hγ t, smul_one_eq_diagonal]]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp [hπ]

/-- **Localization for diagonal symmetric matrices.** The graph `{x + i A x}` of the diagonal
symmetric matrix `A t = diag (a_j t)` is framed by `diag (e^{i arctan (a_j t)})`. Along a path of
such graphs, the Maslov index relative to `ℝⁿ` is half the change of the signature of `A`,
`∑ j, (sign (a_j 1) - sign (a_j 0)) / 2`. -/
theorem maslovIndex_eq_sum_sign_of_diagonal_arctan {U V : unitaryGroup n ℂ} (γ : Path U V)
    {a : n → I → ℝ} (ha : ∀ j, Continuous (a j))
    (hγ : ∀ t, (γ t : Matrix n n ℂ) =
      diagonal fun j => Complex.exp (Real.arctan (a j t) * Complex.I)) :
    maslovIndex γ = ∑ j, (Real.sign (a j 1) - Real.sign (a j 0)) / 2 := by
  rw [maslovIndex_eq_sum_of_diagonal γ (fun j => Real.continuous_arctan.comp (ha j)) hγ]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- Since `|arctan a| < π / 2`, the half-integer count of `arctan a` is `sign a / 2`.
  have key (b : ℝ) : ((⌊Real.arctan b / Real.pi⌋ + ⌈Real.arctan b / Real.pi⌉ : ℤ) : ℝ) / 2 =
      Real.sign b / 2 := by
    rw [TauCeti.floor_add_ceil_div_eq_sign_of_abs_lt (abs_lt.2
      ⟨by linarith [Real.neg_pi_div_two_lt_arctan b, Real.pi_pos],
        by linarith [Real.arctan_lt_pi_div_two b, Real.pi_pos]⟩)]
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [Real.sign_of_neg hb, Real.sign_of_neg (Real.arctan_lt_zero.2 hb)]
    · simp
    · rw [Real.sign_of_pos hb, Real.sign_of_pos (Real.arctan_pos.2 hb)]
  simp only [Function.comp_apply]
  rw [key, key]
  ring

end UnitaryGroup

end Matrix
