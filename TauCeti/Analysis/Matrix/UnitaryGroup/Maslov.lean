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
public import TauCeti.Topology.Circle.Degree

/-!
# The Maslov index of a path of Lagrangian frames

A unitary matrix `U ∈ U(n)` is a frame of the Lagrangian subspace `Λ = U ℝⁿ` of `ℂⁿ`, for the
standard symplectic form `Im ⟪·, ·⟫`. Two frames of the same Lagrangian differ by a real orthogonal
matrix, so the **Souriau map** `W = U Uᵀ` (`Matrix.UnitaryGroup.souriau`) depends only on `Λ`
(`Matrix.UnitaryGroup.souriau_mul_of_mul_transpose_eq_one`). It is a symmetric unitary matrix,
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
* it is additive under direct sums (`Matrix.UnitaryGroup.maslovIndex_sum`);
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

The zero axiom of Robbin and Salamon, that the index vanishes on a path along which the dimension
of `U t ℝⁿ ∩ ℝⁿ` is constant, and the localization axiom for nondiagonal `A` are not proved here,
nor is the comparison with the definition of the index by crossing forms.

## Main declarations

* `Matrix.spectralAngleSum`: the sum of `arg (-λ) / (2π)` over the eigenvalues `λ ≠ 1`.
* `Matrix.UnitaryGroup.souriau`: the Souriau map `U ↦ U Uᵀ`.
* `Matrix.UnitaryGroup.maslovIndex`: the Maslov index of a path of Lagrangian frames.

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

open Complex Polynomial
open scoped unitInterval

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
  Continuous.subtype_mk (continuous_subtype_val.matrix_mul continuous_subtype_val.matrix_transpose)
    _

/-- Changing the frame `U` by a matrix `O` with `O Oᵀ = 1`, for instance a real orthogonal
matrix, does not change its Souriau map. -/
theorem souriau_mul_of_mul_transpose_eq_one (U O : unitaryGroup n α)
    (hO : (O : Matrix n n α) * (O : Matrix n n α)ᵀ = 1) : souriau (U * O) = souriau U := by
  refine Subtype.ext ?_
  simp only [coe_souriau, Submonoid.coe_mul, transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (O : Matrix n n α), hO, Matrix.one_mul]

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

/-- **Independence of the frames.** Two paths of frames with the same Souriau maps, that is,
framing the same path of Lagrangians, have the same Maslov index. -/
theorem maslovIndex_eq_of_souriau_eq {U V U' V' : unitaryGroup n ℂ} (γ : Path U V)
    (γ' : Path U' V') (h : ∀ t, souriau (γ t) = souriau (γ' t)) :
    maslovIndex γ = maslovIndex γ' := by
  have h0 : souriau U = souriau U' := by simpa using h 0
  have h1 : souriau V = souriau V' := by simpa using h 1
  rw [maslovIndex, maslovIndex,
    Circle.angleChange_congr (detSouriauPath γ) (detSouriauPath γ') fun t => by simp [h t], h0, h1]

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
    rw [← Complex.exp_nat_mul]
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
    (fun _ => continuous_const.mul continuous_subtype_val) fun t => by
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
    have hlo : -1 / 2 < Real.arctan b / Real.pi := by
      rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.neg_pi_div_two_lt_arctan b]
    have hhi : Real.arctan b / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ Real.pi_pos]; linarith [Real.arctan_lt_pi_div_two b]
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · have hneg : Real.arctan b / Real.pi < 0 :=
        div_neg_of_neg_of_pos (Real.arctan_lt_zero.2 hb) Real.pi_pos
      rw [(Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
        (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
        Real.sign_of_neg hb]
      norm_num
    · simp
    · have hpos : 0 < Real.arctan b / Real.pi :=
        div_pos (Real.arctan_pos.2 hb) Real.pi_pos
      rw [(Int.floor_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
        (Int.ceil_eq_iff (z := 1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
        Real.sign_of_pos hb]
      norm_num
  simp only [Function.comp_apply]
  rw [key, key]
  ring

end UnitaryGroup

end Matrix
