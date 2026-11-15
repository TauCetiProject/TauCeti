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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Topology.Instances.Matrix

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

The index is natural under the real orthogonal group, which preserves `ℝⁿ`: moving a path of
frames by a fixed real orthogonal matrix does not change it
(`Matrix.UnitaryGroup.maslovIndex_map_mul_left`). The localization axiom for nondiagonal `A` is
deduced from the diagonal case in `TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization`.
For paths of graphs, the comparison with the definition of the index by crossing forms is in
`TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing`.

**The zero axiom.** Robbin and Salamon's zero axiom says that the index vanishes on a path along
which the dimension of `U t ℝⁿ ∩ ℝⁿ` is constant, that is, along which nothing crosses `ℝⁿ`. In
the spectral picture, the crossings are the passages of eigenvalues of `W t` through `1`. We prove
the axiom in this form: if the eigenvalue `1` of the Souriau maps `W t` keeps its algebraic
multiplicity `k` along the path, the index vanishes
(`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_forall_count_eq`). Two facts combine.

* The eigenvalues of `W t` move continuously, matched with multiplicity. Those near the eigenvalue
  `1` of `W t₀` are equal to `1` by the constancy of `k`, and the others stay away from `1`, where
  `arg (-λ)` is continuous, so `t ↦ s(W t)` is continuous (`Matrix.continuousAt_spectralAngleSum`).
* For a unitary `W` of size `n`, `det W = (-1) ^ (n - k) e^{2πi s(W)}`
  (`Matrix.UnitaryGroup.det_eq_neg_one_pow_mul_exp_spectralAngleSum`), because an eigenvalue
  `λ ≠ 1` on the unit circle has `e^{i arg (-λ)} = -λ`.

So `2π s(W t) + π (n - k)` is a continuous angle of `det (W t)`, and the angle it sweeps is
`2π (s(W 1) - s(W 0))`, which the spectral terms of the index cancel. The identification of the
algebraic multiplicity of the eigenvalue `1` of `W` with the dimension of `U ℝⁿ ∩ ℝⁿ` is not
proved here.

## Main declarations

* `Matrix.spectralAngleSum`: the sum of `arg (-λ) / (2π)` over the eigenvalues `λ ≠ 1`.
* `Matrix.continuousAt_spectralAngleSum`: it is continuous along families of matrices in which no
  eigenvalue reaches `1` or leaves it.
* `Matrix.UnitaryGroup.souriau`: the Souriau map `U ↦ U Uᵀ`.
* `Matrix.UnitaryGroup.maslovIndex`: the Maslov index of a path of Lagrangian frames.
* `Matrix.UnitaryGroup.norm_eq_one_of_mem_roots_charpoly`: the eigenvalues of a unitary matrix lie
  on the unit circle.
* `Matrix.UnitaryGroup.det_eq_neg_one_pow_mul_exp_spectralAngleSum`: the determinant of a unitary
  matrix through its spectral angle sum.
* `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_forall_count_eq`: the zero axiom.

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

/-- The spectral angle sum is invariant under conjugation by an invertible matrix `P` with
inverse `Q`. -/
theorem spectralAngleSum_conj {P Q : Matrix n n ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (W : Matrix n n ℂ) : spectralAngleSum (P * W * Q) = spectralAngleSum W := by
  have h := charpoly_units_conj (⟨P, Q, hPQ, hQP⟩ : (Matrix n n ℂ)ˣ) W
  rw [Units.val_mk, inv_eq_left_inv hQP] at h
  rw [spectralAngleSum, spectralAngleSum, h]

/-- Away from `1`, the offset `arg (-z) / (2π)` is continuous at every `z` with `-z` in the slit
plane, for instance at every point of the unit circle other than `1`. -/
private theorem continuousAt_angleOffset {z : ℂ} (hz : z ≠ 1) (hz' : -z ∈ slitPlane) :
    ContinuousAt angleOffset z := by
  have h : (fun w : ℂ => arg (-w) / (2 * Real.pi)) =ᶠ[nhds z] angleOffset := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [angleOffset, hw]
  exact (((continuousAt_arg hz').comp continuous_neg.continuousAt).div_const _).congr h

/-- If `b` takes the value `c` as often as `a` does, and `b i = c` forces `a i = c`, then `a` and
`b` take the value `c` at the same indices. -/
private theorem eq_of_count_map_eq {ι α : Type*} [Fintype ι] [DecidableEq α] {a b : ι → α} {c : α}
    (hcount : ((Finset.univ : Finset ι).val.map b).count c =
      ((Finset.univ : Finset ι).val.map a).count c)
    (hba : ∀ i, b i = c → a i = c) (i : ι) (hai : a i = c) : b i = c := by
  classical
  have hcard : (Finset.univ.filter fun i => a i = c) = Finset.univ.filter fun i => b i = c := by
    refine (Finset.eq_of_subset_of_card_le (fun i => by simpa using hba i) ?_).symm
    rw [Multiset.count_map, Multiset.count_map] at hcount
    simp only [eq_comm (a := c)] at hcount
    exact hcount.ge
  have : i ∈ Finset.univ.filter fun i => b i = c := hcard ▸ by simpa using hai
  simpa using this

/-- **Continuity of the spectral angle sum.** Let `A x` be square complex matrices depending
continuously on `x` at `x₀`, such that no eigenvalue `λ ≠ 1` of `A x₀` is a nonnegative real number,
and such that near `x₀` the algebraic multiplicity of the eigenvalue `1` of `A x` is that of `A x₀`.
Then the spectral angle sum of `A x` is continuous at `x₀`.

The eigenvalues of `A x` stay close to those of `A x₀`, matched with multiplicity. Those near the
eigenvalue `1` of `A x₀` are all equal to `1`, by the constancy of its multiplicity, and contribute
nothing, while the others stay away from `[0, ∞)`, where `arg (-λ)` is continuous. -/
theorem continuousAt_spectralAngleSum {X : Type*} [TopologicalSpace X] {A : X → Matrix n n ℂ}
    {x₀ : X} (hA : ContinuousAt A x₀)
    (hroots : ∀ z ∈ (A x₀).charpoly.roots, z ≠ 1 → -z ∈ slitPlane)
    (hcount : ∀ᶠ x in nhds x₀,
      (A x).charpoly.roots.count 1 = (A x₀).charpoly.roots.count 1) :
    ContinuousAt (fun x => spectralAngleSum (A x)) x₀ := by
  classical
  rw [Metric.continuousAt_iff']
  intro ε hε
  set d := Fintype.card n
  have hε' : 0 < ε / (d + 1) := by positivity
  -- A radius `δ` within which the eigenvalues `≠ 1` of `A x₀` keep their offsets
  -- `ε / (d + 1)`-close and do not move to `1`.
  have hgood : ∀ z ∈ (A x₀).charpoly.roots.toFinset, ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      z ≠ 1 → ∀ w, dist w z < δ → w ≠ 1 ∧ dist (angleOffset w) (angleOffset z) < ε / (d + 1) := by
    intro z hz
    by_cases h1 : z = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 ((eventually_ne_nhds h1).and
      (Metric.continuousAt_iff'.1
        (continuousAt_angleOffset h1 (hroots z (Multiset.mem_toFinset.1 hz) h1)) _ hε'))
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ _ w hw
    exact hball (hw.trans hδ.2)
  obtain ⟨δ, hδ, hδpos⟩ :=
    ((Filter.eventually_all_finset _).2 hgood |>.and self_mem_nhdsWithin).exists
  have hF : ∀ i ≤ d, ContinuousAt (fun x => (A x).charpoly.coeff i) x₀ := fun i _ =>
    (continuous_charpoly_coeff i).continuousAt.comp hA
  have hdeg : ∀ᶠ x in nhds x₀, (A x).charpoly.degree = d :=
    Filter.Eventually.of_forall fun x => charpoly_degree_eq_dim (A x)
  filter_upwards [Polynomial.eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg
    (Set.mem_Ioi.1 hδpos), hcount] with x ⟨a, b, ha, hb, hab⟩ hx
  have hra : (A x₀).charpoly.roots = (Finset.univ : Finset (Fin d)).val.map a :=
    Polynomial.roots_eq_map_of_eq_C_mul_prod_X_sub_C (charpoly_monic _).ne_zero ha
  have hrb : (A x).charpoly.roots = (Finset.univ : Finset (Fin d)).val.map b :=
    Polynomial.roots_eq_map_of_eq_C_mul_prod_X_sub_C (charpoly_monic _).ne_zero hb
  -- An index with `b i = 1` has `a i = 1`; as both values occur equally often, conversely.
  have hba : ∀ i, b i = 1 → a i = 1 := fun i hbi => by
    by_contra hai
    exact (hδ (a i) (by simp [hra]) hai (b i) (by rw [dist_eq_norm, norm_sub_rev]; exact hab i)).1
      hbi
  have hab' := eq_of_count_map_eq (by rwa [← hra, ← hrb]) hba
  rw [spectralAngleSum, spectralAngleSum, hra, hrb, Multiset.map_map, Multiset.map_map,
    ← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum]
  calc dist (∑ i, (angleOffset ∘ b) i) (∑ i, (angleOffset ∘ a) i)
      ≤ ∑ i : Fin d, dist ((angleOffset ∘ b) i) ((angleOffset ∘ a) i) := dist_sum_sum_le _ _ _
    _ ≤ ∑ _i : Fin d, ε / (d + 1) := Finset.sum_le_sum fun i _ => by
        by_cases hai : a i = 1
        · simp [Function.comp_apply, hai, hab' i hai, hε'.le]
        · exact (hδ (a i) (by simp [hra]) hai (b i)
            (by rw [dist_eq_norm, norm_sub_rev]; exact hab i)).2.le
    _ < ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc',
          div_lt_iff₀ (by positivity)]
        nlinarith

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

/-- Moving a frame by `O` conjugates its Souriau map: `(O U) (O U)ᵀ = O (U Uᵀ) Oᵀ`. -/
theorem coe_souriau_mul_left (O U : unitaryGroup n α) :
    (souriau (O * U) : Matrix n n α) = (O : Matrix n n α) * souriau U * (O : Matrix n n α)ᵀ := by
  simp [Matrix.mul_assoc, transpose_mul]

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

/-! ### The zero axiom -/

/-- The eigenvalues of a unitary matrix, with multiplicity, are the diagonal entries of a diagonal
unitary matrix conjugate to it. -/
private theorem exists_roots_charpoly_eq_map (W : unitaryGroup n ℂ) :
    ∃ z : n → Circle, (W : Matrix n n ℂ).charpoly.roots =
      (Finset.univ : Finset n).val.map fun i => (z i : ℂ) := by
  obtain ⟨z, hz⟩ := TauCeti.exists_isConj_unitaryTorusHom W
  obtain ⟨c, hc⟩ := isConj_iff.1 hz
  refine ⟨z, ?_⟩
  have hcc : (c : Matrix n n ℂ) * (c⁻¹ : unitaryGroup n ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel c)
  have hcc' : ((c⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) * c = 1 :=
    congrArg Subtype.val (inv_mul_cancel c)
  have h := charpoly_units_conj (⟨c, (c⁻¹ : unitaryGroup n ℂ), hcc, hcc'⟩ : (Matrix n n ℂ)ˣ) W
  rw [Units.val_mk, inv_eq_left_inv hcc'] at h
  have hD : (c : Matrix n n ℂ) * W * ((c⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) =
      diagonal fun i => (z i : ℂ) := by
    rw [← TauCeti.coe_unitaryTorusHom, ← hc]
    rfl
  rw [← h, hD, charpoly_diagonal]
  exact Polynomial.roots_eq_map_of_eq_C_mul_prod_X_sub_C
    (Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _).ne_zero
    (by rw [(Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _).leadingCoeff,
      Polynomial.C_1, one_mul])

open scoped Matrix.Norms.L2Operator in
/-- The eigenvalues of a unitary matrix lie on the unit circle: this is
`Unitary.spectrum_subset_circle` for the `C⋆`-algebra of matrices with the `ℓ²` operator norm. -/
theorem norm_eq_one_of_mem_roots_charpoly (W : unitaryGroup n ℂ) {z : ℂ}
    (hz : z ∈ (W : Matrix n n ℂ).charpoly.roots) : ‖z‖ = 1 :=
  mem_sphere_zero_iff_norm.1 <| Unitary.spectrum_subset_circle W <|
    mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hz)

/-- A point `z ≠ 1` of the unit circle is not a nonnegative real number, so `-z` lies in the slit
plane. -/
private theorem neg_mem_slitPlane_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    -z ∈ slitPlane := by
  rw [mem_slitPlane_iff, neg_re, neg_im, neg_pos, ne_eq, neg_eq_zero]
  by_contra! h
  refine h1 (Complex.ext ?_ (by simpa using h.2))
  have hre : ‖z‖ = |z.re| := by rw [← Complex.re_add_im z, h.2]; simp
  rw [hz, abs_of_nonneg h.1] at hre
  simpa using hre.symm

/-- **The determinant through the spectral angle sum.** A unitary matrix `W` of size `n` whose
eigenvalue `1` has algebraic multiplicity `k` satisfies `det W = (-1) ^ (n - k) e^{2πi s(W)}`:
each eigenvalue `λ ≠ 1` contributes `e^{i arg (-λ)} = -λ` to the exponential, and the eigenvalue
`1` contributes `1` to both sides. So for an angle `θ` of `det W`, the class of `θ / (2π) - s(W)`
modulo one only depends on `n - k`. -/
theorem det_eq_neg_one_pow_mul_exp_spectralAngleSum (W : unitaryGroup n ℂ) :
    (W : Matrix n n ℂ).det =
      (-1) ^ (Fintype.card n - (W : Matrix n n ℂ).charpoly.roots.count 1) *
        Complex.exp (↑(2 * Real.pi * spectralAngleSum (W : Matrix n n ℂ)) * Complex.I) := by
  classical
  obtain ⟨z, hz⟩ := exists_roots_charpoly_eq_map W
  have hcount : (W : Matrix n n ℂ).charpoly.roots.count 1 =
      (Finset.univ.filter fun i => (z i : ℂ) = 1).card := by
    rw [hz, Multiset.count_map]
    simp only [eq_comm (a := (1 : ℂ))]
    rfl
  have hterm (i : n) : Complex.exp (↑(2 * Real.pi * angleOffset (z i)) * Complex.I) =
      if (z i : ℂ) = 1 then 1 else -(z i : ℂ) := by
    split_ifs with h
    · simp [angleOffset, h]
    · have he := norm_mul_exp_arg_mul_I (-(z i : ℂ))
      have hn : ‖-(z i : ℂ)‖ = 1 := by simp
      rw [hn, Complex.ofReal_one, one_mul] at he
      rw [← he]
      simp only [angleOffset, h, ↓reduceIte]
      congr 2
      push_cast
      field_simp
  have hexp : Complex.exp (↑(2 * Real.pi * spectralAngleSum (W : Matrix n n ℂ)) * Complex.I) =
      ∏ i ∈ Finset.univ.filter fun i => (z i : ℂ) ≠ 1, -(z i : ℂ) := by
    rw [spectralAngleSum, hz, Multiset.map_map, ← Finset.sum_eq_multiset_sum, Finset.mul_sum,
      Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    simp only [Function.comp_apply, hterm, Finset.prod_ite, Finset.prod_const_one, one_mul]
  have hdet : (W : Matrix n n ℂ).det =
      ∏ i ∈ Finset.univ.filter fun i => (z i : ℂ) ≠ 1, (z i : ℂ) := by
    rw [det_eq_prod_roots_charpoly, hz, ← Finset.prod_eq_multiset_prod,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ fun i => (z i : ℂ) = 1,
      Finset.prod_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.prod_const_one, one_mul]
  have hcard : Fintype.card n - (Finset.univ.filter fun i => (z i : ℂ) = 1).card =
      (Finset.univ.filter fun i => (z i : ℂ) ≠ 1).card := by
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (s := Finset.univ) fun i => (z i : ℂ) = 1, Nat.add_sub_cancel_left]
  rw [hexp, hdet, hcount, hcard, Finset.prod_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]

/-- **The zero axiom of Robbin and Salamon.** A path of frames along which the eigenvalue `1` of the
Souriau maps `γ t γ tᵀ` keeps its algebraic multiplicity has Maslov index zero: no eigenvalue of
`γ t γ tᵀ` crosses `1`, so the path of Lagrangians `γ t ℝⁿ` has no crossing with `ℝⁿ`. -/
theorem maslovIndex_eq_zero_of_forall_count_eq {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : ∀ t, (souriau (γ t) : Matrix n n ℂ).charpoly.roots.count 1 =
      (souriau U : Matrix n n ℂ).charpoly.roots.count 1) :
    maslovIndex γ = 0 := by
  set k := (souriau U : Matrix n n ℂ).charpoly.roots.count 1
  set s : I → ℝ := fun t => spectralAngleSum (souriau (γ t) : Matrix n n ℂ) with hs_def
  have hW : Continuous fun t => (souriau (γ t) : Matrix n n ℂ) :=
    continuous_subtype_val.comp (continuous_souriau.comp γ.continuous)
  have hs : Continuous s := continuous_iff_continuousAt.2 fun t₀ =>
    continuousAt_spectralAngleSum hW.continuousAt
      (fun _ hz h1 => neg_mem_slitPlane_of_norm_eq_one
        (norm_eq_one_of_mem_roots_charpoly _ hz) h1)
      (Filter.Eventually.of_forall fun t => (h t).trans (h t₀).symm)
  -- `θ t = 2π s(γ t γ tᵀ) + π (n - k)` is a continuous angle of the Maslov phase.
  have hlift (t : I) : Circle.exp (2 * Real.pi * s t + Real.pi * (Fintype.card n - k : ℕ)) =
      detSouriauPath γ t := by
    refine Circle.ext ?_
    rw [detSouriauPath_apply, coe_detCircle, det_eq_neg_one_pow_mul_exp_spectralAngleSum, h t,
      Circle.coe_exp]
    have he : (↑(2 * Real.pi * s t + Real.pi * ((Fintype.card n - k : ℕ) : ℝ)) * Complex.I : ℂ) =
        ((Fintype.card n - k : ℕ) : ℂ) * (Real.pi * Complex.I) +
          ↑(2 * Real.pi * s t) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [maslovIndex, Circle.angleChange_eq_sub
    (θ := fun t => 2 * Real.pi * s t + Real.pi * ((Fintype.card n - k : ℕ) : ℝ)) _
    ((continuous_const.mul hs).add continuous_const) hlift]
  have h0 : s 0 = spectralAngleSum (souriau U : Matrix n n ℂ) := by simp [hs_def]
  have h1 : s 1 = spectralAngleSum (souriau V : Matrix n n ℂ) := by simp [hs_def]
  rw [h0, h1]
  field_simp
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
