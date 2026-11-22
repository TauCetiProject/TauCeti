/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.Mostow
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Units

/-!
# The Cartan decomposition of a closed matrix group stable under conjugate transpose

Let `H` be a closed subgroup of `GL(n, 𝕜)`, for `𝕜 = ℝ` or `ℂ`, that is stable under the
conjugate transpose `g ↦ gᴴ` (the transpose when `𝕜 = ℝ`) and has finitely many connected
components. Then the polar factors of each `g ∈ H` lie in `H`: writing `g = k * exp X` with `k`
unitary and `X` Hermitian, both `k` and the whole line `t ↦ exp (t X)` lie in `H`. Consequently
`(k, X) ↦ k * exp X` is a homeomorphism from the product of `K_H = H ∩ U(n)` and the Hermitian
part `𝔭_H` of the Lie algebra of `H` onto `H`, and `K_H` is a maximal compact subgroup of `H`.
This is the global Cartan decomposition `H = K_H exp 𝔭_H` of a matrix group stable under the
Cartan involution `g ↦ (gᴴ)⁻¹`.

The point is the line through a positive element. If `p = exp X ∈ H` with `X` Hermitian, the
identity component `H₀` contains some power `p ^ m`, so it suffices to treat a connected `H`. Let
`𝔥` be the Lie algebra `{Y | ∀ t, exp (t Y) ∈ H}` of the closed subgroup `H`, a real Lie
subalgebra stable under `Y ↦ Yᴴ`.

* Conjugation by `p` preserves `𝔥`, hence so does the commutator with `X`, by Mostow's lemma
  `Matrix.IsHermitian.commutator_mem_of_exp_mul_mul_exp_neg_mem`.
* Split `X = X₁ + Z` orthogonally for the real inner product `re (trace (A * Bᴴ))`, with
  `X₁ ∈ 𝔥` and `Z ⊥ 𝔥` both Hermitian. The commutator of `Z` with `Y ∈ 𝔥` lies in `𝔥` and is
  orthogonal to `𝔥`, so `Z` commutes with `𝔥`; in particular `exp Z = exp (-X₁) * p ∈ H`.
* Let `P_c` be the spectral projections of `Z`. On the centralizer of `Z` the function
  `Λ g = ∑ c, c * log ‖det (P_c * g + 1 - P_c)‖` is a continuous homomorphism to `ℝ`, and
  `Λ (exp (t Y)) = t * re (trace (Z * Y))` for `Y` commuting with `Z`. It vanishes on the
  exponential lines of `𝔥`, so its kernel, a closed subgroup whose Lie algebra contains `𝔥`,
  contains the connected group `H` (`TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le`). Hence
  `0 = Λ (exp Z) = re (trace (Z * Z))`, so `Z = 0` and `X = X₁ ∈ 𝔥`.

The finiteness of the component group is needed: the powers of `diag (2, 1/2)` form a closed
subgroup of `GL(2, ℝ)` stable under transpose, which contains no other point of the line
`diag (2 ^ t, 2 ^ (-t))`.

## Main results

* `Matrix.GeneralLinearGroup.exists_mem_coe_eq_exp_smul_of_isClosed`: the line through a
  positive element `exp X` of `H` lies in `H`.
* `Matrix.GeneralLinearGroup.polarUnitary_mem_of_isClosed`: the unitary polar factor of an
  element of `H` lies in `H`.
* `Matrix.GeneralLinearGroup.cartanHomeomorphOfIsClosed`: the homeomorphism
  `K_H × 𝔭_H ≃ₜ H`, `(k, X) ↦ k * exp X`, with `val_cartanHomeomorphOfIsClosed_apply`.
* `Matrix.GeneralLinearGroup.cartan_polar_decomposition`: every `g ∈ H` is uniquely
  `k * exp X` with `k ∈ K_H` and `X ∈ 𝔭_H`.
* `Matrix.GeneralLinearGroup.maximal_isCompact_unitarySubgroup_subgroupOf_of_isClosed`: `K_H` is
  a maximal compact subgroup of `H`.

## References

* G. D. Mostow, *Self-adjoint groups*, Annals of Mathematics (2) 62 (1955), 44–55.
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I, Section 17, and Chapter VII, Section 2.
-/

public section

noncomputable section

open scoped MatrixOrder Manifold

open NormedSpace

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-! ### Auxiliary matrix facts -/

section Aux

/-- The norm of the exponential of a scalar is the real exponential of its real part. -/
private theorem norm_exp_eq (w : 𝕜) : ‖NormedSpace.exp w‖ = Real.exp (RCLike.re w) := by
  have hconj : (starRingEnd 𝕜) (NormedSpace.exp w) = NormedSpace.exp ((starRingEnd 𝕜) w) :=
    NormedSpace.map_exp _ RCLike.continuous_conj w
  have hsq : (‖NormedSpace.exp w‖ : 𝕜) ^ 2 = ((Real.exp (RCLike.re w) ^ 2 : ℝ) : 𝕜) := by
    rw [← RCLike.mul_conj, hconj, ← NormedSpace.exp_add, RCLike.add_conj, ← Real.exp_natCast_mul,
      ← RCLike.exp_ofReal]
    push_cast
    ring_nf
  have h := congrArg RCLike.re hsq
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.ofReal_re] at h
  exact (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h

omit [DecidableEq n] in
/-- The real part of `trace (A * Aᴴ)` vanishes only for `A = 0`. -/
private theorem re_trace_mul_conjTranspose_self_eq_zero {A : Matrix n n 𝕜}
    (h : RCLike.re (A * Aᴴ).trace = 0) : A = 0 := by
  rw [re_trace_mul_conjTranspose_self] at h
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖A i j‖).1 h i (Finset.mem_univ _)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg ‖A i j‖).1 hi j
    (Finset.mem_univ _)
  simpa using hij

/-- For an idempotent `P`, the map `g ↦ P * g + 1 - P` is multiplicative on the matrices
commuting with `P`. -/
private theorem idem_mul_idem {P g h : Matrix n n 𝕜} (hP : P * P = P) (hg : Commute P g) :
    (P * g + 1 - P) * (P * h + 1 - P) = P * (g * h) + 1 - P := by
  have h1 : P * g * P = P * g := by rw [mul_assoc, ← hg.eq, ← mul_assoc, hP]
  have : (P * g + 1 - P) * (P * h + 1 - P) =
      P * g * P * h + P * g - P * g * P + P * h - P * P * h + 1 - P - P + P * P := by
    noncomm_ring
  rw [this, h1, hP]
  noncomm_ring

/-- For an idempotent `P` commuting with `A`, the exponential of `P * A` is `exp A` on the range of
`P` and the identity on the range of `1 - P`. -/
private theorem exp_idem_mul {P A : Matrix n n 𝕜} (hP : P * P = P) (hPA : Commute P A) :
    NormedSpace.exp (P * A) = P * NormedSpace.exp A + 1 - P := by
  have hpow (k : ℕ) : (P * A) ^ (k + 1) = P * A ^ (k + 1) := by
    rw [hPA.mul_pow, IsIdempotentElem.pow_succ_eq k hP]
  open scoped Matrix.Norms.L2Operator in
  have h := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) A).mul_left P).update 0 1
  have hf : Function.update (fun k ↦ P * ((k.factorial⁻¹ : 𝕜) • A ^ k)) 0 1 =
      fun k ↦ (k.factorial⁻¹ : 𝕜) • (P * A) ^ k := by
    funext k
    rcases k with _ | k
    · simp
    · simp [hpow]
  rw [hf] at h
  open scoped Matrix.Norms.L2Operator in
  rw [(NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (P * A)).unique h]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, mul_one]
  abel

end Aux

/-! ### A character of the centralizer of a Hermitian matrix -/

section Character

variable {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)

/-- The spectral projection of the Hermitian matrix `Z` for the real number `c`: the orthogonal
projection onto the eigenspace of `c`, which is `0` unless `c` is an eigenvalue. -/
private def specProj (c : ℝ) : Matrix n n 𝕜 :=
  (hZ.eigenvectorUnitary : Matrix n n 𝕜) *
    diagonal (fun i ↦ if hZ.eigenvalues i = c then 1 else 0) *
      star (hZ.eigenvectorUnitary : Matrix n n 𝕜)

private theorem specProj_mul_self (c : ℝ) : specProj hZ c * specProj hZ c = specProj hZ c := by
  have hUU : star (hZ.eigenvectorUnitary : Matrix n n 𝕜) * hZ.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.property
  simp only [specProj, mul_assoc]
  rw [← mul_assoc (star (hZ.eigenvectorUnitary : Matrix n n 𝕜)), hUU, one_mul,
    ← mul_assoc (diagonal _), diagonal_mul_diagonal]
  congr 3
  funext i
  split_ifs <;> simp

private theorem sum_smul_specProj :
    ∑ c ∈ Finset.univ.image hZ.eigenvalues, (c : 𝕜) • specProj hZ c = Z := by
  set U : Matrix n n 𝕜 := (hZ.eigenvectorUnitary : Matrix n n 𝕜)
  have hspec := hZ.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hdiag : ∑ c ∈ Finset.univ.image hZ.eigenvalues,
      (c : 𝕜) • diagonal (fun i ↦ if hZ.eigenvalues i = c then (1 : 𝕜) else 0) =
        diagonal (RCLike.ofReal ∘ hZ.eigenvalues) := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Function.comp_apply]
      rw [Finset.sum_ite_eq (Finset.univ.image hZ.eigenvalues) (hZ.eigenvalues i)]
      simp
    · simp [diagonal_apply_ne _ hij]
  calc ∑ c ∈ Finset.univ.image hZ.eigenvalues, (c : 𝕜) • specProj hZ c
      = U * (∑ c ∈ Finset.univ.image hZ.eigenvalues,
          (c : 𝕜) • diagonal (fun i ↦ if hZ.eigenvalues i = c then (1 : 𝕜) else 0)) *
            star U := by
        rw [Finset.mul_sum, Finset.sum_mul]
        simp [specProj, U]
    _ = Z := by rw [hdiag]; exact hspec.symm

private theorem commute_specProj {g : Matrix n n 𝕜} (hg : Commute g Z) (c : ℝ) :
    Commute g (specProj hZ c) := by
  set U : Matrix n n 𝕜 := (hZ.eigenvectorUnitary : Matrix n n 𝕜)
  set d := hZ.eigenvalues
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.property
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hZ.eigenvectorUnitary.property
  have hD : star U * Z * U = diagonal (RCLike.ofReal ∘ d) := by
    have h := hZ.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
  set h := star U * g * U
  have hg' : g = U * h * star U := by
    simp only [h, ← mul_assoc, hUU', one_mul]
    rw [mul_assoc, hUU', mul_one]
  -- In the eigenbasis, `h` commutes with the diagonal matrix of eigenvalues.
  have hhD : h * diagonal (RCLike.ofReal ∘ d) = diagonal (RCLike.ofReal ∘ d) * h := by
    rw [← hD]
    simp only [h, mul_assoc]
    rw [← mul_assoc U (star U), hUU', one_mul, ← mul_assoc U (star U), hUU', one_mul,
      ← mul_assoc g Z, hg.eq, mul_assoc Z g]
  have hentry (i j : n) (hij : d i ≠ d j) : h i j = 0 := by
    have := congrArg (fun M ↦ M i j) hhD
    simp only [mul_diagonal, diagonal_mul, Function.comp_apply] at this
    have hne : (d j : 𝕜) - d i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij.symm)
    have : h i j * ((d j : 𝕜) - d i) = 0 := by rw [mul_sub, this]; ring
    exact (mul_eq_zero.1 this).resolve_right hne
  have hcomm : h * diagonal (fun i ↦ if d i = c then (1 : 𝕜) else 0) =
      diagonal (fun i ↦ if d i = c then (1 : 𝕜) else 0) * h := by
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases hi : d i = c <;> by_cases hj : d j = c
    · simp [hi, hj]
    · simp [hi, hj, hentry i j (by rw [hi]; exact Ne.symm hj)]
    · simp [hi, hj, hentry i j (by rw [hj]; exact hi)]
    · simp [hi, hj]
  change g * specProj hZ c = specProj hZ c * g
  simp only [specProj]
  rw [hg']
  simp only [mul_assoc]
  rw [← mul_assoc (star U) U, hUU, one_mul, ← mul_assoc (star U) U, hUU, one_mul,
    ← mul_assoc h, hcomm, mul_assoc]

/-- The character `Λ g = ∑ c, c * log ‖det (P_c * g + 1 - P_c)‖` of the centralizer of `Z`, where
`P_c` are the spectral projections of `Z`. -/
private def charFun (g : Matrix n n 𝕜) : ℝ :=
  ∑ c ∈ Finset.univ.image hZ.eigenvalues,
    c * Real.log ‖(specProj hZ c * g + 1 - specProj hZ c).det‖

private theorem det_specProj_mul_ne_zero {g : GL n 𝕜} (hg : Commute (g : Matrix n n 𝕜) Z)
    (c : ℝ) : (specProj hZ c * g + 1 - specProj hZ c).det ≠ 0 := by
  have h := idem_mul_idem (h := ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)) (specProj_mul_self hZ c)
    (commute_specProj hZ hg c).symm
  rw [Units.mul_inv, mul_one, add_sub_cancel_left] at h
  have := congrArg Matrix.det h
  rw [det_mul, det_one] at this
  exact left_ne_zero_of_mul_eq_one this

private theorem charFun_mul {g h : GL n 𝕜} (hg : Commute (g : Matrix n n 𝕜) Z)
    (hh : Commute (h : Matrix n n 𝕜) Z) :
    charFun hZ ((g : Matrix n n 𝕜) * h) = charFun hZ g + charFun hZ h := by
  simp only [charFun, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← idem_mul_idem (specProj_mul_self hZ c) (commute_specProj hZ hg c).symm, det_mul,
    norm_mul, Real.log_mul (norm_ne_zero_iff.2 (det_specProj_mul_ne_zero hZ hg c))
      (norm_ne_zero_iff.2 (det_specProj_mul_ne_zero hZ hh c))]

private theorem charFun_exp {M : Matrix n n 𝕜} (hM : Commute M Z) :
    charFun hZ (NormedSpace.exp M) = RCLike.re (Z * M).trace := by
  have h (c : ℝ) : specProj hZ c * NormedSpace.exp M + 1 - specProj hZ c =
      NormedSpace.exp (specProj hZ c * M) :=
    (exp_idem_mul (specProj_mul_self hZ c) (commute_specProj hZ hM c).symm).symm
  simp only [charFun, h, det_exp, norm_exp_eq, Real.log_exp]
  conv_rhs => rw [← sum_smul_specProj hZ]
  simp only [Finset.sum_mul, trace_sum, map_sum, smul_mul_assoc, trace_smul, smul_eq_mul,
    RCLike.re_ofReal_mul]

/-- The kernel of the character `charFun` on the centralizer of `Z`. -/
private def charSubgroup : Subgroup (GL n 𝕜) where
  carrier := {g | Commute (g : Matrix n n 𝕜) Z ∧ charFun hZ g = 0}
  one_mem' := ⟨Commute.one_left Z, by simp [charFun]⟩
  mul_mem' {g h} hg hh := ⟨by simpa using hg.1.mul_left hh.1, by
    simp only [Units.val_mul, charFun_mul hZ hg.1 hh.1, hg.2, hh.2, add_zero]⟩
  inv_mem' {g} hg := by
    have hinv : Commute ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) Z := by
      simpa using hg.1.units_inv_left
    refine ⟨hinv, ?_⟩
    have := charFun_mul hZ hg.1 hinv
    rw [Units.mul_inv, hg.2, zero_add] at this
    simpa [charFun] using this.symm

private theorem isClosed_charSubgroup : IsClosed (charSubgroup hZ : Set (GL n 𝕜)) := by
  have hC : IsClosed {g : GL n 𝕜 | Commute (g : Matrix n n 𝕜) Z} :=
    isClosed_eq (Units.continuous_val.mul continuous_const)
      (continuous_const.mul Units.continuous_val)
  have hcont : ContinuousOn (fun g : GL n 𝕜 ↦ charFun hZ g)
      {g : GL n 𝕜 | Commute (g : Matrix n n 𝕜) Z} := by
    refine continuousOn_finsetSum _ fun c _ ↦ ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log ?_ fun g hg ↦ norm_ne_zero_iff.2 (det_specProj_mul_ne_zero hZ hg c)
    exact (((continuous_const.mul Units.continuous_val).add continuous_const).sub
      continuous_const).matrix_det.norm.continuousOn
  exact hcont.preimage_isClosed_of_isClosed hC isClosed_singleton

end Character

/-! ### The Lie algebra of a closed subgroup in matrix coordinates -/

section LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The exponential of a matrix, as an invertible matrix. -/
private def expGL (Y : Matrix n n 𝕜) : GL n 𝕜 :=
  (Matrix.isUnit_exp Y).unit

private theorem coe_expGL (Y : Matrix n n 𝕜) : (expGL Y : Matrix n n 𝕜) = NormedSpace.exp Y :=
  IsUnit.unit_spec _

private theorem expGL_neg (Y : Matrix n n 𝕜) : expGL (-Y) = (expGL Y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  rw [Units.val_mul, coe_expGL, coe_expGL, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left
    (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero, Units.val_one]

variable {H : Subgroup (GL n 𝕜)}

attribute [local instance] TauCeti.normedAlgebraRatOfReal in
open scoped Matrix.Norms.L2Operator in
/-- For a closed subgroup, the exponential lines staying in it are the elements of its abstract
Lie algebra, read in matrix coordinates. -/
private theorem forall_expGL_mem_iff (hH : IsClosed (H : Set (GL n 𝕜))) (Y : Matrix n n 𝕜) :
    letI := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    (∀ t : ℝ, expGL (t • Y) ∈ H) ↔
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm Y ∈
        TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) H := by
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hH]
  have h (t : ℝ) : TauCeti.expUnit (t • Y) = expGL (t • Y) :=
    Units.ext ((TauCeti.expUnit_coe _).trans (coe_expGL _).symm)
  simp only [h]

/-- The Lie algebra `{Y | ∀ t, exp (t Y) ∈ H}` of a closed subgroup of `GL n 𝕜`, as a real
subspace of the matrices. -/
private def lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) : Submodule ℝ (Matrix n n 𝕜) where
  carrier := {Y | ∀ t : ℝ, expGL (t • Y) ∈ H}
  zero_mem' t := by
    convert H.one_mem
    exact Units.ext (by simp [coe_expGL])
  add_mem' {Y W} hY hW := by
    let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    refine (forall_expGL_mem_iff hH (Y + W)).2 ?_
    rw [map_add]
    exact add_mem ((forall_expGL_mem_iff hH Y).1 hY) ((forall_expGL_mem_iff hH W).1 hW)
  smul_mem' c Y hY t := by simpa [smul_smul] using hY (t * c)

private theorem mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {Y : Matrix n n 𝕜} :
    Y ∈ lieAlg hH ↔ ∀ t : ℝ, expGL (t • Y) ∈ H :=
  Iff.rfl

/-- The Lie algebra of a closed subgroup is closed under the commutator. -/
private theorem commutator_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {Y W : Matrix n n 𝕜}
    (hY : Y ∈ lieAlg hH) (hW : W ∈ lieAlg hH) : Y * W - W * Y ∈ lieAlg hH := by
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  have := LieSubalgebra.lie_mem _ ((forall_expGL_mem_iff hH Y).1 hY)
    ((forall_expGL_mem_iff hH W).1 hW)
  rw [← LieEquiv.map_lie, Ring.lie_def] at this
  exact (forall_expGL_mem_iff hH _).2 this

open scoped Matrix.Norms.L2Operator in
/-- A closed connected subgroup lies in every closed subgroup whose Lie algebra contains its own. -/
private theorem le_of_lieAlg_le (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {L : Subgroup (GL n 𝕜)}
    (hL : IsClosed (L : Set (GL n 𝕜))) (h : lieAlg hH ≤ lieAlg hL) : H ≤ L := by
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  refine TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le (I := 𝓘(ℝ, Matrix n n 𝕜)) hH hconn hL
    fun x hx ↦ ?_
  rw [← (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm_apply_apply x] at hx ⊢
  exact (forall_expGL_mem_iff hL _).1 (h ((forall_expGL_mem_iff hH _).2 hx))

/-- The Lie algebra of a subgroup is invariant under conjugation by the subgroup. -/
private theorem conj_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {g : GL n 𝕜} (hg : g ∈ H)
    {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg hH) :
    (g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) ∈ lieAlg hH := fun t ↦ by
  have : expGL (t • ((g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜))) =
      g * expGL (t • Y) * g⁻¹ := by
    refine Units.ext ?_
    rw [coe_expGL, Units.val_mul, Units.val_mul, coe_expGL, ← Matrix.exp_units_conj,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [this]
  exact H.mul_mem (H.mul_mem hg (hY t)) (H.inv_mem hg)

/-- The Lie algebra of a subgroup stable under the conjugate transpose is stable under it. -/
private theorem star_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg hH) :
    star Y ∈ lieAlg hH := fun t ↦ by
  have : expGL (t • star Y) = star (expGL (t • Y)) := by
    refine Units.ext ?_
    rw [coe_expGL, Units.coe_star, coe_expGL, star_eq_conjTranspose, star_eq_conjTranspose,
      ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
  rw [this]
  exact hstar _ (hY t)

end LieAlgebra

/-! ### The line through a positive element -/

section Line

omit [DecidableEq n] in
/-- A Hermitian matrix splits as `X₁ + Z` with `X₁` Hermitian in a real subspace `V` stable under
the conjugate transpose and `Z` Hermitian and orthogonal to `V` for `re (trace (A * B))`. -/
private theorem exists_add_orthogonal {V : Submodule ℝ (Matrix n n 𝕜)}
    (hV : ∀ Y ∈ V, star Y ∈ V) {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    ∃ X₁ ∈ V, ∃ Z : Matrix n n 𝕜, Z.IsHermitian ∧ X = X₁ + Z ∧
      ∀ W ∈ V, RCLike.re (Z * W).trace = 0 := by
  let B : LinearMap.BilinForm ℝ (Matrix n n 𝕜) :=
    LinearMap.mk₂ ℝ (fun A C ↦ RCLike.re (A * Cᴴ).trace)
      (fun A A' C ↦ by simp [add_mul]) (fun c A C ↦ by simp [RCLike.real_smul_eq_coe_mul])
      (fun A C C' ↦ by simp [mul_add]) (fun c A C ↦ by simp [RCLike.real_smul_eq_coe_mul])
  have hB (A C : Matrix n n 𝕜) : B A C = RCLike.re (A * Cᴴ).trace := rfl
  have hsymm (A C : Matrix n n 𝕜) : B C A = B A C := by
    rw [hB, hB, show C * Aᴴ = (A * Cᴴ)ᴴ by simp [conjTranspose_mul], trace_conjTranspose,
      RCLike.star_def, RCLike.conj_re]
  have hrefl : B.IsRefl := fun A C h ↦ by rwa [hsymm]
  have hcompl : IsCompl V (B.orthogonal V) := by
    refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 ?_
    refine Submodule.disjoint_def.2 fun A hA hA' ↦ re_trace_mul_conjTranspose_self_eq_zero ?_
    exact hA' A hA
  obtain ⟨X₀, hX₀, Z₀, hZ₀, hsum⟩ := Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top :
    X ∈ V ⊔ B.orthogonal V)
  -- `Z₀ ⊥ V` gives `re (trace (Z₀ * W)) = 0` and `re (trace (Z₀ᴴ * W)) = 0` for `W ∈ V`.
  have horth (W : Matrix n n 𝕜) (hW : W ∈ V) : RCLike.re (Z₀ * W).trace = 0 := by
    have h : B (star W) Z₀ = 0 := hZ₀ (star W) (hV W hW)
    rwa [hsymm, hB, star_eq_conjTranspose, conjTranspose_conjTranspose] at h
  have horth' (W : Matrix n n 𝕜) (hW : W ∈ V) : RCLike.re (Z₀ᴴ * W).trace = 0 := by
    have h : B W Z₀ = 0 := hZ₀ W hW
    rwa [hB, trace_mul_comm] at h
  refine ⟨(1 / 2 : ℝ) • (X₀ + star X₀), V.smul_mem _ (V.add_mem hX₀ (hV _ hX₀)),
    (1 / 2 : ℝ) • (Z₀ + Z₀ᴴ), ?_, ?_, fun W hW ↦ ?_⟩
  · simp [IsHermitian, conjTranspose_smul, add_comm]
  · have hX' : X = (1 / 2 : ℝ) • (X + Xᴴ) := by
      rw [hX.eq, ← two_smul ℝ X, smul_smul]
      norm_num
    rw [hX', ← hsum, conjTranspose_add, star_eq_conjTranspose, ← smul_add]
    congr 1
    abel
  · rw [Matrix.smul_mul, trace_smul, add_mul, trace_add, RCLike.smul_re, map_add, horth W hW,
      horth' W hW, add_zero, mul_zero]

variable {H : Subgroup (GL n 𝕜)}

/-- **The character argument.** Let `H` be a closed connected subgroup and `Z` a Hermitian matrix
commuting with the Lie algebra of `H` and orthogonal to it. If `exp Z ∈ H` then `Z = 0`. -/
private theorem eq_zero_of_expGL_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)
    (hcomm : ∀ Y ∈ lieAlg hH, Commute Y Z) (horth : ∀ Y ∈ lieAlg hH, RCLike.re (Z * Y).trace = 0)
    (hZH : expGL Z ∈ H) : Z = 0 := by
  have hle : H ≤ charSubgroup hZ := le_of_lieAlg_le hH hconn (isClosed_charSubgroup hZ)
    fun Y hY t ↦ ⟨by rw [coe_expGL]; exact ((hcomm Y hY).smul_left t).exp_left, by
      rw [coe_expGL, charFun_exp hZ ((hcomm Y hY).smul_left t), mul_smul_comm, trace_smul,
        RCLike.smul_re, horth Y hY, mul_zero]⟩
  have h := (hle hZH).2
  rw [coe_expGL, charFun_exp hZ (Commute.refl Z)] at h
  refine re_trace_mul_conjTranspose_self_eq_zero ?_
  rwa [hZ.eq]

/-- **The line through a positive element of a closed connected group.** Let `H` be a closed
connected subgroup of `GL n 𝕜` stable under the conjugate transpose. If `exp X ∈ H` for a
Hermitian `X`, then `X` lies in the Lie algebra of `H`. -/
private theorem mem_lieAlg_of_isPreconnected (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hconn : IsPreconnected (H : Set (GL n 𝕜)))
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (hXH : expGL X ∈ H) : X ∈ lieAlg hH := by
  -- Mostow's lemma: the commutator with `X` preserves the Lie algebra.
  have hXcomm (Y : Matrix n n 𝕜) (hY : Y ∈ lieAlg hH) : X * Y - Y * X ∈ lieAlg hH := by
    refine hX.commutator_mem_of_exp_mul_mul_exp_neg_mem (fun Y hY ↦ ?_) hY
    have := conj_mem_lieAlg hH hXH hY
    rwa [← expGL_neg, coe_expGL, coe_expGL] at this
  obtain ⟨X₁, hX₁, Z, hZ, rfl, horth⟩ := exists_add_orthogonal (fun _ ↦ star_mem_lieAlg hH hstar) hX
  -- `Z` commutes with the Lie algebra: the commutator lies in it and is orthogonal to it.
  have hcomm (Y : Matrix n n 𝕜) (hY : Y ∈ lieAlg hH) : Commute Y Z := by
    set A := Z * Y - Y * Z
    have hA : A ∈ lieAlg hH := by
      have := (lieAlg hH).sub_mem (hXcomm Y hY) (commutator_mem_lieAlg hH hX₁ hY)
      convert this using 1
      simp only [A]
      noncomm_ring
    have hAorth (W : Matrix n n 𝕜) (hW : W ∈ lieAlg hH) : RCLike.re (A * W).trace = 0 := by
      have h := horth _ (commutator_mem_lieAlg hH hY hW)
      have hAW : A * W = Z * (Y * W - W * Y) + (Z * W * Y - Y * Z * W) := by
        simp only [A]
        noncomm_ring
      rwa [hAW, trace_add, trace_sub, Matrix.mul_assoc Y, trace_mul_comm Y, sub_self, add_zero]
    have h0 := re_trace_mul_conjTranspose_self_eq_zero
      (hAorth _ (star_mem_lieAlg hH hstar hA))
    exact (sub_eq_zero.1 h0).symm
  -- Hence `exp Z = exp (-X₁) * exp X` lies in `H`, and the character argument gives `Z = 0`.
  have hZH : expGL Z ∈ H := by
    have : expGL Z = (expGL X₁)⁻¹ * expGL (X₁ + Z) := by
      refine Units.ext ?_
      rw [Units.val_mul, ← expGL_neg, coe_expGL, coe_expGL, coe_expGL,
        ← Matrix.exp_add_of_commute (-X₁) (X₁ + Z)
          ((Commute.refl X₁).neg_left.add_right (hcomm X₁ hX₁).neg_left), neg_add_cancel_left]
    rw [this]
    exact H.mul_mem (H.inv_mem (by simpa using hX₁ 1)) hXH
  rw [eq_zero_of_expGL_mem hH hconn hZ hcomm horth hZH, add_zero]
  exact hX₁

/-- Some positive power of an element of a topological group with finitely many components lies
in the identity component. -/
private theorem exists_pow_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [Finite (ConnectedComponents G)] (p : G) :
    ∃ m : ℕ, 0 < m ∧ p ^ m ∈ connectedComponent (1 : G) := by
  have key (i j : ℕ) (hij : i < j)
      (h : ConnectedComponents.mk (p ^ i) = ConnectedComponents.mk (p ^ j)) :
      ∃ m : ℕ, 0 < m ∧ p ^ m ∈ connectedComponent (1 : G) := by
    refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
    have hj : p ^ j ∈ connectedComponent (p ^ i) :=
      ConnectedComponents.coe_eq_coe.1 h ▸ mem_connectedComponent
    have hsub := (Homeomorph.mulLeft (p ^ i)⁻¹).continuous.image_connectedComponent_subset
      (p ^ i) ⟨p ^ j, hj, rfl⟩
    simp only [Homeomorph.coe_mulLeft, inv_mul_cancel] at hsub
    convert hsub using 1
    rw [eq_inv_mul_iff_mul_eq, ← pow_add, Nat.add_sub_cancel' hij.le]
  obtain ⟨i, j, hij, h⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ ↦ ConnectedComponents.mk (p ^ k)
  rcases hij.lt_or_gt with hij | hij
  · exact key i j hij h
  · exact key j i hij h.symm

variable (H) in
/-- The identity component of a subgroup of `GL n 𝕜`, as a subgroup of `GL n 𝕜`. -/
private def identityComponent : Subgroup (GL n 𝕜) :=
  (Subgroup.connectedComponentOfOne H).map H.subtype

private theorem coe_identityComponent :
    (identityComponent H : Set (GL n 𝕜)) = Subtype.val '' connectedComponent (1 : H) :=
  Subgroup.coe_map _ _

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜` stable
under the conjugate transpose, with finitely many connected components. If `exp X ∈ H` for a
Hermitian `X`, then `X` lies in the Lie algebra of `H`. -/
private theorem mem_lieAlg_of_finite (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) (hXH : expGL X ∈ H) : X ∈ lieAlg hH := by
  -- Pass to the identity component, which is closed, connected and stable under `star`.
  have hc : IsClosed (identityComponent H : Set (GL n 𝕜)) := by
    rw [coe_identityComponent]
    exact hH.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hconn : IsPreconnected (identityComponent H : Set (GL n 𝕜)) := by
    rw [coe_identityComponent]
    exact isPreconnected_connectedComponent.image _ continuous_subtypeVal.continuousOn
  have hstar₀ (g : GL n 𝕜) (hg : g ∈ identityComponent H) : star g ∈ identityComponent H := by
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    let f : H → H := fun h ↦ ⟨star (h : GL n 𝕜), hstar _ h.property⟩
    have hf : Continuous f := (continuous_star.comp continuous_subtypeVal).subtype_mk _
    have hsub := hf.image_connectedComponent_subset (1 : H)
    have hf1 : f 1 = 1 := Subtype.ext (star_one _)
    rw [hf1] at hsub
    exact Subgroup.mem_map.2 ⟨f h, hsub ⟨h, hh, rfl⟩, rfl⟩
  have hle : identityComponent H ≤ H := Subgroup.map_subtype_le _
  -- Some power `exp (m X)` lies in the identity component.
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem_connectedComponent_one (⟨expGL X, hXH⟩ : H)
  have hpow : expGL ((m : ℝ) • X) ∈ identityComponent H := by
    have : expGL ((m : ℝ) • X) = expGL X ^ m := by
      refine Units.ext ?_
      rw [coe_expGL, Units.val_pow_eq_pow_val, coe_expGL, Nat.cast_smul_eq_nsmul,
        Matrix.exp_nsmul]
    rw [this]
    exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
  have hmX : ((m : ℝ) • X).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, star_trivial, hX.eq]
  have h := mem_lieAlg_of_isPreconnected hc hstar₀ hconn hmX hpow
  intro t
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have := hle (h (t / m))
  rwa [smul_smul, div_mul_cancel₀ t hm'] at this

end Line

/-! ### The Cartan decomposition -/

section Cartan

variable {H : Subgroup (GL n 𝕜)}

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜`, for
`𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose and with finitely many connected components.
If `H` contains `exp X` for a Hermitian matrix `X`, then it contains `exp (t X)` for every real
`t`. -/
theorem exists_mem_coe_eq_exp_smul_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) {g : GL n 𝕜} (hg : g ∈ H) (hgX : (g : Matrix n n 𝕜) = NormedSpace.exp X)
    (t : ℝ) : ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X) := by
  have hXH : expGL X ∈ H := by
    convert hg
    exact Units.ext (by rw [coe_expGL, hgX])
  exact ⟨_, mem_lieAlg_of_finite hH hstar hfin hX hXH t, coe_expGL _⟩

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable (H) in
/-- **The Cartan decomposition of a closed matrix group stable under the conjugate transpose.**
Let `H` be a closed subgroup of `GL n 𝕜`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose
and with finitely many connected components. Then `(k, X) ↦ k * exp X` is a homeomorphism from the
product of the unitary elements `K_H` of `H` (the orthogonal ones when `𝕜 = ℝ`) and the Hermitian
part `𝔭_H` of the Lie algebra of `H`, the Hermitian `X` with `exp (t X) ∈ H` for all real `t`, onto
`H`. -/
def cartanHomeomorphOfIsClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) :
    {k : unitaryGroup n 𝕜 // Unitary.toUnits k ∈ H} ×
        {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
          ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))} ≃ₜ H := by
  -- The general statement needs a complete normed `ℝ`-algebra with an isometric functional
  -- calculus, which `Matrix n n 𝕜` is for the scoped `ℓ²` operator norm.
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  have hline (x : Matrix n n 𝕜) : (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) ↔
      ∀ t : ℝ, ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • x) := by
    refine ⟨fun h t ↦ ⟨_, h t, TauCeti.expUnit_coe _⟩, fun h t ↦ ?_⟩
    obtain ⟨g, hg, hgx⟩ := h t
    convert hg
    exact Units.ext (by rw [TauCeti.expUnit_coe, hgx])
  have hexp (x : Matrix n n 𝕜) (hx : IsSelfAdjoint x) (hxH : TauCeti.expUnit x ∈ H) (t : ℝ) :
      TauCeti.expUnit (t • x) ∈ H :=
    (hline x).2 (exists_mem_coe_eq_exp_smul_of_isClosed hH hstar hfin hx.isHermitian hxH
      (TauCeti.expUnit_coe x)) t
  let eP : {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
        ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))} ≃ₜ
      {x : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ, TauCeti.expUnit (t • (x : Matrix n n 𝕜)) ∈ H} :=
    { toFun X := ⟨X.val, (hline _).2 X.property⟩
      invFun x := ⟨x.val, (hline _).1 x.property⟩
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }
  exact ((Homeomorph.refl _).prodCongr eP).trans (H.cartanHomeomorph hstar hexp)

/-- The Cartan decomposition of `H` sends `(k, X)` to `k * exp X`. -/
@[simp]
theorem val_cartanHomeomorphOfIsClosed_apply (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H))
    (p : {k : unitaryGroup n 𝕜 // Unitary.toUnits k ∈ H} ×
      {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
        ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))}) :
    ((cartanHomeomorphOfIsClosed H hH hstar hfin p : GL n 𝕜) : Matrix n n 𝕜) =
      (p.1 : Matrix n n 𝕜) *
        NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact Subgroup.val_cartanHomeomorph_apply _ _ _

/-- The unitary factor of the Cartan decomposition of `g ∈ H` is the polar unitary factor of
`g`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_fst (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    (((cartanHomeomorphOfIsClosed H hH hstar hfin).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact Subgroup.coe_cartanHomeomorph_symm_apply_fst _ _ _

/-- The Hermitian factor of the Cartan decomposition of `g ∈ H` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_snd (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((cartanHomeomorphOfIsClosed H hH hstar hfin).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  open scoped Matrix.Norms.L2Operator in
  let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
  exact Subgroup.coe_cartanHomeomorph_symm_apply_snd _ _ _

/-- **The global Cartan decomposition** `H = K_H exp 𝔭_H` of a closed subgroup `H` of `GL n 𝕜`
stable under the conjugate transpose, with finitely many connected components: every `g ∈ H`
factors uniquely as `k * exp X` with `k` a unitary element of `H` and `X` a Hermitian matrix with
`exp (t X) ∈ H` for every real `t`. -/
theorem cartan_polar_decomposition (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {g : GL n 𝕜}
    (hg : g ∈ H) :
    ∃! p : {k : unitaryGroup n 𝕜 // Unitary.toUnits k ∈ H} ×
        {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
          ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))},
      (g : Matrix n n 𝕜) =
        (p.1 : Matrix n n 𝕜) * NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) :
          Matrix n n 𝕜) := by
  let e := cartanHomeomorphOfIsClosed H hH hstar hfin
  refine ⟨e.symm ⟨g, hg⟩, ?_, fun p hp ↦ ?_⟩
  · dsimp only
    rw [← val_cartanHomeomorphOfIsClosed_apply hH hstar hfin, Homeomorph.apply_symm_apply]
  · refine e.injective (Subtype.ext (Units.ext ?_))
    rw [Homeomorph.apply_symm_apply, val_cartanHomeomorphOfIsClosed_apply, ← hp]

/-- The unitary polar factor of an element of a closed subgroup `H` of `GL n 𝕜` stable under the
conjugate transpose, with finitely many connected components, lies in `H`. -/
theorem polarUnitary_mem_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {g : GL n 𝕜}
    (hg : g ∈ H) : Unitary.toUnits g.polarUnitary ∈ H := by
  have h := ((cartanHomeomorphOfIsClosed H hH hstar hfin).symm ⟨g, hg⟩).1.property
  rwa [coe_cartanHomeomorphOfIsClosed_symm_apply_fst] at h

/-- **The unitary elements form a maximal compact subgroup** of a closed subgroup `H` of
`GL n 𝕜` stable under the conjugate transpose, with finitely many connected components. -/
theorem maximal_isCompact_unitarySubgroup_subgroupOf_of_isClosed
    (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
    (hfin : Finite (ConnectedComponents H)) :
    Maximal (fun K : Subgroup H ↦ IsCompact (K : Set H))
      ((unitarySubgroup (GL n 𝕜)).subgroupOf H) :=
  maximal_isCompact_unitarySubgroup_subgroupOf
    (fun _ hg ↦ polarUnitary_mem_of_isClosed hH hstar hfin hg) hH

end Cartan

end Matrix.GeneralLinearGroup
