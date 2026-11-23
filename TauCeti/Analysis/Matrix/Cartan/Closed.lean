/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.Mostow
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Units
import TauCeti.Topology.Algebra.Group.Connected

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
* Let `P_c = cfc ({c}.indicator 1) Z` be the spectral projections of `Z`. On the centralizer of
  `Z` the function `Λ g = ∑ c, c * log ‖det (P_c * g + 1 - P_c)‖` is a continuous homomorphism to
  `ℝ`, and
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
* `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_exp_of_isClosed`: every `g ∈ H` is uniquely
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


/-! ### Orthogonal splitting for the real trace pairing -/

section Orthogonal

open scoped InnerProductSpace Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- A Hermitian matrix splits as `X₁ + Z` with `X₁` Hermitian in a real subspace `V` stable under
the conjugate transpose and `Z` Hermitian and orthogonal to `V` for `re (trace (A * B))`. -/
private theorem exists_add_orthogonal {V : Submodule ℝ (Matrix n n 𝕜)}
    (hV : ∀ Y ∈ V, star Y ∈ V) {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    ∃ X₁ ∈ V, ∃ Z : Matrix n n 𝕜, Z.IsHermitian ∧ X = X₁ + Z ∧
      ∀ W ∈ V, RCLike.re (Z * W).trace = 0 := by
  -- Split `X` orthogonally for the real Frobenius inner product `re (trace (Aᴴ * B))`.
  let := Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := 𝕜)
  let : InnerProductSpace ℝ (Matrix n n 𝕜) := Matrix.frobeniusInnerProductSpace
  have hinner (A B : Matrix n n 𝕜) : ⟪A, B⟫_ℝ = RCLike.re (Aᴴ * B).trace := by
    rw [frobenius_inner_def, ← frobenius_inner_eq_trace_conjTranspose_mul, frobenius_inner_def,
      map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_sum]; rfl
  obtain ⟨X₀, hX₀, Z₀, hZ₀, hsum⟩ := V.exists_add_mem_mem_orthogonal X
  -- `Z₀ ⊥ V` gives `re (trace (Z₀ * W)) = 0` and `re (trace (Z₀ᴴ * W)) = 0` for `W ∈ V`.
  have horth (W : Matrix n n 𝕜) (hW : W ∈ V) : RCLike.re (Z₀ * W).trace = 0 := by
    have h := Submodule.inner_right_of_mem_orthogonal (hV W hW) hZ₀
    rwa [hinner, star_eq_conjTranspose, conjTranspose_conjTranspose, trace_mul_comm] at h
  have horth' (W : Matrix n n 𝕜) (hW : W ∈ V) : RCLike.re (Z₀ᴴ * W).trace = 0 := by
    have h := Submodule.inner_left_of_mem_orthogonal hW hZ₀
    rwa [hinner] at h
  refine ⟨(1 / 2 : ℝ) • (X₀ + star X₀), V.smul_mem _ (V.add_mem hX₀ (hV _ hX₀)),
    (1 / 2 : ℝ) • (Z₀ + Z₀ᴴ), ?_, ?_, fun W hW ↦ ?_⟩
  · simp [IsHermitian, conjTranspose_smul, add_comm]
  · have hX' : X = (1 / 2 : ℝ) • (X + Xᴴ) := by
      rw [hX.eq, ← two_smul ℝ X, smul_smul]
      norm_num
    rw [hX', hsum, conjTranspose_add, star_eq_conjTranspose, ← smul_add]
    congr 1
    abel
  · rw [Matrix.smul_mul, trace_smul, add_mul, trace_add, RCLike.smul_re, map_add, horth W hW,
      horth' W hW, add_zero, mul_zero]

end Orthogonal

/-! In the rest of the file, `Matrix n n 𝕜` carries the `ℓ²` operator norm, a complete normed
`ℝ`-algebra, so that its group of units has the Lie group structure and exponential of
`TauCeti.expUnit`. -/

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

/-! ### A character of the centralizer of a Hermitian matrix -/

section Character

variable {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)

/-- The spectral projections `cfc ({c}.indicator 1) Z` of the Hermitian matrix `Z`, weighted by
the eigenvalues `c`, sum to `Z`. -/
private theorem sum_smul_cfc_indicator :
    ∑ c ∈ Finset.univ.image hZ.eigenvalues, c • cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z = Z := by
  have hspec := hZ.spectrum_real_eq_range_eigenvalues
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Z) :=
    (hspec ▸ Set.finite_range hZ.eigenvalues).continuousOn f
  calc ∑ c ∈ Finset.univ.image hZ.eigenvalues, c • cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z
      = cfc (∑ c ∈ Finset.univ.image hZ.eigenvalues,
          fun x ↦ c * Set.indicator {c} (1 : ℝ → ℝ) x) Z := by
        rw [cfc_sum _ _ _ fun c _ ↦ hc _]
        exact Finset.sum_congr rfl fun c _ ↦ (cfc_const_mul c _ Z (hc _)).symm
    _ = cfc (fun x : ℝ ↦ x) Z := cfc_congr fun x hx ↦ by
        obtain ⟨i, rfl⟩ := hspec ▸ hx
        simp [Set.indicator_apply]
    _ = Z := cfc_id' ℝ Z hZ.isSelfAdjoint

/-- A matrix commuting with `Z` commutes with its spectral projections. -/
private theorem commute_cfc_indicator {g : Matrix n n 𝕜} (hg : Commute g Z) (c : ℝ) :
    Commute g (cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z) :=
  (Commute.cfc_real hg.symm _).symm

omit hZ in
private theorem isIdempotentElem_cfc_indicator (c : ℝ) :
    IsIdempotentElem (cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z) :=
  (TauCeti.isStarProjection_cfc_indicator Z {c}).isIdempotentElem

omit hZ in
/-- The character `Λ g = ∑ c, c * log ‖det (P_c * g + 1 - P_c)‖` of the centralizer of `Z`, where
`P_c = cfc ({c}.indicator 1) Z` are the spectral projections of `Z`. -/
private def charFun (g : Matrix n n 𝕜) : ℝ :=
  ∑ c ∈ Finset.univ.image hZ.eigenvalues,
    c * Real.log ‖(cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z * g + 1 -
      cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z).det‖

private theorem det_cfc_indicator_mul_ne_zero {g : GL n 𝕜} (hg : Commute (g : Matrix n n 𝕜) Z)
    (c : ℝ) :
    (cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z * g + 1 -
      cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z).det ≠ 0 := by
  have h := (isIdempotentElem_cfc_indicator (Z := Z) c).mul_add_one_sub_mul_mul_add_one_sub
    (commute_cfc_indicator hg c).symm ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)
  rw [Units.mul_inv, mul_one, add_sub_cancel_left] at h
  have := congrArg Matrix.det h
  rw [det_mul, det_one] at this
  exact left_ne_zero_of_mul_eq_one this

private theorem charFun_mul {g h : GL n 𝕜} (hg : Commute (g : Matrix n n 𝕜) Z)
    (hh : Commute (h : Matrix n n 𝕜) Z) :
    charFun hZ ((g : Matrix n n 𝕜) * h) = charFun hZ g + charFun hZ h := by
  simp only [charFun, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← (isIdempotentElem_cfc_indicator c).mul_add_one_sub_mul_mul_add_one_sub
      (commute_cfc_indicator hg c).symm, det_mul, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (det_cfc_indicator_mul_ne_zero hg c))
      (norm_ne_zero_iff.2 (det_cfc_indicator_mul_ne_zero hh c))]

private theorem charFun_exp {M : Matrix n n 𝕜} (hM : Commute M Z) :
    charFun hZ (NormedSpace.exp M) = RCLike.re (Z * M).trace := by
  have h (c : ℝ) : cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z * NormedSpace.exp M + 1 -
      cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z =
      NormedSpace.exp (cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z * M) :=
    ((isIdempotentElem_cfc_indicator c).exp_mul (commute_cfc_indicator hM c).symm).symm
  simp only [charFun, h, det_exp, RCLike.norm_exp, Real.log_exp]
  conv_rhs => rw [← sum_smul_cfc_indicator hZ]
  simp only [Finset.sum_mul, trace_sum, map_sum, smul_mul_assoc, trace_smul, RCLike.smul_re]

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
    refine ContinuousOn.log ?_ fun g hg ↦
      norm_ne_zero_iff.2 (det_cfc_indicator_mul_ne_zero hg c)
    exact (((continuous_const.mul Units.continuous_val).add continuous_const).sub
      continuous_const).matrix_det.norm.continuousOn
  exact hcont.preimage_isClosed_of_isClosed hC isClosed_singleton

end Character

/-! ### The Lie algebra of a closed subgroup in matrix coordinates -/

section LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {H : Subgroup (GL n 𝕜)}

/-- The Lie algebra `{Y | ∀ t, exp (t Y) ∈ H}` of a closed subgroup of `GL n 𝕜`, as a real
subspace of the matrices. -/
private def lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) : Submodule ℝ (Matrix n n 𝕜) where
  carrier := {Y | ∀ t : ℝ, TauCeti.expUnit (t • Y) ∈ H}
  zero_mem' t := by simp
  add_mem' {Y W} hY hW := by
    refine (TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hH
      (Y + W)).1 ?_
    rw [map_add]
    exact add_mem
      ((TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hH Y).2 hY)
      ((TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hH W).2 hW)
  smul_mem' c Y hY t := by simpa [smul_smul] using hY (t * c)

/-- Membership in `lieAlg` is membership in the abstract Lie algebra of `H`, read in matrix
coordinates. -/
private theorem mem_lieAlg_iff (hH : IsClosed (H : Set (GL n 𝕜))) (Y : Matrix n n 𝕜) :
    Y ∈ lieAlg hH ↔ (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm Y ∈
      TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) H :=
  (TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hH Y).symm

/-- The Lie algebra of a closed subgroup is closed under the commutator. -/
private theorem commutator_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {Y W : Matrix n n 𝕜}
    (hY : Y ∈ lieAlg hH) (hW : W ∈ lieAlg hH) : Y * W - W * Y ∈ lieAlg hH := by
  have := LieSubalgebra.lie_mem _ ((mem_lieAlg_iff hH Y).1 hY) ((mem_lieAlg_iff hH W).1 hW)
  rw [← LieEquiv.map_lie, Ring.lie_def] at this
  exact (mem_lieAlg_iff hH _).2 this

/-- A closed connected subgroup lies in every closed subgroup whose Lie algebra contains its own. -/
private theorem le_of_lieAlg_le (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {L : Subgroup (GL n 𝕜)}
    (hL : IsClosed (L : Set (GL n 𝕜))) (h : lieAlg hH ≤ lieAlg hL) : H ≤ L := by
  refine TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le (I := 𝓘(ℝ, Matrix n n 𝕜)) hH hconn hL
    fun x hx ↦ ?_
  rw [← (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm_apply_apply x] at hx ⊢
  exact (mem_lieAlg_iff hL _).1 (h ((mem_lieAlg_iff hH _).2 hx))

/-- The Lie algebra of a subgroup is invariant under conjugation by the subgroup. -/
private theorem conj_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {g : GL n 𝕜} (hg : g ∈ H)
    {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg hH) :
    (g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) ∈ lieAlg hH := fun t ↦ by
  have : TauCeti.expUnit (t • ((g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜))) =
      g * TauCeti.expUnit (t • Y) * g⁻¹ := by
    refine Units.ext ?_
    rw [TauCeti.expUnit_coe, Units.val_mul, Units.val_mul, TauCeti.expUnit_coe,
      ← Matrix.exp_units_conj, Matrix.mul_smul, Matrix.smul_mul]
  rw [this]
  exact H.mul_mem (H.mul_mem hg (hY t)) (H.inv_mem hg)

/-- The Lie algebra of a subgroup stable under the conjugate transpose is stable under it. -/
private theorem star_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg hH) :
    star Y ∈ lieAlg hH := fun t ↦ by
  have : TauCeti.expUnit (t • star Y) = star (TauCeti.expUnit (t • Y)) := by
    refine Units.ext ?_
    rw [TauCeti.expUnit_coe, Units.coe_star, TauCeti.expUnit_coe, star_eq_conjTranspose,
      star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
  rw [this]
  exact hstar _ (hY t)

end LieAlgebra

/-! ### The line through a positive element -/

section Line

variable {H : Subgroup (GL n 𝕜)}

/-- **The character argument.** Let `H` be a closed connected subgroup and `Z` a Hermitian matrix
commuting with the Lie algebra of `H` and orthogonal to it. If `exp Z ∈ H` then `Z = 0`. -/
private theorem eq_zero_of_expUnit_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)
    (hcomm : ∀ Y ∈ lieAlg hH, Commute Y Z) (horth : ∀ Y ∈ lieAlg hH, RCLike.re (Z * Y).trace = 0)
    (hZH : TauCeti.expUnit Z ∈ H) : Z = 0 := by
  have hle : H ≤ charSubgroup hZ := le_of_lieAlg_le hH hconn (isClosed_charSubgroup hZ)
    fun Y hY t ↦ ⟨by rw [TauCeti.expUnit_coe]; exact ((hcomm Y hY).smul_left t).exp_left, by
      rw [TauCeti.expUnit_coe, charFun_exp hZ ((hcomm Y hY).smul_left t), mul_smul_comm,
        trace_smul, RCLike.smul_re, horth Y hY, mul_zero]⟩
  have h := (hle hZH).2
  rw [TauCeti.expUnit_coe, charFun_exp hZ (Commute.refl Z)] at h
  refine re_trace_mul_conjTranspose_self_eq_zero_iff.1 ?_
  rwa [hZ.eq]

/-- **The line through a positive element of a closed connected group.** Let `H` be a closed
connected subgroup of `GL n 𝕜` stable under the conjugate transpose. If `exp X ∈ H` for a
Hermitian `X`, then `X` lies in the Lie algebra of `H`. -/
private theorem mem_lieAlg_of_isPreconnected (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hconn : IsPreconnected (H : Set (GL n 𝕜)))
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (hXH : TauCeti.expUnit X ∈ H) : X ∈ lieAlg hH := by
  -- Mostow's lemma: the commutator with `X` preserves the Lie algebra.
  have hXcomm (Y : Matrix n n 𝕜) (hY : Y ∈ lieAlg hH) : X * Y - Y * X ∈ lieAlg hH := by
    refine hX.commutator_mem_of_exp_mul_mul_exp_neg_mem (fun Y hY ↦ ?_) hY
    have := conj_mem_lieAlg hH hXH hY
    rwa [← TauCeti.expUnit_neg, TauCeti.expUnit_coe, TauCeti.expUnit_coe] at this
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
    have h0 := re_trace_mul_conjTranspose_self_eq_zero_iff.1
      (hAorth _ (star_mem_lieAlg hH hstar hA))
    exact (sub_eq_zero.1 h0).symm
  -- Hence `exp Z = exp (-X₁) * exp X` lies in `H`, and the character argument gives `Z = 0`.
  have hZH : TauCeti.expUnit Z ∈ H := by
    have : TauCeti.expUnit Z = (TauCeti.expUnit X₁)⁻¹ * TauCeti.expUnit (X₁ + Z) := by
      rw [← TauCeti.expUnit_neg, ← TauCeti.expUnit_add_of_commute
        ((Commute.refl X₁).neg_left.add_right (hcomm X₁ hX₁).neg_left), neg_add_cancel_left]
    rw [this]
    exact H.mul_mem (H.inv_mem (by simpa using hX₁ 1)) hXH
  rw [eq_zero_of_expUnit_mem hH hconn hZ hcomm horth hZH, add_zero]
  exact hX₁

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
    (hX : X.IsHermitian) (hXH : TauCeti.expUnit X ∈ H) : X ∈ lieAlg hH := by
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
  obtain ⟨m, hm, hmem⟩ :=
    TauCeti.exists_pow_mem_connectedComponentOfOne (⟨TauCeti.expUnit X, hXH⟩ : H)
  have hpow : TauCeti.expUnit ((m : ℝ) • X) ∈ identityComponent H := by
    have : TauCeti.expUnit ((m : ℝ) • X) = TauCeti.expUnit X ^ m := by
      refine Units.ext ?_
      rw [TauCeti.expUnit_coe, Units.val_pow_eq_pow_val, TauCeti.expUnit_coe,
        Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
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
  have hXH : TauCeti.expUnit X ∈ H := by
    convert hg
    exact Units.ext (by rw [TauCeti.expUnit_coe, hgX])
  exact ⟨_, mem_lieAlg_of_finite hH hstar hfin hX hXH t, TauCeti.expUnit_coe _⟩

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
  simp [cartanHomeomorphOfIsClosed]

/-- The unitary factor of the Cartan decomposition of `g ∈ H` is the polar unitary factor of
`g`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_fst (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    (((cartanHomeomorphOfIsClosed H hH hstar hfin).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary := by
  simp [cartanHomeomorphOfIsClosed]

/-- The Hermitian factor of the Cartan decomposition of `g ∈ H` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_snd (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((cartanHomeomorphOfIsClosed H hH hstar hfin).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  simp [cartanHomeomorphOfIsClosed, CFC.log]

/-- **The global Cartan decomposition** `H = K_H exp 𝔭_H` of a closed subgroup `H` of `GL n 𝕜`
stable under the conjugate transpose, with finitely many connected components: every `g ∈ H`
factors uniquely as `k * exp X` with `k` a unitary element of `H` and `X` a Hermitian matrix with
`exp (t X) ∈ H` for every real `t`. -/
theorem existsUnique_unitary_mul_exp_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
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
