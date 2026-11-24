/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.FunctionalCalculus
import TauCeti.Analysis.Matrix.Exponential.Mostow
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Geometry.Lie.Exponential.Units.Basic
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

* `Subgroup.exists_mem_coe_eq_exp_smul_of_isClosed`: the line through a positive element `exp X` of
  `H` lies in `H`; `Subgroup.exists_mem_coe_eq_exp_smul_of_pow_mem_connectedComponentOfOne` needs
  only a positive power of `exp X` in the identity component instead of finitely many components.
* `Subgroup.toUnits_polarUnitary_mem_of_isClosed` and
  `Subgroup.mul_inv_toUnits_polarUnitary_mem_of_isClosed`: the unitary and positive polar factors
  of an element of `H` lie in `H`.
* `Subgroup.cartanHomeomorphOfIsClosed`: the homeomorphism `K_H × 𝔭_H ≃ₜ H`,
  `(k, X) ↦ k * exp X`, with `val_cartanHomeomorphOfIsClosed_apply`.
* `Subgroup.existsUnique_unitary_mul_exp_of_isClosed`: every `g ∈ H` is uniquely `k * exp X` with
  `k ∈ K_H` and `X ∈ 𝔭_H`.
* `Subgroup.maximal_isCompact_unitarySubgroup_subgroupOf_of_isClosed`: `K_H` is a maximal compact
  subgroup of `H`.

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


/-! In the rest of the file, `Matrix n n 𝕜` carries the `ℓ²` operator norm, a complete normed
`ℝ`-algebra, so that its group of units has the Lie group structure and exponential of
`TauCeti.expUnit`. -/

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### A character of the centralizer of a Hermitian matrix -/

section Character

variable {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)

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
      cfc (Set.indicator {c} (1 : ℝ → ℝ)) Z).det ≠ 0 :=
  ((isUnit_iff_isUnit_det _).1 ((isIdempotentElem_cfc_indicator (Z := Z) c).isUnit_mul_add_one_sub
    g.isUnit (commute_cfc_indicator hg c).symm)).ne_zero

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
  conv_rhs => rw [← hZ.sum_smul_cfc_indicator]
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
    simp only [charFun]
    refine continuousOn_finsetSum _ fun c _ ↦ ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log ?_ fun g hg ↦
      norm_ne_zero_iff.2 (det_cfc_indicator_mul_ne_zero hg c)
    exact (((continuous_const.mul Units.continuous_val).add continuous_const).sub
      continuous_const).matrix_det.norm.continuousOn
  exact hcont.preimage_isClosed_of_isClosed hC isClosed_singleton

end Character

/-! ### The Lie algebra of a closed subgroup in matrix coordinates -/

section LieAlgebra

variable {H : Subgroup (GL n 𝕜)}

/-- The Lie algebra of a subgroup of `GL n 𝕜` in matrix coordinates. -/
private abbrev lieAlg (H : Subgroup (GL n 𝕜)) : LieSubalgebra ℝ (Matrix n n 𝕜) :=
  TauCeti.Lie.unitsLieSubalgebraOfSubgroup H

/-- For a closed subgroup, the Lie algebra is `{Y | ∀ t, exp (t Y) ∈ H}`. -/
private theorem mem_lieAlg_iff (hH : IsClosed (H : Set (GL n 𝕜))) {Y : Matrix n n 𝕜} :
    Y ∈ lieAlg H ↔ ∀ t : ℝ, TauCeti.expUnit (t • Y) ∈ H :=
  TauCeti.Lie.mem_unitsLieSubalgebraOfSubgroup_iff hH Y

/-- The Lie algebra of a subgroup is closed under the commutator. -/
private theorem commutator_mem_lieAlg {Y W : Matrix n n 𝕜} (hY : Y ∈ lieAlg H)
    (hW : W ∈ lieAlg H) : Y * W - W * Y ∈ lieAlg H := by
  simpa only [Ring.lie_def] using (lieAlg H).lie_mem hY hW

/-- A closed connected subgroup lies in every closed subgroup whose Lie algebra contains its own. -/
private theorem le_of_lieAlg_le (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {L : Subgroup (GL n 𝕜)}
    (hL : IsClosed (L : Set (GL n 𝕜))) (h : lieAlg H ≤ lieAlg L) : H ≤ L := by
  refine TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le (I := 𝓘(ℝ, Matrix n n 𝕜)) hH hconn hL
    fun x hx ↦ ?_
  rw [← (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm_apply_apply x] at hx ⊢
  exact (TauCeti.Lie.mem_unitsLieSubalgebraOfSubgroup L _).1
    (h ((TauCeti.Lie.mem_unitsLieSubalgebraOfSubgroup H _).2 hx))

/-- The unit exponential commutes with conjugation by a unit. -/
private theorem expUnit_units_conj (g : GL n 𝕜) (Y : Matrix n n 𝕜) :
    TauCeti.expUnit ((g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)) =
      g * TauCeti.expUnit Y * g⁻¹ :=
  Units.ext <| by
    rw [TauCeti.expUnit_coe, Units.val_mul, Units.val_mul, TauCeti.expUnit_coe,
      Matrix.exp_units_conj]

/-- The unit exponential commutes with the conjugate transpose. -/
private theorem expUnit_star (Y : Matrix n n 𝕜) :
    TauCeti.expUnit (star Y) = star (TauCeti.expUnit Y) :=
  Units.ext <| by
    rw [TauCeti.expUnit_coe, Units.coe_star, TauCeti.expUnit_coe, star_eq_conjTranspose,
      star_eq_conjTranspose, Matrix.exp_conjTranspose]

/-- The Lie algebra of a subgroup is invariant under conjugation by the subgroup. -/
private theorem conj_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜))) {g : GL n 𝕜} (hg : g ∈ H)
    {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg H) :
    (g : Matrix n n 𝕜) * Y * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) ∈ lieAlg H := by
  rw [mem_lieAlg_iff hH] at hY ⊢
  intro t
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, expUnit_units_conj]
  exact H.mul_mem (H.mul_mem hg (hY t)) (H.inv_mem hg)

/-- The Lie algebra of a subgroup stable under the conjugate transpose is stable under it. -/
private theorem star_mem_lieAlg (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) {Y : Matrix n n 𝕜} (hY : Y ∈ lieAlg H) :
    star Y ∈ lieAlg H := by
  rw [mem_lieAlg_iff hH] at hY ⊢
  intro t
  rw [← star_trivial t, ← star_smul, expUnit_star]
  exact hstar _ (hY t)

end LieAlgebra

/-! ### The line through a positive element -/

section Line

variable {H : Subgroup (GL n 𝕜)}

/-- **The character argument.** Let `H` be a closed connected subgroup and `Z` a Hermitian matrix
commuting with the Lie algebra of `H` and orthogonal to it. If `exp Z ∈ H` then `Z = 0`. -/
private theorem eq_zero_of_expUnit_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)
    (hcomm : ∀ Y ∈ lieAlg H, Commute Y Z) (horth : ∀ Y ∈ lieAlg H, RCLike.re (Z * Y).trace = 0)
    (hZH : TauCeti.expUnit Z ∈ H) : Z = 0 := by
  have hle : H ≤ charSubgroup hZ := le_of_lieAlg_le hH hconn (isClosed_charSubgroup hZ)
    fun Y hY ↦ (mem_lieAlg_iff (isClosed_charSubgroup hZ)).2 fun t ↦
      ⟨by rw [TauCeti.expUnit_coe]; exact ((hcomm Y hY).smul_left t).exp_left, by
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
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (hXH : TauCeti.expUnit X ∈ H) : X ∈ lieAlg H := by
  -- Mostow's lemma: the commutator with `X` preserves the Lie algebra.
  have hXcomm (Y : Matrix n n 𝕜) (hY : Y ∈ (lieAlg H).toSubmodule) :
      X * Y - Y * X ∈ (lieAlg H).toSubmodule := by
    refine hX.commutator_mem_of_exp_mul_mul_exp_neg_mem (fun Y hY ↦ ?_) hY
    have := conj_mem_lieAlg hH hXH hY
    rwa [← TauCeti.expUnit_neg, TauCeti.expUnit_coe, TauCeti.expUnit_coe] at this
  obtain ⟨X₁, hX₁, -, Z, hZ, rfl, horth⟩ :=
    hX.exists_add_orthogonal (V := (lieAlg H).toSubmodule) fun _ ↦ star_mem_lieAlg hH hstar
  -- `Z` commutes with the Lie algebra: the commutator lies in it and is orthogonal to it.
  have hcomm (Y : Matrix n n 𝕜) (hY : Y ∈ lieAlg H) : Commute Y Z := by
    set A := Z * Y - Y * Z
    have hA : A ∈ lieAlg H := by
      have := (lieAlg H).sub_mem (hXcomm Y hY) (commutator_mem_lieAlg hX₁ hY)
      convert this using 1
      simp only [A]
      noncomm_ring
    -- Cyclicity of the trace moves the commutator with `Y` from `Z` to `W`.
    have htr (W : Matrix n n 𝕜) : (A * W).trace = (Z * (Y * W - W * Y)).trace := by
      simp only [A, Matrix.sub_mul, Matrix.mul_sub, trace_sub, Matrix.mul_assoc]
      rw [trace_mul_comm Y, Matrix.mul_assoc]
    have hAorth (W : Matrix n n 𝕜) (hW : W ∈ lieAlg H) : RCLike.re (A * W).trace = 0 := by
      rw [htr]
      exact horth _ (commutator_mem_lieAlg hY hW)
    have h0 := re_trace_mul_conjTranspose_self_eq_zero_iff.1
      (hAorth _ (star_mem_lieAlg hH hstar hA))
    exact (sub_eq_zero.1 h0).symm
  -- Hence `exp Z = exp (-X₁) * exp X` lies in `H`, and the character argument gives `Z = 0`.
  have hZH : TauCeti.expUnit Z ∈ H := by
    have : TauCeti.expUnit Z = (TauCeti.expUnit X₁)⁻¹ * TauCeti.expUnit (X₁ + Z) := by
      rw [← TauCeti.expUnit_neg, ← TauCeti.expUnit_add_of_commute
        ((Commute.refl X₁).neg_left.add_right (hcomm X₁ hX₁).neg_left), neg_add_cancel_left]
    rw [this]
    exact H.mul_mem (H.inv_mem (by simpa using (mem_lieAlg_iff hH).1 hX₁ 1)) hXH
  rw [eq_zero_of_expUnit_mem hH hconn hZ hcomm horth hZH, add_zero]
  exact hX₁

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜` stable
under the conjugate transpose. If `exp X ∈ H` for a Hermitian `X` and some positive power of
`exp X` lies in the identity component of `H`, then `X` lies in the Lie algebra of `H`. -/
private theorem mem_lieAlg_of_pow_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    (hXH : TauCeti.expUnit X ∈ H)
    (hm : ∃ m : ℕ, 0 < m ∧
      (⟨TauCeti.expUnit X, hXH⟩ : H) ^ m ∈ Subgroup.connectedComponentOfOne H) :
    X ∈ lieAlg H := by
  -- Pass to the identity component, which is closed, connected and stable under `star`.
  set H₀ := H.ambientConnectedComponentOfOne
  have hstar₀ (g : GL n 𝕜) (hg : g ∈ H₀) : star g ∈ H₀ := by
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_ambientConnectedComponentOfOne.1 hg
    let f : H → H := fun h ↦ ⟨star (h : GL n 𝕜), hstar _ h.property⟩
    have hf : Continuous f := (continuous_star.comp continuous_subtypeVal).subtype_mk _
    have hsub := hf.image_connectedComponent_subset (1 : H)
    have hf1 : f 1 = 1 := Subtype.ext (star_one _)
    rw [hf1] at hsub
    exact Subgroup.mem_ambientConnectedComponentOfOne.2 ⟨f h, hsub ⟨h, hh, rfl⟩, rfl⟩
  obtain ⟨m, hm, hmem⟩ := hm
  -- `exp (m X) = (exp X) ^ m` lies in the identity component.
  have hpow : TauCeti.expUnit ((m : ℝ) • X) ∈ H₀ := by
    have h := map_pow (TauCeti.expUnitHom X) (Multiplicative.ofAdd (1 : ℝ)) m
    rw [← ofAdd_nsmul, TauCeti.expUnitHom_apply, TauCeti.expUnitHom_apply, one_smul,
      nsmul_one] at h
    rw [h]
    exact Subgroup.mem_ambientConnectedComponentOfOne.2 ⟨_, hmem, rfl⟩
  have hmX : ((m : ℝ) • X).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, star_trivial, hX.eq]
  have h := (mem_lieAlg_iff (H.isClosed_ambientConnectedComponentOfOne hH)).1
    (mem_lieAlg_of_isPreconnected (H.isClosed_ambientConnectedComponentOfOne hH) hstar₀
      H.isPreconnected_ambientConnectedComponentOfOne hmX hpow)
  refine (mem_lieAlg_iff hH).2 fun t ↦ ?_
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have := H.ambientConnectedComponentOfOne_le (h (t / m))
  rwa [smul_smul, div_mul_cancel₀ t hm'] at this

end Line

end Matrix.GeneralLinearGroup

/-! ### The Cartan decomposition -/

namespace Subgroup

open Matrix Matrix.GeneralLinearGroup

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {H : Subgroup (GL n 𝕜)}

/-- A unit of `H` whose matrix is `exp x` is the unit exponential of `x`. -/
private theorem expUnit_mem_of_coe_eq {x : Matrix n n 𝕜} {g : GL n 𝕜} (hg : g ∈ H)
    (hgx : (g : Matrix n n 𝕜) = NormedSpace.exp x) : TauCeti.expUnit x ∈ H := by
  have h : g = TauCeti.expUnit x := Units.ext (by rw [TauCeti.expUnit_coe, hgx])
  rwa [← h]

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜`, for
`𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose. If `H` contains `g = exp X` for a Hermitian
matrix `X`, and some positive power of `g` lies in the identity component of `H`, then `H`
contains `exp (t X)` for every real `t`. -/
theorem exists_mem_coe_eq_exp_smul_of_pow_mem_connectedComponentOfOne
    (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) {g : GL n 𝕜} (hg : g ∈ H) (hgX : (g : Matrix n n 𝕜) = NormedSpace.exp X)
    (hm : ∃ m : ℕ, 0 < m ∧ (⟨g, hg⟩ : H) ^ m ∈ Subgroup.connectedComponentOfOne H) (t : ℝ) :
    ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X) := by
  obtain rfl : g = TauCeti.expUnit X := Units.ext (by rw [TauCeti.expUnit_coe, hgX])
  exact ⟨_, (mem_lieAlg_iff hH).1 (mem_lieAlg_of_pow_mem hH hstar hX hg hm) t,
    TauCeti.expUnit_coe _⟩

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜`, for
`𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose and with finitely many connected components.
If `H` contains `exp X` for a Hermitian matrix `X`, then it contains `exp (t X)` for every real
`t`. -/
theorem exists_mem_coe_eq_exp_smul_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) {g : GL n 𝕜} (hg : g ∈ H) (hgX : (g : Matrix n n 𝕜) = NormedSpace.exp X)
    (t : ℝ) : ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X) :=
  haveI := hfin
  exists_mem_coe_eq_exp_smul_of_pow_mem_connectedComponentOfOne hH hstar hX hg hgX
    (TauCeti.exists_pow_mem_connectedComponentOfOne _) t

variable (H) in
/-- **The Cartan decomposition of a closed matrix group stable under the conjugate transpose.**
Let `H` be a closed subgroup of `GL n 𝕜`, for `𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose
and with finitely many connected components. Then `(k, X) ↦ k * exp X` is a homeomorphism from the
product of the unitary elements `K_H` of `H` (the orthogonal ones when `𝕜 = ℝ`) and the Hermitian
part `𝔭_H` of the Lie algebra of `H`, the Hermitian `X` with `exp (t X) ∈ H` for all real `t`, onto
`H`.

It is `Subgroup.cartanHomeomorph`, whose line hypothesis is
`Subgroup.exists_mem_coe_eq_exp_smul_of_isClosed`, with the domain `𝔭_H` written through the
matrix exponential, so that the statement does not depend on a choice of norm on matrices. -/
def cartanHomeomorphOfIsClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) :
    {k : unitaryGroup n 𝕜 // Unitary.toUnits k ∈ H} ×
        {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
          ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))} ≃ₜ H := by
  have hline (x : Matrix n n 𝕜) : (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ H) ↔
      ∀ t : ℝ, ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • x) := by
    refine ⟨fun h t ↦ ⟨_, h t, TauCeti.expUnit_coe _⟩, fun h t ↦ ?_⟩
    obtain ⟨g, hg, hgx⟩ := h t
    exact expUnit_mem_of_coe_eq hg hgx
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
    ((H.cartanHomeomorphOfIsClosed hH hstar hfin p : GL n 𝕜) : Matrix n n 𝕜) =
      (p.1 : Matrix n n 𝕜) *
        NormedSpace.exp ((p.2 : selfAdjoint (Matrix n n 𝕜)) : Matrix n n 𝕜) := by
  rw [cartanHomeomorphOfIsClosed, Homeomorph.trans_apply, Subgroup.val_cartanHomeomorph_apply]
  rfl

/-- The unitary factor of the Cartan decomposition of `g ∈ H` is the polar unitary factor of
`g`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_fst (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    (((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary := by
  rw [cartanHomeomorphOfIsClosed, Homeomorph.symm_trans_apply]
  exact Subgroup.coe_cartanHomeomorph_symm_apply_fst _ _ g

/-- The Hermitian factor of the Cartan decomposition of `g ∈ H` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_snd (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  rw [cartanHomeomorphOfIsClosed, Homeomorph.symm_trans_apply]
  exact Subgroup.coe_cartanHomeomorph_symm_apply_snd _ _ g

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
  refine (existsUnique_congr fun p ↦ ?_).1
    ((H.cartanHomeomorphOfIsClosed hH hstar hfin).bijective.existsUnique ⟨g, hg⟩)
  rw [Subtype.ext_iff, Units.ext_iff, val_cartanHomeomorphOfIsClosed_apply, eq_comm]

/-- The unitary polar factor of an element of a closed subgroup `H` of `GL n 𝕜` stable under the
conjugate transpose, with finitely many connected components, lies in `H`. -/
theorem toUnits_polarUnitary_mem_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {g : GL n 𝕜}
    (hg : g ∈ H) : Unitary.toUnits g.polarUnitary ∈ H := by
  have h := ((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm ⟨g, hg⟩).1.property
  rwa [coe_cartanHomeomorphOfIsClosed_symm_apply_fst] at h

/-- The positive polar factor `g u⁻¹` of an element `g = (g u⁻¹) u` of a closed subgroup `H` of
`GL n 𝕜` stable under the conjugate transpose, with finitely many connected components, lies in
`H`; its matrix is `√(g gᴴ)` (`Matrix.GeneralLinearGroup.coe_mul_inv_toUnits_polarUnitary`). -/
theorem mul_inv_toUnits_polarUnitary_mem_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {g : GL n 𝕜}
    (hg : g ∈ H) : g * (Unitary.toUnits g.polarUnitary)⁻¹ ∈ H :=
  H.mul_mem hg (H.inv_mem (toUnits_polarUnitary_mem_of_isClosed hH hstar hfin hg))

/-- **The unitary elements form a maximal compact subgroup** of a closed subgroup `H` of
`GL n 𝕜` stable under the conjugate transpose, with finitely many connected components. -/
theorem maximal_isCompact_unitarySubgroup_subgroupOf_of_isClosed
    (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H)
    (hfin : Finite (ConnectedComponents H)) :
    Maximal (fun K : Subgroup H ↦ IsCompact (K : Set H))
      ((unitarySubgroup (GL n 𝕜)).subgroupOf H) :=
  maximal_isCompact_unitarySubgroup_subgroupOf
    (fun _ hg ↦ toUnits_polarUnitary_mem_of_isClosed hH hstar hfin hg) hH

end Subgroup
