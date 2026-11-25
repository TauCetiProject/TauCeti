/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Cartan.Basic
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Algebra.Group.Submonoid.Units
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.FunctionalCalculus
import TauCeti.Analysis.Matrix.Exponential.Mostow
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Geometry.Lie.Exponential.Units.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
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
* `Subgroup.toUnits_polarUnitary_mem_of_isClosed`,
  `Subgroup.inv_toUnits_polarUnitary_mul_mem_of_isClosed` and
  `Subgroup.mul_inv_toUnits_polarUnitary_mem_of_isClosed`: the unitary and positive polar factors
  of an element of `H` lie in `H`.
* `Subgroup.forall_exists_mem_coe_eq_exp_smul_iff_mem_linearLieSubalgebra`: the Hermitian part
  `𝔭_H` is the Hermitian part of the Lie algebra `Subgroup.linearLieSubalgebra H`.
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

open scoped MatrixOrder

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
  (isUnit_det_mul_add_one_sub (isIdempotentElem_cfc_indicator (Z := Z) c) g.isUnit
    (commute_cfc_indicator hg c).symm).ne_zero

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

/-- The character `charFun` vanishes at the identity. -/
private theorem charFun_one : charFun hZ 1 = 0 := by
  simp only [charFun, Matrix.mul_one, add_sub_cancel_left, det_one, norm_one, Real.log_one,
    mul_zero, Finset.sum_const_zero]

/-- The character `charFun` on the units of the centralizer of `Z`, as a homomorphism to
`Multiplicative ℝ`. -/
private def charHom : (Submonoid.centralizer {Z}).units →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (charFun hZ (g : GL n 𝕜))
  map_one' := by rw [OneMemClass.coe_one, Units.val_one, charFun_one, ofAdd_zero]
  map_mul' g h := by
    rw [← ofAdd_add, ← charFun_mul hZ (Submonoid.mem_units_centralizer_singleton_iff.1 g.property)
      (Submonoid.mem_units_centralizer_singleton_iff.1 h.property), Subgroup.coe_mul, Units.val_mul]

/-- The kernel of the character `charFun` on the centralizer of `Z`, as a subgroup of
`GL n 𝕜`. -/
private def charSubgroup : Subgroup (GL n 𝕜) :=
  (charHom hZ).ker.map (Submonoid.centralizer {Z}).units.subtype

private theorem mem_charSubgroup {g : GL n 𝕜} :
    g ∈ charSubgroup hZ ↔ Commute (g : Matrix n n 𝕜) Z ∧ charFun hZ g = 0 := by
  simp only [charSubgroup, Subgroup.mem_map, MonoidHom.mem_ker, charHom, MonoidHom.coe_mk,
    OneHom.coe_mk, ofAdd_eq_one, Subgroup.coe_subtype]
  refine ⟨?_, fun h ↦ ⟨⟨g, Submonoid.mem_units_centralizer_singleton_iff.2 h.1⟩, h.2, rfl⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨Submonoid.mem_units_centralizer_singleton_iff.1 x.property, hx⟩

private theorem isClosed_charSubgroup : IsClosed (charSubgroup hZ : Set (GL n 𝕜)) := by
  -- Commuting with `Z` is the preimage of the centralizer of `{Z}`, which is closed.
  have hC : IsClosed {g : GL n 𝕜 | Commute (g : Matrix n n 𝕜) Z} := by
    convert (Set.isClosed_centralizer {Z}).preimage Units.continuous_val using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  have hcont : ContinuousOn (fun g : GL n 𝕜 ↦ charFun hZ g)
      {g : GL n 𝕜 | Commute (g : Matrix n n 𝕜) Z} := by
    simp only [charFun]
    refine continuousOn_finsetSum _ fun c _ ↦ ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log ?_ fun g hg ↦
      norm_ne_zero_iff.2 (det_cfc_indicator_mul_ne_zero hg c)
    exact (((continuous_const.mul Units.continuous_val).add continuous_const).sub
      continuous_const).matrix_det.norm.continuousOn
  have hset : (charSubgroup hZ : Set (GL n 𝕜)) =
      {g : GL n 𝕜 | Commute (g : Matrix n n 𝕜) Z} ∩ (fun g : GL n 𝕜 ↦ charFun hZ g) ⁻¹' {0} :=
    Set.ext fun _ ↦ mem_charSubgroup hZ
  rw [hset]
  exact hcont.preimage_isClosed_of_isClosed hC isClosed_singleton

end Character

/-! ### The Lie algebra of a closed subgroup in matrix coordinates -/

section LieAlgebra

variable {H : Subgroup (GL n 𝕜)}

/-- The Lie algebra of a subgroup is closed under the commutator. -/
private theorem commutator_mem_lieAlg {Y W : Matrix n n 𝕜}
    (hY : Y ∈ H.linearLieSubalgebra) (hW : W ∈ H.linearLieSubalgebra) :
    Y * W - W * Y ∈ H.linearLieSubalgebra := by
  simpa only [Ring.lie_def] using H.linearLieSubalgebra.lie_mem hY hW

end LieAlgebra

/-! ### The line through a positive element -/

section Line

variable {H : Subgroup (GL n 𝕜)}

/-- **The character argument.** Let `H` be a closed connected subgroup and `Z` a Hermitian matrix
commuting with the Lie algebra of `H` and orthogonal to it. If `exp Z ∈ H` then `Z = 0`. -/
private theorem eq_zero_of_expUnit_mem (hH : IsClosed (H : Set (GL n 𝕜)))
    (hconn : IsPreconnected (H : Set (GL n 𝕜))) {Z : Matrix n n 𝕜} (hZ : Z.IsHermitian)
    (hcomm : ∀ Y ∈ H.linearLieSubalgebra, Commute Y Z)
    (horth : ∀ Y ∈ H.linearLieSubalgebra, RCLike.re (Z * Y).trace = 0)
    (hZH : TauCeti.expUnit Z ∈ H) : Z = 0 := by
  have hle : H ≤ charSubgroup hZ :=
    Subgroup.le_of_linearLieSubalgebra_le hH hconn (isClosed_charSubgroup hZ) fun Y hY ↦
      (Subgroup.mem_linearLieSubalgebra_iff (isClosed_charSubgroup hZ)).2 <|
        Subgroup.mem_linearLieAlgebra_iff.2 fun t ↦
        (mem_charSubgroup hZ).2
          ⟨by rw [TauCeti.expUnit_coe]; exact ((hcomm Y hY).smul_left t).exp_left, by
            rw [TauCeti.expUnit_coe, charFun_exp hZ ((hcomm Y hY).smul_left t), mul_smul_comm,
              trace_smul, RCLike.smul_re, horth Y hY, mul_zero]⟩
  have h := ((mem_charSubgroup hZ).1 (hle hZH)).2
  rw [TauCeti.expUnit_coe, charFun_exp hZ (Commute.refl Z)] at h
  refine re_trace_mul_conjTranspose_self_eq_zero_iff.1 ?_
  rwa [hZ.eq]

/-- **The line through a positive element of a closed connected group.** Let `H` be a closed
connected subgroup of `GL n 𝕜` stable under the conjugate transpose. If `exp X ∈ H` for a
Hermitian `X`, then `X` lies in the Lie algebra of `H`. -/
private theorem mem_lieAlg_of_isPreconnected (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hconn : IsPreconnected (H : Set (GL n 𝕜)))
    {X : Matrix n n 𝕜} (hX : X.IsHermitian) (hXH : TauCeti.expUnit X ∈ H) :
    X ∈ H.linearLieSubalgebra := by
  -- Mostow's lemma: the commutator with `X` preserves the Lie algebra.
  have hXcomm (Y : Matrix n n 𝕜) (hY : Y ∈ H.linearLieSubalgebra.toSubmodule) :
      X * Y - Y * X ∈ H.linearLieSubalgebra.toSubmodule := by
    refine hX.commutator_mem_of_exp_mul_mul_exp_neg_mem (fun Y hY ↦ ?_) hY
    have := H.conj_mem_linearLieSubalgebra hXH hY
    rwa [← TauCeti.expUnit_neg, TauCeti.expUnit_coe, TauCeti.expUnit_coe] at this
  obtain ⟨X₁, hX₁, -, Z, hZ, rfl, horth⟩ :=
    hX.exists_add_orthogonal (V := H.linearLieSubalgebra.toSubmodule) fun _ ↦
      Subgroup.star_mem_linearLieSubalgebra hH hstar
  -- `Z` commutes with the Lie algebra: the commutator lies in it and is orthogonal to it.
  have hcomm (Y : Matrix n n 𝕜) (hY : Y ∈ H.linearLieSubalgebra) : Commute Y Z := by
    set A := Z * Y - Y * Z
    have hA : A ∈ H.linearLieSubalgebra := by
      have :=
        H.linearLieSubalgebra.sub_mem (hXcomm Y hY) (commutator_mem_lieAlg hX₁ hY)
      convert this using 1
      simp only [A]
      noncomm_ring
    -- Cyclicity of the trace moves the commutator with `Y` from `Z` to `W`.
    have htr (W : Matrix n n 𝕜) : (A * W).trace = (Z * (Y * W - W * Y)).trace := by
      simp only [A, Matrix.sub_mul, Matrix.mul_sub, trace_sub, Matrix.mul_assoc]
      rw [trace_mul_comm Y, Matrix.mul_assoc]
    have hAorth (W : Matrix n n 𝕜) (hW : W ∈ H.linearLieSubalgebra) :
        RCLike.re (A * W).trace = 0 := by
      rw [htr]
      exact horth _ (commutator_mem_lieAlg hY hW)
    have h0 := re_trace_mul_conjTranspose_self_eq_zero_iff.1
      (hAorth _ (Subgroup.star_mem_linearLieSubalgebra hH hstar hA))
    exact (sub_eq_zero.1 h0).symm
  -- Hence `exp Z = exp (-X₁) * exp X` lies in `H`, and the character argument gives `Z = 0`.
  have hZH : TauCeti.expUnit Z ∈ H := by
    have : TauCeti.expUnit Z = (TauCeti.expUnit X₁)⁻¹ * TauCeti.expUnit (X₁ + Z) := by
      rw [← TauCeti.expUnit_neg, ← TauCeti.expUnit_add_of_commute
        ((Commute.refl X₁).neg_left.add_right (hcomm X₁ hX₁).neg_left), neg_add_cancel_left]
    rw [this]
    have hX₁H := Subgroup.mem_linearLieAlgebra_iff.1 ((H.mem_linearLieSubalgebra_iff hH).1 hX₁) 1
    rw [one_smul] at hX₁H
    exact H.mul_mem (H.inv_mem hX₁H) hXH
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
    X ∈ H.linearLieSubalgebra := by
  -- Pass to the identity component, which is closed, connected and stable under `star`.
  set H₀ := H.ambientConnectedComponentOfOne
  have hstar₀ (g : GL n 𝕜) (hg : g ∈ H₀) : star g ∈ H₀ :=
    H.mapsTo_ambientConnectedComponentOfOne continuous_star (fun g hg ↦ hstar g hg) (star_one _)
      hg
  obtain ⟨m, hm, hmem⟩ := hm
  -- `exp (m X) = (exp X) ^ m` lies in the identity component.
  have hpow : TauCeti.expUnit ((m : ℝ) • X) ∈ H₀ := by
    rw [TauCeti.expUnit_natCast_smul]
    exact Subgroup.mem_ambientConnectedComponentOfOne.2 ⟨_, hmem, rfl⟩
  have hmX : ((m : ℝ) • X).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, star_trivial, hX.eq]
  have h :=
    (Subgroup.mem_linearLieSubalgebra_iff (H.isClosed_ambientConnectedComponentOfOne hH)).1
    (mem_lieAlg_of_isPreconnected (H.isClosed_ambientConnectedComponentOfOne hH) hstar₀
      H.isPreconnected_ambientConnectedComponentOfOne hmX hpow)
  refine (H.mem_linearLieSubalgebra_iff hH).2 <| Subgroup.mem_linearLieAlgebra_iff.2 fun t ↦ ?_
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have := H.ambientConnectedComponentOfOne_le (Subgroup.mem_linearLieAlgebra_iff.1 h (t / m))
  rwa [smul_smul, div_mul_cancel₀ t hm'] at this

end Line

end Matrix.GeneralLinearGroup

/-! ### The Cartan decomposition -/

namespace Subgroup

open Matrix Matrix.GeneralLinearGroup

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal TauCeti.normedAlgebraRatOfReal

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {H : Subgroup (GL n 𝕜)}

/-- A unit whose matrix is `exp x` is the unit exponential of `x`. -/
private theorem eq_expUnit_of_coe_eq {x : Matrix n n 𝕜} {g : GL n 𝕜}
    (hgx : (g : Matrix n n 𝕜) = NormedSpace.exp x) : g = TauCeti.expUnit x :=
  Units.ext (by rw [TauCeti.expUnit_coe, hgx])

/-- **The line through a positive element.** Let `H` be a closed subgroup of `GL n 𝕜`, for
`𝕜 = ℝ` or `ℂ`, stable under the conjugate transpose. If `H` contains `g = exp X` for a Hermitian
matrix `X`, and some positive power of `g` lies in the identity component of `H`, then `H`
contains `exp (t X)` for every real `t`. -/
theorem exists_mem_coe_eq_exp_smul_of_pow_mem_connectedComponentOfOne
    (hH : IsClosed (H : Set (GL n 𝕜))) (hstar : ∀ g ∈ H, star g ∈ H) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) {g : GL n 𝕜} (hg : g ∈ H) (hgX : (g : Matrix n n 𝕜) = NormedSpace.exp X)
    (hm : ∃ m : ℕ, 0 < m ∧ (⟨g, hg⟩ : H) ^ m ∈ Subgroup.connectedComponentOfOne H) (t : ℝ) :
    ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X) := by
  obtain rfl := eq_expUnit_of_coe_eq hgX
  exact H.mem_linearLieAlgebra_iff_forall_exp.1
    ((H.mem_linearLieSubalgebra_iff hH).1 (mem_lieAlg_of_pow_mem hH hstar hX hg hm)) t

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

/-- The exponential-line condition of the domain of `Subgroup.cartanHomeomorphOfIsClosed`, written
through the matrix exponential, is membership in the Lie algebra
`Subgroup.linearLieSubalgebra H` of a closed subgroup `H` of `GL n 𝕜`, for the
`ℓ²` operator norm on matrices. -/
theorem forall_exists_mem_coe_eq_exp_smul_iff_mem_linearLieSubalgebra
    (hH : IsClosed (H : Set (GL n 𝕜))) (X : Matrix n n 𝕜) :
    (∀ t : ℝ, ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • X)) ↔
      X ∈ H.linearLieSubalgebra := by
  rw [H.mem_linearLieSubalgebra_iff hH, mem_linearLieAlgebra_iff_forall_exp]

/-- For a closed subgroup `H` of `GL n 𝕜` stable under the conjugate transpose and with finitely
many connected components, the line through a Hermitian `x` with `exp x ∈ H` lies in `H`: the line
hypothesis of `Subgroup.cartanHomeomorph`. -/
private theorem expUnit_smul_mem_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (x : Matrix n n 𝕜)
    (hx : IsSelfAdjoint x) (hxH : TauCeti.expUnit x ∈ H) (t : ℝ) :
    TauCeti.expUnit (t • x) ∈ H :=
  mem_linearLieAlgebra_iff.1 (mem_linearLieAlgebra_iff_forall_exp.2
    (exists_mem_coe_eq_exp_smul_of_isClosed hH hstar hfin hx.isHermitian hxH
      (TauCeti.expUnit_coe x))) t

/-- The Hermitian factor domain of `Subgroup.cartanHomeomorphOfIsClosed`, written through the
matrix exponential, is the domain of `Subgroup.cartanHomeomorph`, written through the unit
exponential. -/
private def lineDomainHomeomorph (H : Subgroup (GL n 𝕜)) :
    {X : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ,
        ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))} ≃ₜ
      {x : selfAdjoint (Matrix n n 𝕜) // ∀ t : ℝ, TauCeti.expUnit (t • (x : Matrix n n 𝕜)) ∈ H} :=
  (Homeomorph.refl _).subtype fun _ ↦
    mem_linearLieAlgebra_iff_forall_exp.symm.trans mem_linearLieAlgebra_iff

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
          ∃ h ∈ H, (h : Matrix n n 𝕜) = NormedSpace.exp (t • (X : Matrix n n 𝕜))} ≃ₜ H :=
  ((Homeomorph.refl _).prodCongr (lineDomainHomeomorph H)).trans
    (H.cartanHomeomorph hstar (expUnit_smul_mem_of_isClosed hH hstar hfin))

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
  rw [cartanHomeomorphOfIsClosed, Homeomorph.trans_apply, Subgroup.val_cartanHomeomorph_apply,
    Homeomorph.coe_prodCongr, Prod.map_fst, Prod.map_snd, Homeomorph.refl_apply, id_eq]
  -- The second factor of `cartanHomeomorphOfIsClosed` only changes the membership proof of the
  -- Hermitian factor, not its value.
  rfl

/-- The unitary factor of the Cartan decomposition of `g ∈ H` is the polar unitary factor of
`g`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_fst (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    (((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).1 : unitaryGroup n 𝕜) =
      (g : GL n 𝕜).polarUnitary := by
  rw [cartanHomeomorphOfIsClosed, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.coe_prodCongr, Prod.map_fst, Homeomorph.refl_symm, Homeomorph.refl_apply, id_eq]
  exact Subgroup.coe_cartanHomeomorph_symm_apply_fst _ _ g

/-- The Hermitian factor of the Cartan decomposition of `g ∈ H` is the logarithm of `√(gᴴ g)`. -/
@[simp]
theorem coe_cartanHomeomorphOfIsClosed_symm_apply_snd (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) (g : H) :
    ((((H.cartanHomeomorphOfIsClosed hH hstar hfin).symm g).2 : selfAdjoint (Matrix n n 𝕜)) :
        Matrix n n 𝕜) =
      cfc Real.log (CFC.sqrt (star ((g : GL n 𝕜) : Matrix n n 𝕜) * (g : GL n 𝕜))) := by
  rw [cartanHomeomorphOfIsClosed, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.coe_prodCongr, Prod.map_snd]
  -- The inverse of the Hermitian subtype equivalence keeps the value.
  refine (congrArg Subtype.val (Homeomorph.subtype_symm_apply_coe _ _ _)).trans ?_
  rw [Homeomorph.refl_symm, Homeomorph.refl_apply, ← CFC.log]
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
  -- Transport the general uniqueness along the identification of the Hermitian factor domains,
  -- which keeps both factors' values.
  exact ((Homeomorph.refl _).prodCongr (lineDomainHomeomorph H)).toEquiv.existsUnique_congr_right.2
    (H.existsUnique_unitary_mul_exp hstar (expUnit_smul_mem_of_isClosed hH hstar hfin) hg)

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

/-- The positive polar factor `u⁻¹ g` of an element `g = u (u⁻¹ g)` of a closed subgroup `H` of
`GL n 𝕜` stable under the conjugate transpose, with finitely many connected components, lies in
`H`. This is the factor `exp X` of the Cartan decomposition `g = u * exp X`; its matrix is
`√(gᴴ g)`. -/
theorem inv_toUnits_polarUnitary_mul_mem_of_isClosed (hH : IsClosed (H : Set (GL n 𝕜)))
    (hstar : ∀ g ∈ H, star g ∈ H) (hfin : Finite (ConnectedComponents H)) {g : GL n 𝕜}
    (hg : g ∈ H) : (Unitary.toUnits g.polarUnitary)⁻¹ * g ∈ H :=
  H.mul_mem (H.inv_mem (toUnits_polarUnitary_mem_of_isClosed hH hstar hfin hg)) hg

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
