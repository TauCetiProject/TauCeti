/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Restrict
public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Gelfand numbers

The `n`-th Gelfand number of a bounded operator `T : E →L[𝕜] F` is
`cₙ(T) = inf {‖T|_M‖ : M ≤ E closed, codim M ≤ n}`, the infimum of the norms of the
restrictions of `T` to closed subspaces of codimension at most `n`. The codimension of `M` is
the rank of the quotient `E ⧸ M`, and the restriction is `T ∘L M.subtypeL`. The indexing is
zero-based, so `c₀(T) = ‖T‖`.

The closedness condition does not change the value: restricting to the closure of a subspace
does not increase the norm of the restriction, and does not increase the codimension
(`ContinuousLinearMap.gelfandNumber_le`). The upper bound therefore applies to arbitrary
subspaces of codimension at most `n`.

The Gelfand numbers form a strict s-number sequence over every nontrivially normed field,
without completeness of the field or of the spaces. The two-sided ideal inequality pulls an
admissible subspace back along the right factor, the rank axiom uses the kernel, and the
normalization on identities uses that every subspace of codimension below the dimension is
nonzero.

## Main declarations

* `ContinuousLinearMap.gelfandNumber`: the Gelfand numbers `cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_le`: every subspace of codimension at most `n` bounds
  `cₙ(T)` by the norm of the restriction of `T` to it.
* `ContinuousLinearMap.le_gelfandNumber_iff`: lower bounds for `cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_comp_comp_le`: `cₙ(B T A) ≤ ‖B‖ cₙ(T) ‖A‖`.
* `ContinuousLinearMap.gelfandNumber_id`: `cₙ(id_E) = 1` when `n` is below the rank of `E`.
* `TauCeti.SNumbers.isStrictSNumberSequence_gelfand`: the Gelfand numbers form a strict
  s-number sequence.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.4.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `n`-th Gelfand number `cₙ(T)` of a bounded linear map `T`: the infimum of the norms
`‖T|_M‖` of the restrictions of `T` to closed subspaces `M` of codimension at most `n`, the
codimension being the rank of `E ⧸ M`. The indexing is zero-based, so `c₀(T) = ‖T‖`
(`gelfandNumber_zero`). -/
noncomputable def gelfandNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ M : {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ n},
    ‖T ∘L M.1.subtypeL‖₊

/-- `cₙ(T)` is the infimum of `‖T|_M‖` over the closed subspaces `M` of codimension at most
`n`. -/
theorem gelfandNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n =
      ⨅ M : {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ n},
        ‖T ∘L M.1.subtypeL‖₊ := by
  rw [gelfandNumber]

private instance (n : ℕ) :
    Nonempty {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ n} :=
  ⟨⟨⊤, Submodule.top_coe (R := 𝕜) (M := E) ▸ isClosed_univ, by simp⟩⟩

/-- **Upper bound.** Every subspace `M` of codimension at most `n`, closed or not, bounds `cₙ(T)`
by the norm of the restriction of `T` to `M`. -/
theorem gelfandNumber_le (T : E →L[𝕜] F) {n : ℕ} {M : Submodule 𝕜 E}
    (hM : Module.rank 𝕜 (E ⧸ M) ≤ n) : T.gelfandNumber n ≤ ‖T ∘L M.subtypeL‖₊ := by
  rw [← T.nnnorm_comp_subtypeL_topologicalClosure M, gelfandNumber]
  -- The closure is closed, and its codimension is at most that of `M`.
  have hrank : Module.rank 𝕜 (E ⧸ M.topologicalClosure) ≤ n :=
    (LinearMap.rank_le_of_surjective _
      (Submodule.factor_surjective M.le_topologicalClosure)).trans hM
  exact ciInf_le (f := fun M : {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧
      Module.rank 𝕜 (E ⧸ M) ≤ n} ↦ ‖T ∘L M.1.subtypeL‖₊) (OrderBot.bddBelow _)
    ⟨M.topologicalClosure, M.isClosed_topologicalClosure, hrank⟩

/-- **Lower-bound characterization.** `c ≤ cₙ(T)` exactly when `c ≤ ‖T|_M‖` for every closed
subspace `M` of codimension at most `n`. -/
theorem le_gelfandNumber_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ T.gelfandNumber n ↔ ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      Module.rank 𝕜 (E ⧸ M) ≤ n → c ≤ ‖T ∘L M.subtypeL‖₊ := by
  rw [gelfandNumber, le_ciInf_iff (OrderBot.bddBelow _), Subtype.forall]
  exact forall_congr' fun M ↦ ⟨fun h hc hr ↦ h ⟨hc, hr⟩, fun h hM ↦ h hM.1 hM.2⟩

/-- **Near-optimal subspaces.** If `cₙ(T) < c`, some closed subspace of codimension at most `n`
carries a restriction of `T` of norm below `c`. -/
theorem exists_nnnorm_comp_subtypeL_lt {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : T.gelfandNumber n < c) : ∃ M : Submodule 𝕜 E, IsClosed (M : Set E) ∧
      Module.rank 𝕜 (E ⧸ M) ≤ n ∧ ‖T ∘L M.subtypeL‖₊ < c := by
  rw [gelfandNumber] at h
  obtain ⟨⟨M, hc, hr⟩, hlt⟩ := exists_lt_of_ciInf_lt h
  exact ⟨M, hc, hr, hlt⟩

/-- The Gelfand numbers are bounded by the operator norm. -/
theorem gelfandNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.gelfandNumber n ≤ ‖T‖₊ :=
  (T.gelfandNumber_le (M := ⊤) (by simp)).trans <|
    opNNNorm_le_bound _ _ fun x ↦ T.le_opNNNorm x

/-- **Zeroth Gelfand number.** `c₀(T) = ‖T‖`, since the only subspace of codimension `0` is the
whole space. -/
@[simp]
theorem gelfandNumber_zero (T : E →L[𝕜] F) : T.gelfandNumber 0 = ‖T‖₊ := by
  refine (T.gelfandNumber_le_nnnorm 0).antisymm (le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_)
  have htop : M = ⊤ := Submodule.Quotient.subsingleton_iff.mp <|
    rank_zero_iff.mp (le_antisymm (by exact_mod_cast hM) bot_le)
  subst htop
  exact opNNNorm_le_bound _ _ fun x ↦
    (T ∘L (⊤ : Submodule 𝕜 E).subtypeL).le_opNNNorm ⟨x, Submodule.mem_top⟩

/-- The Gelfand numbers form an antitone sequence. -/
theorem antitone_gelfandNumber (T : E →L[𝕜] F) : Antitone T.gelfandNumber :=
  fun _ _ hmn ↦ le_gelfandNumber_iff.mpr fun _ _ hM ↦
    T.gelfandNumber_le (hM.trans (by exact_mod_cast hmn))

/-- The Gelfand numbers of the zero map vanish. -/
@[simp]
theorem zero_gelfandNumber (n : ℕ) : (0 : E →L[𝕜] F).gelfandNumber n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).gelfandNumber_le_nnnorm n) bot_le

/-- **Vanishing from rank.** A bounded map of rank at most `n` has `cₙ(T) = 0`: its kernel has
codimension `rank T`, and `T` vanishes on it. -/
theorem gelfandNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T.gelfandNumber n = 0 := by
  have hrank : Module.rank 𝕜 (E ⧸ LinearMap.ker (T : E →ₗ[𝕜] F)) ≤ n := by
    have h := (LinearMap.quotKerEquivRange (T : E →ₗ[𝕜] F)).lift_rank_eq
    exact Cardinal.lift_le_nat_iff.mp (h.trans_le (Cardinal.lift_le_nat_iff.mpr hT))
  refine le_antisymm ((T.gelfandNumber_le hrank).trans (opNNNorm_le_bound _ _ fun x ↦ ?_)) bot_le
  have hx : T x = 0 := x.2
  simp [hx]

/-- **Perturbative triangle bound.** `cₙ(S + T) ≤ cₙ(S) + ‖T‖`. -/
theorem gelfandNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).gelfandNumber n ≤ S.gelfandNumber n + ‖T‖₊ := by
  have h := NNReal.le_iInf_add_iInf (a := (S + T).gelfandNumber n) (g := fun _ : Unit ↦ ‖T‖₊)
    (f := fun M : {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ n} ↦
      ‖S ∘L M.1.subtypeL‖₊) fun M _ ↦ by
    refine ((S + T).gelfandNumber_le M.2.2).trans ?_
    rw [add_comp]
    refine (nnNorm_add_le _ _).trans ?_
    gcongr
    exact (opNNNorm_comp_le _ _).trans <| mul_le_of_le_one_right' (by
      exact_mod_cast Submodule.norm_subtypeL_le M.1)
  rwa [ciInf_const, ← gelfandNumber_def] at h

/-- **Two-sided ideal inequality.** `cₙ(B T A) ≤ ‖B‖ cₙ(T) ‖A‖`: a subspace `M` admissible for
`T` pulls back along `A` to a subspace of no larger codimension. -/
theorem gelfandNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).gelfandNumber n ≤ ‖B‖₊ * T.gelfandNumber n * ‖A‖₊ := by
  rw [gelfandNumber_def T, NNReal.mul_iInf, NNReal.iInf_mul]
  refine le_ciInf fun M ↦ ?_
  -- `E ⧸ A⁻¹(M)` embeds into `F ⧸ M`, so the preimage has codimension at most `n`.
  have hrank : Module.rank 𝕜 (E ⧸ M.1.comap (A : E →ₗ[𝕜] F)) ≤ n := by
    have hinj : Function.Injective
        ((M.1.comap (A : E →ₗ[𝕜] F)).mapQ M.1 (A : E →ₗ[𝕜] F) le_rfl) := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]
    have h := LinearMap.lift_rank_le_of_injective _ hinj
    exact Cardinal.lift_le_nat_iff.mp (h.trans (Cardinal.lift_le_nat_iff.mpr M.2.2))
  refine ((B ∘L T ∘L A).gelfandNumber_le hrank).trans (opNNNorm_le_bound _ _ fun x ↦ ?_)
  have hx : A x ∈ M.1 := x.2
  calc ‖B (T (A x))‖₊ ≤ ‖B‖₊ * ‖T (A x)‖₊ := B.le_opNNNorm _
    _ ≤ ‖B‖₊ * (‖T ∘L M.1.subtypeL‖₊ * ‖A x‖₊) := by
      gcongr; exact (T ∘L M.1.subtypeL).le_opNNNorm ⟨A x, hx⟩
    _ ≤ ‖B‖₊ * (‖T ∘L M.1.subtypeL‖₊ * (‖A‖₊ * ‖x‖₊)) := by gcongr; exact A.le_opNNNorm _
    _ = ‖B‖₊ * ‖T ∘L M.1.subtypeL‖₊ * ‖A‖₊ * ‖x‖₊ := by ring

/-- **Identity normalization.** If `n` is strictly below the rank of a normed space `E`, then
`cₙ(id_E) = 1`: every subspace of codimension at most `n` is nonzero, so its inclusion has
norm `1`. -/
theorem gelfandNumber_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
    (hn : (n : Cardinal) < Module.rank 𝕜 E) : (ContinuousLinearMap.id 𝕜 E).gelfandNumber n = 1 := by
  refine le_antisymm ((gelfandNumber_le_nnnorm _ n).trans ?_)
    (le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_)
  · exact_mod_cast norm_id_le
  have hne : M ≠ ⊥ := by
    rintro rfl
    rw [(Submodule.quotEquivOfEqBot ⊥ rfl).rank_eq] at hM
    exact hn.not_ge hM
  have : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hne
  rw [id_comp, ← NNReal.coe_le_coe, coe_nnNorm, Submodule.norm_subtypeL]
  simp

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The family of Gelfand numbers on all normed spaces over the scalar field. -/
noncomputable def gelfand : SNumberFamily 𝕜 :=
  fun T ↦ T.gelfandNumber

/-- Evaluation of the Gelfand family is the Gelfand number. -/
@[simp]
theorem gelfand_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : gelfand T n = T.gelfandNumber n := (rfl)

/-- Gelfand numbers form a strict s-number sequence over every nontrivially normed field. -/
theorem isStrictSNumberSequence_gelfand : IsStrictSNumberSequence (gelfand (𝕜 := 𝕜)) where
  norm T := T.gelfandNumber_zero
  antitone T := T.antitone_gelfandNumber
  add_le S T n := S.gelfandNumber_add_le T n
  comp_le B T A n := B.gelfandNumber_comp_comp_le T A n
  eq_zero_of_rank_le hT := ContinuousLinearMap.gelfandNumber_eq_zero_of_rank_le hT
  normalize n := ContinuousLinearMap.gelfandNumber_id <| by
    rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq]
    simp
  normalize_of_lt_rank n hn := ContinuousLinearMap.gelfandNumber_id hn

end TauCeti.SNumbers
