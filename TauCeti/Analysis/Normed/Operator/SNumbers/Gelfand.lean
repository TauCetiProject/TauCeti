/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Restrict
public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.LinearAlgebra.Dimension.Submodule

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
without completeness of the field or of the spaces, and are bounded above by the approximation
numbers (`ContinuousLinearMap.gelfandNumber_le_singularValue`). The two-sided ideal inequality
pulls an admissible subspace back along the right factor, the rank axiom uses the kernel, and
the normalization on identities uses that every subspace of codimension below the dimension is
nonzero. Postcomposition with a linear isometry preserves the norm of every restriction, so the
Gelfand numbers are injective.

The Gelfand numbers are moreover additive and multiplicative in the index: intersecting
admissible subspaces adds codimensions, and for a composite `S T` the subspace admissible for
`S` is pulled back along `T` first. With `n = 0` additivity recovers the perturbation axiom.

## Main declarations

* `ContinuousLinearMap.gelfandNumber`: the Gelfand numbers `cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_le`: every subspace of codimension at most `n` bounds
  `cₙ(T)` by the norm of the restriction of `T` to it.
* `ContinuousLinearMap.le_gelfandNumber_iff`: lower bounds for `cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_comp_comp_le`: `cₙ(B T A) ≤ ‖B‖ cₙ(T) ‖A‖`.
* `ContinuousLinearMap.gelfandNumber_add_index_le`: additivity,
  `c_{m+n}(S + T) ≤ cₘ(S) + cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_comp_add_le_mul`: multiplicativity,
  `c_{m+n}(S T) ≤ cₘ(S) cₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_le_singularValue`: `cₙ(T) ≤ aₙ(T)`.
* `ContinuousLinearMap.gelfandNumber_id`: `cₙ(id_E) = 1` when `n` is below the rank of `E`.
* `TauCeti.SNumbers.isStrictSNumberSequence_gelfand`: the Gelfand numbers form a strict
  s-number sequence.
* `LinearIsometry.gelfandNumber_toContinuousLinearMap_comp`,
  `TauCeti.SNumbers.isInjective_gelfand`: the Gelfand numbers are injective, unchanged under
  postcomposition with a linear isometry.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4, and
  Theorem 9.5 for additivity.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.4.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  blueprint Theorems 3.6 and 3.8, for the multiplicativity of Gelfand and Kolmogorov numbers.
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
    ‖T ∘L M.val.subtypeL‖₊

/-- `cₙ(T)` is the infimum of `‖T|_M‖` over the closed subspaces `M` of codimension at most
`n`. -/
theorem gelfandNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n =
      ⨅ M : {M : Submodule 𝕜 E // IsClosed (M : Set E) ∧ Module.rank 𝕜 (E ⧸ M) ≤ n},
        ‖T ∘L M.val.subtypeL‖₊ := by
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
      Module.rank 𝕜 (E ⧸ M) ≤ n} ↦ ‖T ∘L M.val.subtypeL‖₊) (OrderBot.bddBelow _)
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
  have hx : T x = 0 := x.property
  simp [hx]

/-- **Mixed-index additivity.** `c_{m+n}(S + T) ≤ cₘ(S) + cₙ(T)`: the intersection of subspaces
admissible for `S` and for `T` has codimension at most `m + n`. -/
theorem gelfandNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).gelfandNumber (m + n) ≤ S.gelfandNumber m + T.gelfandNumber n := by
  rw [gelfandNumber_def S, gelfandNumber_def T]
  refine NNReal.le_iInf_add_iInf fun M N ↦ ?_
  have hrank : Module.rank 𝕜 (E ⧸ (M.val ⊓ N.val)) ≤ ↑(m + n) := by
    rw [Nat.cast_add]
    exact (Submodule.rank_quotient_inf_le M.val N.val).trans (add_le_add M.property.2 N.property.2)
  refine ((S + T).gelfandNumber_le hrank).trans ?_
  rw [add_comp]
  exact (nnNorm_add_le _ _).trans (add_le_add (S.nnnorm_comp_subtypeL_mono inf_le_left)
    (T.nnnorm_comp_subtypeL_mono inf_le_right))

/-- **Perturbative triangle bound.** `cₙ(S + T) ≤ cₙ(S) + ‖T‖`. -/
theorem gelfandNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).gelfandNumber n ≤ S.gelfandNumber n + ‖T‖₊ := by
  simpa using S.gelfandNumber_add_index_le T n 0

/-- **Two-sided ideal inequality.** `cₙ(B T A) ≤ ‖B‖ cₙ(T) ‖A‖`: a subspace `M` admissible for
`T` pulls back along `A` to a subspace of no larger codimension. -/
theorem gelfandNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).gelfandNumber n ≤ ‖B‖₊ * T.gelfandNumber n * ‖A‖₊ := by
  rw [gelfandNumber_def T, NNReal.mul_iInf, NNReal.iInf_mul]
  refine le_ciInf fun M ↦ ?_
  -- `E ⧸ A⁻¹(M)` embeds into `F ⧸ M`, so the preimage has codimension at most `n`.
  refine ((B ∘L T ∘L A).gelfandNumber_le
    (Submodule.rank_quotient_comap_le_of_le M.property.2 (A : E →ₗ[𝕜] F))).trans
    (opNNNorm_le_bound _ _ fun x ↦ ?_)
  have hx : A x ∈ M.val := x.property
  calc ‖B (T (A x))‖₊ ≤ ‖B‖₊ * ‖T (A x)‖₊ := B.le_opNNNorm _
    _ ≤ ‖B‖₊ * (‖T ∘L M.val.subtypeL‖₊ * ‖A x‖₊) := by
      gcongr; exact (T ∘L M.val.subtypeL).le_opNNNorm ⟨A x, hx⟩
    _ ≤ ‖B‖₊ * (‖T ∘L M.val.subtypeL‖₊ * (‖A‖₊ * ‖x‖₊)) := by gcongr; exact A.le_opNNNorm _
    _ = ‖B‖₊ * ‖T ∘L M.val.subtypeL‖₊ * ‖A‖₊ * ‖x‖₊ := by ring

/-- **Mixed-index multiplicativity.** `c_{m+n}(S T) ≤ cₘ(S) cₙ(T)`: intersect a subspace
admissible for `T` with the preimage under `T` of a subspace admissible for `S`. -/
theorem gelfandNumber_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    (S ∘L T).gelfandNumber (m + n) ≤ S.gelfandNumber m * T.gelfandNumber n := by
  rw [gelfandNumber_def S, gelfandNumber_def T, NNReal.iInf_mul]
  refine le_ciInf fun N ↦ ?_
  rw [NNReal.mul_iInf]
  refine le_ciInf fun M ↦ ?_
  have hrank : Module.rank 𝕜 (E ⧸ (M.val ⊓ N.val.comap (T : E →ₗ[𝕜] F))) ≤ ↑(m + n) := by
    rw [Nat.cast_add, add_comm (m : Cardinal)]
    exact (Submodule.rank_quotient_inf_le _ _).trans
      (add_le_add M.property.2
        (Submodule.rank_quotient_comap_le_of_le N.property.2 (T : E →ₗ[𝕜] F)))
  refine ((S ∘L T).gelfandNumber_le hrank).trans (opNNNorm_le_bound _ _ fun x ↦ ?_)
  have hxM : (x : E) ∈ M.val := x.property.1
  have hxN : T x ∈ N.val := x.property.2
  calc ‖S (T x)‖₊ ≤ ‖S ∘L N.val.subtypeL‖₊ * ‖T x‖₊ :=
        (S ∘L N.val.subtypeL).le_opNNNorm ⟨T x, hxN⟩
    _ ≤ ‖S ∘L N.val.subtypeL‖₊ * (‖T ∘L M.val.subtypeL‖₊ * ‖x‖₊) := by
      gcongr
      exact (T ∘L M.val.subtypeL).le_opNNNorm ⟨x, hxM⟩
    _ = ‖S ∘L N.val.subtypeL‖₊ * ‖T ∘L M.val.subtypeL‖₊ * ‖x‖₊ := (mul_assoc _ _ _).symm

/-- The `n`-th Gelfand number is bounded above by the `n`-th approximation number: `cₙ(T) ≤ aₙ(T)`.
Neither completeness nor Hausdorffness of the spaces is required. -/
theorem gelfandNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  have h := R.gelfandNumber_add_le (T - R) n
  simpa [gelfandNumber_eq_zero_of_rank_le hR] using h

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

namespace LinearIsometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Injectivity.** Postcomposition with a linear isometry leaves the Gelfand numbers unchanged:
`cₙ(J T) = cₙ(T)`, since `J` preserves the norm of every restriction of `T`. -/
@[simp]
theorem gelfandNumber_toContinuousLinearMap_comp (J : F →ₗᵢ[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (J.toContinuousLinearMap ∘L T).gelfandNumber n = T.gelfandNumber n := by
  simp_rw [ContinuousLinearMap.gelfandNumber_def, ContinuousLinearMap.comp_assoc]
  exact iInf_congr fun _ ↦ NNReal.eq J.norm_toContinuousLinearMap_comp

end LinearIsometry

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

/-- Gelfand numbers form an injective family. -/
theorem isInjective_gelfand : IsInjective (gelfand (𝕜 := 𝕜)) where
  linearIsometry_comp J T n := J.gelfandNumber_toContinuousLinearMap_comp T n

end TauCeti.SNumbers
