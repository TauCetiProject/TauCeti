/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.Fredholm.SelfAdjoint.SpectralGap
public import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
public import TauCeti.Analysis.Normed.Operator.IdempotentRange

/-!
# Finite spectral cutoffs and spectral counts

Let `T` be a bounded self-adjoint operator on a Hilbert space. A number `c > 0` is a *finite
spectral cutoff* of `T` if neither `c` nor `-c` is a spectral value of `T` and the spectral
projection `𝟙_(-c, c)(T)` has finite rank. Then the part of the spectrum of `T` in `(-c, c)` is a
finite set of eigenvalues of finite multiplicity, and the *spectral count*
`spectralCount T c`, the rank of the spectral projection `𝟙_[0, c)(T)`, is the number of these
eigenvalues in `[0, c)` counted with multiplicity.

These are the local data of spectral flow (Phillips). Along a continuous path of self-adjoint
operators, the count `spectralCount (A t) c` changes exactly when an eigenvalue crosses `0`, as
long as `c` stays a finite spectral cutoff. Two facts make this usable:

* a finite spectral cutoff of `T₀` remains one for every self-adjoint `T` near `T₀`
  (`TauCeti.IsFiniteSpectralCutoff.eventually_isFiniteSpectralCutoff`), and
* for two finite spectral cutoffs `c₁`, `c₂` of `T₀`, the difference
  `spectralCount T c₁ - spectralCount T c₂`, which counts the eigenvalues between `c₂` and `c₁`,
  is constant for self-adjoint `T` near `T₀`
  (`TauCeti.IsFiniteSpectralCutoff.eventually_spectralCount_sub_eq`).

Both rest on the continuity of `T ↦ 𝟙_Ω(T)` near a self-adjoint `T₀` whose spectrum avoids the
frontier of `Ω`, and on the local constancy of the rank of a continuous family of projections.
Every self-adjoint Fredholm operator has a finite spectral cutoff
(`TauCeti.exists_isFiniteSpectralCutoff_of_isFredholm`), by its spectral gap at zero.

The spectral projections are those of the real continuous functional calculus, on a Hilbert space
over any `RCLike` field for which that calculus is isometric: complex Hilbert spaces, and real
ones by `ContinuousLinearMap.instIsometricContinuousFunctionalCalculusRealIsSelfAdjoint`.

## Main definitions

* `TauCeti.IsFiniteSpectralCutoff T c`: `c > 0` is a finite spectral cutoff of the self-adjoint
  operator `T`.
* `TauCeti.spectralCount T c`: the rank of the spectral projection of `T` onto `[0, c)`.

## Main results

* `TauCeti.range_cfc_indicator_le_of_subset`: spectral projections are monotone in the set.
* `TauCeti.eventually_nonempty_continuousLinearEquiv_range_cfc_indicator`: if the spectrum of a
  self-adjoint `T₀` avoids the frontier of `Ω`, then for self-adjoint `T` near `T₀` the ranges of
  `𝟙_Ω(T)` and `𝟙_Ω(T₀)` are isomorphic.
* `TauCeti.IsFiniteSpectralCutoff.finite_spectrum_inter_Ioo`: the spectrum in `(-c, c)` is finite.
* `TauCeti.IsFiniteSpectralCutoff.finiteDimensional_range_cfc_indicator_Ico`: the spectral
  projection onto `[0, c)` has finite rank.
* `TauCeti.IsFiniteSpectralCutoff.eventually_isFiniteSpectralCutoff`: finite spectral cutoffs
  persist under small self-adjoint perturbations.
* `TauCeti.IsFiniteSpectralCutoff.eventually_spectralCount_sub_eq`: the difference of the spectral
  counts at two cutoffs is locally constant.
* `TauCeti.exists_isFiniteSpectralCutoff_of_isFredholm`: self-adjoint Fredholm operators have
  finite spectral cutoffs.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAlgebra ℝ (E →L[𝕜] E)] [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-! ### Spectral projections -/

/-- **Spectral projections have locally constant rank.** If the spectrum of a self-adjoint
operator `T₀` avoids the frontier of `Ω`, then for every self-adjoint `T` near `T₀` the ranges of
the spectral projections `𝟙_Ω(T₀)` and `𝟙_Ω(T)` are isomorphic. -/
theorem eventually_nonempty_continuousLinearEquiv_range_cfc_indicator {T₀ : E →L[𝕜] E}
    (hT₀ : IsSelfAdjoint T₀) {Ω : Set ℝ} (hΩ : Disjoint (spectrum ℝ T₀) (frontier Ω)) :
    ∀ᶠ T in 𝓝[{T | IsSelfAdjoint T}] T₀,
      Nonempty ((cfc (Ω.indicator 1) T₀).range ≃L[𝕜] (cfc (Ω.indicator 1) T).range) := by
  set U : Set (E →L[𝕜] E) := {T | IsSelfAdjoint T ∧ Disjoint (spectrum ℝ T) (frontier Ω)}
  -- `U` is a neighbourhood of `T₀` among the self-adjoint operators.
  have hU : U ∈ 𝓝[{T | IsSelfAdjoint T}] T₀ := by
    have h := (upperHemicontinuous_spectrum ℝ (E →L[𝕜] E)).upperHemicontinuousAt T₀ _
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 hΩ.subset_compl_right)
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with T hT hsa
    exact ⟨hsa, subset_compl_iff_disjoint_right.1 (subset_of_mem_nhdsSet hT)⟩
  -- The spectral projection is continuous on `U`, so its rank is locally constant there.
  have hcont : ContinuousOn (fun T ↦ cfc (Ω.indicator (1 : ℝ → ℝ)) T) U :=
    ContinuousOn.cfc_of_mem_nhdsSet _ (s := (frontier Ω)ᶜ)
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 <| iUnion₂_subset fun T hT ↦
        hT.2.subset_compl_right) continuousOn_id (fun T hT ↦ hT.1)
      (ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const)
        disjoint_compl_left)
  have hmem : T₀ ∈ U := ⟨hT₀, hΩ⟩
  have h := eventually_nonempty_continuousLinearEquiv_range
    (continuousOn_iff_continuous_domRestrict.1 hcont)
    (fun T ↦ (isStarProjection_cfc_indicator (T : E →L[𝕜] E) Ω).isIdempotentElem) ⟨T₀, hmem⟩
  refine nhdsWithin_le_of_mem hU ?_
  rw [nhdsWithin_eq_map_subtype_coe hmem]
  exact Filter.eventually_map.2 h

/-- If `Ω' ⊆ Ω` and both indicators are continuous on the spectrum of `T`, the spectral projection
onto `Ω'` maps into the range of the spectral projection onto `Ω`. -/
theorem range_cfc_indicator_le_of_subset {T : E →L[𝕜] E} {Ω Ω' : Set ℝ} (hsub : Ω' ⊆ Ω)
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc (Ω'.indicator 1) T).range ≤ (cfc (Ω.indicator 1) T).range := by
  have h : cfc (Ω'.indicator (1 : ℝ → ℝ)) T = cfc (Ω.indicator 1) T * cfc (Ω'.indicator 1) T := by
    rw [← cfc_mul _ _ T hΩ hΩ', ← Pi.mul_def, ← inter_indicator_one, inter_eq_right.2 hsub]
  rw [h, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.range_comp_le_range _ _

/-! ### Finite spectral cutoffs -/

/-- `c` is a **finite spectral cutoff** of the operator `T`: `T` is self-adjoint, `c > 0`, neither
`c` nor `-c` lies in the spectrum of `T`, and the spectral projection `𝟙_(-c, c)(T)` has finite
rank. -/
structure IsFiniteSpectralCutoff (T : E →L[𝕜] E) (c : ℝ) : Prop where
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint T
  /-- The cutoff is positive. -/
  pos : 0 < c
  /-- The cutoff is not a spectral value. -/
  notMem_spectrum : c ∉ spectrum ℝ T
  /-- Its negative is not a spectral value. -/
  neg_notMem_spectrum : -c ∉ spectrum ℝ T
  /-- The spectral projection onto `(-c, c)` has finite rank. -/
  finiteDimensional_range : FiniteDimensional 𝕜 (cfc ((Ioo (-c) c).indicator 1) T).range

namespace IsFiniteSpectralCutoff

variable {T : E →L[𝕜] E} {c : ℝ}

/-- The spectrum avoids the frontier `{-c, c}` of `(-c, c)`. -/
theorem disjoint_spectrum_frontier_Ioo (h : IsFiniteSpectralCutoff T c) :
    Disjoint (spectrum ℝ T) (frontier (Ioo (-c) c)) := by
  rw [frontier_Ioo (by linarith [h.pos]), disjoint_iff_forall_ne]
  rintro x hx _ (rfl | rfl) rfl
  exacts [h.neg_notMem_spectrum hx, h.notMem_spectrum hx]

/-- The indicator of `(-c, c)` is continuous on the spectrum, so `𝟙_(-c, c)(T)` is a genuine
spectral projection. -/
theorem continuousOn_indicator_Ioo (h : IsFiniteSpectralCutoff T c) :
    ContinuousOn ((Ioo (-c) c).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
  ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const)
    h.disjoint_spectrum_frontier_Ioo

/-- A finite spectral cutoff of `T₀` is a finite spectral cutoff of every self-adjoint operator
near `T₀`. -/
theorem eventually_isFiniteSpectralCutoff (h : IsFiniteSpectralCutoff T c) :
    ∀ᶠ T' in 𝓝[{T | IsSelfAdjoint T}] T, IsFiniteSpectralCutoff T' c := by
  have hsp := (upperHemicontinuous_spectrum ℝ (E →L[𝕜] E)).upperHemicontinuousAt T _
    ((Set.toFinite {c, -c}).isClosed.isOpen_compl.mem_nhdsSet.2 fun x hx hx' ↦ by
      rcases hx' with rfl | rfl
      exacts [h.notMem_spectrum hx, h.neg_notMem_spectrum hx])
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsp,
    eventually_nonempty_continuousLinearEquiv_range_cfc_indicator h.isSelfAdjoint
      h.disjoint_spectrum_frontier_Ioo] with T' hT' hsp' ⟨e⟩
  have := h.finiteDimensional_range
  exact ⟨hT', h.pos, fun hc ↦ subset_of_mem_nhdsSet hsp' hc (by simp),
    fun hc ↦ subset_of_mem_nhdsSet hsp' hc (by simp), e.toLinearEquiv.finiteDimensional⟩

/-- If a family `A` is continuous within `s` at `x₀` and self-adjoint on `s`, a finite spectral
cutoff of `A x₀` is one of `A x` for every `x` near `x₀` in `s`. -/
theorem eventually_of_continuousWithinAt {X : Type*} [TopologicalSpace X] {A : X → E →L[𝕜] E}
    {s : Set X} {x₀ : X} (hc : IsFiniteSpectralCutoff (A x₀) c) (hA : ContinuousWithinAt A s x₀)
    (hsa : ∀ x ∈ s, IsSelfAdjoint (A x)) :
    ∀ᶠ x in 𝓝[s] x₀, IsFiniteSpectralCutoff (A x) c :=
  (tendsto_nhdsWithin_iff.2 ⟨hA, eventually_nhdsWithin_of_forall hsa⟩).eventually
    hc.eventually_isFiniteSpectralCutoff

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

omit [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- `T` commutes with its spectral projection onto `(-c, c)`. -/
private theorem mul_cfc_indicator_Ioo_comm (h : IsFiniteSpectralCutoff T c) :
    T * cfc ((Ioo (-c) c).indicator 1) T = cfc ((Ioo (-c) c).indicator 1) T * T := by
  have hT := h.isSelfAdjoint
  have hχ := h.continuousOn_indicator_Ioo
  have h1 : T * cfc ((Ioo (-c) c).indicator 1) T =
      cfc (fun x ↦ x * (Ioo (-c) c).indicator (1 : ℝ → ℝ) x) T := by
    rw [cfc_mul (fun x ↦ x) _ T continuousOn_id hχ, cfc_id' ℝ T]
  have h2 : cfc ((Ioo (-c) c).indicator 1) T * T =
      cfc (fun x ↦ (Ioo (-c) c).indicator (1 : ℝ → ℝ) x * x) T := by
    rw [cfc_mul _ (fun x ↦ x) T hχ continuousOn_id, cfc_id' ℝ T]
  rw [h1, h2]
  simp_rw [mul_comm]

/-- A nonzero spectral value `l ∈ (-c, c)` below a finite spectral cutoff `c` is an eigenvalue of
`T`, with an eigenvector in the range of `𝟙_(-c, c)(T)`: it is a nonzero spectral value of the
finite-rank, hence compact, operator `S = T 𝟙_(-c, c)(T)`. -/
private theorem exists_mem_range_apply_eq_smul (h : IsFiniteSpectralCutoff T c) {l : ℝ}
    (hl : l ∈ spectrum ℝ T) (hlI : l ∈ Ioo (-c) c) (hl0 : l ≠ 0) :
    ∃ v ∈ (cfc ((Ioo (-c) c).indicator 1) T).range, v ≠ 0 ∧ T v = algebraMap ℝ 𝕜 l • v := by
  set χ := (Ioo (-c) c).indicator (1 : ℝ → ℝ)
  have hχ : ContinuousOn χ (spectrum ℝ T) := h.continuousOn_indicator_Ioo
  set P := cfc χ T
  have : FiniteDimensional 𝕜 P.range := h.finiteDimensional_range
  set S := cfc (fun x ↦ x * χ x) T with hS
  have hSc : ContinuousOn (fun x ↦ x * χ x) (spectrum ℝ T) := continuousOn_id.mul hχ
  have hTP : T * P = S := by
    rw [hS, cfc_mul (fun x ↦ x) χ T continuousOn_id hχ, cfc_id' ℝ T (ha := h.isSelfAdjoint)]
  have hPS : P * S = S := by
    rw [hS, ← cfc_mul _ _ T hχ hSc]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo (-c) c <;> simp [χ, hx]
  -- `S` has finite rank, so it is compact, and `l` is a nonzero spectral value of `S`.
  have hSrange : S.range ≤ P.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨S v, by simpa [mul_apply_eq_comp] using congr($hPS v)⟩
  have hcomp : IsCompactOperator S := LinearMap.HasFiniteRange.isCompactOperator <|
    (Submodule.fg_iff_finiteDimensional _).2 (Submodule.finiteDimensional_of_le hSrange)
  have hlS : l ∈ spectrum ℝ S := by
    rw [hS, cfc_map_spectrum _ _ h.isSelfAdjoint hSc]
    exact ⟨l, hl, by simp [χ, hlI]⟩
  have hl' : algebraMap ℝ 𝕜 l ≠ 0 := by simpa using hl0
  obtain ⟨v, hv⟩ := ((hcomp.hasEigenvalue_iff_mem_spectrum hl').2
    ((spectrum.algebraMap_mem_iff 𝕜).2 hlS)).exists_hasEigenvector
  have hSv : S v = algebraMap ℝ 𝕜 l • v := Module.End.mem_eigenspace_iff.1 hv.1
  -- The eigenvector lies in the range of `P`, where `S` agrees with `T`.
  have hvP : v ∈ P.range := ⟨(algebraMap ℝ 𝕜 l)⁻¹ • S v, by
    rw [map_smul, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, hPS, hSv, smul_smul,
      inv_mul_cancel₀ hl', one_smul]⟩
  have hPv : P v = v := ContinuousLinearMap.IsIdempotentElem.apply_coe_range
    (isStarProjection_cfc_indicator T _).isIdempotentElem ⟨v, hvP⟩
  exact ⟨v, hvP, hv.2, by rw [← hPv, ← mul_apply_eq_comp, hTP, hPv, hSv]⟩

/-- The part of the spectrum in `(-c, c)` below a finite spectral cutoff `c` is finite: it consists
of eigenvalues of the restriction of `T` to the finite-dimensional range of `𝟙_(-c, c)(T)`. -/
theorem finite_spectrum_inter_Ioo (h : IsFiniteSpectralCutoff T c) :
    (spectrum ℝ T ∩ Ioo (-c) c).Finite := by
  set P := cfc ((Ioo (-c) c).indicator (1 : ℝ → ℝ)) T
  have : FiniteDimensional 𝕜 P.range := h.finiteDimensional_range
  have hinv : ∀ v ∈ P.range, (T : E →ₗ[𝕜] E) v ∈ P.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨T v, by simpa [mul_apply_eq_comp] using congr($(h.mul_cfc_indicator_Ioo_comm) v).symm⟩
  set Tv : Module.End 𝕜 P.range := (T : E →ₗ[𝕜] E).restrict hinv
  refine ((Tv.finite_hasEigenvalue.preimage (algebraMap ℝ 𝕜).injective.injOn).insert 0).subset ?_
  rintro l ⟨hl, hlI⟩
  rcases eq_or_ne l 0 with rfl | hl0
  · exact mem_insert _ _
  obtain ⟨v, hvP, hv0, hTv⟩ := h.exists_mem_range_apply_eq_smul hl hlI hl0
  refine mem_insert_of_mem _ <| Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvP⟩)
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), fun h0 ↦ hv0 congr(Subtype.val $h0)⟩
  simpa [Tv] using hTv

/-- Below a finite spectral cutoff, `0` is isolated from the left in the spectrum: some interval
`[-δ, 0)` with `0 < δ < c` contains no spectral value. -/
theorem exists_pos_lt_disjoint_spectrum_Ico (h : IsFiniteSpectralCutoff T c) :
    ∃ δ, 0 < δ ∧ δ < c ∧ Disjoint (spectrum ℝ T) (Ico (-δ) 0) := by
  set F := spectrum ℝ T ∩ Ioo (-c) c ∩ Iio 0
  have hF : IsClosed F := (h.finite_spectrum_inter_Ioo.subset inter_subset_left).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hF.isOpen_compl 0 (fun h0 ↦ lt_irrefl _ h0.2)
  refine ⟨min ε c / 2, by have := h.pos; positivity, by
    have := h.pos; have := min_le_right ε c; linarith, disjoint_left.2 fun x hx hxI ↦ ?_⟩
  have hmin : 0 < min ε c := lt_min hε h.pos
  have hxF : x ∈ F := ⟨⟨hx, by
    constructor <;> linarith [hxI.1, hxI.2, min_le_right ε c]⟩, hxI.2⟩
  refine hball ?_ hxF
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [hxI.1, hxI.2, min_le_left ε c]

/-- Below a finite spectral cutoff `c`, the indicator of `[0, c)` is continuous on the spectrum, so
its functional calculus is a genuine spectral projection. -/
theorem continuousOn_indicator_Ico (h : IsFiniteSpectralCutoff T c) :
    ContinuousOn ((Ico 0 c).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) := by
  obtain ⟨δ, hδ, hδc, hdisj⟩ := h.exists_pos_lt_disjoint_spectrum_Ico
  have hfr : Disjoint (spectrum ℝ T) (frontier (Ioo (-δ) c)) := by
    rw [frontier_Ioo (by linarith), disjoint_iff_forall_ne]
    rintro x hx _ (rfl | rfl) rfl
    exacts [disjoint_left.1 hdisj hx ⟨le_rfl, by linarith⟩, h.notMem_spectrum hx]
  refine (ContinuousOn.indicator_of_disjoint_frontier (f := (1 : ℝ → ℝ))
    (by exact continuousOn_const) hfr).congr
    fun x hx ↦ ?_
  have hx' : x ∉ Ico (-δ) 0 := disjoint_left.1 hdisj hx
  by_cases h0 : 0 ≤ x
  · by_cases hxc : x < c
    · simp [indicator_of_mem, h0, hxc, show -δ < x by linarith]
    · simp [indicator_of_notMem, hxc]
  · have : x < -δ := by
      by_contra! hle
      exact hx' ⟨hle, not_le.1 h0⟩
    simp [indicator_of_notMem, h0, show ¬ -δ < x by linarith]

/-- The spectral projection onto `[0, c)` below a finite spectral cutoff `c` has finite rank. -/
theorem finiteDimensional_range_cfc_indicator_Ico (h : IsFiniteSpectralCutoff T c) :
    FiniteDimensional 𝕜 (cfc ((Ico 0 c).indicator 1) T).range :=
  have := h.finiteDimensional_range
  Submodule.finiteDimensional_of_le <| range_cfc_indicator_le_of_subset
    (Ico_subset_Ioo_left (by linarith [h.pos])) h.continuousOn_indicator_Ioo
    h.continuousOn_indicator_Ico

end IsFiniteSpectralCutoff

/-! ### Spectral counts -/

/-- The **spectral count** of `T` below `c`: the rank of the spectral projection `𝟙_[0, c)(T)`.
When `c` is a finite spectral cutoff of `T` this is the number of eigenvalues of `T` in `[0, c)`,
counted with multiplicity. -/
noncomputable def spectralCount (T : E →L[𝕜] E) (c : ℝ) : ℕ :=
  Module.finrank 𝕜 (cfc ((Ico 0 c).indicator 1) T).range

/-- The spectral count is the rank of the spectral projection onto `[0, c)`. -/
theorem spectralCount_def (T : E →L[𝕜] E) (c : ℝ) :
    spectralCount T c = Module.finrank 𝕜 (cfc ((Ico 0 c).indicator 1) T).range :=
  (rfl)

namespace IsFiniteSpectralCutoff

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] {T : E →L[𝕜] E} {c₁ c₂ : ℝ}

omit [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- The spectrum avoids the frontier of `[c₂, c₁)` for finite spectral cutoffs `c₁`, `c₂`. -/
private theorem disjoint_spectrum_frontier_Ico (h₁ : IsFiniteSpectralCutoff T c₁)
    (h₂ : IsFiniteSpectralCutoff T c₂) : Disjoint (spectrum ℝ T) (frontier (Ico c₂ c₁)) := by
  rcases lt_or_ge c₂ c₁ with h | h
  · rw [frontier_Ico h, disjoint_iff_forall_ne]
    rintro x hx _ (rfl | rfl) rfl
    exacts [h₂.notMem_spectrum hx, h₁.notMem_spectrum hx]
  · simp [Ico_eq_empty_of_le h]

/-- For finite spectral cutoffs `c₂ ≤ c₁` of `T`, the spectral count below `c₁` is the spectral
count below `c₂` plus the rank of the spectral projection onto `[c₂, c₁)`. -/
theorem spectralCount_eq_add (h₁ : IsFiniteSpectralCutoff T c₁) (h₂ : IsFiniteSpectralCutoff T c₂)
    (h : c₂ ≤ c₁) : spectralCount T c₁ =
      spectralCount T c₂ + Module.finrank 𝕜 (cfc ((Ico c₂ c₁).indicator 1) T).range := by
  have hfr := disjoint_spectrum_frontier_Ico h₁ h₂
  have hQc : ContinuousOn ((Ico c₂ c₁).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
    ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const) hfr
  set P := cfc ((Ico 0 c₂).indicator (1 : ℝ → ℝ)) T
  set Q := cfc ((Ico c₂ c₁).indicator (1 : ℝ → ℝ)) T
  have hdisj : Disjoint (Ico 0 c₂) (Ico c₂ c₁) := Ico_disjoint_Ico_same
  have hPQ : P * Q = 0 := by
    rw [← cfc_mul _ _ T h₂.continuousOn_indicator_Ico hQc, ← Pi.mul_def, ← inter_indicator_one,
      hdisj.inter_eq, indicator_empty, cfc_const_zero]
  have hQP : Q * P = 0 := by
    rw [← cfc_mul _ _ T hQc h₂.continuousOn_indicator_Ico, ← Pi.mul_def, ← inter_indicator_one,
      hdisj.symm.inter_eq, indicator_empty, cfc_const_zero]
  have hsum : cfc ((Ico 0 c₁).indicator (1 : ℝ → ℝ)) T = P + Q := by
    rw [← cfc_add (a := T) _ _ h₂.continuousOn_indicator_Ico hQc]
    congr 1
    funext x
    rw [← Ico_union_Ico_eq_Ico h₂.pos.le h, indicator_union_of_disjoint hdisj]
  have hPi : IsIdempotentElem P := (isStarProjection_cfc_indicator T _).isIdempotentElem
  have hQi : IsIdempotentElem Q := (isStarProjection_cfc_indicator T _).isIdempotentElem
  have : FiniteDimensional 𝕜 P.range := h₂.finiteDimensional_range_cfc_indicator_Ico
  have : FiniteDimensional 𝕜 Q.range := by
    have := h₁.finiteDimensional_range_cfc_indicator_Ico
    exact Submodule.finiteDimensional_of_le <| range_cfc_indicator_le_of_subset
      (Ico_subset_Ico_left h₂.pos.le) h₁.continuousOn_indicator_Ico hQc
  rw [spectralCount_def, spectralCount_def, hsum,
    ContinuousLinearMap.IsIdempotentElem.range_add hPi hQi hPQ hQP,
    ← Submodule.finrank_sup_add_finrank_inf_eq,
    (ContinuousLinearMap.IsIdempotentElem.disjoint_range hPi hPQ).eq_bot, finrank_bot, add_zero]

private theorem eventually_spectralCount_sub_eq_of_le (h₁ : IsFiniteSpectralCutoff T c₁)
    (h₂ : IsFiniteSpectralCutoff T c₂) (h : c₂ ≤ c₁) :
    ∀ᶠ T' in 𝓝[{T | IsSelfAdjoint T}] T,
      (spectralCount T' c₁ : ℤ) - spectralCount T' c₂ =
        (spectralCount T c₁ : ℤ) - spectralCount T c₂ := by
  have hfr := disjoint_spectrum_frontier_Ico h₁ h₂
  filter_upwards [h₁.eventually_isFiniteSpectralCutoff, h₂.eventually_isFiniteSpectralCutoff,
    eventually_nonempty_continuousLinearEquiv_range_cfc_indicator h₁.isSelfAdjoint hfr]
    with T' h₁' h₂' ⟨e⟩
  rw [h₁.spectralCount_eq_add h₂ h, h₁'.spectralCount_eq_add h₂' h,
    e.toLinearEquiv.finrank_eq]
  push_cast
  ring

/-- **The difference of spectral counts is locally constant.** For finite spectral cutoffs `c₁` and
`c₂` of `T`, the difference `spectralCount T' c₁ - spectralCount T' c₂`, which counts the
eigenvalues between the two cutoffs, is the same for every self-adjoint `T'` near `T`. -/
theorem eventually_spectralCount_sub_eq (h₁ : IsFiniteSpectralCutoff T c₁)
    (h₂ : IsFiniteSpectralCutoff T c₂) :
    ∀ᶠ T' in 𝓝[{T | IsSelfAdjoint T}] T,
      (spectralCount T' c₁ : ℤ) - spectralCount T' c₂ =
        (spectralCount T c₁ : ℤ) - spectralCount T c₂ := by
  rcases le_total c₂ c₁ with h | h
  · exact eventually_spectralCount_sub_eq_of_le h₁ h₂ h
  · filter_upwards [eventually_spectralCount_sub_eq_of_le h₂ h₁ h] with T' hT'
    linarith

end IsFiniteSpectralCutoff

/-- **Self-adjoint Fredholm operators have finite spectral cutoffs**: by the spectral gap at zero,
for small `c > 0` the spectral projection onto `(-c, c)` maps into the finite-dimensional
kernel. -/
theorem exists_isFiniteSpectralCutoff_of_isFredholm {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (hF : T.IsFredholm) : ∃ c, IsFiniteSpectralCutoff T c := by
  obtain ⟨c, hc, hcT, hcT', hle⟩ := hT.exists_pos_range_cfc_indicator_Ioo_le_ker_of_isFredholm hF
  have := hF.finite_ker
  exact ⟨c, hT, hc, hcT, hcT', Submodule.finiteDimensional_of_le hle⟩

end TauCeti
