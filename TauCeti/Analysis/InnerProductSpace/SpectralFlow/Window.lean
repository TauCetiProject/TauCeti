/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Analysis.InnerProductSpace.Spectral.ContinuousFunctionalCalculus
import TauCeti.LinearAlgebra.Projection.Add
import TauCeti.Topology.Algebra.Indicator

/-!
# Spectral windows of self-adjoint operators

Let `T` be a bounded self-adjoint operator on a real or complex Hilbert space `E`. For a set
`s ⊆ ℝ`, the spectral projector `cfc (s.indicator 1) T` projects onto the part of the spectrum of
`T` in `s`, and its rank `T.spectralRank s` counts the eigenvalues of `T` in `s` with multiplicity.

A number `r > 0` is a **spectral window** of `T` (`ContinuousLinearMap.IsSpectralWindow`) when
`±r` are not in the spectrum and the spectral projector of `(-r, r)` has finite rank. This is the
local datum in Phillips' definition of spectral flow: near an operator with window `r`, the
eigenvalues in `(-r, r)` are finitely many and cannot leave the window, so the number of them in
`[0, r)` changes only when an eigenvalue crosses `0`.

The main facts are the following.

* The spectrum meets a window in finitely many points
  (`ContinuousLinearMap.IsSpectralWindow.finite_spectrum_inter`): on the finite-dimensional range of
  the window projector, `T` has a minimal polynomial, and it vanishes at every spectral point of
  the window. Hence every point of the spectrum in the window is isolated, and the indicator of
  any subset of the window is continuous on the spectrum. In particular the spectral projector of
  `[0, r)` is a genuine functional calculus of `T`, even when `0` is an eigenvalue.
* Spectral ranks add over disjoint parts of a window
  (`ContinuousLinearMap.IsSpectralWindow.spectralRank_union`).
* Windows persist along convergent families of self-adjoint operators
  (`ContinuousLinearMap.IsSpectralWindow.eventually`), since the rank of a spectral projector is
  locally constant as long as the frontier of its set misses the spectrum
  (`IsSelfAdjoint.eventually_rank_range_cfc_indicator_eq`).
* For two windows `r` and `r'` of the limit, the difference of the counts in `[0, r)` and `[0, r')`
  is locally constant (`ContinuousLinearMap.IsSpectralWindow.eventually_spectralRank_sub_eq`), since
  it is the count in `[r, r')` up to sign. This makes spectral flow independent of the windows used
  to compute it.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
-/

public section

open Set Filter Topology Module Polynomial

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAlgebra ℝ (E →L[𝕜] E)] [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- The rank of the spectral projector `cfc (s.indicator 1) T` of `T` onto `s`. When `T` is
self-adjoint, the indicator of `s` is continuous on the spectrum of `T` (for instance when `s` lies
in a spectral window, `ContinuousLinearMap.IsSpectralWindow.continuousOn_indicator`) and the
projector has finite rank, this is the number of eigenvalues of `T` in `s`, counted with
multiplicity. Otherwise it is a junk value: `0` if the projector has infinite rank, or if the
indicator is discontinuous on the spectrum, where `cfc` returns `0`. -/
noncomputable def spectralRank (T : E →L[𝕜] E) (s : Set ℝ) : ℕ :=
  finrank 𝕜 (cfc (s.indicator (1 : ℝ → ℝ)) T).range

theorem spectralRank_def (T : E →L[𝕜] E) (s : Set ℝ) :
    spectralRank T s = finrank 𝕜 (cfc (s.indicator (1 : ℝ → ℝ)) T).range :=
  (rfl)

/-- A **spectral window** of a self-adjoint operator `T` is a number `r > 0` such that `r` and
`-r` are not in the spectrum of `T` and the spectral projector of `T` onto `(-r, r)` has finite
rank. -/
structure IsSpectralWindow (T : E →L[𝕜] E) (r : ℝ) : Prop where
  isSelfAdjoint : IsSelfAdjoint T
  pos : 0 < r
  notMem_spectrum : r ∉ spectrum ℝ T
  neg_notMem_spectrum : -r ∉ spectrum ℝ T
  finiteDimensional_range_Ioo :
    FiniteDimensional 𝕜 (cfc ((Ioo (-r) r).indicator (1 : ℝ → ℝ)) T).range

namespace IsSpectralWindow

variable {T : E →L[𝕜] E} {r : ℝ}

/-- The frontier `{-r, r}` of a spectral window misses the spectrum. -/
theorem disjoint_frontier_Ioo (hT : IsSpectralWindow T r) :
    Disjoint (frontier (Ioo (-r) r)) (spectrum ℝ T) := by
  rw [frontier_Ioo (by linarith [hT.pos])]
  simp [hT.notMem_spectrum, hT.neg_notMem_spectrum]

/-- The indicator of a spectral window is continuous on the spectrum. -/
private theorem continuousOn_indicator_Ioo (hT : IsSpectralWindow T r) :
    ContinuousOn ((Ioo (-r) r).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier hT.disjoint_frontier_Ioo

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

/-- The spectrum meets a spectral window in finitely many points. -/
theorem finite_spectrum_inter (hT : IsSpectralWindow T r) :
    (spectrum ℝ T ∩ Ioo (-r) r).Finite := by
  have hsa := hT.isSelfAdjoint
  have := hT.finiteDimensional_range_Ioo
  set P := cfc ((Ioo (-r) r).indicator (1 : ℝ → ℝ)) T with hP
  set F := (P : E →ₗ[𝕜] E).range
  have hcomm : T * P = P * T := by
    have := cfc_commute_cfc (R := ℝ) id ((Ioo (-r) r).indicator (1 : ℝ → ℝ)) T
    rwa [cfc_id ℝ T] at this
  have hF : ∀ x ∈ F, T x ∈ F := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, by simpa using congr($hcomm x).symm⟩
  -- View `F` as a real vector space, through `ℝ → 𝕜`.
  let : Module ℝ F := Module.compHom F (algebraMap ℝ 𝕜)
  have : IsScalarTower ℝ 𝕜 F := .of_algebraMap_smul fun _ _ ↦ rfl
  have : FiniteDimensional ℝ F := Module.Finite.trans 𝕜 F
  let C : Module.End ℝ F := ((T : E →ₗ[𝕜] E).restrict hF).restrictScalars ℝ
  have hμ : minpoly ℝ C ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral C)
  -- A real polynomial in `T` acts on `F` as the same polynomial in its restriction `C`.
  have haeval (q : ℝ[X]) (y : F) : aeval T q (y : E) = (aeval C q y : E) := by
    have hsc : Function.Semiconj ((↑) : F → E) C T := fun _ ↦ rfl
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a =>
      simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_one_mul]
      rw [← algebraMap_smul 𝕜 a (T ^ n), ← algebraMap_smul 𝕜 a (C ^ n)]
      simp only [_root_.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
        FunLike.coe_pow_eq_iterate, hsc.iterate_right n y]
  -- So the minimal polynomial of `T` on the range of the window projector kills that range.
  have hzero : aeval T (minpoly ℝ C) * P = 0 := by
    ext x
    simpa [minpoly.aeval] using haeval (minpoly ℝ C) ⟨P x, x, rfl⟩
  rw [← cfc_polynomial (minpoly ℝ C) T, hP,
    ← cfc_mul _ _ T (Polynomial.continuous _).continuousOn hT.continuousOn_indicator_Ioo] at hzero
  -- So every spectral point of the window is a root of the minimal polynomial.
  refine ((minpoly ℝ C).roots.toFinset.finite_toSet).subset fun x ⟨hx, hxI⟩ ↦ ?_
  have := eqOn_of_cfc_eq_cfc (hzero.trans (cfc_zero ℝ T).symm)
    ((Polynomial.continuous _).continuousOn.mul hT.continuousOn_indicator_Ioo) continuousOn_const
    hsa hx
  simp only [indicator_of_mem hxI, Pi.one_apply, mul_one] at this
  simpa [Polynomial.mem_roots hμ] using this

/-- Inside a spectral window, the indicator of any subset of the window is continuous on the
spectrum, since the spectrum meets the window in isolated points. -/
theorem continuousOn_indicator (hT : IsSpectralWindow T r) {s : Set ℝ} (hs : s ⊆ Ioo (-r) r) :
    ContinuousOn (s.indicator (1 : ℝ → ℝ)) (spectrum ℝ T) := by
  intro x hx
  by_cases hxI : x ∈ Ioo (-r) r
  · -- `x` is isolated in the spectrum: the other spectral points of the window form a finite set.
    have hU : Ioo (-r) r \ ((spectrum ℝ T ∩ Ioo (-r) r) \ {x}) ∈ 𝓝 x :=
      (isOpen_Ioo.sdiff hT.finite_spectrum_inter.sdiff.isClosed).mem_nhds ⟨hxI, fun h ↦ h.2 rfl⟩
    refine (continuousWithinAt_const (b := s.indicator 1 x)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [inter_mem_nhdsWithin (spectrum ℝ T) hU] with y ⟨hyT, hyU⟩
    have : y = x := by
      by_contra hne
      exact hyU.2 ⟨⟨hyT, hyU.1⟩, hne⟩
    rw [this]
  · -- Outside the closed window the indicator vanishes near `x`.
    have hxr : x ≠ r := fun h ↦ hT.notMem_spectrum (h ▸ hx)
    have hxr' : x ≠ -r := fun h ↦ hT.neg_notMem_spectrum (h ▸ hx)
    have hU : (Icc (-r) r)ᶜ ∈ 𝓝 x := isClosed_Icc.isOpen_compl.mem_nhds fun h ↦
      hxI ⟨lt_of_le_of_ne h.1 (Ne.symm hxr'), lt_of_le_of_ne h.2 hxr⟩
    refine ContinuousAt.continuousWithinAt <| (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hU] with y hy
    rw [indicator_of_notMem fun h ↦ hy (Ioo_subset_Icc_self (hs h))]

/-- The spectral projector of a subset of a spectral window has finite rank. -/
theorem finiteDimensional_range (hT : IsSpectralWindow T r) {s : Set ℝ} (hs : s ⊆ Ioo (-r) r) :
    FiniteDimensional 𝕜 (cfc (s.indicator (1 : ℝ → ℝ)) T).range := by
  have := hT.finiteDimensional_range_Ioo
  have hmul : cfc (s.indicator (1 : ℝ → ℝ)) T =
      cfc ((Ioo (-r) r).indicator (1 : ℝ → ℝ)) T * cfc (s.indicator (1 : ℝ → ℝ)) T := by
    rw [← cfc_mul _ _ T hT.continuousOn_indicator_Ioo (hT.continuousOn_indicator hs)]
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x ∈ s
    · simp [indicator_of_mem hx, indicator_of_mem (hs hx)]
    · simp [indicator_of_notMem hx]
  rw [hmul]
  exact Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

/-- Spectral ranks are additive over disjoint parts of a spectral window. -/
theorem spectralRank_union (hT : IsSpectralWindow T r) {s t : Set ℝ} (hs : s ⊆ Ioo (-r) r)
    (ht : t ⊆ Ioo (-r) r) (hst : Disjoint s t) :
    spectralRank T (s ∪ t) = spectralRank T s + spectralRank T t := by
  have hsc := hT.continuousOn_indicator hs
  have htc := hT.continuousOn_indicator ht
  have := hT.finiteDimensional_range hs
  have := hT.finiteDimensional_range ht
  have hidem (u : Set ℝ) :
      IsIdempotentElem ((cfc (u.indicator (1 : ℝ → ℝ)) T : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
    IsIdempotentElem.toLinearMap (TauCeti.isStarProjection_cfc_indicator T u).isIdempotentElem
  -- Spectral projectors of disjoint sets are orthogonal.
  have hzero {u v : Set ℝ} (huv : Disjoint u v)
      (hu : ContinuousOn (u.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
      (hv : ContinuousOn (v.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
      ((cfc (u.indicator (1 : ℝ → ℝ)) T : E →L[𝕜] E) : E →ₗ[𝕜] E) *
        ((cfc (v.indicator (1 : ℝ → ℝ)) T : E →L[𝕜] E) : E →ₗ[𝕜] E) = 0 := by
    rw [← ContinuousLinearMap.toLinearMap_mul, ← cfc_mul _ _ T hu hv]
    convert congrArg ((↑) : (E →L[𝕜] E) → E →ₗ[𝕜] E) (cfc_zero ℝ T) using 2
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x ∈ u
    · simp [indicator_of_mem hx, indicator_of_notMem (huv.notMem_of_mem_left hx)]
    · simp [indicator_of_notMem hx]
  simp only [spectralRank_def]
  rw [indicator_union_of_disjoint hst, cfc_add (a := T) _ _ hsc htc,
    ContinuousLinearMap.toLinearMap_add, LinearMap.IsIdempotentElem.finrank_range_add_of_mul_eq_zero
      (hidem s) (hidem t) (hzero hst hsc htc) (hzero hst.symm htc hsc)]

end IsSpectralWindow

section Family

variable {ι : Type*} {l : Filter ι} {A : ι → E →L[𝕜] E} {T : E →L[𝕜] E}

/-- A spectral window of the limit of a convergent family of self-adjoint operators is a spectral
window of the nearby operators. -/
theorem IsSpectralWindow.eventually {r : ℝ} (hT : IsSpectralWindow T r)
    (hA : Tendsto A l (𝓝 T)) (hsa : ∀ᶠ i in l, IsSelfAdjoint (A i)) :
    ∀ᶠ i in l, IsSpectralWindow (A i) r := by
  have hd := hT.disjoint_frontier_Ioo
  filter_upwards [hsa,
    hA.eventually (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hd),
    (tendsto_nhdsWithin_iff.2 ⟨hA, hsa⟩).eventually
      (hT.isSelfAdjoint.eventually_rank_range_cfc_indicator_eq hd)]
    with i hi hdi hrank
  rw [frontier_Ioo (by linarith [hT.pos]), disjoint_insert_left, disjoint_singleton_left] at hdi
  exact ⟨hi, hT.pos, hdi.2, hdi.1, Module.rank_lt_aleph0_iff.1 <|
      hrank ▸ Module.rank_lt_aleph0_iff.2 hT.finiteDimensional_range_Ioo⟩

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

/-- **Comparison of spectral windows.** For two spectral windows `r` and `r'` of the limit of a
convergent family of self-adjoint operators, the difference between the numbers of eigenvalues in
`[0, r)` and in `[0, r')` is eventually constant along the family. -/
theorem IsSpectralWindow.eventually_spectralRank_sub_eq {r r' : ℝ} (hr : IsSpectralWindow T r)
    (hr' : IsSpectralWindow T r') (hA : Tendsto A l (𝓝 T))
    (hsa : ∀ᶠ i in l, IsSelfAdjoint (A i)) :
    ∀ᶠ i in l, (spectralRank (A i) (Ico 0 r) : ℤ) - spectralRank (A i) (Ico 0 r') =
      (spectralRank T (Ico 0 r) : ℤ) - spectralRank T (Ico 0 r') := by
  wlog hle : r ≤ r' generalizing r r'
  · filter_upwards [this hr' hr (le_of_not_ge hle)] with i hi
    linarith
  -- For a window `r'` of `S`, the count in `[0, r')` is the count in `[0, r)` plus that in
  -- `[r, r')`.
  have hsplit {S : E →L[𝕜] E} (hS : IsSpectralWindow S r') :
      spectralRank S (Ico 0 r') = spectralRank S (Ico 0 r) + spectralRank S (Ico r r') := by
    rw [← hS.spectralRank_union (s := Ico 0 r) (t := Ico r r')
      (fun x hx ↦ ⟨by linarith [hS.pos, hx.1], by linarith [hx.2]⟩)
      (fun x hx ↦ ⟨by linarith [hS.pos, hr.pos, hx.1], hx.2⟩)
      (Set.disjoint_left.2 fun x hx hx' ↦ (not_le.2 hx.2) hx'.1),
      Ico_union_Ico_eq_Ico hr.pos.le hle]
  -- The count in `[r, r')` is locally constant, since `r` and `r'` are not in the spectrum.
  have hd : Disjoint (frontier (Ico r r')) (spectrum ℝ T) := by
    rcases hle.lt_or_eq with hlt | rfl
    · rw [frontier_Ico hlt]
      simp [hr.notMem_spectrum, hr'.notMem_spectrum]
    · simp
  filter_upwards [hr'.eventually hA hsa, (tendsto_nhdsWithin_iff.2 ⟨hA, hsa⟩).eventually
    (hr.isSelfAdjoint.eventually_rank_range_cfc_indicator_eq hd)] with i hi hrank
  rw [hsplit hi, hsplit hr', spectralRank_def (A i) (Ico r r'), spectralRank_def T (Ico r r'),
    finrank, finrank, hrank]
  push_cast
  ring

end Family

section Scalar

/-- The spectral rank of a scalar operator `c` on a set is `finrank 𝕜 E` if the set contains `c`,
and zero otherwise. (`finrank 𝕜 E` is itself zero when `E` is infinite-dimensional.) -/
theorem spectralRank_algebraMap (c : ℝ) (s : Set ℝ) [Decidable (c ∈ s)] :
    spectralRank (algebraMap ℝ (E →L[𝕜] E) c) s = if c ∈ s then finrank 𝕜 E else 0 := by
  rw [spectralRank_def, cfc_algebraMap]
  split_ifs with h
  · rw [indicator_of_mem h, Pi.one_apply, map_one, toLinearMap_one, Module.End.one_eq_id,
      LinearMap.range_id, finrank_top]
  · rw [indicator_of_notMem h, map_zero, toLinearMap_zero, LinearMap.range_zero, finrank_bot]

/-- On a finite-dimensional space, every `r > |c|` is a spectral window of the scalar operator
`c`. -/
theorem isSpectralWindow_algebraMap [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] [FiniteDimensional 𝕜 E]
    {c r : ℝ} (h : |c| < r) : IsSpectralWindow (algebraMap ℝ (E →L[𝕜] E) c) r := by
  -- The spectrum is `{c}`, or empty on the zero space.
  have hσ : spectrum ℝ (algebraMap ℝ (E →L[𝕜] E) c) ⊆ {c} := by
    rcases subsingleton_or_nontrivial (E →L[𝕜] E) with _ | _ <;>
      simp [spectrum.of_subsingleton]
  refine ⟨?_, (abs_nonneg c).trans_lt h, fun hr ↦ ?_, fun hr ↦ ?_, inferInstance⟩
  · rw [IsScalarTower.algebraMap_apply ℝ 𝕜]
    exact IsSelfAdjoint.algebraMap _ (RCLike.conj_ofReal c)
  · exact (le_abs_self c).not_gt (hσ hr ▸ h)
  · exact (neg_abs_le c).not_gt (by linarith [hσ hr ▸ neg_lt_neg h])

end Scalar

end ContinuousLinearMap
