/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Differential.Basic
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Microlocality
import TauCeti.Analysis.Distribution.LineDeriv

/-!
# Differential systems on distributions and microlocal elliptic regularity

Let `V` and `W` be finite-dimensional complex inner product spaces. A differential system on `ℝⁿ`
from `V`-valued to `W`-valued functions, in the form in which it acts on distributions, is

`P T = ∑ i ∈ t, A i (g i ∂^(m i) T)`,

with constant matrices `A i : V →L[ℂ] W`, smooth real coefficient functions `g i` and iterated
directional derivatives `∂^(m i)` of orders `k i ≤ M`. Every system with smooth matrix coefficients
has this form, by expanding the coefficients in a basis of `V →L[ℂ] W`. Its classical symbol is
`TauCeti.ClassicalSymbol.ofDifferentialSymbol` with the coefficients `x ↦ g i x • A i`, whose
quantization has kernel supported on the diagonal and so acts on all `V`-valued distributions
(`TauCeti.Symbol.quantizeDistribution`). This file shows that this action is the differential
system `P` (`TauCeti.ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol_smul`); for
`V = W = ℂ` it is the scalar statement
`TauCeti.ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol`, from which it is deduced entry
by entry (`TauCeti.Symbol.mapCLM_quantizeDistribution_eq_sum`).

The characteristic set of the classical symbol of a differential operator of order `M` consists of
the covectors `(x, ξ)`, `ξ ≠ 0`, at which the matrix
`σ_M(P)(x, ξ) = ∑ i ∈ t with k i = M, (∏ l, Complex.I * ⟪ξ, m i l⟫) • g i x • A i`
is not invertible (`TauCeti.ClassicalSymbol.characteristicSet_toSymbol_ofDifferentialSymbol`).
The microlocal elliptic regularity of properly supported systems
(`TauCeti.Symbol.vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet`) then
gives **microlocal elliptic regularity for differential systems**: for every `V`-valued
distribution `T`,

`WF(T) ⊆ WF(P T) ∪ Char(P)`

(`Distribution.vectorWaveFrontSet_subset_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_union`), while
`WF(P T) ⊆ WF(T)` always
(`Distribution.vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_subset`). So a system
elliptic at every point and every nonzero covector, such as `d + d*` or a Dirac operator in
coordinates, preserves wave front sets and singular supports
(`Distribution.vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible`,
`Distribution.singularSupport_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible`).

For a system, ellipticity is invertibility of the matrix `σ_M(P)(x, ξ)`, not the nonvanishing of
some entry: the scalar theorem
`Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`
does not apply entrywise, since a component of `P T` involves every component of `T`.

## Main results

* `TauCeti.ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol_smul`: the action on
  distributions of the classical symbol of a differential system is the differential system.
* `TauCeti.ClassicalSymbol.characteristicSet_toSymbol_ofDifferentialSymbol`: the characteristic set
  of a differential operator is where its principal symbol is not invertible.
* `Distribution.vectorWaveFrontSet_subset_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_union`:
  microlocal elliptic regularity `WF(T) ⊆ WF(P T) ∪ Char(P)` for differential systems.
* `Distribution.vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible`,
  `Distribution.singularSupport_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible`:
  elliptic systems preserve wave front sets and singular supports.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1 (microlocal elliptic regularity for scalar operators).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between vector bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Distributions LineDeriv InnerProductSpace

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ} {ι : Type*} {k : ι → ℕ}

/-! ### The characteristic set of a differential operator -/

section CharacteristicSet

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **The characteristic set of a differential operator** of order `M` consists of the points
`(x, ξ)`, `ξ ≠ 0`, at which the differential symbol of its summands of order exactly `M` is not
invertible. -/
theorem characteristicSet_toSymbol_ofDifferentialSymbol (M : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ M) :
    (ofDifferentialSymbol M s v b hb hk).toSymbol.characteristicSet =
      {p | p.2 ≠ 0 ∧ ¬ (differentialSymbol {i ∈ s | k i = M} v b p).IsInvertible} := by
  rw [characteristicSet_toSymbol]
  ext ⟨x, ξ⟩
  exact and_congr_right fun hξ ↦ by
    rw [coefficient_principal_ofDifferentialSymbol M s v b hb hk hξ]

end CharacteristicSet

/-! ### Differential systems on distributions -/

section System

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {M : ℕ} {t : Finset ι} {m : ∀ i, Fin (k i) → CoordinateSpace n}
  {g : ι → CoordinateSpace n → ℝ} {A : ι → V →L[ℂ] W} {hk : ∀ i ∈ t, k i ≤ M}
  {hb : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ g i x • A i} {R : ℝ}

omit [CompleteSpace V] [FiniteDimensional ℂ V] [CompleteSpace W] [FiniteDimensional ℂ W] in
/-- The scalar entry `ℓ ∘ a ∘ e` of the symbol `a` of the differential system with coefficients
`g i • A i` is the symbol of the scalar differential operator with coefficients
`ℓ (A i e) g i`. -/
private theorem coefficient_map_entryMap_ofDifferentialSymbol (ℓ : W →L[ℂ] ℂ) (e : V)
    (hb' : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ (ℓ (A i e) * g i x) • ContinuousLinearMap.id ℂ ℂ) :
    ((ofDifferentialSymbol M t m (fun i x ↦ g i x • A i) hb hk).toSymbol.map
      (Symbol.entryMap ℓ e)).coefficient =
      (ofDifferentialSymbol M t m (fun i x ↦ (ℓ (A i e) * g i x) • ContinuousLinearMap.id ℂ ℂ)
        hb' hk).toSymbol.coefficient := by
  funext p
  ext
  simp only [Symbol.coefficient_map, coefficient_toSymbol_ofDifferentialSymbol,
    Symbol.entryMap_apply, differentialSymbol_def]
  simp [map_sum, mul_comm, mul_left_comm]

/-- **Differential systems on distributions.** For the system
`P = ∑ i ∈ t, A i g i ∂^(m i)` with constant matrices `A i : V →L[ℂ] W` and smooth real
coefficients `g i`, the action of the quantization of its classical symbol on a `V`-valued
distribution `T` by transposition is the differential system
`P T = ∑ i ∈ t, A i (g i ∂^(m i) T)`, with the distributional derivatives of `T`. -/
theorem quantizeDistribution_ofDifferentialSymbol_smul (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (ha : (ofDifferentialSymbol M t m (fun i x ↦ g i x • A i) hb hk).toSymbol.HasNearDiagonalKernel
      R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    Symbol.quantizeDistribution ha T =
      ∑ i ∈ t, Distribution.mapCLM ((A i).restrictScalars ℝ)
        (Distribution.smulLeftCLM (hg i) (∂^{m i} T)) := by
  let e := Module.finBasis ℂ V
  have hb' (ℓ : W →L[ℂ] ℂ) (j : Fin (Module.finrank ℂ V)) :
      ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ (ℓ (A i (e j)) * g i x) • ContinuousLinearMap.id ℂ ℂ :=
    fun i _ ↦ (contDiff_const.mul (ofRealCLM.contDiff.comp (hg i))).smul contDiff_const
  ext φ
  refine ext_inner_left ℂ fun w ↦ ?_
  -- Read both sides through the functional `ℓ = ⟪w, ·⟫`, entry by entry in the basis `e` of `V`.
  set ℓ : W →L[ℂ] ℂ := innerSL ℂ w
  have hentry (j : Fin (Module.finrank ℂ V)) :
      Symbol.quantizeDistribution (ha.map ℓ _ (Symbol.entryMap_apply ℓ (e j))) =
        Symbol.quantizeDistribution
          (hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol M t m _ (hb' ℓ j) hk one_pos) :=
    Symbol.quantizeDistribution_congr _ _
      (coefficient_map_entryMap_ofDifferentialSymbol ℓ (e j) (hb' ℓ j))
  have h := congrArg (fun S : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ) ↦ S φ)
    (Symbol.mapCLM_quantizeDistribution_eq_sum ha e ℓ T)
  simp only [Distribution.mapCLM_apply, ContinuousLinearMap.coe_restrictScalars', hentry,
    quantizeDistribution_ofDifferentialSymbol hg] at h
  rw [← innerSL_apply_apply, h]
  -- Expand the values of `T` in the basis `e`: `ℓ (A i X) = ∑ j, ℓ (A i (e j)) e*_j X`.
  have hX (i : ι) (X : V) : ℓ (A i X) = ∑ j, ℓ (A i (e j)) * e.repr X j := by
    calc ℓ (A i X) = ℓ (A i (∑ j, e.repr X j • e j)) := by rw [e.sum_repr]
      _ = ∑ j, ℓ (A i (e j)) * e.repr X j := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  simp only [sum_apply, smul_apply,
    Distribution.smulLeftCLM_apply, Distribution.iteratedLineDerivOp_apply_apply,
    Distribution.mapCLM_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [Finset.sum_comm, ← innerSL_apply_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hX, ← Complex.coe_smul, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul, Module.Basis.coord_apply,
    LinearMap.coe_toContinuousLinearMap']
  push_cast
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Complex.real_smul]; push_cast; ring

end System

end ClassicalSymbol

end TauCeti

/-! ### Microlocal elliptic regularity for differential systems -/

namespace Distribution

open TauCeti

variable {n : ℕ} {ι : Type*} {k : ι → ℕ} {V W : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W] {M : ℕ} {t : Finset ι}
  {m : ∀ i, Fin (k i) → CoordinateSpace n} {g : ι → CoordinateSpace n → ℝ} {A : ι → V →L[ℂ] W}

/-- **Differential systems do not enlarge wave front sets.** For the system
`P = ∑ i ∈ t, A i g i ∂^(m i)` with constant matrices `A i : V →L[ℂ] W` and smooth real
coefficients `g i`, `WF(P T) ⊆ WF(T)` for every `V`-valued distribution `T`. -/
theorem vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_subset
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ)
      (smulLeftCLM (hg i) (∂^{m i} T))).vectorWaveFrontSet ⊆ T.vectorWaveFrontSet := by
  have hb : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ g i x • A i := fun i _ ↦ (hg i).smul contDiff_const
  have ha := ClassicalSymbol.hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol (t.sup k) t m _
    hb (fun _ hi ↦ Finset.le_sup hi) one_pos
  rw [← ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol_smul hg ha]
  exact Symbol.vectorWaveFrontSet_quantizeDistribution_subset ha T

/-- **Microlocal elliptic regularity for differential systems.** For
the system `P = ∑ i ∈ t, A i g i ∂^(m i)` of order at most `M`, with constant matrices
`A i : V →L[ℂ] W` and smooth real coefficients `g i`, every `V`-valued distribution `T` satisfies
`WF(T) ⊆ WF(P T) ∪ Char(P)`, where `Char(P)` consists of the covectors `(x, ξ)`, `ξ ≠ 0`, at which
the principal symbol `∑ i ∈ t with k i = M, (∏ l, Complex.I * ⟪ξ, m i l⟫) • g i x • A i` is not
invertible. -/
theorem vectorWaveFrontSet_subset_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_union
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, k i ≤ M)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.vectorWaveFrontSet ⊆
      (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ)
        (smulLeftCLM (hg i) (∂^{m i} T))).vectorWaveFrontSet ∪
        {p | p.2 ≠ 0 ∧
          ¬ (differentialSymbol {i ∈ t | k i = M} m (fun i x ↦ g i x • A i) p).IsInvertible} := by
  have hb : ∀ i ∈ t, ContDiff ℝ ∞ fun x ↦ g i x • A i := fun i _ ↦ (hg i).smul contDiff_const
  have ha := ClassicalSymbol.hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol M t m _ hb hk
    one_pos
  rw [← ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol_smul hg ha,
    ← ClassicalSymbol.characteristicSet_toSymbol_ofDifferentialSymbol M t m _ hb hk]
  exact Symbol.vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet ha T

/-- **Elliptic differential systems preserve wave front sets.** If the principal symbol of the
system `P = ∑ i ∈ t, A i g i ∂^(m i)` of order at most `M` is invertible at every point and every
nonzero covector, then `WF(P T) = WF(T)` for every `V`-valued distribution `T`. -/
theorem vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, k i ≤ M)
    (hell : ∀ x ξ, ξ ≠ 0 →
      (differentialSymbol {i ∈ t | k i = M} m (fun i x ↦ g i x • A i) (x, ξ)).IsInvertible)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ)
      (smulLeftCLM (hg i) (∂^{m i} T))).vectorWaveFrontSet = T.vectorWaveFrontSet := by
  refine (vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_subset hg T).antisymm
    fun p hp ↦ ?_
  rcases vectorWaveFrontSet_subset_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_union (A := A) hg hk
    T hp with h | ⟨hξ, hinv⟩
  · exact h
  · exact absurd (hell p.1 p.2 hξ) hinv

/-- **Elliptic differential systems preserve singular supports.** If the principal symbol of the
system `P = ∑ i ∈ t, A i g i ∂^(m i)` of order at most `M` is invertible at every point and every
nonzero covector, then `P T` is smooth exactly where the `V`-valued distribution `T` is. -/
theorem singularSupport_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hk : ∀ i ∈ t, k i ≤ M)
    (hell : ∀ x ξ, ξ ≠ 0 →
      (differentialSymbol {i ∈ t | k i = M} m (fun i x ↦ g i x • A i) (x, ξ)).IsInvertible)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ)
      (smulLeftCLM (hg i) (∂^{m i} T))).singularSupport = T.singularSupport := by
  rw [← fst_image_vectorWaveFrontSet (F := W), ← fst_image_vectorWaveFrontSet T,
    vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_iteratedLineDerivOp_of_isInvertible hg hk hell]

end Distribution
