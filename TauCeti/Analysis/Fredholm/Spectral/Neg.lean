/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Topology.Algebra.Indicator
import TauCeti.Topology.Order.Interval.Basic

/-!
# The spectral flow of the negated path

Let `A` be a continuous path of self-adjoint Fredholm operators on a real or complex Hilbert space
over `[a, b]`. The eigenvalues of `-A t` are those of `A t` with the opposite sign, so an eigenvalue
crossing `0` upwards along `A` crosses downwards along `-A`, and one expects the spectral flow of
`-A` to be minus that of `A`. Phillips' counts are not symmetric, though: they place the eigenvalue
`0` with the nonnegative ones. So an eigenvalue that only reaches `0` at an endpoint counts for one
of the two paths and not for the other, and the correct statement is

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`

(`TauCeti.spectralFlow_neg`). In particular negation negates the spectral flow when the endpoints
are invertible (`TauCeti.spectralFlow_neg_of_ker_eq_bot`). This is how the two sign conventions for
the trajectory operator, `d/ds + A` and `d/ds - A`, are compared.

The proof compares local counts. A spectral cut of `A` is one of `-A`
(`TauCeti.isSpectralCutOn_neg_iff`), since the interval `[-c, c]` is symmetric. At an operator `S`
with a cut `c`, the eigenvalues of `-S` in `[0, c]` are those of `S` in `[-c, 0]`, and together
with those of `S` in `[0, c]` they make up all the eigenvalues of `S` in `[-c, c]`, the eigenvalue
`0` counted twice:

`#(-S, [0, c]) + #(S, [0, c]) = #(S, [-c, c]) + dim ker S`

(`TauCeti.spectralCount_neg_add_spectralCount`). Along an interval with a cut, the middle term is
constant, so `t ↦ dim ker A(t) - F t` is a spectral flow potential of `-A` whenever `F` is one of
`A`.

## Main results

* `TauCeti.isSpectralCutOn_neg_iff`: spectral cuts of the negated family.
* `TauCeti.spectralCount_neg_add_spectralCount`: the eigenvalue counts of `-S` and of `S`.
* `TauCeti.spectralFlow_neg`: the spectral flow of `-A`.
* `TauCeti.spectralFlow_neg_of_ker_eq_bot`: with invertible endpoints, negating the path negates
  its spectral flow.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
-/

public section

open Filter Metric Set Topology
open scoped Pointwise

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

/-- **Spectral cuts of the negated family.** `c` is a spectral cut of `u ↦ -A u` on `s` exactly
when it is a spectral cut of `A` on `s`. -/
theorem isSpectralCutOn_neg_iff {α : Type*} {A : α → H →L[𝕜] H} {c : ℝ} {s : Set α} :
    IsSpectralCutOn (fun u ↦ -A u) c s ↔ IsSpectralCutOn A c s := by
  simp only [isSpectralCutOn_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun u _ ↦ ?_
  have hmem : -c ∉ spectrum ℝ (-A u) ∧ c ∉ spectrum ℝ (-A u) ↔
      -c ∉ spectrum ℝ (A u) ∧ c ∉ spectrum ℝ (A u) := by
    simp only [← spectrum.neg_eq, Set.mem_neg, neg_neg]
    exact and_comm
  rw [← and_assoc, ← and_assoc, hmem]
  refine and_congr_right fun ⟨h₁, h₂⟩ ↦ ?_
  have hf : ContinuousOn ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (spectrum ℝ (-A u)) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Icc (by rwa [← spectrum.neg_eq, Set.mem_neg, neg_neg])
        (by rwa [← spectrum.neg_eq, Set.mem_neg]))
  rw [cfc_indicator_neg _ hf, neg_Icc, neg_neg]

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- **The eigenvalue counts of `-S` and of `S`.** Let `S` be self-adjoint and `c > 0` with `±c`
outside its spectrum and a spectral projection for `[-c, c]` of finite rank. The eigenvalues of
`-S` in `[0, c]` are those of `S` in `[-c, 0]`, so together with the eigenvalues of `S` in `[0, c]`
they are the eigenvalues of `S` in `[-c, c]`, with the eigenvalue `0` counted twice. -/
theorem spectralCount_neg_add_spectralCount {S : H →L[𝕜] H} (hS : IsSelfAdjoint S) {c : ℝ}
    (hc : 0 < c) (h₁ : -c ∉ spectrum ℝ S) (h₂ : c ∉ spectrum ℝ S)
    (hfd : FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range) :
    spectralCount c (-S) + spectralCount c S =
      Module.finrank 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range +
        Module.finrank 𝕜 S.ker := by
  have hfr : Disjoint (frontier (Icc (-c) c)) (spectrum ℝ S) := disjoint_frontier_Icc h₁ h₂
  have hcut : ContinuousOn ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier hfr
  have hfin : (spectrum ℝ S ∩ Icc (-c) c).Finite :=
    hS.finite_spectrum_inter_of_finiteDimensional_range_cfc_indicator hcut hfd
  -- Every subset of `[-c, c]` has an indicator continuous on the spectrum and a spectral
  -- projection of finite rank.
  have hcont {Ω : Set ℝ} (hΩ : Ω ⊆ Icc (-c) c) :
      ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    hfin.continuousOn_indicator hΩ hfr
  have hfd' {Ω : Set ℝ} (hΩ : Ω ⊆ Icc (-c) c) :
      FiniteDimensional 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range :=
    Submodule.finiteDimensional_of_le (S.range_cfc_indicator_le_of_subset hΩ (hcont hΩ) hcut)
  have hneg : Icc (-c) (0 : ℝ) ⊆ Icc (-c) c := Icc_subset_Icc le_rfl hc.le
  have hpos : Ioc (0 : ℝ) c ⊆ Icc (-c) c := Ioc_subset_Icc_self.trans
    (Icc_subset_Icc (by linarith) le_rfl)
  have hzero : Icc (0 : ℝ) 0 ⊆ Icc (-c) c := Icc_subset_Icc (by linarith) hc.le
  have := hfd' hneg
  have := hfd' hpos
  have := hfd' hzero
  -- The count of `-S` is the rank of the spectral projection of `S` for `[-c, 0]`.
  have hcount : spectralCount c (-S) =
      Module.finrank 𝕜 (cfc ((Icc (-c) 0).indicator (1 : ℝ → ℝ)) S).range := by
    -- `-S` also has finitely many spectral values in `[-c, c]`, and `±c` outside its spectrum.
    have hfin' : (spectrum ℝ (-S) ∩ Icc (-c) c).Finite := by
      rw [← spectrum.neg_eq, ← neg_neg (Icc (-c) c), neg_Icc, neg_neg, ← inter_neg]
      exact hfin.neg
    have hf : ContinuousOn ((Icc 0 c).indicator (1 : ℝ → ℝ)) (spectrum ℝ (-S)) :=
      hfin'.continuousOn_indicator (Icc_subset_Icc (by linarith) le_rfl)
        (disjoint_frontier_Icc (by rwa [← spectrum.neg_eq, Set.mem_neg, neg_neg])
          (by rwa [← spectrum.neg_eq, Set.mem_neg]))
    rw [spectralCount_def, cfc_indicator_neg _ hf, neg_Icc, neg_zero]
  have hdisj : Disjoint (Icc (-c) (0 : ℝ)) (Ioc 0 c) :=
    disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.2) hx'.1
  have hdisj₀ : Disjoint (Icc (0 : ℝ) 0) (Ioc 0 c) :=
    disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.2) hx'.1
  -- `[-c, c] = [-c, 0] ∪ (0, c]` and `[0, c] = {0} ∪ (0, c]`.
  have hall := S.finrank_range_cfc_indicator_union hdisj (hcont hneg) (hcont hpos)
  have hnonneg := S.finrank_range_cfc_indicator_union hdisj₀ (hcont hzero) (hcont hpos)
  rw [Icc_union_Ioc_eq_Icc (by linarith) hc.le] at hall
  rw [Icc_union_Ioc_eq_Icc le_rfl hc.le] at hnonneg
  -- `0` is isolated in the spectrum, so the projection for `{0}` is the kernel projection.
  have hG : ((spectrum ℝ S ∩ Icc (-c) c) \ {0}).Finite := hfin.sdiff
  have hiso : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ∉ spectrum ℝ S := by
    filter_upwards [nhdsWithin_le_nhds (hG.isClosed.compl_mem_nhds fun h ↦ h.2 rfl),
      nhdsWithin_le_nhds (Icc_mem_nhds (neg_neg_of_pos hc) hc), self_mem_nhdsWithin]
      with x hx hxc hx0 hxσ using hx ⟨⟨hxσ, hxc⟩, hx0⟩
  rw [hcount, spectralCount_def, hall, hnonneg, Icc_self,
    hS.cfc_indicator_singleton_zero_eq_starProjection_ker hiso, Submodule.range_starProjection]
  ring

variable {A : ℝ → H →L[𝕜] H} {a b : ℝ}

/-- **The spectral flow of the negated path.** For a continuous path `A` of self-adjoint Fredholm
operators on `[a, b]`,

`SF(-A; a, b) = dim ker A(b) - dim ker A(a) - SF(A; a, b)`.

The correction comes from Phillips' convention, which counts the eigenvalue `0` with the
nonnegative ones, for `A` as for `-A`. -/
theorem spectralFlow_neg (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    spectralFlow (fun t ↦ -A t) a b =
      (Module.finrank 𝕜 (A b).ker : ℤ) - Module.finrank 𝕜 (A a).ker - spectralFlow A a b := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  -- `t ↦ dim ker A(t) - F t` is a spectral flow potential of `-A`.
  have hG : IsSpectralFlowPotential (fun t ↦ -A t) a b
      fun t ↦ (Module.finrank 𝕜 (A t).ker : ℤ) - F t := by
    rw [isSpectralFlowPotential_iff]
    intro s t c has hst htb hc
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hsa' : ∀ u ∈ Icc s t, IsSelfAdjoint (A u) := fun u hu ↦ hsa u (hsub hu)
    have hcA := isSpectralCutOn_neg_iff.1 hc
    have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
    have ht : t ∈ Icc s t := ⟨hst, le_rfl⟩
    have hcount (u : ℝ) (hu : u ∈ Icc s t) := spectralCount_neg_add_spectralCount (hsa' u hu)
      hcA.pos (hcA.neg_notMem_spectrum hu) (hcA.notMem_spectrum hu)
      (hcA.finiteDimensional_range_cfc_indicator_Icc hu)
    -- The rank of the spectral projection for `[-c, c]` is constant along `[s, t]`.
    have hrank := isPreconnected_Icc.finrank_range_cfc_indicator_eq (hA.mono hsub) hsa'
      (fun u hu ↦ disjoint_frontier_Icc (hcA.neg_notMem_spectrum hu) (hcA.notMem_spectrum hu))
      hs ht
    have := hFp.sub_eq has hst htb hcA
    have := hcount s hs
    have := hcount t ht
    linarith
  rw [spectralFlow_eq_sub (A := fun t ↦ -A t) hab hA.neg (fun t ht ↦ (hsa t ht).neg)
      (fun t ht ↦ (hF t ht).neg) hG,
    spectralFlow_eq_sub hab hA hsa hF hFp]
  ring

/-- **Negation with invertible endpoints.** For a continuous path `A` of self-adjoint Fredholm
operators on `[a, b]` whose endpoints are injective, the spectral flow of `-A` is minus that of
`A`. -/
theorem spectralFlow_neg_of_ker_eq_bot (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥) :
    spectralFlow (fun t ↦ -A t) a b = -spectralFlow A a b := by
  rw [spectralFlow_neg hab hA hsa hF, ha, hb, finrank_bot]
  ring

end TauCeti
