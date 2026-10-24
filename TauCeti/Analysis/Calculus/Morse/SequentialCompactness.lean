/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CompactSublevel
public import TauCeti.Dynamics.Flow.Convergence
import TauCeti.Analysis.Calculus.Morse.Stable
import TauCeti.Analysis.Calculus.Morse.Transversality

/-!
# Sequential compactness of index-two Morse trajectories

For a Morse--Smale negative gradient flow with compact sublevels, a sequence of connecting
orbits of index difference two has an unbroken limit or a limit with exactly two nonconstant
components. We represent each original orbit by its point on a fixed regular intermediate
level. In the broken case, one component is the limit of these representatives and the other
is the limit of time translates of the same subsequence; the translating times diverge in the
appropriate direction. The breaking critical point has the unique intervening Morse index.

This is sequential convergence of trajectories, rather than merely a chain inferred from
closure incidence. It does not construct a topology on a compactified moduli space or prove
gluing.

## Reference

M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Metric Set Topology
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}

section

variable (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
  (hM : HasNondegenerateCriticalPointsOn f univ)
  (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c})
  (htr : IsMorseSmale f hf)

include hfs hM hcompact htr

/-- A forward break of an index-one tail must land in the original stable manifold. The
subsequence and divergent times retain the actual approximating trajectories. -/
private theorem exists_forward_break_of_index_one {q r y : E}
    (hr : IsNondegenerateCriticalPoint f r) (hqr : q ≠ r)
    (hind : morseIndex f r = morseIndex f q + 1)
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) r)
    {u : ℕ → E} (hu : Tendsto u atTop (𝓝 y))
    (huq : ∀ n, u n ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    ∃ z, z ∈ Flow.unstableSet (negativeGradientFlow f hf) r ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∧
      ∃ (n : ℕ → ℕ) (t : ℕ → ℝ), StrictMono n ∧
        Tendsto t atTop atTop ∧
        Tendsto (fun k ↦ negativeGradientFlow f hf (t k) (u (n k))) atTop (𝓝 z) := by
  let φ := negativeGradientFlow f hf
  let _ : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hfwd, hbwd⟩ :=
    (hpos.and
      ((hr.eventually_forall_mem_stableSet_of_forall_mem_closedBall
        (isNegativeGradient_negativeGradientFlow f hf)).and
      (hr.eventually_forall_mem_unstableSet_of_forall_mem_closedBall
        (isNegativeGradient_negativeGradientFlow f hf)))).exists
  obtain ⟨z, hzU, hzε, n, t, hn, ht, hzlim⟩ :=
    Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hε
      (isCompact_sphere r ε) hfwd hbwd hy hu
      (Frequently.of_forall fun n ↦ (Flow.disjoint_stableSet hqr).notMem_of_mem_left (huq n))
  have hzS : z ∈ closure (Flow.stableSet φ q) :=
    mem_closure_of_tendsto hzlim (Eventually.of_forall fun k ↦
      Flow.isInvariant_stableSet φ q (t k) (huq (n k)))
  obtain ⟨b, hb, hzb⟩ := exists_stableSet_of_isCompact_sublevel hfs hf hM z (hcompact _)
  have hrb : r ≠ b := by
    intro hrb
    subst b
    have hzr := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
      (isNegativeGradient_negativeGradientFlow f hf)
      (fun _ ↦ (hfs.differentiable (by norm_num)).differentiableAt)
      hfs.continuous.continuousAt ⟨hzU, hzb⟩
    simp [hzr] at hzε
    linarith
  have hbr := htr.morseIndex_lt hr hb hfs hrb hzU hzb
  have hbq : b = q := by
    by_contra hbq
    have hqb := hb.morseIndex_lt_of_mem_closure_stableSet_inter_stableSet hfs hf
      (Ne.symm hbq) ⟨z, hzS, hzb⟩
      (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _)) htr
    omega
  subst b
  obtain ⟨ψ, hψ, hnψ⟩ := strictMono_subseq_of_tendsto_atTop hn
  exact ⟨z, ⟨hzU, hzb⟩, n ∘ ψ, t ∘ ψ, hnψ, ht.comp hψ.tendsto_atTop,
    hzlim.comp hψ.tendsto_atTop⟩

/-- A backward break of an index-one head must originate in the original unstable manifold. -/
private theorem exists_backward_break_of_index_one {p r y : E}
    (hr : IsNondegenerateCriticalPoint f r) (hpr : p ≠ r)
    (hind : morseIndex f p = morseIndex f r + 1)
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) r)
    {u : ℕ → E} (hu : Tendsto u atTop (𝓝 y))
    (hup : ∀ n, u n ∈ Flow.unstableSet (negativeGradientFlow f hf) p) :
    ∃ z, z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) r ∧
      ∃ (n : ℕ → ℕ) (t : ℕ → ℝ), StrictMono n ∧
        Tendsto t atTop atBot ∧
        Tendsto (fun k ↦ negativeGradientFlow f hf (t k) (u (n k))) atTop (𝓝 z) := by
  let φ := negativeGradientFlow f hf
  let _ : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hfwd, hbwd⟩ :=
    (hpos.and
      ((hr.eventually_forall_mem_stableSet_of_forall_mem_closedBall
        (isNegativeGradient_negativeGradientFlow f hf)).and
      (hr.eventually_forall_mem_unstableSet_of_forall_mem_closedBall
        (isNegativeGradient_negativeGradientFlow f hf)))).exists
  obtain ⟨z, hzS, hzε, n, t, hn, ht, hzlim⟩ :=
    Flow.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet hε
      (isCompact_sphere r ε) hfwd hbwd hy hu
      (Frequently.of_forall fun n ↦ (Flow.disjoint_unstableSet hpr).notMem_of_mem_left (hup n))
  have hzU : z ∈ closure (Flow.unstableSet φ p) :=
    mem_closure_of_tendsto hzlim (Eventually.of_forall fun k ↦
      Flow.isInvariant_unstableSet φ p (t k) (hup (n k)))
  obtain ⟨a, ha, hza⟩ :=
    exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
      hfs hf hM (hcompact _) hzU
  have har : a ≠ r := by
    intro har
    subst a
    have hzr := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
      (isNegativeGradient_negativeGradientFlow f hf)
      (fun _ ↦ (hfs.differentiable (by norm_num)).differentiableAt)
      hfs.continuous.continuousAt ⟨hza, hzS⟩
    simp [hzr] at hzε
    linarith
  have hra := htr.morseIndex_lt ha hr hfs har hza hzS
  have hap : a = p := by
    by_contra hap
    have hap' := ha.morseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hfs hf
      (Ne.symm hap) ⟨z, hzU, hza⟩
      (fun {_} hw ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
        hfs hf hM (hcompact _) hw) htr
    omega
  subst a
  obtain ⟨ψ, hψ, hnψ⟩ := strictMono_subseq_of_tendsto_atTop hn
  exact ⟨z, ⟨hza, hzS⟩, n ∘ ψ, t ∘ ψ, hnψ, ht.comp hψ.tendsto_atTop,
    hzlim.comp hψ.tendsto_atTop⟩

/-- **Index-two sequential compactness at a regular intermediate level.** Every sequence in
`Wᵘ(p) ∩ Wˢ(q) ∩ {f = c}` has a subsequence converging locally uniformly in time to an
unbroken connecting trajectory or to one component of a pair broken at a critical point `r`.
In the latter case,
a second limit of time translates of that same subsequence supplies the other component.
The times tend to `+∞` if the level lies on the first component and to `-∞` if it lies on the
second; both components have index difference one.

Regularity is required on the whole level, so the first limit cannot be a constant critical
trajectory. The statement concerns actual sequential limits, without asserting a manifold
structure or gluing for the compactification. -/
theorem exists_subseq_unbroken_or_broken_of_morseIndex_eq_add_two
    {p q : E}
    (hind : morseIndex f p = morseIndex f q + 2)
    {c : ℝ}
    (hreg : ∀ y, f y = c → fderiv ℝ f y ≠ 0)
    (u : ℕ → E)
    (hu : ∀ n, u n ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
      Flow.stableSet (negativeGradientFlow f hf) q ∩ {z | f z = c}) :
    ∃ (n : ℕ → ℕ) (y : E), StrictMono n ∧ f y = c ∧
      TendstoLocallyUniformly (fun k s ↦ negativeGradientFlow f hf s (u (n k)))
        (fun s ↦ negativeGradientFlow f hf s y) atTop ∧
      (y ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
          Flow.stableSet (negativeGradientFlow f hf) q ∨
        ∃ (r z : E) (t : ℕ → ℝ), IsNondegenerateCriticalPoint f r ∧
          morseIndex f p = morseIndex f r + 1 ∧
          morseIndex f r = morseIndex f q + 1 ∧
          TendstoLocallyUniformly
            (fun k s ↦ negativeGradientFlow f hf (s + t k) (u (n k)))
            (fun s ↦ negativeGradientFlow f hf s z) atTop ∧
          ((y ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
              Flow.stableSet (negativeGradientFlow f hf) r ∧
            z ∈ Flow.unstableSet (negativeGradientFlow f hf) r ∩
              Flow.stableSet (negativeGradientFlow f hf) q ∧ Tendsto t atTop atTop) ∨
           (y ∈ Flow.unstableSet (negativeGradientFlow f hf) r ∩
              Flow.stableSet (negativeGradientFlow f hf) q ∧
            z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∩
              Flow.stableSet (negativeGradientFlow f hf) r ∧ Tendsto t atTop atBot))) := by
  -- Extract representatives on the compact level, then identify their two critical endpoints.
  -- Strict index drops leave at most one extra component; a second exit-point extraction
  -- recovers it from the original sequence while preserving the first orbit limit.
  let φ := negativeGradientFlow f hf
  obtain ⟨y, -, n, hn, hlim⟩ := (hcompact c).tendsto_subseq
    (x := u) (fun n ↦ (hu n).2.le)
  have hyc : f y = c :=
    (isClosed_eq hfs.continuous continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall fun k ↦ (hu (n k)).2)
  have hyU : y ∈ closure (Flow.unstableSet φ p) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ (hu (n k)).1.1)
  have hyS : y ∈ closure (Flow.stableSet φ q) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ (hu (n k)).1.2)
  obtain ⟨a, ha, hya⟩ :=
    exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
      hfs hf hM (hcompact _) hyU
  obtain ⟨b, hb, hyb⟩ := exists_stableSet_of_isCompact_sublevel hfs hf hM y (hcompact _)
  have hab : a ≠ b := by
    intro hab
    subst b
    have hya' := Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
      (isNegativeGradient_negativeGradientFlow f hf)
      (fun _ ↦ (hfs.differentiable (by norm_num)).differentiableAt)
      hfs.continuous.continuousAt ⟨hya, hyb⟩
    exact hreg y hyc (hya' ▸ ha.fderiv_eq_zero)
  have hba := htr.morseIndex_lt ha hb hfs hab hya hyb
  have hpa : a ≠ p → morseIndex f a < morseIndex f p := fun hap ↦
    ha.morseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hfs hf (Ne.symm hap)
      ⟨y, hyU, hya⟩
      (fun {_} hw ↦ exists_unstableSet_of_mem_closure_unstableSet_of_isCompact_sublevel
        hfs hf hM (hcompact _) hw) htr
  have hqb : b ≠ q → morseIndex f q < morseIndex f b := fun hbq ↦
    hb.morseIndex_lt_of_mem_closure_stableSet_inter_stableSet hfs hf (Ne.symm hbq)
      ⟨y, hyS, hyb⟩
      (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _)) htr
  -- Three nonconstant components would force an index drop of at least three.
  have hends : a = p ∨ b = q := by
    by_cases hap : a = p
    · exact Or.inl hap
    · right
      by_contra hbq
      have := hpa hap
      have := hqb hbq
      omega
  rcases hends with hap | hbq
  · subst a
    by_cases hbq : b = q
    · subst b
      exact ⟨n, y, hn, hyc, φ.tendstoLocallyUniformly_orbit hlim, Or.inl ⟨hya, hyb⟩⟩
    · have hqb' := hqb hbq
      have hpb : morseIndex f p = morseIndex f b + 1 := by omega
      have hbq' : morseIndex f b = morseIndex f q + 1 := by omega
      obtain ⟨z, hz, m, t, hm, ht, hzlim⟩ :=
        exists_forward_break_of_index_one hfs hf hM hcompact htr hb (Ne.symm hbq)
          hbq' hyb hlim (fun k ↦ (hu (n k)).1.2)
      exact ⟨n ∘ m, y, hn.comp hm, hyc,
        φ.tendstoLocallyUniformly_orbit (hlim.comp hm.tendsto_atTop),
        Or.inr ⟨b, z, t, hb, hpb, hbq',
          (φ.tendstoLocallyUniformly_orbit hzlim).congr
            (fun k s ↦ (φ.map_add s (t k) (u (n (m k)))).symm),
          Or.inl ⟨⟨hya, hyb⟩, hz, ht⟩⟩⟩
  · subst b
    by_cases hap : a = p
    · subst a
      exact ⟨n, y, hn, hyc, φ.tendstoLocallyUniformly_orbit hlim, Or.inl ⟨hya, hyb⟩⟩
    · have hpa' := hpa hap
      have hpa'' : morseIndex f p = morseIndex f a + 1 := by omega
      have haq : morseIndex f a = morseIndex f q + 1 := by omega
      obtain ⟨z, hz, m, t, hm, ht, hzlim⟩ :=
        exists_backward_break_of_index_one hfs hf hM hcompact htr ha (Ne.symm hap)
          hpa'' hya hlim (fun k ↦ (hu (n k)).1.1)
      exact ⟨n ∘ m, y, hn.comp hm, hyc,
        φ.tendstoLocallyUniformly_orbit (hlim.comp hm.tendsto_atTop),
        Or.inr ⟨a, z, t, ha, hpa'', haq,
          (φ.tendstoLocallyUniformly_orbit hzlim).congr
            (fun k s ↦ (φ.map_add s (t k) (u (n (m k)))).symm),
          Or.inr ⟨⟨hya, hyb⟩, hz, ht⟩⟩⟩

end

end TauCeti
