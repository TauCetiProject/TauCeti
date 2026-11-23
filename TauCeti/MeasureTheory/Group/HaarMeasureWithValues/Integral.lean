/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Basic
public import TauCeti.Topology.Algebra.Group.LocallyConstant.CompactSupport

/-!
# Integration against a Haar measure with values in a ring

Let `G` be a topological group, `A` a commutative semiring, `μ` an `A`-valued Haar measure on `G`
(`TauCeti.HaarMeasureWithValues A G`, with no normalisation) and `M` an `A`-module. A locally
constant function `f : G → M` with compact support, an element of `C_c^∞(G, M)`, is a finite sum
`f = ∑ 1_{K_i} • m_i` of indicators of compact open sets, and its integral is
`∫ f dμ = ∑ μ(K_i) • m_i` (`TauCeti.HaarMeasureWithValues.integral`). No topology or completeness
is needed on `M`, and taking `M = A` gives the scalar integral on `C_c^∞(G, A)`.

The integral is defined through the expansion of `f` by its nonzero fibres. The sum does not
depend on the expansion: for any finite family of pairwise disjoint compact open sets `K i` on which
`f` takes the values `v i`, and off whose union `f` vanishes, `∫ f dμ = ∑ μ(K i) • v i`
(`TauCeti.HaarMeasureWithValues.integral_eq_sum`). Two such families are compared through their
common refinement `K i ∩ L j`, using finite additivity of `μ`. Linearity follows by applying this to
the family of joint fibres of two test functions, and then the formula holds for every expansion
by indicators, with overlaps allowed (`TauCeti.HaarMeasureWithValues.integral_eq_sum_indicator`).

## Main definitions

* `TauCeti.HaarMeasureWithValues.integral μ`: the `A`-linear map `C_c^∞(G, M) → M`, `f ↦ ∫ f dμ`.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_eq_sum`: the integral computed from any finite family of
  pairwise disjoint compact open sets adapted to `f`.
* `TauCeti.HaarMeasureWithValues.integral_compactOpenIndicator`: `∫ 1_K • m dμ = μ(K) • m`.
* `TauCeti.HaarMeasureWithValues.integral_eq_sum_indicator`: the integral of a finite sum of
  indicators `∑ 1_{K_i} • m_i`, with overlaps allowed, is `∑ μ(K_i) • m_i`.
* `TauCeti.HaarMeasureWithValues.integral_locallyConstant_map`: naturality under `A`-linear maps
  `M → N`.
* `TauCeti.HaarMeasureWithValues.integral_eq_smul_sum_of_discrete`: on a finite discrete group,
  `∫ f dμ = μ({1}) • ∑_g f(g)`.
* `TauCeti.HaarMeasureWithValues.integral_eq_smul_sum`: for a compact open subgroup `U` and a
  right `U`-invariant test function, the integral is the coset sum `μ(U) • ∑_{gU} f(g)`.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.2, pp. 28–29.
-/

public section

open Set TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti.HaarMeasureWithValues

section JointFiber

variable {G M : Type*} [TopologicalSpace G] [AddCommMonoid M]

/-- The compact open set where `f` and `g` take the values `m` and `n` and are not both zero. -/
private def jointFiber {f g : LocallyConstant G M} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (m n : M) : CompactOpens G where
  carrier := f ⁻¹' {m} ∩ g ⁻¹' {n} ∩ (Function.support f ∪ Function.support g)
  isCompact' := by
    refine ((hasCompactSupport_iff_isCompact_support.1 hf).union
      (hasCompactSupport_iff_isCompact_support.1 hg)).of_isClosed_subset ?_ inter_subset_right
    exact ((f.isLocallyConstant.isClopen_fiber m).isClosed.inter
      (g.isLocallyConstant.isClopen_fiber n).isClosed).inter
      (f.isClopen_support.isClosed.union g.isClopen_support.isClosed)
  isOpen' := ((f.isLocallyConstant.isClopen_fiber m).isOpen.inter
    (g.isLocallyConstant.isClopen_fiber n).isOpen).inter
    (f.isClopen_support.isOpen.union g.isClopen_support.isOpen)

private theorem mem_jointFiber {f g : LocallyConstant G M} {hf : HasCompactSupport f}
    {hg : HasCompactSupport g} {m n : M} {x : G} :
    x ∈ jointFiber hf hg m n ↔ f x = m ∧ g x = n ∧ (f x ≠ 0 ∨ g x ≠ 0) := by
  change x ∈ f ⁻¹' {m} ∩ g ⁻¹' {n} ∩ (Function.support f ∪ Function.support g) ↔ _
  simp [and_assoc]

/-- The joint fibres of two test functions, indexed by pairs of values, form a family of pairwise
disjoint compact open sets on which both functions are constant, covering both supports. -/
private theorem jointFiber_spec {f g : LocallyConstant G M} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    ((((finite_range_of_hasCompactSupport hf).toFinset ×ˢ
        (finite_range_of_hasCompactSupport hg).toFinset : Finset (M × M)) : Set (M × M)
      ).PairwiseDisjoint fun p ↦ (jointFiber hf hg p.1 p.2 : Set G)) ∧
      (∀ p : M × M, ∀ x ∈ jointFiber hf hg p.1 p.2, f x = p.1 ∧ g x = p.2) ∧
      ∀ x, (f x ≠ 0 ∨ g x ≠ 0) → ∃ p ∈ (finite_range_of_hasCompactSupport hf).toFinset ×ˢ
        (finite_range_of_hasCompactSupport hg).toFinset, x ∈ jointFiber hf hg p.1 p.2 := by
  refine ⟨fun p _ q _ hpq ↦ Set.disjoint_left.2 fun x hxp hxq ↦ hpq ?_,
    fun p x hx ↦ ⟨(mem_jointFiber.1 hx).1, (mem_jointFiber.1 hx).2.1⟩, fun x hx ↦
      ⟨(f x, g x), by simp, mem_jointFiber.2 ⟨rfl, rfl, hx⟩⟩⟩
  obtain ⟨h1, h2, -⟩ := mem_jointFiber.1 hxp
  obtain ⟨h1', h2', -⟩ := mem_jointFiber.1 hxq
  exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')

end JointFiber

variable {A G M : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

section Semiring

variable [Semiring A] [AddCommMonoid M] [Module A M] (μ : HaarMeasureWithValues A G)

/-- Refining an expansion: if `f` takes the value `v i` on `K i`, and the pairwise disjoint compact
open sets `L j` cover the support of `f`, then `∑ μ(K i) • v i = ∑ μ(K i ∩ L j) • v i`. -/
private theorem sum_eq_sum_sum_inf [QuasiSeparatedSpace G] {f : G → M} {ι κ : Type*}
    {s : Finset ι} {K : ι → CompactOpens G} {v : ι → M} (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i)
    {t : Finset κ} {L : κ → CompactOpens G}
    (hL : (t : Set κ).PairwiseDisjoint fun j ↦ (L j : Set G))
    (hLf : ∀ x, f x ≠ 0 → ∃ j ∈ t, x ∈ L j) :
    ∑ i ∈ s, μ (K i) • v i = ∑ i ∈ s, ∑ j ∈ t, μ (K i ⊓ L j) • v i := by
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  by_cases h0 : v i = 0
  · simp [h0]
  have hdisj : (t : Set κ).PairwiseDisjoint fun j ↦ ((K i ⊓ L j : CompactOpens G) : Set G) :=
    fun j hj j' hj' hjj' ↦ (hL hj hj' hjj').mono inter_subset_right inter_subset_right
  rw [← Finset.sum_smul, ← μ.apply_finsetSup hdisj]
  congr 2
  refine CompactOpens.ext (Set.ext fun x ↦ ⟨fun hx ↦ ?_, ?_⟩)
  · obtain ⟨j, hj, hxj⟩ := hLf x (by rwa [hv i hi x hx])
    rw [CompactOpens.coe_finsetSup]
    exact mem_biUnion hj ⟨hx, hxj⟩
  · rw [CompactOpens.coe_finsetSup]
    simp only [mem_iUnion]
    exact fun ⟨_, _, hx⟩ ↦ hx.1

/-- **Independence of the expansion.** Two finite families of pairwise disjoint compact open sets
adapted to the same function, each covering its support, give the same sum. -/
private theorem sum_eq_sum_of_adapted [QuasiSeparatedSpace G] {f : G → M} {ι κ : Type*}
    {s : Finset ι} {K : ι → CompactOpens G} {v : ι → M}
    (hK : (s : Set ι).PairwiseDisjoint fun i ↦ (K i : Set G)) (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i)
    (hKf : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ K i) {t : Finset κ} {L : κ → CompactOpens G} {w : κ → M}
    (hL : (t : Set κ).PairwiseDisjoint fun j ↦ (L j : Set G)) (hw : ∀ j ∈ t, ∀ x ∈ L j, f x = w j)
    (hLf : ∀ x, f x ≠ 0 → ∃ j ∈ t, x ∈ L j) :
    ∑ i ∈ s, μ (K i) • v i = ∑ j ∈ t, μ (L j) • w j := by
  rw [sum_eq_sum_sum_inf μ hv hL hLf, sum_eq_sum_sum_inf μ hw hK hKf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [inf_comm]
  -- On a nonempty overlap both values are the value of `f`; an empty overlap has volume `0`.
  by_cases h : ∃ x, x ∈ K i ∧ x ∈ L j
  · obtain ⟨x, hxK, hxL⟩ := h
    rw [← hv i hi x hxK, ← hw j hj x hxL]
  · have hbot : L j ⊓ K i = ⊥ := CompactOpens.ext (Set.eq_empty_of_forall_notMem fun x hx ↦
      h ⟨x, hx.2, hx.1⟩)
    rw [hbot, apply_bot, zero_smul, zero_smul]

/-- The integral of a test function through its expansion by nonzero fibres; see
`TauCeti.HaarMeasureWithValues.integralAux_eq_sum` for its value on any adapted family. -/
private noncomputable def integralAux (f : LocallyConstant G M) (hf : HasCompactSupport f) : M :=
  ∑ m ∈ (exists_pairwiseDisjoint_sum_indicator hf).choose,
    μ ((exists_pairwiseDisjoint_sum_indicator hf).choose_spec.choose m) • m

private theorem integralAux_eq_sum [QuasiSeparatedSpace G] {f : LocallyConstant G M}
    (hf : HasCompactSupport f) {ι : Type*} {s : Finset ι} {K : ι → CompactOpens G} {v : ι → M}
    (hK : (s : Set ι).PairwiseDisjoint fun i ↦ (K i : Set G)) (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i)
    (hKf : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ K i) :
    integralAux μ f hf = ∑ i ∈ s, μ (K i) • v i := by
  obtain ⟨-, hfib, hdisj, hsum⟩ :=
    (exists_pairwiseDisjoint_sum_indicator hf).choose_spec.choose_spec
  refine sum_eq_sum_of_adapted μ hdisj (fun m hm x hx ↦ ?_) (fun x hx ↦ ?_) hK hv hKf
  · have : x ∈ ((exists_pairwiseDisjoint_sum_indicator hf).choose_spec.choose m : Set G) := hx
    rw [hfib m hm] at this
    exact this
  · -- A point outside every fibre contributes nothing to the expansion of `f`.
    by_contra! h
    refine hx ?_
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun m hm ↦ indicator_of_notMem (h m hm) _

end Semiring

section CommSemiring

variable [CommSemiring A] [AddCommMonoid M] [Module A M] (μ : HaarMeasureWithValues A G)

variable [QuasiSeparatedSpace G]

private theorem integralAux_add {f g : LocallyConstant G M} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    integralAux μ (f + g) (hf.add hg) = integralAux μ f hf + integralAux μ g hg := by
  obtain ⟨hd, hv, hcov⟩ := jointFiber_spec hf hg
  rw [integralAux_eq_sum μ hf hd (v := Prod.fst) (fun p _ x hx ↦ (hv p x hx).1)
      fun x hx ↦ hcov x (.inl hx),
    integralAux_eq_sum μ hg hd (v := Prod.snd) (fun p _ x hx ↦ (hv p x hx).2)
      fun x hx ↦ hcov x (.inr hx),
    integralAux_eq_sum μ (hf.add hg) hd (v := fun p ↦ p.1 + p.2)
      (fun p _ x hx ↦ by simp [(hv p x hx).1, (hv p x hx).2]) fun x hx ↦ hcov x <| by
        by_contra! h
        exact hx (by simp [h.1, h.2])]
  simp only [smul_add, Finset.sum_add_distrib]

private theorem integralAux_smul (c : A) {f : LocallyConstant G M} (hf : HasCompactSupport f) :
    integralAux μ (c • f) (hf.smul_left (f := fun _ ↦ c)) = c • integralAux μ f hf := by
  obtain ⟨hd, hv, hcov⟩ := jointFiber_spec hf hf
  rw [integralAux_eq_sum μ hf hd (v := Prod.fst) (fun p _ x hx ↦ (hv p x hx).1)
      fun x hx ↦ hcov x (.inl hx),
    integralAux_eq_sum μ (hf.smul_left (f := fun _ ↦ c)) hd (v := fun p ↦ c • p.1)
      (fun p _ x hx ↦ by simp [(hv p x hx).1]) fun x hx ↦ hcov x <| .inl fun h ↦ hx (by simp [h]),
    Finset.smul_sum]
  simp only [smul_comm c]

/-- **The integral** `∫ f dμ` of a locally constant function `f : G → M` with compact support
against an `A`-valued Haar measure `μ`: the sum `∑ μ(K_i) • m_i` over any finite expansion
`f = ∑ 1_{K_i} • m_i` by indicators of compact open sets
(`TauCeti.HaarMeasureWithValues.integral_eq_sum_indicator`). For `M = A` this is the scalar
integral on `C_c^∞(G, A)`. -/
noncomputable def integral : compactlySupported A G M →ₗ[A] M where
  toFun f := integralAux μ f (mem_compactlySupported.1 f.property)
  map_add' _ _ := integralAux_add μ _ _
  map_smul' c _ := integralAux_smul μ c _

/-- **Independence of the expansion.** For any finite family of pairwise disjoint compact open sets
`K i` such that `f` takes the value `v i` on `K i` and vanishes off their union,
`∫ f dμ = ∑ μ(K i) • v i`. -/
theorem integral_eq_sum (f : compactlySupported A G M) {ι : Type*} {s : Finset ι}
    {K : ι → CompactOpens G} {v : ι → M}
    (hK : (s : Set ι).PairwiseDisjoint fun i ↦ (K i : Set G))
    (hv : ∀ i ∈ s, ∀ x ∈ K i, (f : LocallyConstant G M) x = v i)
    (hKf : ∀ x, (f : LocallyConstant G M) x ≠ 0 → ∃ i ∈ s, x ∈ K i) :
    μ.integral f = ∑ i ∈ s, μ (K i) • v i :=
  integralAux_eq_sum μ (mem_compactlySupported.1 f.property) hK hv hKf

/-- The integral against the zero Haar measure vanishes. -/
@[simp]
theorem zero_integral (f : compactlySupported A G M) :
    (0 : HaarMeasureWithValues A G).integral f = 0 := by
  simp [integral, integralAux, zero_apply]

/-- The integral of the indicator `1_K • m` of a compact open set is `μ(K) • m`. -/
@[simp]
theorem integral_compactOpenIndicator [T2Space G] (K : CompactOpens G) (m : M) :
    μ.integral ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      μ K • m := by
  classical
  rw [integral_eq_sum μ _ (s := {()}) (K := fun _ ↦ K) (v := fun _ ↦ m) (by simp)
    (fun _ _ x hx ↦ compactOpenIndicator_of_mem hx m) fun x hx ↦ ⟨(), by simp, by_contra fun h ↦
      hx (compactOpenIndicator_of_notMem h m)⟩]
  simp

/-- **Expansions with overlaps.** If `f = ∑ 1_{K_i} • m_i` is a finite sum of indicators of compact
open sets, possibly overlapping, then `∫ f dμ = ∑ μ(K_i) • m_i`. -/
theorem integral_eq_sum_indicator [T2Space G] (f : compactlySupported A G M) {ι : Type*}
    (s : Finset ι) (K : ι → CompactOpens G) (m : ι → M)
    (hf : (f : LocallyConstant G M) = ∑ i ∈ s, compactOpenIndicator (K i) (m i)) :
    μ.integral f = ∑ i ∈ s, μ (K i) • m i := by
  have : f = ∑ i ∈ s, ⟨compactOpenIndicator (K i) (m i),
      compactOpenIndicator_mem_compactlySupported (K i) (m i)⟩ :=
    Subtype.ext (by rw [hf, Submodule.coe_sum])
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ integral_compactOpenIndicator μ (K i) (m i)

/-- **Naturality.** Integration commutes with `A`-linear maps `φ : M → N`. -/
theorem integral_locallyConstant_map {N : Type*} [AddCommMonoid N] [Module A N] (φ : M →ₗ[A] N)
    (f : compactlySupported A G M) :
    μ.integral ⟨(f : LocallyConstant G M).map φ, mem_compactlySupported.2
      ((mem_compactlySupported.1 f.property).comp_left (map_zero φ))⟩ = φ (μ.integral f) := by
  obtain ⟨hd, hv, hcov⟩ := jointFiber_spec (mem_compactlySupported.1 f.property)
    (mem_compactlySupported.1 f.property)
  rw [integral_eq_sum μ f hd (v := Prod.fst) (fun p _ x hx ↦ (hv p x hx).1)
      fun x hx ↦ hcov x (.inl hx),
    integral_eq_sum μ _ hd (v := fun p ↦ φ p.1) (fun p _ x hx ↦ by simp [(hv p x hx).1])
      fun x hx ↦ hcov x (.inl fun h ↦ hx (by simp [h])), map_sum]
  simp

/-- **Coset sums.** For a compact open subgroup `U` and a test function `f` invariant under right
translation by `U`, the integral is the sum over the cosets `gU` of `μ(U) • f(g)`, written through
the finitely supported function on `G ⧸ U` attached to `f`. -/
theorem integral_eq_smul_sum [IsTopologicalGroup G] (U : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) (f : compactlySupportedRightInvariant A M (U : Subgroup G)) :
    μ.integral ⟨f, compactlySupportedRightInvariant_le_compactlySupported _ f.property⟩ =
      μ (U.toCompactOpens hU) •
        (compactlySupportedRightInvariantEquiv U hU f).sum fun _ m ↦ m := by
  classical
  set φ := compactlySupportedRightInvariantEquiv U hU f
  -- `x ∈ q.out • U` exactly when `x` lies in the coset `q`.
  have hmem (q : G ⧸ (U : Subgroup G)) (x : G) :
      x ∈ q.out • U.toCompactOpens hU ↔ (x : G ⧸ (U : Subgroup G)) = q := by
    rw [CompactOpens.mem_smul_iff_inv_smul_mem, OpenSubgroup.mem_toCompactOpens, smul_eq_mul,
      ← OpenSubgroup.mem_toSubgroup, ← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  rw [integral_eq_sum μ _ (s := φ.support) (K := fun q ↦ q.out • U.toCompactOpens hU)
      (v := fun q ↦ φ q) (fun q _ q' _ hqq' ↦ Set.disjoint_left.2 fun x hx hx' ↦
        hqq' (((hmem q x).1 hx).symm.trans ((hmem q' x).1 hx')))
      (fun q _ x hx ↦ by simp [φ, ← (hmem q x).1 hx])
      fun x hx ↦ ⟨x, by simpa [φ] using hx, (hmem _ x).2 rfl⟩,
    Finsupp.sum, Finset.smul_sum]
  simp

/-- **Finite discrete groups.** On a finite discrete group the integral is the volume of a point
times the sum of the values: `∫ f dμ = μ({1}) • ∑_g f(g)`. -/
theorem integral_eq_smul_sum_of_discrete [DiscreteTopology G] [Fintype G]
    (f : compactlySupported A G M) :
    μ.integral f = μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ •
      ∑ g, (f : LocallyConstant G M) g := by
  classical
  let K : G → CompactOpens G := fun g ↦ ⟨⟨{g}, isCompact_singleton⟩, isOpen_discrete _⟩
  -- Each point is a translate of the identity, so all points have the same volume.
  have hK (g : G) : μ (K g) = μ (K 1) := by
    rw [← μ.apply_smul g (K 1)]
    congr 1
    exact CompactOpens.ext (by simp [K, CompactOpens.coe_smul])
  rw [integral_eq_sum μ f (s := Finset.univ) (K := K) (v := fun g ↦ (f : LocallyConstant G M) g)
      (fun g _ g' _ hgg' ↦ Set.disjoint_singleton.2 hgg')
      -- Membership in the compact open set `K g` is membership in `{g}`.
      (fun g _ x hx ↦ by rw [show x = g from hx]) fun x _ ↦ ⟨x, Finset.mem_univ x, rfl⟩,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [hK]

end CommSemiring

end TauCeti.HaarMeasureWithValues
