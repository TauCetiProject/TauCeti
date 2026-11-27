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
common refinement `K i ∩ L j`, using finite additivity of `μ`; on the support of the first family
`K i ∩ L j` is compact, so no separation hypothesis on `G` is needed. Linearity follows by applying
this to the nonzero fibres of the pair `x ↦ (f x, g x)` of two test functions, and then the formula
holds for every expansion by indicators, with overlaps allowed
(`TauCeti.HaarMeasureWithValues.integral_eq_sum_smul_of_eq_sum_compactOpenIndicator`).

## Main definitions

* `TauCeti.HaarMeasureWithValues.integral μ`: the `A`-linear map `C_c^∞(G, M) → M`, `f ↦ ∫ f dμ`.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_eq_sum`: the integral computed from any finite family of
  pairwise disjoint compact open sets adapted to `f`.
* `TauCeti.HaarMeasureWithValues.integral_compactOpenIndicator`: `∫ 1_K • m dμ = μ(K) • m`.
* `TauCeti.HaarMeasureWithValues.integral_eq_sum_smul_of_eq_sum_compactOpenIndicator`: the
  integral of a finite sum of indicators `∑ 1_{K_i} • m_i`, with overlaps allowed, is
  `∑ μ(K_i) • m_i`.
* `TauCeti.HaarMeasureWithValues.eq_integral_of_apply_compactOpenIndicator`: uniqueness; a linear
  map with these values on indicators is the integral.
* `TauCeti.HaarMeasureWithValues.integral_smul_measure`: `∫ f d(cμ) = c ∫ f dμ`.
* `TauCeti.HaarMeasureWithValues.integral_comp_comm`: naturality under `A`-linear maps `M → N`.
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

variable {A G M : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

omit [Group G] [ContinuousConstSMul G G] in
/-- The nonzero fibres in an expansion `F = ∑ 1_{K p} • p` of a test function are adapted to `F`:
`F` takes the value `p` on `K p`, and every point where `F` is nonzero lies in some `K p`. -/
private theorem adapted_of_sum_indicator {N : Type*} [AddCommMonoid N] {F : LocallyConstant G N}
    {s : Finset N} {K : N → CompactOpens G} (hfib : ∀ p ∈ s, (K p : Set G) = F ⁻¹' {p})
    (hsum : ⇑F = ∑ p ∈ s, (K p : Set G).indicator fun _ ↦ p) :
    (∀ p ∈ s, ∀ x ∈ K p, F x = p) ∧ ∀ x, F x ≠ 0 → ∃ p ∈ s, x ∈ K p := by
  refine ⟨fun p hp x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rwa [← SetLike.mem_coe, hfib p hp] at hx
  · -- A point outside every fibre contributes nothing to the expansion of `F`.
    by_contra! h
    refine hx ?_
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun p hp ↦ indicator_of_notMem (h p hp) _

section Semiring

variable [Semiring A] [AddCommMonoid M] [Module A M] (μ : HaarMeasureWithValues A G)

open Classical in
/-- The volume of a set that is compact and open, and `0` for any other set. -/
private noncomputable def volume (S : Set G) : A :=
  if h : IsCompact S ∧ IsOpen S then μ ⟨⟨S, h.1⟩, h.2⟩ else 0

private theorem volume_coe (K : CompactOpens G) : volume μ (K : Set G) = μ K := by
  rw [volume, dite_eq_left ⟨K.isCompact, K.isOpen⟩]
  exact congrArg μ (CompactOpens.ext rfl)

private theorem volume_empty : volume μ (∅ : Set G) = 0 := by
  rw [← CompactOpens.coe_bot, volume_coe, apply_bot]

/-- Refining an expansion: if `f` takes the value `v i` on `K i`, and the pairwise disjoint compact
open sets `L j` cover the support of `f`, then `∑ μ(K i) • v i = ∑ μ(K i ∩ L j) • v i`. -/
private theorem sum_eq_sum_sum_inter {f : G → M} {ι κ : Type*} {s : Finset ι}
    {K : ι → CompactOpens G} {v : ι → M} (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i) {t : Finset κ}
    {L : κ → CompactOpens G} (hL : (t : Set κ).PairwiseDisjoint fun j ↦ (L j : Set G))
    (hLf : ∀ x, f x ≠ 0 → ∃ j ∈ t, x ∈ L j) :
    ∑ i ∈ s, μ (K i) • v i = ∑ i ∈ s, ∑ j ∈ t, volume μ ((K i : Set G) ∩ L j) • v i := by
  classical
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  by_cases h0 : v i = 0
  · simp [h0]
  -- Since `f = v i ≠ 0` on `K i`, the sets `L j` cover `K i`, so `K i ∩ L j` is `K i` minus the
  -- other `L j'`: a compact set.
  have hcov (x : G) (hx : x ∈ K i) : ∃ j ∈ t, x ∈ L j := hLf x (by rwa [hv i hi x hx])
  have hc (j : κ) (hj : j ∈ t) : IsCompact ((K i : Set G) ∩ L j) := by
    have h : (K i : Set G) ∩ L j = (K i : Set G) \ ⋃ j' ∈ t.erase j, (L j' : Set G) := by
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_iUnion, Finset.mem_erase, SetLike.mem_coe,
        not_exists]
      refine ⟨fun ⟨hxK, hxL⟩ ↦ ⟨hxK, fun j' ⟨hj', hj't⟩ hxL' ↦
        Set.disjoint_left.1 (hL hj't hj hj') hxL' hxL⟩, fun ⟨hxK, hx⟩ ↦ ⟨hxK, ?_⟩⟩
      obtain ⟨j', hj't, hxL'⟩ := hcov x hxK
      by_cases hjj : j' = j
      · exact hjj ▸ hxL'
      · exact absurd hxL' (hx j' ⟨hjj, hj't⟩)
    rw [h]
    exact (K i).isCompact.diff (isOpen_biUnion fun j' _ ↦ (L j').isOpen)
  let P : κ → CompactOpens G := fun j ↦
    if hj : j ∈ t then ⟨⟨(K i : Set G) ∩ L j, hc j hj⟩, (K i).isOpen.inter (L j).isOpen⟩ else ⊥
  have hP (j : κ) (hj : j ∈ t) : (P j : Set G) = (K i : Set G) ∩ L j := by
    simp only [P, dite_eq_left hj]
    rfl
  have hdisj : (t : Set κ).PairwiseDisjoint fun j ↦ (P j : Set G) := fun j hj j' hj' hjj' ↦ by
    rw [Function.onFun, hP j hj, hP j' hj']
    exact (hL hj hj' hjj').mono inter_subset_right inter_subset_right
  have hsup : t.sup P = K i := by
    refine CompactOpens.ext (Set.ext fun x ↦ ?_)
    simp only [CompactOpens.coe_finsetSup, mem_iUnion, exists_prop]
    refine ⟨fun ⟨j, hj, hx⟩ ↦ ?_, fun hx ↦ ?_⟩
    · rw [hP j hj] at hx
      exact hx.1
    · obtain ⟨j, hj, hxL⟩ := hcov x hx
      exact ⟨j, hj, by rw [hP j hj]; exact ⟨hx, hxL⟩⟩
  have hμ : μ (K i) = ∑ j ∈ t, μ (P j) := by rw [← μ.apply_finsetSup hdisj, hsup]
  rw [← Finset.sum_smul, hμ]
  exact congrArg (· • v i) (Finset.sum_congr rfl fun j hj ↦ by rw [← volume_coe, hP j hj])

/-- **Independence of the expansion.** Two finite families of pairwise disjoint compact open sets
adapted to the same function, each covering its support, give the same sum. -/
private theorem sum_eq_sum_of_adapted {f : G → M} {ι κ : Type*}
    {s : Finset ι} {K : ι → CompactOpens G} {v : ι → M}
    (hK : (s : Set ι).PairwiseDisjoint fun i ↦ (K i : Set G)) (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i)
    (hKf : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ K i) {t : Finset κ} {L : κ → CompactOpens G} {w : κ → M}
    (hL : (t : Set κ).PairwiseDisjoint fun j ↦ (L j : Set G)) (hw : ∀ j ∈ t, ∀ x ∈ L j, f x = w j)
    (hLf : ∀ x, f x ≠ 0 → ∃ j ∈ t, x ∈ L j) :
    ∑ i ∈ s, μ (K i) • v i = ∑ j ∈ t, μ (L j) • w j := by
  rw [sum_eq_sum_sum_inter μ hv hL hLf, sum_eq_sum_sum_inter μ hw hK hKf, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [inter_comm]
  -- On a nonempty overlap both values are the value of `f`; an empty overlap has volume `0`.
  by_cases h : ∃ x, x ∈ K i ∧ x ∈ L j
  · obtain ⟨x, hxK, hxL⟩ := h
    rw [← hv i hi x hxK, ← hw j hj x hxL]
  · have hempty : (L j : Set G) ∩ K i = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ h ⟨x, hx.2, hx.1⟩
    rw [hempty, volume_empty, zero_smul, zero_smul]

/-- The integral of a test function through its expansion by nonzero fibres; see
`TauCeti.HaarMeasureWithValues.integralAux_eq_sum` for its value on any adapted family. -/
private noncomputable def integralAux (f : LocallyConstant G M) (hf : HasCompactSupport f) : M :=
  ∑ m ∈ (exists_pairwiseDisjoint_sum_indicator hf).choose,
    μ ((exists_pairwiseDisjoint_sum_indicator hf).choose_spec.choose m) • m

private theorem integralAux_eq_sum {f : LocallyConstant G M}
    (hf : HasCompactSupport f) {ι : Type*} {s : Finset ι} {K : ι → CompactOpens G} {v : ι → M}
    (hK : (s : Set ι).PairwiseDisjoint fun i ↦ (K i : Set G)) (hv : ∀ i ∈ s, ∀ x ∈ K i, f x = v i)
    (hKf : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ K i) :
    integralAux μ f hf = ∑ i ∈ s, μ (K i) • v i := by
  obtain ⟨-, hfib, hdisj, hsum⟩ :=
    (exists_pairwiseDisjoint_sum_indicator hf).choose_spec.choose_spec
  obtain ⟨hv', hcov⟩ := adapted_of_sum_indicator hfib hsum
  exact sum_eq_sum_of_adapted μ hdisj hv' hcov hK hv hKf

/-- **Naturality of the auxiliary integral.** If `g = φ ∘ f` for an `A`-linear map `φ`, then the
integral of `g` is `φ` applied to the integral of `f`. -/
private theorem integralAux_comp_left {N : Type*} [AddCommMonoid N] [Module A N] (φ : M →ₗ[A] N)
    {f : LocallyConstant G M} (hf : HasCompactSupport f) {g : LocallyConstant G N}
    (hg : HasCompactSupport g) (hfg : ∀ x, g x = φ (f x)) :
    integralAux μ g hg = φ (integralAux μ f hf) := by
  obtain ⟨s, K, -, hfib, hd, hsum⟩ := exists_pairwiseDisjoint_sum_indicator hf
  obtain ⟨hv, hcov⟩ := adapted_of_sum_indicator hfib hsum
  rw [integralAux_eq_sum μ hf hd hv hcov,
    integralAux_eq_sum μ hg hd (v := φ) (fun m hm x hx ↦ by rw [hfg, hv m hm x hx])
      fun x hx ↦ hcov x fun h ↦ hx (by rw [hfg, h, map_zero]), map_sum]
  simp only [map_smul]

end Semiring

section CommSemiring

variable [CommSemiring A] [AddCommMonoid M] [Module A M] (μ : HaarMeasureWithValues A G)

private theorem integralAux_add {f g : LocallyConstant G M} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    integralAux μ (f + g) (hf.add hg) = integralAux μ f hf + integralAux μ g hg := by
  -- Expand the pair `x ↦ (f x, g x)` by its nonzero fibres: both functions are constant on them.
  let F : LocallyConstant G (M × M) :=
    ⟨fun x ↦ (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  have hF : HasCompactSupport F := hf.comp₂_left hg (m := Prod.mk) rfl
  have hFx (x : G) : F x = (f x, g x) := rfl
  obtain ⟨s, K, -, hfib, hd, hsum⟩ := exists_pairwiseDisjoint_sum_indicator hF
  obtain ⟨hv, hcov⟩ := adapted_of_sum_indicator hfib hsum
  have hv₁ (p : M × M) (hp : p ∈ s) (x : G) (hx : x ∈ K p) : f x = p.1 := by
    rw [← hv p hp x hx, hFx]
  have hv₂ (p : M × M) (hp : p ∈ s) (x : G) (hx : x ∈ K p) : g x = p.2 := by
    rw [← hv p hp x hx, hFx]
  have hF0 (x : G) (h : F x = 0) : f x = 0 ∧ g x = 0 := by rwa [hFx, Prod.mk_eq_zero] at h
  rw [integralAux_eq_sum μ hf hd hv₁ fun x hx ↦ hcov x fun h ↦ hx (hF0 x h).1,
    integralAux_eq_sum μ hg hd hv₂ fun x hx ↦ hcov x fun h ↦ hx (hF0 x h).2,
    integralAux_eq_sum μ (hf.add hg) hd (v := fun p ↦ p.1 + p.2)
      (fun p hp x hx ↦ by simp [hv₁ p hp x hx, hv₂ p hp x hx]) fun x hx ↦ hcov x fun h ↦ hx <| by
        simp [(hF0 x h).1, (hF0 x h).2]]
  simp only [smul_add, Finset.sum_add_distrib]

private theorem integralAux_smul (c : A) {f : LocallyConstant G M} (hf : HasCompactSupport f) :
    integralAux μ (c • f) (hf.smul_left (f := fun _ ↦ c)) = c • integralAux μ f hf := by
  rw [integralAux_comp_left μ (c • LinearMap.id) hf (hf.smul_left (f := fun _ ↦ c))
    fun x ↦ by simp]
  simp

/-- **The integral** `∫ f dμ` of a locally constant function `f : G → M` with compact support
against an `A`-valued Haar measure `μ`: the sum `∑ μ(K_i) • m_i` over any finite expansion
`f = ∑ 1_{K_i} • m_i` by indicators of compact open sets
(`TauCeti.HaarMeasureWithValues.integral_eq_sum_smul_of_eq_sum_compactOpenIndicator`). For
`M = A` this is the scalar integral on `C_c^∞(G, A)`. -/
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
theorem integral_zero_measure (f : compactlySupported A G M) :
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

/-- An `A`-linear map on `C_c^∞(G, M)` sending each indicator `1_K • m` of a compact open set to
`μ(K) • m` sends any expansion `f = ∑ 1_{K_i} • m_i`, possibly overlapping, to
`∑ μ(K_i) • m_i`. -/
private theorem apply_eq_sum_smul_of_eq_sum_compactOpenIndicator [T2Space G]
    (L : compactlySupported A G M →ₗ[A] M)
    (hL : ∀ (K : CompactOpens G) (m : M),
      L ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ = μ K • m)
    (f : compactlySupported A G M) {ι : Type*} (s : Finset ι) (K : ι → CompactOpens G)
    (m : ι → M) (hf : (f : LocallyConstant G M) = ∑ i ∈ s, compactOpenIndicator (K i) (m i)) :
    L f = ∑ i ∈ s, μ (K i) • m i := by
  have : f = ∑ i ∈ s, ⟨compactOpenIndicator (K i) (m i),
      compactOpenIndicator_mem_compactlySupported (K i) (m i)⟩ :=
    Subtype.ext (by rw [hf, Submodule.coe_sum])
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hL (K i) (m i)

/-- **Expansions with overlaps.** If `f = ∑ 1_{K_i} • m_i` is a finite sum of indicators of compact
open sets, possibly overlapping, then `∫ f dμ = ∑ μ(K_i) • m_i`. -/
theorem integral_eq_sum_smul_of_eq_sum_compactOpenIndicator [T2Space G]
    (f : compactlySupported A G M) {ι : Type*} (s : Finset ι) (K : ι → CompactOpens G)
    (m : ι → M) (hf : (f : LocallyConstant G M) = ∑ i ∈ s, compactOpenIndicator (K i) (m i)) :
    μ.integral f = ∑ i ∈ s, μ (K i) • m i :=
  apply_eq_sum_smul_of_eq_sum_compactOpenIndicator μ μ.integral (integral_compactOpenIndicator μ)
    f s K m hf

/-- **Uniqueness.** An `A`-linear map on `C_c^∞(G, M)` sending each indicator `1_K • m` of a
compact open set to `μ(K) • m` is the integral against `μ`. -/
theorem eq_integral_of_apply_compactOpenIndicator [T2Space G]
    (L : compactlySupported A G M →ₗ[A] M)
    (hL : ∀ (K : CompactOpens G) (m : M),
      L ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ = μ K • m) :
    L = μ.integral := by
  ext f
  obtain ⟨s, K, hf⟩ := exists_eq_sum_compactOpenIndicator (mem_compactlySupported.1 f.property)
  rw [apply_eq_sum_smul_of_eq_sum_compactOpenIndicator μ L hL f s K id hf,
    integral_eq_sum_smul_of_eq_sum_compactOpenIndicator μ f s K id hf]

/-- **Integrals against a rescaled measure**: `∫ f d(cμ) = c ∫ f dμ`. -/
@[simp]
theorem integral_smul_measure [T2Space G] (c : A) (f : compactlySupported A G M) :
    (c • μ).integral f = c • μ.integral f := by
  have h := eq_integral_of_apply_compactOpenIndicator (c • μ)
      (c • μ.integral : compactlySupported A G M →ₗ[A] M) fun K m ↦ by
    rw [LinearMap.smul_apply, integral_compactOpenIndicator, smul_apply, smul_assoc]
  exact (LinearMap.congr_fun h f).symm

/-- **Naturality.** Integration commutes with `A`-linear maps `φ : M → N`. -/
@[simp]
theorem integral_comp_comm {N : Type*} [AddCommMonoid N] [Module A N] (φ : M →ₗ[A] N)
    (f : compactlySupported A G M) :
    μ.integral ⟨(f : LocallyConstant G M).map φ, mem_compactlySupported.2
      ((mem_compactlySupported.1 f.property).comp_left (map_zero φ))⟩ = φ (μ.integral f) :=
  integralAux_comp_left μ φ (mem_compactlySupported.1 f.property)
    ((mem_compactlySupported.1 f.property).comp_left (map_zero φ)) fun _ ↦ rfl

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
  rw [integral_eq_sum μ _ (s := φ.support) (K := fun q ↦ q.out • U.toCompactOpens hU)
      (v := fun q ↦ φ q) (U.pairwiseDisjoint_out_smul_toCompactOpens hU _)
      (fun q _ x hx ↦ by simp [φ, ← (U.mem_out_smul_toCompactOpens_iff hU q x).1 hx])
      fun x hx ↦ ⟨x, by simpa [φ] using hx, (U.mem_out_smul_toCompactOpens_iff hU _ x).2 rfl⟩,
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
  have hKcoe (g : G) : (K g : Set G) = {g} := rfl
  have hKmem (g x : G) : x ∈ K g ↔ x = g := by
    rw [← SetLike.mem_coe, hKcoe, mem_singleton_iff]
  -- Each point is a translate of the identity, so all points have the same volume.
  have hK (g : G) : μ (K g) = μ (K 1) := by
    rw [← μ.apply_smul g (K 1)]
    congr 1
    exact CompactOpens.ext (by simp [hKcoe, CompactOpens.coe_smul])
  rw [integral_eq_sum μ f (s := Finset.univ) (K := K) (v := fun g ↦ (f : LocallyConstant G M) g)
      (fun g _ g' _ hgg' ↦ by
        rw [Function.onFun, hKcoe, hKcoe]
        exact Set.disjoint_singleton.2 hgg')
      (fun g _ x hx ↦ by rw [(hKmem g x).1 hx]) fun x _ ↦ ⟨x, Finset.mem_univ x, (hKmem x x).2 rfl⟩,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by rw [hK]

end CommSemiring

end TauCeti.HaarMeasureWithValues
