/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Hom
import TauCeti.LinearAlgebra.FixedSubmodule
import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Orbit-sum realizations of a folded root system

Let `P` be a root pairing with finitely many roots, `b` a base of `P`, and `σ` an automorphism of
`P`. When `σ` permutes the simple roots of `b`, the orbit sums `RootPairing.orbitSum P σ i` lie in
the fixed submodule `E^σ = LinearMap.fixedSubmodule σ.weightMap`, and the distinct orbit sums are
indexed by `RootPairing.foldedIndices P σ`.

An **orbit-sum realization** (`RootPairing.OrbitSumRealization P b σ`) bundles a reduced
crystallographic root system on `E^σ` and its linear dual `Module.Dual R E^σ`, indexed by
`P.foldedIndices σ`, together with a base whose simple roots are the orbit sums of the simple roots
of `b`. Its pairing is evaluation, and each root index maps to its ambient orbit-sum vector.

Before turning to specific folding constructions, this file develops the linear algebra of
simple-orbit sums that holds for *every* based automorphism, together with the structural properties
shared by all orbit-sum realizations:

* **Linear independence, spanning, and cone expansions of simple-orbit sums.** Without any
  orthogonality hypothesis on the orbits of `σ`, distinct simple-root orbits have distinct orbit
  sums (`RootPairing.orbitSum_eq_orbitSum_iff_of_mem_support`), the simple-orbit sums are linearly
  independent in `E^σ` (`RootPairing.linearIndepOn_foldedRoot_simpleFoldedIndices`), they span
  `E^σ` whenever `P` is a root system (`RootPairing.span_foldedRoot_simpleFoldedIndices_eq_top`),
  and in characteristic zero every orbit sum of a positive root expands as a natural combination of
  simple-orbit sums (`RootPairing.foldedRoot_mem_closure_simpleFoldedIndices_of_isPos`).
* **Uniqueness.** In characteristic zero over an integral domain, the root vectors, the evaluation
  pairing, and the base-support characterization determine the coroots, reflections, and base
  uniquely (`RootPairing.OrbitSumRealization.ext`,
  `RootPairing.OrbitSumRealization.instSubsingleton`).
* **Positive-root lifts.** In characteristic zero, a folded root of any orbit-sum realization is
  positive relative to the folded base if and only if it is the orbit sum of a `b`-positive root
  (`RootPairing.OrbitSumRealization.isPos_iff_exists_isPos`).
* **Identity and intertwining equivalences.** The identity automorphism `1 : P.Aut` admits a
  realization canonically equivalent to `(P, b)` (`RootPairing.OrbitSumRealization.one`,
  `RootPairing.OrbitSumRealization.equivSelfOne`), and based equivalences intertwining two
  automorphisms transport realizations and induce based equivalences between them
  (`RootPairing.OrbitSumRealization.map`,
  `RootPairing.OrbitSumRealization.equivOfIntertwining`).

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pages 1–3.
-/

public section

namespace RootPairing

open Finset Function Set Submodule TauCeti

section SimpleOrbits

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] (b : P.Base) (σ : P.Aut)

/-- Each distinct orbit-sum index viewed as a vector in the fixed submodule `E^σ`. -/
noncomputable def foldedRoot (γ : P.foldedIndices σ) :
    LinearMap.fixedSubmodule σ.weightMap :=
  ⟨(γ : M), by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp γ.property
    exact hi ▸ P.orbitSum_mem_fixedSubmodule σ i⟩

@[simp]
theorem coe_foldedRoot (γ : P.foldedIndices σ) :
    (P.foldedRoot σ γ : M) = (γ : M) :=
  (rfl)

theorem foldedRoot_injective : Injective (P.foldedRoot σ) :=
  fun _ _ h ↦ Subtype.ext (by simpa only [coe_foldedRoot] using congrArg Subtype.val h)

/-- The finite set of folded root indices arising as orbit sums of simple roots of `b`. -/
noncomputable def simpleFoldedIndices : Finset (P.foldedIndices σ) :=
  (Set.toFinite {γ : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (γ : M)}).toFinset

@[simp]
theorem mem_simpleFoldedIndices {γ : P.foldedIndices σ} :
    γ ∈ P.simpleFoldedIndices b σ ↔ ∃ j ∈ b.support, P.orbitSum σ j = (γ : M) := by
  simp [simpleFoldedIndices]

variable {P b σ}

/-- If `σ` maps `b.support` into itself, every member of the root orbit of a simple root is
simple. -/
theorem mem_support_of_mem_orbitIndices (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ P.orbitIndices σ i) : j ∈ b.support := by
  rcases mem_orbitIndices_iff_exists_pow.mp hj with ⟨k, rfl⟩
  clear hj
  induction k with
  | zero => simpa using hi
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hσ _ ih

omit [Finite ι] in
/-- Since `b.support` is finite and `σ.indexEquiv` is injective, mapping `b.support` into itself is
equivalent to preserving `b.support` in both directions. -/
theorem mem_support_indexEquiv_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i : ι} :
    σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  classical
  have hmap := congrArg Base.support (b.map_eq_of_forall_mem_support hσ)
  rw [b.support_map_eq] at hmap
  conv_lhs => rw [← hmap, Finset.mem_image]
  exact ⟨fun ⟨j, hj, hji⟩ ↦ σ.indexEquiv.injective hji ▸ hj, fun hi ↦ ⟨i, hi, rfl⟩⟩

/-- Over a nontrivial ring, two simple roots have the same orbit sum if and only if they lie in the
same `σ`-orbit. -/
theorem orbitSum_eq_orbitSum_iff_of_mem_support [Nontrivial R]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.orbitSum σ i = P.orbitSum σ j ↔ j ∈ P.orbitIndices σ i := by
  refine ⟨fun heq ↦ ?_, fun hmem ↦ (orbitSum_eq_of_mem hmem).symm⟩
  classical
  have hsubI : P.orbitIndices σ i ⊆ b.support := fun k hk ↦ mem_support_of_mem_orbitIndices hσ hi hk
  have hsubJ : P.orbitIndices σ j ⊆ b.support := fun k hk ↦ mem_support_of_mem_orbitIndices hσ hj hk
  have hsum :
      ∑ k ∈ b.support, (if k ∈ P.orbitIndices σ i then (1 : R) else 0) • P.root k =
        ∑ k ∈ b.support, (if k ∈ P.orbitIndices σ j then (1 : R) else 0) • P.root k := by
    simp_rw [ite_smul, one_smul, zero_smul, sum_ite_mem, Finset.inter_eq_right.mpr hsubI,
      Finset.inter_eq_right.mpr hsubJ, ← orbitSum_def, heq]
  have hcoeff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support
    (fun k ↦ (if k ∈ P.orbitIndices σ i then (1 : R) else 0) -
      (if k ∈ P.orbitIndices σ j then (1 : R) else 0))
    (fun _ hk ↦ hk) (by simp_rw [sub_smul, sum_sub_distrib, hsum, sub_self]) j hj
  by_contra hnot
  simp [self_mem_orbitIndices P σ j, hnot] at hcoeff

/-- If `x` is fixed by `σ` and expands in the simple roots of `b`, its coefficients are constant
along `σ`-orbits. -/
theorem coeff_eq_of_mem_orbitIndices_of_weightMap_eq
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {c : ι → R}
    (hx : σ.weightMap (∑ k ∈ b.support, c k • P.root k) = ∑ k ∈ b.support, c k • P.root k)
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ P.orbitIndices σ i) :
    c j = c i := by
  classical
  have hstep {k : ι} (hk : k ∈ b.support) : c (σ.indexEquiv k) = c k := by
    have himg : b.support.image σ.indexEquiv = b.support := by
      simpa only [b.support_map_eq] using
        congrArg Base.support (b.map_eq_of_forall_mem_support hσ)
    have hlhs : σ.weightMap (∑ l ∈ b.support, c l • P.root l) =
        ∑ l ∈ b.support, c (σ.indexEquiv.symm l) • P.root l := by
      conv_rhs => rw [← himg, Finset.sum_image σ.indexEquiv.injective.injOn]
      rw [map_sum]
      refine sum_congr rfl fun l _ ↦ ?_
      simp [Hom.root_weightMap_apply]
    rw [hlhs] at hx
    have hdiff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support
      (fun l ↦ c (σ.indexEquiv.symm l) - c l) (fun _ hl ↦ hl)
      (by simp_rw [sub_smul, sum_sub_distrib, hx, sub_self])
      (σ.indexEquiv k) (hσ k hk)
    simpa [sub_eq_zero] using (sub_eq_zero.mp hdiff).symm
  rcases mem_orbitIndices_iff_exists_pow.mp hj with ⟨m, rfl⟩
  clear hj
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : (σ.indexEquiv ^ m) i ∈ b.support :=
      mem_support_of_mem_orbitIndices hσ hi (mem_orbitIndices_iff_exists_pow.mpr ⟨m, rfl⟩)
    rw [pow_succ', Equiv.Perm.mul_apply, hstep hm, ih]

/-- **Simple-orbit sums are linearly independent** in the fixed submodule `E^σ`. No spanning or
orthogonality hypothesis is needed. -/
theorem linearIndepOn_foldedRoot_simpleFoldedIndices
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    LinearIndepOn R (P.foldedRoot σ) (P.simpleFoldedIndices b σ) := by
  classical
  nontriviality R
  rw [linearIndepOn_iff']
  intro s c hs hc γ hγs
  have hsmem {δ : P.foldedIndices σ} (hδ : δ ∈ s) : δ ∈ P.simpleFoldedIndices b σ :=
    Finset.mem_coe.mp (hs hδ)
  obtain ⟨j₀, hj₀, hj₀eq⟩ := (mem_simpleFoldedIndices P b σ).mp (hsmem hγs)
  choose rep hrep_mem hrep_eq using fun δ : P.simpleFoldedIndices b σ ↦
    (mem_simpleFoldedIndices P b σ).mp δ.property
  let orb (δ : P.foldedIndices σ) : Finset ι :=
    if hδ : δ ∈ P.simpleFoldedIndices b σ then P.orbitIndices σ (rep ⟨δ, hδ⟩) else ∅
  have horb_sub {δ : P.foldedIndices σ} (hδ : δ ∈ s) : orb δ ⊆ b.support := by
    simp only [orb, hsmem hδ, ↓reduceDIte]
    exact fun k hk ↦ mem_support_of_mem_orbitIndices hσ (hrep_mem ⟨δ, hsmem hδ⟩) hk
  have horb_disj : (s : Set (P.foldedIndices σ)).PairwiseDisjoint orb := by
    intro δ₁ hδ₁ δ₂ hδ₂ hne
    have hδ₁' := hsmem (Finset.mem_coe.mp hδ₁)
    have hδ₂' := hsmem (Finset.mem_coe.mp hδ₂)
    simp only [Function.onFun, orb, hδ₁', hδ₂', ↓reduceDIte, Finset.disjoint_left]
    intro k hk₁ hk₂
    apply hne
    apply Subtype.ext
    rw [← hrep_eq ⟨δ₁, hδ₁'⟩, ← hrep_eq ⟨δ₂, hδ₂'⟩,
      ← orbitSum_eq_of_mem hk₁, ← orbitSum_eq_of_mem hk₂]
  have horb_sum {δ : P.foldedIndices σ} (hδ : δ ∈ s) :
      ∑ k ∈ orb δ, P.root k = (δ : M) := by
    simp only [orb, hsmem hδ, ↓reduceDIte, ← orbitSum_def, hrep_eq ⟨δ, hsmem hδ⟩]
  have hcoezero : ∑ δ ∈ s, c δ • (δ : M) = 0 := by
    simpa [coe_foldedRoot] using congrArg Subtype.val hc
  have hexpand :
      ∑ k ∈ s.biUnion orb,
        (∑ δ ∈ s, if k ∈ orb δ then c δ else 0) • P.root k = 0 := by
    calc ∑ k ∈ s.biUnion orb, (∑ δ ∈ s, if k ∈ orb δ then c δ else 0) • P.root k
        = ∑ δ ∈ s, ∑ k ∈ s.biUnion orb, (if k ∈ orb δ then c δ else 0) • P.root k := by
          simp_rw [sum_smul]
          exact sum_comm
      _ = ∑ δ ∈ s, c δ • (δ : M) := by
          refine sum_congr rfl fun δ hδ ↦ ?_
          simp_rw [ite_smul, zero_smul, sum_ite_mem,
            Finset.inter_eq_right.mpr (subset_biUnion_of_mem orb hδ), ← smul_sum, horb_sum hδ]
      _ = 0 := hcoezero
  have hbi_sub : s.biUnion orb ⊆ b.support :=
    biUnion_subset.mpr fun δ hδ ↦ horb_sub hδ
  have hj₀_orb : j₀ ∈ orb γ := by
    simp only [orb, hsmem hγs, ↓reduceDIte]
    exact (orbitSum_eq_orbitSum_iff_of_mem_support hσ (hrep_mem ⟨γ, hsmem hγs⟩) hj₀).mp
      ((hrep_eq ⟨γ, hsmem hγs⟩).trans hj₀eq.symm)
  have hj₀_bi : j₀ ∈ s.biUnion orb := mem_biUnion.mpr ⟨γ, hγs, hj₀_orb⟩
  have hval := linearIndepOn_iff'.mp b.linearIndepOn_root (s.biUnion orb)
    (fun k ↦ ∑ δ ∈ s, if k ∈ orb δ then c δ else 0) hbi_sub hexpand j₀ hj₀_bi
  rw [sum_eq_single γ] at hval
  · simpa [hj₀_orb] using hval
  · intro δ hδ hne
    have hnot : j₀ ∉ orb δ :=
      Finset.disjoint_left.mp (horb_disj hγs hδ hne.symm) hj₀_orb
    simp [hnot]
  · intro hnot
    exact False.elim (hnot hγs)

/-- Partitioning a `σ`-fixed combination of simple roots into simple-orbit sums. -/
private theorem sum_support_eq_sum_simpleFoldedIndices
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {c : ι → R}
    (hc_const : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, c j = c i) :
    ∃ d : P.foldedIndices σ → R,
      (∀ γ : P.foldedIndices σ, ∀ i ∈ b.support, P.orbitSum σ i = (γ : M) → d γ = c i) ∧
      ∑ i ∈ b.support, c i • P.root i =
        ∑ γ ∈ P.simpleFoldedIndices b σ, d γ • (γ : M) := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    exact ⟨0, fun _ _ _ _ ↦ Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  choose rep hrep_mem hrep_eq using fun γ : P.simpleFoldedIndices b σ ↦
    (mem_simpleFoldedIndices P b σ).mp γ.property
  let d (γ : P.foldedIndices σ) : R :=
    if hγ : γ ∈ P.simpleFoldedIndices b σ then c (rep ⟨γ, hγ⟩) else 0
  refine ⟨d, fun γ i hi hγi ↦ ?_, ?_⟩
  · have hγ : γ ∈ P.simpleFoldedIndices b σ :=
      (mem_simpleFoldedIndices P b σ).mpr ⟨i, hi, hγi⟩
    simp only [d, hγ, ↓reduceDIte]
    exact hc_const i hi _ <|
      (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi (hrep_mem ⟨γ, hγ⟩)).mp
        (hγi.trans (hrep_eq ⟨γ, hγ⟩).symm)
  · let orb (γ : P.foldedIndices σ) : Finset ι :=
      if hγ : γ ∈ P.simpleFoldedIndices b σ then P.orbitIndices σ (rep ⟨γ, hγ⟩) else ∅
    have hpart : (P.simpleFoldedIndices b σ).biUnion orb = b.support := by
      ext k
      rw [Finset.mem_biUnion]
      refine ⟨fun ⟨γ, hγ, hk⟩ ↦ ?_, fun hk ↦ ?_⟩
      · simp only [orb, hγ, ↓reduceDIte] at hk
        exact mem_support_of_mem_orbitIndices hσ (hrep_mem ⟨γ, hγ⟩) hk
      · let γk : P.foldedIndices σ := ⟨P.orbitSum σ k, orbitSum_mem_foldedIndices P σ k⟩
        have hγk : γk ∈ P.simpleFoldedIndices b σ :=
          (mem_simpleFoldedIndices P b σ).mpr ⟨k, hk, rfl⟩
        refine ⟨γk, hγk, ?_⟩
        simp only [orb, hγk, ↓reduceDIte]
        exact (orbitSum_eq_orbitSum_iff_of_mem_support hσ (hrep_mem ⟨γk, hγk⟩) hk).mp
          (hrep_eq ⟨γk, hγk⟩)
    have hdisj :
        (P.simpleFoldedIndices b σ : Set (P.foldedIndices σ)).PairwiseDisjoint orb := by
      intro γ₁ hγ₁ γ₂ hγ₂ hne
      have hγ₁' : γ₁ ∈ P.simpleFoldedIndices b σ := Finset.mem_coe.mp hγ₁
      have hγ₂' : γ₂ ∈ P.simpleFoldedIndices b σ := Finset.mem_coe.mp hγ₂
      simp only [Function.onFun, orb, hγ₁', hγ₂', ↓reduceDIte, Finset.disjoint_left]
      intro k hk₁ hk₂
      exact hne <| Subtype.ext <| by
        rw [← hrep_eq ⟨γ₁, hγ₁'⟩, ← hrep_eq ⟨γ₂, hγ₂'⟩,
          ← orbitSum_eq_of_mem hk₁, ← orbitSum_eq_of_mem hk₂]
    rw [← hpart, sum_biUnion hdisj]
    refine sum_congr rfl fun γ hγ ↦ ?_
    simp only [orb, d, hγ, ↓reduceDIte]
    have hconst :
        ∑ k ∈ P.orbitIndices σ (rep ⟨γ, hγ⟩), c k • P.root k =
          ∑ k ∈ P.orbitIndices σ (rep ⟨γ, hγ⟩), c (rep ⟨γ, hγ⟩) • P.root k :=
      sum_congr rfl fun k hk ↦ by rw [hc_const _ (hrep_mem ⟨γ, hγ⟩) k hk]
    rw [hconst, ← smul_sum, ← orbitSum_def, hrep_eq ⟨γ, hγ⟩]

/-- **Simple-orbit sums span `E^σ`** when `P` is a root system and `σ` permutes `b.support`. -/
theorem span_foldedRoot_simpleFoldedIndices_eq_top [P.IsRootSystem]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Submodule.span R (P.foldedRoot σ '' (P.simpleFoldedIndices b σ : Set (P.foldedIndices σ))) =
      ⊤ := by
  rw [eq_top_iff']
  intro x
  classical
  let c : ι → R := fun i ↦ if hi : i ∈ b.support then b.toWeightBasis.repr (x : M) ⟨i, hi⟩ else 0
  have hx_sum : (x : M) = ∑ i ∈ b.support, c i • P.root i := by
    conv_lhs => rw [← b.toWeightBasis.sum_repr (x : M)]
    rw [← Finset.sum_attach b.support]
    exact sum_congr rfl fun i _ ↦ by simp [c, i.property]
  have hx_fix :
      σ.weightMap (∑ i ∈ b.support, c i • P.root i) = ∑ i ∈ b.support, c i • P.root i := by
    rw [← hx_sum]
    exact LinearMap.mem_fixedSubmodule_iff.mp x.property
  obtain ⟨d, -, hd_eq⟩ := sum_support_eq_sum_simpleFoldedIndices (P := P) (b := b) (σ := σ) hσ
    (fun i hi j hj ↦ coeff_eq_of_mem_orbitIndices_of_weightMap_eq hσ hx_fix hi hj)
  have hx_eq : x = ∑ γ ∈ P.simpleFoldedIndices b σ, d γ • P.foldedRoot σ γ :=
    Subtype.ext (by simpa [coe_foldedRoot, ← hd_eq] using hx_sum)
  rw [hx_eq]
  exact sum_mem fun γ hγ ↦ Submodule.smul_mem _ _ (subset_span ⟨γ, hγ, rfl⟩)

/-- **All folded roots span `E^σ`** when `P` is a root system and `σ` permutes `b.support`. -/
theorem span_range_foldedRoot_eq_top [P.IsRootSystem]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Submodule.span R (range (P.foldedRoot σ)) = ⊤ :=
  top_unique <| (span_foldedRoot_simpleFoldedIndices_eq_top hσ).symm.trans_le
    (Submodule.span_mono (image_subset_range _ _))

/-- In characteristic zero, the orbit sum of a `b`-positive root lies in the additive monoid
generated by the simple-orbit sums. -/
theorem foldedRoot_mem_closure_simpleFoldedIndices_of_isPos [CharZero R]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {r : ι} (hr : b.IsPos r)
    {γ : P.foldedIndices σ} (hγ : P.orbitSum σ r = (γ : M)) :
    P.foldedRoot σ γ ∈
      AddSubmonoid.closure
        (P.foldedRoot σ '' (P.simpleFoldedIndices b σ : Set (P.foldedIndices σ))) := by
  classical
  obtain ⟨n, hn⟩ := (mem_posRootCone P b).mp (P.orbitSum_mem_posRootCone hσ hr)
  have horb_sum : P.orbitSum σ r = ∑ i ∈ b.support, (n i : R) • P.root i := by
    rw [hn]
    exact sum_congr rfl fun i _ ↦ (Nat.cast_smul_eq_nsmul R (n i) (P.root i)).symm
  have hfix : σ.weightMap (∑ i ∈ b.support, (n i : R) • P.root i) =
      ∑ i ∈ b.support, (n i : R) • P.root i := by
    rw [← horb_sum, weightMap_orbitSum_self]
  have hn_const : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, n j = n i := fun i hi j hj ↦
    Nat.cast_injective (R := R) (coeff_eq_of_mem_orbitIndices_of_weightMap_eq hσ hfix hi hj)
  choose rep hrep_mem hrep_eq using fun δ : P.simpleFoldedIndices b σ ↦
    (mem_simpleFoldedIndices P b σ).mp δ.property
  let k : P.foldedIndices σ → ℕ :=
    fun δ ↦ if hδ : δ ∈ P.simpleFoldedIndices b σ then n (rep ⟨δ, hδ⟩) else 0
  obtain ⟨d, hd_val, hd_sum⟩ := sum_support_eq_sum_simpleFoldedIndices (P := P) (b := b) (σ := σ) hσ
    (c := fun i ↦ (n i : R)) (fun i hi j hj ↦ congrArg Nat.cast (hn_const i hi j hj))
  have hγ_eq : P.foldedRoot σ γ = ∑ δ ∈ P.simpleFoldedIndices b σ, k δ • P.foldedRoot σ δ := by
    apply Subtype.ext
    rw [coe_foldedRoot, ← hγ, horb_sum, hd_sum, Submodule.coe_sum]
    refine sum_congr rfl fun δ hδ ↦ ?_
    have hk : (k δ : R) = d δ := by
      simp only [k, hδ, ↓reduceDIte]
      exact (hd_val δ (rep ⟨δ, hδ⟩) (hrep_mem ⟨δ, hδ⟩) (hrep_eq ⟨δ, hδ⟩)).symm
    rw [Submodule.coe_smul_of_tower, coe_foldedRoot, ← Nat.cast_smul_eq_nsmul R, hk]
  rw [hγ_eq]
  refine (AddSubmonoid.closure _).sum_mem fun δ hδ ↦ (AddSubmonoid.closure _).nsmul_mem ?_ (k δ)
  exact AddSubmonoid.subset_closure ⟨δ, Finset.mem_coe.mpr hδ, rfl⟩

/-- In characteristic zero, every folded root or its negative lies in the additive monoid generated
by the simple-orbit sums. -/
theorem foldedRoot_mem_or_neg_mem_closure_simpleFoldedIndices [CharZero R]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (γ : P.foldedIndices σ) :
    P.foldedRoot σ γ ∈
        AddSubmonoid.closure
          (P.foldedRoot σ '' (P.simpleFoldedIndices b σ : Set (P.foldedIndices σ))) ∨
      -P.foldedRoot σ γ ∈
        AddSubmonoid.closure
          (P.foldedRoot σ '' (P.simpleFoldedIndices b σ : Set (P.foldedIndices σ))) := by
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp γ.property
  by_cases hpos : b.IsPos r
  · exact Or.inl (foldedRoot_mem_closure_simpleFoldedIndices_of_isPos hσ hpos hr)
  · right
    have hneg_pos : b.IsPos (P.reflectionPerm r r) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hpos)
    let negγ : P.foldedIndices σ :=
      ⟨P.orbitSum σ (P.reflectionPerm r r), orbitSum_mem_foldedIndices P σ _⟩
    have hneg_eq : -P.foldedRoot σ γ = P.foldedRoot σ negγ := by
      apply Subtype.ext
      simp [negγ, orbitSum_reflectionPerm_self, hr]
    rw [hneg_eq]
    exact foldedRoot_mem_closure_simpleFoldedIndices_of_isPos hσ hneg_pos rfl

end SimpleOrbits

/-! ### Orbit-sum realizations -/

section Realization

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A realization bundles a native based root pairing on the fixed submodule `E^σ` and its linear
dual. Its roots are the actual distinct orbit-sum vectors, its pairing is evaluation, and its base
consists of the simple-orbit sums. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι]
    (b : P.Base) (σ : P.Aut) where
  /-- The native pairing on the fixed space and its linear dual. -/
  pairing : RootPairing (P.foldedIndices σ) R (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- Its finite simple base. -/
  base : pairing.Base
  /-- Both root and coroot families span. -/
  rootSystem : pairing.IsRootSystem
  /-- No proportional roots except a root and its negative. -/
  reduced : pairing.IsReduced
  /-- All root-coroot pairings are integers. -/
  crystallographic : pairing.IsCrystallographic
  /-- The perfect pairing is evaluation against the fixed-space dual. -/
  evaluation : ∀ x y, pairing.toLinearMap x y = y x
  /-- Each root is its actual orbit-sum vector in the ambient space. -/
  root_eq : ∀ i, (pairing.root i : M) = (i : M)
  /-- Simple roots are the original simple-orbit sums. -/
  base_eq : ∀ i, i ∈ base.support ↔
    ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

namespace OrbitSumRealization

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

instance instIsRootSystem (F : P.OrbitSumRealization b σ) : F.pairing.IsRootSystem :=
  F.rootSystem

instance instIsReduced (F : P.OrbitSumRealization b σ) : F.pairing.IsReduced :=
  F.reduced

instance instIsCrystallographic (F : P.OrbitSumRealization b σ) : F.pairing.IsCrystallographic :=
  F.crystallographic

@[simp]
theorem toLinearMap_eq (F : P.OrbitSumRealization b σ) :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) :=
  LinearMap.ext₂ F.evaluation

@[simp]
theorem root_eq_foldedRoot (F : P.OrbitSumRealization b σ) (γ : P.foldedIndices σ) :
    F.pairing.root γ = P.foldedRoot σ γ :=
  Subtype.ext (F.root_eq γ)

@[simp]
theorem coroot'_eq_coroot (F : P.OrbitSumRealization b σ) (γ : P.foldedIndices σ) :
    F.pairing.coroot' γ = F.pairing.coroot γ := by
  ext x
  simp [RootPairing.coroot']

theorem pairing_eq_coroot_apply (F : P.OrbitSumRealization b σ) (γ δ : P.foldedIndices σ) :
    F.pairing.pairing γ δ = F.pairing.coroot δ (F.pairing.root γ) := by
  rw [RootPairing.pairing, F.evaluation]

@[simp]
theorem support_base_eq_simpleFoldedIndices (F : P.OrbitSumRealization b σ) :
    F.base.support = P.simpleFoldedIndices b σ := by
  ext γ
  rw [F.base_eq, mem_simpleFoldedIndices]

/-! #### Uniqueness -/

section Unique

variable [CharZero R] [IsDomain R]

/-- Any linear functional on `E^σ` taking the value `2` at a folded root `γ` and whose
pre-reflection preserves the set of folded roots coincides with `F.pairing.coroot γ`. -/
theorem coroot_eq_of_mapsTo_preReflection (F : P.OrbitSumRealization b σ)
    (γ : P.foldedIndices σ) (f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
    (hf_two : f (F.pairing.root γ) = 2)
    (hf_maps : MapsTo (Module.preReflection (F.pairing.root γ) f)
      (range F.pairing.root) (range F.pairing.root)) :
    F.pairing.coroot γ = f := by
  have : Module.IsReflexive R (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_isPerfPair F.pairing.toLinearMap
  have hrefl : (F.pairing.reflection γ : _ → _) =
      Module.preReflection (F.pairing.root γ) (F.pairing.coroot γ) := by
    ext x
    simp [RootPairing.reflection_apply, F.coroot'_eq_coroot, Module.preReflection_apply]
  refine Module.Dual.eq_of_preReflection_mapsTo (finite_range F.pairing.root)
    IsRootSystem.span_root_eq_top ?_ ?_ hf_two hf_maps
  · simpa [F.evaluation] using F.pairing.root_coroot_two γ
  · rw [← hrefl]
    exact F.pairing.mapsTo_reflection_root γ

/-- Two orbit-sum realizations of `(P, b, σ)` have equal underlying root pairings. -/
theorem pairing_eq (F₁ F₂ : P.OrbitSumRealization b σ) : F₁.pairing = F₂.pairing :=
  IsRootSystem.ext (F₁.toLinearMap_eq.trans F₂.toLinearMap_eq.symm)
    (DFunLike.ext _ _ fun γ ↦ (F₁.root_eq_foldedRoot γ).trans (F₂.root_eq_foldedRoot γ).symm)

/-- **Uniqueness of an orbit-sum realization.** In characteristic zero over a domain, the root
vectors, evaluation pairing, and simple-support specification determine the realization uniquely. -/
@[ext]
theorem ext (F₁ F₂ : P.OrbitSumRealization b σ) : F₁ = F₂ := by
  obtain ⟨P₁, b₁, hRS₁, hRed₁, hCr₁, hEv₁, hR₁, hB₁⟩ := F₁
  obtain ⟨P₂, b₂, hRS₂, hRed₂, hCr₂, hEv₂, hR₂, hB₂⟩ := F₂
  have hP : P₁ = P₂ :=
    pairing_eq ⟨P₁, b₁, hRS₁, hRed₁, hCr₁, hEv₁, hR₁, hB₁⟩
      ⟨P₂, b₂, hRS₂, hRed₂, hCr₂, hEv₂, hR₂, hB₂⟩
  subst hP
  have hb : b₁ = b₂ := Base.ext <| by
    ext γ
    exact (hB₁ γ).trans (hB₂ γ).symm
  subst hb
  rfl

instance instSubsingleton : Subsingleton (P.OrbitSumRealization b σ) :=
  ⟨ext⟩

end Unique

/-! #### Positivity and positive-root lifts -/

section Positivity

variable [CharZero R]

/-- Every vector in the positive root cone of an orbit-sum realization lies in the ambient positive
root cone of `(P, b)`. -/
theorem coe_mem_posRootCone (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} (hx : x ∈ posRootCone F.pairing F.base) :
    (x : M) ∈ posRootCone P b := by
  obtain ⟨n, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
  rw [Submodule.coe_sum]
  refine (posRootCone P b).sum_mem fun γ hγ ↦ ?_
  obtain ⟨j, hj, hj_eq⟩ := (F.base_eq γ).mp hγ
  rw [Submodule.coe_smul_of_tower, F.root_eq γ, ← hj_eq]
  exact (posRootCone P b).nsmul_mem
    (P.orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hj)) (n γ)

/-- For a root `i` with orbit sum `γ`, positivity of `γ` in `F.base` is equivalent to positivity of
`i` in `b`. -/
theorem isPos_iff_of_orbitSum_eq (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {γ : P.foldedIndices σ} {i : ι} (hi : P.orbitSum σ i = (γ : M)) :
    F.base.IsPos γ ↔ b.IsPos i := by
  refine ⟨fun hγpos ↦ ?_, fun hipos ↦ ?_⟩
  · have hcone : (F.pairing.root γ : M) ∈ posRootCone P b :=
      F.coe_mem_posRootCone hσ
        (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr hγpos))
    rw [F.root_eq γ, ← hi] at hcone
    by_contra hneg
    have hneg_cone : -P.orbitSum σ i ∈ posRootCone P b := by
      rw [← orbitSum_reflectionPerm_self]
      exact P.orbitSum_mem_posRootCone hσ
        ((isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hneg))
    exact P.orbitSum_ne_zero hσ i
      ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem hcone hneg_cone)
  · by_contra hγneg
    let γ' : P.foldedIndices σ := F.pairing.reflectionPerm γ γ
    have hγ'_pos : F.base.IsPos γ' :=
      (isPos_reflectionPerm_self_iff_mem_negRoots F.pairing F.base γ).mpr
        ((mem_negRoots F.pairing F.base γ).mpr hγneg)
    have hcone_neg : (F.pairing.root γ' : M) ∈ posRootCone P b :=
      F.coe_mem_posRootCone hσ
        (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr hγ'_pos))
    have hroot_neg : (F.pairing.root γ' : M) = -P.orbitSum σ i := by
      rw [F.pairing.root_reflectionPerm, F.pairing.reflection_apply_self, Submodule.coe_neg,
        F.root_eq γ, hi]
    rw [hroot_neg] at hcone_neg
    exact P.orbitSum_ne_zero hσ i
      ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem
        (P.orbitSum_mem_posRootCone hσ hipos) hcone_neg)

/-- **Positive-root lift characterization.** A folded root of an orbit-sum realization is positive
if and only if it is the orbit sum of a `b`-positive root. -/
theorem isPos_iff_exists_isPos (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (γ : P.foldedIndices σ) :
    F.base.IsPos γ ↔ ∃ i, b.IsPos i ∧ P.orbitSum σ i = (γ : M) := by
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp γ.property
  refine ⟨fun hγ ↦ ⟨r, (F.isPos_iff_of_orbitSum_eq hσ hr).mp hγ, hr⟩, ?_⟩
  rintro ⟨i, hi, hi_eq⟩
  exact (F.isPos_iff_of_orbitSum_eq hσ hi_eq).mpr hi

end Positivity

/-- Pushforward of a root pairing along linear and index equivalences, bundled as an equivalence of
root pairings. -/
private noncomputable def mapEquiv {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₂] [Module R N₂] (Q : RootPairing ι₁ R M₁ N₁)
    (e : ι₁ ≃ ι₂) (f : M₁ ≃ₗ[R] M₂) (g : N₁ ≃ₗ[R] N₂) :
    Q.Equiv (Q.map e f g) where
  weightMap := f.toLinearMap
  coweightMap := g.symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by ext y x; simp [RootPairing.map]
  root_weightMap := by ext i; simp [RootPairing.map]
  coroot_coweightMap := by ext j; simp [RootPairing.map]
  bijective_weightMap := f.bijective
  bijective_coweightMap := g.symm.bijective

/-- Reducedness transports along any equivalence of root pairings. -/
private theorem isReduced_of_equiv {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₂] [Module R N₂] {Q₁ : RootPairing ι₁ R M₁ N₁}
    {Q₂ : RootPairing ι₂ R M₂ N₂} [Q₁.IsReduced] (e : Q₁.Equiv Q₂) : Q₂.IsReduced := by
  rw [isReduced_iff]
  intro i j hdep
  obtain ⟨i, rfl⟩ := e.indexEquiv.surjective i
  obtain ⟨j, rfl⟩ := e.indexEquiv.surjective j
  rw [e.toHom.linearIndependent_root_indexEquiv_iff e.bijective_weightMap.injective] at hdep
  rcases IsReduced.eq_or_eq_neg (P := Q₁) i j hdep with h | h
  · exact .inl (congrArg Q₂.root (congrArg e.indexEquiv (Q₁.root.injective h)))
  · refine .inr ?_
    rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, h, map_neg]

/-! #### Identity realization -/

section One

variable (P)

/-- The index bijection between `ι` and `P.foldedIndices 1` sending `i` to `P.orbitSum 1 i`. -/
noncomputable def oneIndexEquiv : ι ≃ P.foldedIndices 1 :=
  Equiv.ofBijective (fun i ↦ ⟨P.orbitSum 1 i, orbitSum_mem_foldedIndices P 1 i⟩)
    ⟨fun _ _ h ↦ P.root.injective (by simpa [orbitSum_one] using congrArg Subtype.val h),
      fun ⟨_, hx⟩ ↦
        let ⟨i, hi⟩ := mem_foldedIndices.mp hx
        ⟨i, Subtype.ext hi⟩⟩

@[simp]
theorem coe_oneIndexEquiv (i : ι) :
    ((oneIndexEquiv P i : P.foldedIndices 1) : M) = P.root i :=
  orbitSum_one P i

variable (b) in
/-- For the identity automorphism `1 : P.Aut`, a reduced crystallographic root system `P` with base
`b` is its own orbit-sum realization on `E^1 = ⊤`. -/
noncomputable def one [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] :
    P.OrbitSumRealization b 1 :=
  let eM : M ≃ₗ[R] LinearMap.fixedSubmodule (1 : P.Aut).weightMap :=
    (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (by ext x; simp [LinearMap.mem_fixedSubmodule_iff])).symm
  let eN := (eM.dualMap.trans P.flip.toPerfPair.symm).symm
  let eI : ι ≃ P.foldedIndices 1 := oneIndexEquiv P
  let Q := P.map eI eM eN
  let eqv : P.Equiv Q := mapEquiv P eI eM eN
  { pairing := Q
    base := b.map eqv
    rootSystem := inferInstance
    reduced := isReduced_of_equiv eqv
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by
      change P.toLinearMap (eM.symm x) (eN.symm y) = y x
      have hy : eN.symm y = P.toLinearMap.flip.toPerfPair.symm (eM.dualMap y) := rfl
      rw [hy, LinearMap.apply_toPerfPair_flip, LinearEquiv.dualMap_apply, eM.apply_symm_apply]
    root_eq := fun γ ↦ by
      obtain ⟨i, rfl⟩ := eI.surjective γ
      change (eM (P.root (eI.symm (eI i))) : M) = (eI i : M)
      rw [eI.symm_apply_apply]
      exact (LinearEquiv.coe_ofTop_symm_apply
        (LinearMap.fixedSubmodule (1 : P.Aut).weightMap) (P.root i)).trans
        (coe_oneIndexEquiv P i).symm
    base_eq := fun γ ↦ by
      classical
      simp only [Base.support_map_eq, Finset.mem_image]
      exact ⟨fun ⟨j, hj, h⟩ ↦ ⟨j, hj, h ▸ by simp [eqv, mapEquiv, eI]⟩,
        fun ⟨j, hj, hj_eq⟩ ↦ ⟨j, hj, Subtype.ext (by simpa [eqv, mapEquiv, eI] using hj_eq)⟩⟩ }

variable {P}

/-- Any orbit-sum realization for `1 : P.Aut` is canonically based-equivalent to `(P, b)`, acting
as the submodule inclusion `E^1 → M` on weights. -/
noncomputable def equivSelfOne [CharZero R] [IsDomain R] [P.IsRootSystem]
    (F : P.OrbitSumRealization b 1) :
    F.pairing.Equiv P :=
  let eM : LinearMap.fixedSubmodule (1 : P.Aut).weightMap ≃ₗ[R] M :=
    LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (by ext x; simp [LinearMap.mem_fixedSubmodule_iff])
  Equiv.mk' F.pairing P eM (oneIndexEquiv P).symm fun γ ↦ by
    obtain ⟨i, rfl⟩ := (oneIndexEquiv P).surjective γ
    rw [(oneIndexEquiv P).symm_apply_apply]
    exact (F.root_eq (oneIndexEquiv P i)).trans (coe_oneIndexEquiv P i)

theorem weightMap_equivSelfOne_apply [CharZero R] [IsDomain R] [P.IsRootSystem]
    (F : P.OrbitSumRealization b 1)
    (x : LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :
    (F.equivSelfOne).weightMap x = (x : M) :=
  (rfl)

@[simp]
theorem map_base_equivSelfOne [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsReduced]
    [P.IsCrystallographic] (F : P.OrbitSumRealization b 1) :
    F.base.map F.equivSelfOne = b := by
  classical
  obtain rfl : F = one P b := Subsingleton.elim _ _
  apply Base.ext
  have hsupp : (one P b).base.support = b.support.image (oneIndexEquiv P) :=
    Base.support_map_eq _ _
  have hidx : ((one P b).equivSelfOne).indexEquiv = (oneIndexEquiv P).symm := rfl
  rw [Base.support_map_eq, hsupp, hidx, Finset.image_image]
  simp

end One

/-! #### Transport along intertwining equivalences -/

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι₂] {b₂ : P₂.Base} {τ : P₂.Aut}

/-- An equivalence of root pairings intertwining `σ` and `τ` on root indices maps
`P.foldedIndices σ` bijectively onto `P₂.foldedIndices τ` via its weight map. -/
noncomputable def _root_.RootPairing.foldedIndicesEquiv (e : P.Equiv P₂)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j)) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ where
  toFun γ := ⟨e.weightMap (γ : M), by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp γ.property
    exact mem_foldedIndices.mpr
      ⟨e.indexEquiv i, (P.weightMap_orbitSum e h i).symm.trans (congrArg e.weightMap hi)⟩⟩
  invFun δ := ⟨e.symm.weightMap (δ : M₂), by
    have hsymm : ∀ k, e.symm.indexEquiv (τ.indexEquiv k) = σ.indexEquiv (e.symm.indexEquiv k) := by
      intro k
      simp only [Equiv.inv_indexEquiv]
      rw [e.indexEquiv.symm_apply_eq, h, e.indexEquiv.apply_symm_apply]
    obtain ⟨k, hk⟩ := mem_foldedIndices.mp δ.property
    exact mem_foldedIndices.mpr ⟨e.symm.indexEquiv k,
      (P₂.weightMap_orbitSum e.symm hsymm k).symm.trans (congrArg e.symm.weightMap hk)⟩⟩
  left_inv γ := Subtype.ext (e.weightEquiv.symm_apply_apply (γ : M))
  right_inv δ := Subtype.ext (e.weightEquiv.apply_symm_apply (δ : M₂))

@[simp]
theorem _root_.RootPairing.coe_foldedIndicesEquiv_apply (e : P.Equiv P₂)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (γ : P.foldedIndices σ) :
    ((P.foldedIndicesEquiv e h γ : P₂.foldedIndices τ) : M₂) = e.weightMap (γ : M) :=
  (rfl)

omit [Finite ι] [Finite ι₂] in
/-- For root systems, intertwining `σ` and `τ` on root indices implies intertwining their weight
maps. -/
theorem _root_.RootPairing.weightEquiv_comp_weightMap_of_indexEquiv [P.IsRootSystem]
    (e : P.Equiv P₂)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j)) :
    e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap := by
  refine LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun j ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.weightEquiv_apply]
  rw [Hom.root_weightMap_apply, Hom.root_weightMap_apply, h, Hom.root_weightMap_apply,
    Hom.root_weightMap_apply]

/-- Transport an orbit-sum realization along a based equivalence intertwining `σ` and `τ`. -/
noncomputable def map (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (hb : ∀ j, j ∈ b.support ↔ e.indexEquiv j ∈ b₂.support) :
    P₂.OrbitSumRealization b₂ τ :=
  let eM := e.weightEquiv.fixedSubmoduleCongr hw
  let eN := eM.symm.dualMap
  let eI := P.foldedIndicesEquiv e h
  let Q := F.pairing.map eI eM eN
  let eqv : F.pairing.Equiv Q := mapEquiv F.pairing eI eM eN
  { pairing := Q
    base := F.base.map eqv
    rootSystem := inferInstance
    reduced := isReduced_of_equiv eqv
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by simp [Q, RootPairing.map, eN]
    root_eq := fun δ ↦ by
      obtain ⟨γ, rfl⟩ := eI.surjective δ
      simp [Q, RootPairing.map, eM, eI]
    base_eq := fun δ ↦ by
      classical
      simp only [Base.support_map_eq, Finset.mem_image]
      refine ⟨?_, ?_⟩
      · rintro ⟨γ, hγ, rfl⟩
        obtain ⟨j, hj, hj_eq⟩ := (F.base_eq γ).mp hγ
        refine ⟨e.indexEquiv j, (hb j).mp hj, ?_⟩
        rw [← P.weightMap_orbitSum e h j]
        simpa [eqv, mapEquiv, eI] using congrArg e.weightMap hj_eq
      · rintro ⟨k, hk, hk_eq⟩
        refine ⟨eI.symm δ, (F.base_eq _).mpr
          ⟨e.indexEquiv.symm k, (hb _).mpr (by simpa using hk), ?_⟩,
          by simp [eqv, mapEquiv]⟩
        apply e.weightEquiv.injective
        have horb := P.weightMap_orbitSum e h (e.indexEquiv.symm k)
        rw [e.indexEquiv.apply_symm_apply] at horb
        obtain ⟨γ, rfl⟩ := eI.surjective δ
        simpa [eI, horb] using hk_eq }

/-- **Equivalence of realizations induced by an intertwining based equivalence.** -/
noncomputable def equivOfIntertwining [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j)) :
    F.pairing.Equiv F₂.pairing :=
  Equiv.mk' F.pairing F₂.pairing (e.weightEquiv.fixedSubmoduleCongr hw) (P.foldedIndicesEquiv e h)
    fun γ ↦ Subtype.ext (by simp)

@[simp]
theorem coe_weightMap_equivOfIntertwining [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((equivOfIntertwining F F₂ e hw h).weightMap x : M₂) = e.weightMap (x : M) :=
  e.weightEquiv.fixedSubmoduleCongr_apply hw x

@[simp]
theorem indexEquiv_equivOfIntertwining [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (γ : P.foldedIndices σ) :
    (equivOfIntertwining F F₂ e hw h).indexEquiv γ = P.foldedIndicesEquiv e h γ :=
  (rfl)

@[simp]
theorem map_base_equivOfIntertwining [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (hb : ∀ j, j ∈ b.support ↔ e.indexEquiv j ∈ b₂.support) :
    F.base.map (equivOfIntertwining F F₂ e hw h) = F₂.base := by
  classical
  obtain rfl : F₂ = F.map e hw h hb := Subsingleton.elim _ _
  apply Base.ext
  ext δ
  simp [Base.support_map_eq, map, mapEquiv]

end Map

end OrbitSumRealization

end Realization

end RootPairing
