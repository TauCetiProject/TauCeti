/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression
public import TauCeti.Topology.Homotopy.Extension.CWComplex

/-!
# The cellular approximation theorem

Let `C` and `C'` be relative CW complexes with bases `D` and `E`. This file proves that every map
`f : C → C'` sending `D` into `E` is homotopic, relative to `D`, to a cellular map: one sending
the skeleton `skeletonLT C n` into `skeletonLT C' n` for every `n`
(`TauCeti.exists_isCellular_homotopicRel`). For CW complexes, with empty bases, every map is
homotopic to a cellular map (`TauCeti.exists_isCellular_homotopic`). Constructions defined only
for cellular maps, such as induced maps of cellular chain complexes, therefore apply to every map
of CW complexes up to homotopy.

The proof is Hatcher's. Suppose `f` already sends `skeletonLT C n` into `skeletonLT C' n`.
Through the characteristic map of an `n`-cell of `C`, `f` is a map of a closed `n`-ball sending
its boundary sphere into `skeletonLT C' n`. Since the ball has dimension `n`, the compression
lemma `TauCeti.exists_homotopicRel_skeletonLT_finrank` homotopes it, relative to its boundary,
into `skeletonLT C' (n + 1)`. These homotopies glue over the closed `n`-cells
(`TauCeti.exists_continuousMap_prod_skeletonLT_succ`) to a homotopy on `skeletonLT C (n + 1)`
that is stationary on `skeletonLT C n`, and the homotopy extension property of
`skeletonLT C (n + 1)` (`TauCeti.hasHomotopyExtensionProperty_skeletonLT`) extends it over `C`
(`TauCeti.exists_homotopicRel_mapsTo_skeletonLT_succ`).

Performing the `n`-th of these homotopies during the time interval `[1 - 2⁻ⁿ, 1 - 2⁻ⁿ⁻¹]` gives
a single homotopy. It is continuous because on `skeletonLT C n` all the later homotopies are
stationary, so there it is a finite concatenation, and a map out of `I × C` is continuous as soon
as it is continuous on `I` times every skeleton
(`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`).

## Main results

* `TauCeti.exists_homotopicRel_mapsTo_skeletonLT_succ`: the inductive step, a map sending
  `skeletonLT C n` into `skeletonLT C' n` is homotopic relative to `skeletonLT C n` to one that
  also sends `skeletonLT C (n + 1)` into `skeletonLT C' (n + 1)`.
* `TauCeti.exists_isCellular_homotopicRel`: **the cellular approximation theorem** for relative
  CW complexes.
* `TauCeti.exists_isCellular_homotopic`: the cellular approximation theorem for CW complexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.8.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II, Section 4.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

namespace TauCeti

universe u v w

section Step

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] {C' E : Set Y} [RelCWComplex C' E]

/-- **The inductive step of cellular approximation.** A map `f : C → C'` sending the skeleton
`skeletonLT C n` into `skeletonLT C' n` is homotopic, relative to `skeletonLT C n`, to a map that
also sends `skeletonLT C (n + 1)` into `skeletonLT C' (n + 1)`. -/
theorem exists_homotopicRel_mapsTo_skeletonLT_succ (n : ℕ) (f : C(C, C'))
    (hf : MapsTo f {x : C | (x : X) ∈ skeletonLT C n} {y : C' | (y : Y) ∈ skeletonLT C' n}) :
    ∃ g : C(C, C'), f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C n} ∧
      MapsTo g {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)}
        {y : C' | (y : Y) ∈ skeletonLT C' ((n + 1 : ℕ) : ℕ∞)} := by
  have hsucc : (skeletonLT C' n : Set Y) ⊆ skeletonLT C' ((n + 1 : ℕ) : ℕ∞) :=
    skeletonLT_mono (by exact_mod_cast n.le_succ)
  -- Read `f` on each closed `n`-cell through its characteristic map.
  let φ (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, C') :=
    f.comp ⟨fun y ↦ ⟨map n j y, (skeletonLT C _).subset_complex
      (map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2))⟩,
      (continuous_map_closedBall j).subtype_mk _⟩
  -- The boundary sphere of the cell is already sent into `skeletonLT C' n`.
  have hφ (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1) :
      (φ j y : Y) ∈ (skeletonLT C' n : Set Y) :=
    hf (cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩)
  -- Compress each of these maps into `skeletonLT C' (n + 1)`, relative to the sphere.
  have hcomp (j : cell C n) := exists_homotopicRel_skeletonLT_finrank (C := C')
    (isCompact_closedBall (0 : Fin n → ℝ) 1) (n := n) (Module.finrank_fin_fun ℝ).le (φ j)
  choose ψ hψ hψmem using hcomp
  let H (j : cell C n) := (hψ j).some
  -- Glue the compressions over the closed `n`-cells, stationary on `skeletonLT C n`.
  obtain ⟨F, hFG, hFH⟩ := exists_continuousMap_prod_skeletonLT_succ (Z := I) (n := n)
    (f.comp ⟨fun p : I × (skeletonLT C n : Set X) ↦ ⟨p.2, (skeletonLT C n).subset_complex p.2.2⟩,
      by fun_prop⟩)
    (fun j ↦ (H j).toContinuousMap)
    (fun j t y hy ↦ (H j).eq_fst t (hsucc (hφ j y hy)))
  -- `F` starts at `f`, and ends in `skeletonLT C' (n + 1)`.
  have hF₀ (x : X) (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
      F (0, ⟨x, hx⟩) = f ⟨x, (skeletonLT C _).subset_complex hx⟩ := by
    obtain hx' | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hx
    · exact hFG 0 x hx'
    · exact (hFH j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩).trans ((H j).apply_zero _)
  have hF₁ (x : X) (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
      (F (1, ⟨x, hx⟩) : Y) ∈ (skeletonLT C' ((n + 1 : ℕ) : ℕ∞) : Set Y) := by
    obtain hx' | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hx
    · rw [hFG 1 x hx']
      exact hsucc (hf hx')
    · rw [hFH j 1 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩]
      convert hψmem j _ using 2
      exact (H j).apply_one _
  -- Extend `F` over `C` by the homotopy extension property of `skeletonLT C (n + 1)`.
  have hHEP := hasHomotopyExtensionProperty_skeletonLT (C := C) (n + 1)
  obtain ⟨G, hG₀, hGF⟩ := hHEP.exists_extension_of_isClosed hHEP.isClosed f
    (F.comp ⟨fun p ↦ (p.1, ⟨p.2.1, p.2.2⟩), by fun_prop⟩) fun a ↦ hF₀ a.1.1 a.2
  refine ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, ⟨⟨⟨G, hG₀, fun _ ↦ rfl⟩, fun t x hx ↦ ?_⟩⟩,
    fun x hx ↦ ?_⟩
  · exact (hGF t ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩).trans (hFG t x.1 hx)
  · exact (hGF 1 ⟨x, hx⟩).symm ▸ hF₁ x.1 hx

end Step

section Approximation

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] {C' E : Set Y} [RelCWComplex C' E]
  (f : C(C, C')) (hf : MapsTo f {x : C | (x : X) ∈ D} {y : C' | (y : Y) ∈ E})

/-- The successive approximations of `f`: the `m`-th one sends `skeletonLT C m` into
`skeletonLT C' m`, and is obtained from the previous one by
`TauCeti.exists_homotopicRel_mapsTo_skeletonLT_succ`. -/
private def approx : (m : ℕ) → {g : C(C, C') //
    MapsTo g {x : C | (x : X) ∈ skeletonLT C m} {y : C' | (y : Y) ∈ skeletonLT C' m}}
  | 0 => ⟨f, by simpa only [Nat.cast_zero, ← SetLike.mem_coe, skeletonLT_zero_eq_base] using hf⟩
  | m + 1 => ⟨(exists_homotopicRel_mapsTo_skeletonLT_succ m _ (approx m).2).choose,
      (exists_homotopicRel_mapsTo_skeletonLT_succ m _ (approx m).2).choose_spec.2⟩

/-- The homotopy from the `m`-th to the `(m + 1)`-st approximation of `f`, stationary on
`skeletonLT C m`. -/
private def approxHomotopy (m : ℕ) :
    (approx f hf m).1.HomotopyRel (approx f hf (m + 1)).1 {x : C | (x : X) ∈ skeletonLT C m} :=
  (exists_homotopicRel_mapsTo_skeletonLT_succ m _ (approx f hf m).2).choose_spec.1.some

/-- The time `1 - 2⁻ᵐ` at which the homotopy from the `m`-th to the `(m + 1)`-st approximation
starts. -/
private def stageTime (m : ℕ) : ℝ := 1 - 2⁻¹ ^ m

private lemma stageTime_lt_succ (m : ℕ) : stageTime m < stageTime (m + 1) := by
  simp only [stageTime, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) m]

private lemma stageTime_nonneg (m : ℕ) : 0 ≤ stageTime m := by
  simp only [stageTime, sub_nonneg]
  exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma stageTime_le_one (m : ℕ) : stageTime m ≤ 1 := by
  simp only [stageTime, sub_le_self_iff]
  positivity

/-- The time reparametrisation running the `m`-th homotopy during
`[stageTime m, stageTime (m + 1)]`. -/
private def stageParam (m : ℕ) : C(I, I) :=
  ⟨fun t ↦ projIcc 0 1 zero_le_one (2 ^ (m + 1) * ((t : ℝ) - stageTime m)),
    continuous_projIcc.comp (by fun_prop)⟩

private lemma stageParam_of_le {m : ℕ} {t : I} (ht : (t : ℝ) ≤ stageTime m) :
    stageParam m t = 0 :=
  projIcc_of_le_left zero_le_one (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 ht))

private lemma stageParam_of_ge {m : ℕ} {t : I} (ht : stageTime (m + 1) ≤ t) :
    stageParam m t = 1 := by
  refine projIcc_of_right_le zero_le_one ?_
  have h : (2 : ℝ) ^ (m + 1) * (stageTime (m + 1) - stageTime m) = 1 := by
    rw [show stageTime (m + 1) - stageTime m = 2⁻¹ ^ (m + 1) by
      simp only [stageTime, pow_succ]; ring, ← mul_pow]
    norm_num
  rw [← h]
  gcongr

/-- The concatenation of the first `m` homotopies between successive approximations of `f`, the
`k`-th one run during `[stageTime k, stageTime (k + 1)]`, followed by the constant homotopy at
the `m`-th approximation. -/
private def approxConcat : (m : ℕ) → {Φ : C(I × C, C') //
    ∀ (t : I) x, stageTime m ≤ t → Φ (t, x) = (approx f hf m).1 x}
  | 0 => ⟨(approx f hf 0).1.comp .snd, fun _ _ _ ↦ rfl⟩
  | m + 1 => ⟨⟨fun p ↦ if (p.1 : ℝ) ≤ stageTime m then (approxConcat m).1 p
      else approxHomotopy f hf m (stageParam m p.1, p.2),
      (approxConcat m).1.continuous.if_le (by fun_prop) (by fun_prop) continuous_const
        fun p hp ↦ by
          rw [(approxConcat m).2 _ _ hp.ge, stageParam_of_le hp.le,
            (approxHomotopy f hf m).apply_zero]⟩,
    fun t x ht ↦ by
      have ht' : ¬ (t : ℝ) ≤ stageTime m := (stageTime_lt_succ m).trans_le ht |>.not_ge
      simp only [ContinuousMap.coe_mk, ht', ↓reduceIte, stageParam_of_ge ht,
        ContinuousMap.HomotopyWith.apply_one]⟩

private lemma approxConcat_zero (m : ℕ) (x : C) : (approxConcat f hf m).1 (0, x) = f x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [approxConcat, ContinuousMap.coe_mk, Icc.coe_zero, stageTime_nonneg, ↓reduceIte, ih]

private lemma approxConcat_succ_of_mem {m : ℕ} (t : I) {x : C}
    (hx : (x : X) ∈ (skeletonLT C m : Set X)) :
    (approxConcat f hf (m + 1)).1 (t, x) = (approxConcat f hf m).1 (t, x) := by
  simp only [approxConcat, ContinuousMap.coe_mk]
  split_ifs with ht
  · rfl
  · rw [(approxHomotopy f hf m).eq_fst _ hx, (approxConcat f hf m).2 _ _ (not_le.1 ht).le]

end Approximation

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {C D : Set X} [RelCWComplex C D] {C' E : Set Y} [RelCWComplex C' E]

/-- **The cellular approximation theorem** (Hatcher, Theorem 4.8). Every map `f : C → C'` of
relative CW complexes sending the base `D` into the base `E` is homotopic, relative to `D`, to a
cellular map. -/
theorem exists_isCellular_homotopicRel (f : TopCat.of C ⟶ TopCat.of C')
    (hf : MapsTo f {x : C | (x : X) ∈ D} {y : C' | (y : Y) ∈ E}) :
    ∃ g : TopCat.of C ⟶ TopCat.of C', IsCellular C C' g ∧
      f.hom.HomotopicRel g.hom {x : C | (x : X) ∈ D} := by
  -- Glue the concatenations of the first `m` homotopies over the skeleta.
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT (C := C) (Z := I) (k := 0)
    (fun m ↦ (approxConcat f.hom hf m).1.comp
      ⟨fun p : I × (skeletonLT C ((0 + m : ℕ) : ℕ∞) : Set X) ↦
        (p.1, ⟨p.2, (skeletonLT C _).subset_complex p.2.2⟩), by fun_prop⟩)
    fun m t x hx ↦ approxConcat_succ_of_mem f.hom hf t (by simpa using hx)
  have hG' (m : ℕ) (t : I) (x : C) (hx : (x : X) ∈ (skeletonLT C m : Set X)) :
      G (t, x) = (approxConcat f.hom hf m).1 (t, x) :=
    hG m t x (by simpa using hx)
  refine ⟨TopCat.ofHom ⟨fun x ↦ G (1, x), by fun_prop⟩, fun n x hx ↦ ?_,
    ⟨⟨⟨G, fun x ↦ ?_, fun _ ↦ rfl⟩, fun t x hx ↦ ?_⟩⟩⟩
  · -- On `skeletonLT C n` the final map is the `n`-th approximation.
    have h := hG' n 1 x hx
    rw [(approxConcat f.hom hf n).2 1 x (stageTime_le_one n)] at h
    exact h ▸ (approx f.hom hf n).2 hx
  · obtain ⟨m, hm⟩ := exists_mem_skeletonLT_add 0 x.2
    exact (hG' m 0 x (by simpa using hm)).trans (approxConcat_zero f.hom hf m x)
  · -- On the base `D = skeletonLT C 0` the homotopy is stationary.
    exact hG' 0 t x (by rw [Nat.cast_zero, skeletonLT_zero_eq_base]; exact hx)

/-- **The cellular approximation theorem for CW complexes** (Hatcher, Theorem 4.8). Every map of
CW complexes is homotopic to a cellular map. -/
theorem exists_isCellular_homotopic {C : Set X} [CWComplex C] {C' : Set Y} [CWComplex C']
    (f : TopCat.of C ⟶ TopCat.of C') :
    ∃ g : TopCat.of C ⟶ TopCat.of C', IsCellular C C' g ∧ f.hom.Homotopic g.hom := by
  obtain ⟨g, hg, hfg⟩ := exists_isCellular_homotopicRel f fun _ hx ↦ absurd hx (notMem_empty _)
  exact ⟨g, hg, hfg.homotopic⟩

end TauCeti
