/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
public import TauCeti.MeasureTheory.Measure.ContentOfOpens
import Mathlib.MeasureTheory.Function.Floor

/-!
# The mass measure of a functional of locally finite mass

Let `Ω` be an open set of a finite-dimensional real normed space `E` and let
`T : 𝓓^{n}(Ω, F) → ℝ` be a real-linear map on `F`-valued test functions with locally finite mass
(`Distribution.HasLocallyFiniteMass`). With `F = E [⋀^Fin k]→L[ℝ] ℝ` this is a `k`-current of
locally finite mass. This file constructs its **mass measure** `‖T‖`, a regular Borel measure on
the subtype `Ω`, finite on compact subsets of `Ω`, such that:

* on every open set `U` of `E`, `‖T‖ (Ω ∩ U)` is the local mass of `T` on `U`, the supremum of
  `|T φ|` over the tests `φ` supported in `U` with `‖φ x‖ ≤ 1`; in particular `‖T‖ Ω = mass T`;
* `|T φ| ≤ ∫ ‖φ‖ d‖T‖` for every test `φ`;
* `‖T‖` is the least outer regular measure with this domination property.

The measure lives on `Ω` and not on `E`: it need not be finite near the frontier of `Ω`.
No Radon representation is claimed for functionals that do not have locally finite mass; for
these `Distribution.massMeasure` is the zero measure by convention.

The construction follows the proof of the Riesz representation theorem. The local mass is
countably subadditive on open sets, by a smooth partition of unity, and additive on disjoint
sets, by changing the signs of the tests. Its outer regularization on compact sets is therefore a
`MeasureTheory.Content` (`TauCeti.contentOfOpens`), whose induced measure is `‖T‖`. The
domination is obtained by cutting the support of `φ` into the level sets of `‖φ‖` and covering
them by open sets of almost the same measure.

## Main declarations

* `Distribution.enorm_apply_le_sum_localMass_mul`: a test whose support is covered by finitely
  many open sets `Vᵢ`, on which `‖φ‖ ≤ cᵢ`, satisfies `|T φ| ≤ ∑ᵢ localMass T Vᵢ * cᵢ`.
* `Distribution.localMass_union_of_disjoint`: the local mass is additive on disjoint open sets.
* `Distribution.massMeasure`: the mass measure `‖T‖`.
* `Distribution.massMeasure_preimage_coe`, `Distribution.massMeasure_univ`: its values on open
  sets and its total mass.
* `Distribution.enorm_apply_le_lintegral_massMeasure`: the domination `|T φ| ≤ ∫ ‖φ‖ d‖T‖`.
* `Distribution.massMeasure_le_of_enorm_apply_le`: minimality among outer regular measures.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7 (the variation measure `‖T‖` of a
  current representable by integration).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2, and Chapter 1, §4 (the
  Riesz representation theorem for functionals on vector-valued functions).
* W. Rudin, *Real and Complex Analysis*, third edition, Theorem 2.14 (the level-set argument
  for the domination).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set Function TauCeti
open scoped BoundedContinuousFunction ENNReal NNReal Distributions Topology

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ]

section LocalMass

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Localization of the mass bound.** If the support of a test `φ` is covered by finitely many
open sets `W i`, and `‖φ‖ ≤ c i` on `W i`, then `‖T φ‖ ≤ ∑ i, localMass T (W i) * c i`. -/
theorem enorm_apply_le_sum_localMass_mul {𝓖 : Type*} [FunLike 𝓖 𝓓^{n}(Ω, F) V]
    [LinearMapClass 𝓖 ℝ 𝓓^{n}(Ω, F) V] (T : 𝓖) {ι : Type*} [Fintype ι] {φ : 𝓓^{n}(Ω, F)}
    {W : ι → Set E} (hW : ∀ i, IsOpen (W i)) (hφW : tsupport φ ⊆ ⋃ i, W i) {c : ι → ℝ≥0∞}
    (hφc : ∀ i, ∀ x ∈ W i, ‖φ x‖ₑ ≤ c i) :
    ‖T φ‖ₑ ≤ ∑ i, localMass T (W i) * c i := by
  classical
  obtain ⟨s, ψ, hψW, rfl, hψφ⟩ := φ.exists_sum_subordinate W hW hφW
  -- Each piece `ψ i` is bounded by `c i`: on `W i` by `‖ψ i‖ ≤ ‖φ‖`, and off `W i` it vanishes.
  have hψc (i : s) (x : E) : ‖ψ i x‖ₑ ≤ c i := by
    by_cases hx : x ∈ W i
    · refine le_trans ?_ (hφc i x hx)
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hψφ i x)
    · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hψW i h)]
  calc ‖T (∑ i, ψ i)‖ₑ ≤ ∑ i, ‖T (ψ i)‖ₑ := by rw [map_sum]; exact enorm_sum_le _ _
    _ ≤ ∑ i : s, localMass T (W i) * c i := Finset.sum_le_sum fun i _ =>
        enorm_apply_le_localMass_mul_of_forall_enorm_le T (hψW i) (hψc i)
    _ ≤ ∑ i, localMass T (W i) * c i := by
        rw [Finset.sum_coe_sort s fun i => localMass T (W i) * c i]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)

/-- The local mass is subadditive on pairs of open sets. -/
theorem localMass_union_le {𝓖 : Type*} [FunLike 𝓖 𝓓^{n}(Ω, F) V]
    [LinearMapClass 𝓖 ℝ 𝓓^{n}(Ω, F) V] (T : 𝓖) {U U' : Set E} (hU : IsOpen U)
    (hU' : IsOpen U') : localMass T (U ∪ U') ≤ localMass T U + localMass T U' := by
  refine localMass_le_iff.2 fun φ hφ hφ1 => ?_
  have h := enorm_apply_le_sum_localMass_mul T (W := fun b : Bool => cond b U U') (c := fun _ => 1)
    (fun b => by cases b <;> assumption) (by rwa [← union_eq_iUnion])
    (fun _ x _ => by simpa [← ofReal_norm] using hφ1 x)
  simpa [add_comm] using h

/-- **Additivity of the local mass on disjoint open sets.** -/
theorem localMass_union_of_disjoint (T : 𝓕) {U U' : Set E} (hU : IsOpen U) (hU' : IsOpen U')
    (h : Disjoint U U') : localMass T (U ∪ U') = localMass T U + localMass T U' :=
  le_antisymm (localMass_union_le T hU hU') (localMass_add_localMass_le T h)

end LocalMass

section Content

/-- A compact subset of `Ω` has an open neighbourhood of finite local mass. -/
private theorem exists_localMass_ne_top {T : 𝓕} (hT : HasLocallyFiniteMass T) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ U : Opens E, K ⊆ (U : Set E) ∧ localMass T U ≠ ⊤ := by
  obtain ⟨U, hU, hKU, hclΩ, hcl⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨U, hU⟩, hKU, ne_top_of_le_ne_top
    ((hasLocallyFiniteMass_iff_localMass_ne_top T).1 hT _ hcl hclΩ) (localMass_mono subset_closure)⟩

/-- The content on the compact subsets of `Ω` whose induced measure is the mass measure: the
outer regularization of the local mass. -/
private def massContent {T : 𝓕} (hT : HasLocallyFiniteMass T) : Content Ω :=
  contentOfOpens (m := fun U => localMass T U) (fun _ _ h => localMass_mono h)
    (fun U V _ _ => localMass_union_le T U.isOpen V.isOpen)
    (fun _ _ _ _ h => localMass_add_localMass_le T (Opens.coe_disjoint.2 h))
    fun _ hK hKΩ => exists_localMass_ne_top hT hK hKΩ

end Content

/-- The level sets of `‖φ‖` on the support of `φ`: the points of the support where
`⌈‖φ x‖ / ε⌉₊ = j + 1`, that is `j * ε < ‖φ x‖ ≤ (j + 1) * ε`. -/
private def levelSet (φ : 𝓓^{n}(Ω, F)) (ε : ℝ) (j : ℕ) : Set Ω :=
  (↑) ⁻¹' tsupport φ ∩ {x | ⌈‖φ x‖ / ε⌉₊ = j + 1}

omit [FiniteDimensional ℝ E] in
private theorem mem_levelSet {φ : 𝓓^{n}(Ω, F)} {ε : ℝ} (hε : 0 < ε) {j : ℕ} {x : Ω}
    (hx : x ∈ levelSet φ ε j) : j * ε < ‖φ x‖ ∧ ‖φ x‖ ≤ (j + 1) * ε := by
  have h := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).1 hx.2
  rwa [Nat.succ_sub_one, Nat.cast_succ, lt_div_iff₀ hε, div_le_iff₀ hε] at h

omit [FiniteDimensional ℝ E] in
variable [MeasurableSpace E] [BorelSpace E] in
/-- On the level sets of `‖φ‖`, the constant `(j + 2) * ε` exceeds `‖φ‖` by at most `2 * ε`, so
the corresponding sum is bounded by the integral of `‖φ‖` plus `2 * ε` times the measure of a
neighbourhood `W` of the support. -/
private theorem sum_measure_levelSet_mul_le (μ : Measure Ω) (φ : 𝓓^{n}(Ω, F)) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) {W : Set E} (hφW : tsupport φ ⊆ W) :
    ∑ j : Fin N, μ (levelSet φ ε j) * ENNReal.ofReal ((j + 2) * ε) ≤
      ∫⁻ x, ‖φ x‖ₑ ∂μ + ENNReal.ofReal (2 * ε) * μ ((↑) ⁻¹' W) := by
  have hφc : Continuous fun x : Ω => φ x := φ.continuous.comp continuous_subtype_val
  have hmeas (j : Fin N) : MeasurableSet (levelSet φ ε j) :=
    ((isClosed_tsupport φ).preimage continuous_subtype_val).measurableSet.inter
      ((hφc.norm.div_const ε).measurable.nat_ceil (measurableSet_singleton _))
  have hdisj : Pairwise (Disjoint on fun j : Fin N => levelSet φ ε j) := fun i j hij =>
    disjoint_left.2 fun x hi hj => hij <| Fin.ext <| by simpa using hi.2.symm.trans hj.2
  calc ∑ j : Fin N, μ (levelSet φ ε j) * ENNReal.ofReal ((j + 2) * ε)
      = ∑ j : Fin N, ∫⁻ _ in levelSet φ ε j, ENNReal.ofReal ((j + 2) * ε) ∂μ := by
        simp only [setLIntegral_const, mul_comm]
    _ ≤ ∑ j : Fin N, ∫⁻ x in levelSet φ ε j, (‖φ x‖ₑ + ENNReal.ofReal (2 * ε)) ∂μ := by
        refine Finset.sum_le_sum fun j _ => setLIntegral_mono
          (hφc.enorm.measurable.add measurable_const) fun x hx => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [(mem_levelSet hε hx).1])
    _ = ∫⁻ x in ⋃ j : Fin N, levelSet φ ε j, (‖φ x‖ₑ + ENNReal.ofReal (2 * ε)) ∂μ := by
        rw [lintegral_iUnion hmeas hdisj, tsum_fintype]
    _ ≤ ∫⁻ x in (↑) ⁻¹' W, (‖φ x‖ₑ + ENNReal.ofReal (2 * ε)) ∂μ :=
        lintegral_mono_set (iUnion_subset fun _ _ hx => hφW hx.1)
    _ ≤ ∫⁻ x, ‖φ x‖ₑ ∂μ + ENNReal.ofReal (2 * ε) * μ ((↑) ⁻¹' W) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        exact add_le_add (setLIntegral_le_lintegral _ _) le_rfl

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- The **mass measure** `‖T‖` of a real-valued linear map `T` on test functions with locally
finite mass: the regular Borel measure on `Ω` whose value on `Ω ∩ U`, for `U` open, is the local
mass of `T` on `U` (`Distribution.massMeasure_preimage_coe`). It dominates evaluation,
`|T φ| ≤ ∫ ‖φ‖ d‖T‖` (`Distribution.enorm_apply_le_lintegral_massMeasure`), and is the least
outer regular measure doing so (`Distribution.massMeasure_le_of_enorm_apply_le`). If `T` does not
have locally finite mass, it is the zero measure by convention. -/
def massMeasure (T : 𝓕) : Measure Ω :=
  open scoped Classical in
  if hT : HasLocallyFiniteMass T then (massContent hT).measure else 0

variable {T : 𝓕}

private theorem massMeasure_eq (hT : HasLocallyFiniteMass T) :
    massMeasure T = (massContent hT).measure := by
  simp [massMeasure, hT]

@[simp]
theorem massMeasure_of_not_hasLocallyFiniteMass (hT : ¬HasLocallyFiniteMass T) :
    massMeasure T = 0 := by
  simp [massMeasure, hT]

instance : (massMeasure T).Regular := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  unfold massMeasure
  split_ifs <;> infer_instance

/-- **The mass measure on open sets.** For an open set `U` of `E`, the mass measure of `Ω ∩ U` is
the local mass of `T` on `U`. -/
theorem massMeasure_preimage_coe (hT : HasLocallyFiniteMass T) {U : Set E} (hU : IsOpen U) :
    massMeasure T ((↑) ⁻¹' U) = localMass T U := by
  rw [massMeasure_eq hT]
  refine contentOfOpens_measure_preimage_coe (U := ⟨U, hU⟩) _ _ _ _
    (localMass_le_iff.2 fun φ hφU hφ => ?_)
  -- The support of `φ` is a compact subset of `Ω ∩ U`.
  have hK : ((↑) '' ((↑) ⁻¹' tsupport φ : Set Ω) : Set E) = tsupport φ := by
    refine image_preimage_eq_of_subset ?_
    simpa using φ.tsupport_subset
  let K : Compacts Ω := ⟨(↑) ⁻¹' tsupport φ, Subtype.isCompact_iff.2 <| by
    rw [hK]; exact φ.hasCompactSupport.isCompact⟩
  exact le_iSup₂_of_le K (preimage_mono hφU)
    (le_opensInf fun V hφV _ => enorm_le_localMass (hK.symm.subset.trans hφV) hφ)

/-- The total mass of the mass measure is the mass. -/
@[simp]
theorem massMeasure_univ (hT : HasLocallyFiniteMass T) : massMeasure T univ = mass T := by
  simpa using massMeasure_preimage_coe hT isOpen_univ

/-- The level-set estimate behind the domination: if `W` is an open neighbourhood of the support
of `φ` of finite mass `M`, then `‖T φ‖ ≤ ∫ ‖φ‖ d‖T‖ + ε * (3 * M + 1)` for every `ε > 0`. -/
private theorem enorm_apply_le_lintegral_add_mul (hT : HasLocallyFiniteMass T)
    (φ : 𝓓^{n}(Ω, F)) {W : Set E} (hW : IsOpen W) (hφW : tsupport φ ⊆ W)
    (hM : massMeasure T ((↑) ⁻¹' W) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ‖T φ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T +
      ENNReal.ofReal ε * (3 * massMeasure T ((↑) ⁻¹' W) + 1) := by
  set μ := massMeasure T
  set M := μ ((↑) ⁻¹' W)
  set I := ∫⁻ x, ‖φ x‖ₑ ∂μ
  set N := ⌈‖(φ : E →ᵇ F)‖ / ε⌉₊
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((j + 2) * ε)
  -- Cover each level set by an open set of almost the same measure.
  obtain ⟨δ, hδ, hδS⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := ∑ j : Fin N, c j)
    (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top) (ENNReal.ofReal_pos.2 hε).ne'
  have hG (j : Fin N) : ∃ G ⊇ levelSet φ ε j, IsOpen G ∧ μ G < μ (levelSet φ ε j) + δ :=
    (levelSet φ ε j).exists_isOpen_lt_of_lt _ <| ENNReal.lt_add_right
      (ne_top_of_le_ne_top hM (measure_mono fun _ hx => hφW hx.1)) (by simpa using hδ.ne')
  choose G hEG hGo hGμ using hG
  -- The open sets `V i` cover the support of `φ`, with `‖φ‖ ≤ b i` on `V i`: the points where
  -- `‖φ‖ < ε`, and neighbourhoods of the level sets.
  let V : Option (Fin N) → Set E := fun i => i.elim (W ∩ {y | ‖φ y‖ < ε})
    fun j => (↑) '' G j ∩ W ∩ {y | ‖φ y‖ < (j + 2) * ε}
  let b : Option (Fin N) → ℝ≥0∞ := fun i => i.elim (ENNReal.ofReal ε) fun j => c j
  have hφn : Continuous fun y => ‖φ y‖ := continuous_norm.comp φ.continuous
  have hVo (i : Option (Fin N)) : IsOpen (V i) := by
    rcases i with _ | j
    · exact hW.inter (isOpen_lt hφn continuous_const)
    · exact ((Ω.isOpen.isOpenMap_subtype_val _ (hGo j)).inter hW).inter
        (isOpen_lt hφn continuous_const)
  have hVb (i : Option (Fin N)) (y : E) (hy : y ∈ V i) : ‖φ y‖ₑ ≤ b i := by
    rw [← ofReal_norm]
    rcases i with _ | j
    · exact ENNReal.ofReal_le_ofReal hy.2.le
    · exact ENNReal.ofReal_le_ofReal hy.2.le
  have hcover : tsupport φ ⊆ ⋃ i, V i := by
    intro y hy
    by_cases hyε : ‖φ y‖ < ε
    · exact mem_iUnion.2 ⟨none, hφW hy, hyε⟩
    -- Otherwise `y` lies in the level set of index `⌈‖φ y‖ / ε⌉₊ - 1`.
    have hpos : 0 < ⌈‖φ y‖ / ε⌉₊ := Nat.ceil_pos.2 (div_pos (hε.trans_le (not_lt.1 hyε)) hε)
    have hN : ⌈‖φ y‖ / ε⌉₊ ≤ N := Nat.ceil_mono <| div_le_div_of_nonneg_right
      (BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) y) hε.le
    let j : Fin N := ⟨⌈‖φ y‖ / ε⌉₊ - 1, by omega⟩
    have hx : (⟨y, φ.tsupport_subset hy⟩ : Ω) ∈ levelSet φ ε j :=
      ⟨hy, (Nat.sub_add_cancel hpos).symm⟩
    refine mem_iUnion.2 ⟨some j, ⟨⟨_, hEG j hx, rfl⟩, hφW hy⟩, ?_⟩
    have h := (mem_levelSet hε hx).2
    rw [mem_ofPred_eq]
    linarith
  have hMW : M = localMass T W := massMeasure_preimage_coe hT hW
  calc ‖T φ‖ₑ ≤ ∑ i, localMass T (V i) * b i := enorm_apply_le_sum_localMass_mul T hVo hcover hVb
    _ = localMass T (W ∩ {y | ‖φ y‖ < ε}) * ENNReal.ofReal ε +
          ∑ j, localMass T (V (some j)) * c j := Fintype.sum_option _
    _ ≤ M * ENNReal.ofReal ε + ∑ j : Fin N, (μ (levelSet φ ε j) + δ) * c j := by
        gcongr with j
        · rw [hMW]
          exact localMass_mono inter_subset_left
        · rw [← massMeasure_preimage_coe hT (hVo _)]
          refine (measure_mono (s := (↑) ⁻¹' V (some j)) fun x hx =>
            Subtype.val_injective.mem_set_image.1 hx.1.1).trans
            (hGμ j).le
    _ = M * ENNReal.ofReal ε + (∑ j : Fin N, μ (levelSet φ ε j) * c j + δ * ∑ j : Fin N, c j) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        simp only [add_mul]
    _ ≤ M * ENNReal.ofReal ε + ((I + ENNReal.ofReal (2 * ε) * M) + ENNReal.ofReal ε) := by
        gcongr
        exact sum_measure_levelSet_mul_le μ φ hε N hφW
    _ = I + ENNReal.ofReal ε * (3 * M + 1) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
        ring

/-- **Domination by the mass measure.** For a linear map `T` with locally finite mass,
`‖T φ‖ ≤ ∫ ‖φ‖ d‖T‖` for every test `φ`. -/
theorem enorm_apply_le_lintegral_massMeasure (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ‖T φ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T := by
  -- A neighbourhood `W` of the support of `φ` of finite measure `M`.
  obtain ⟨W, hW, hφW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure
    φ.hasCompactSupport.isCompact Ω.isOpen φ.tsupport_subset
  set M := massMeasure T ((↑) ⁻¹' W)
  have hM : M ≠ ⊤ := (massMeasure_preimage_coe hT hW).trans_ne <|
    ne_top_of_le_ne_top ((hasLocallyFiniteMass_iff_localMass_ne_top T).1 hT _ hWc hWΩ)
      (localMass_mono subset_closure)
  -- Let `ε → 0` in the level-set estimate.
  set I := ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T
  have h0 : Tendsto ENNReal.ofReal (𝓝[>] (0 : ℝ)) (𝓝 0) := ENNReal.ofReal_zero ▸
    (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun ε : ℝ => I + ENNReal.ofReal ε * (3 * M + 1)) (𝓝[>] 0) (𝓝 I) := by
    simpa using (ENNReal.Tendsto.mul_const h0 (Or.inr (by finiteness : 3 * M + 1 ≠ ⊤))).const_add I
  exact ge_of_tendsto hlim <| eventually_nhdsWithin_of_forall fun ε hε =>
    enorm_apply_le_lintegral_add_mul hT φ hW hφW hM hε

/-- **Minimality of the mass measure.** Every outer regular measure `ν` on `Ω` dominating
evaluation, `‖T φ‖ ≤ ∫ ‖φ‖ dν` for every test `φ`, is at least the mass measure. -/
theorem massMeasure_le_of_enorm_apply_le (ν : Measure Ω) [ν.OuterRegular]
    (h : ∀ φ : 𝓓^{n}(Ω, F), ‖T φ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂ν) : massMeasure T ≤ ν := by
  by_cases hT : HasLocallyFiniteMass T
  swap
  · rw [massMeasure_of_not_hasLocallyFiniteMass hT]
    exact Measure.zero_le ν
  -- The two measures compare on open sets, and both are outer regular.
  have hopen (U : Set Ω) (hU : IsOpen U) : massMeasure T U ≤ ν U := by
    obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
    rw [massMeasure_preimage_coe hT hU']
    refine localMass_le_iff.2 fun φ hφU hφ => (h φ).trans ?_
    rw [← lintegral_indicator_one hU.measurableSet]
    refine lintegral_mono fun x => ?_
    by_cases hx : (x : E) ∈ U'
    · simpa [hx, ← ofReal_norm] using hφ x
    · simp [hx, image_eq_zero_of_notMem_tsupport fun h => hx (hφU h)]
  refine Measure.le_iff'.2 fun s => ?_
  rw [s.measure_eq_iInf_isOpen (massMeasure T), s.measure_eq_iInf_isOpen ν]
  exact iInf₂_mono fun U _ => iInf_mono fun hU => hopen U hU

/-- **Uniqueness of the mass measure.** An outer regular measure on `Ω` whose value on `Ω ∩ U` is
the local mass of `T` on `U`, for every open set `U` of `E`, is the mass measure. -/
theorem eq_massMeasure_of_preimage_coe (hT : HasLocallyFiniteMass T) (ν : Measure Ω)
    [ν.OuterRegular] (h : ∀ U : Set E, IsOpen U → ν ((↑) ⁻¹' U) = localMass T U) :
    ν = massMeasure T := by
  refine Measure.OuterRegular.ext_isOpen fun U hU => ?_
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  rw [h U' hU', massMeasure_preimage_coe hT hU']

end Measure

end Distribution
