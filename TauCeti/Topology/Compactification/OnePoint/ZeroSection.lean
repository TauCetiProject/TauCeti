/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval

/-!
# The complement of the zero section in the one-point compactification of a product

Let `S` be a Hausdorff space and `V` a real normed space. The one-point compactification
`OnePoint (S × V)` of the trivial bundle `S × V → S` contains the zero section
`x ↦ (x, 0)`. Its complement is contractible
(`TauCeti.contractibleSpace_compl_range_onePoint_zeroSection`): pushing every point radially to
infinity, `(x, v) ↦ (x, (1 - t)⁻¹ • v)` for `t < 1` and `∞` at `t = 1`, contracts it onto `∞`.

For compact `S`, `OnePoint (S × V)` is the Thom space `S₊ ∧ Sᵏ` of the trivial bundle of rank
`k = dim V`, and the contractibility of the complement of the zero section identifies its
homology in positive degrees with its homology relative to that complement, the local homology
along the zero section. This is how the Thom isomorphism of the trivial bundle is read off the
Thom space.

## Main results

* `TauCeti.contractibleSpace_compl_range_onePoint_zeroSection`: the complement of the zero section
  is contractible.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (Thom spaces).
-/

public section

noncomputable section

open Filter Function Set Topology OnePoint unitInterval

namespace TauCeti

variable {S V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial push of `OnePoint (S × V)` to infinity at time `t`: the point `(x, v)` goes to
`(x, (1 - t)⁻¹ • v)` for `t ≠ 1`, and everything goes to `∞` at `t = 1`. -/
private def onePointPushOut (t : ℝ) (y : OnePoint (S × V)) : OnePoint (S × V) :=
  if t = 1 then ∞ else OnePoint.map (fun z : S × V ↦ (z.1, (1 - t)⁻¹ • z.2)) y

@[simp]
private lemma onePointPushOut_one (y : OnePoint (S × V)) : onePointPushOut 1 y = ∞ := by
  simp [onePointPushOut]

@[simp]
private lemma onePointPushOut_infty (t : ℝ) : onePointPushOut t (∞ : OnePoint (S × V)) = ∞ := by
  unfold onePointPushOut
  split_ifs <;> rfl

private lemma onePointPushOut_coe {t : ℝ} (ht : t ≠ 1) (z : S × V) :
    onePointPushOut t (z : OnePoint (S × V)) = ((z.1, (1 - t)⁻¹ • z.2) : S × V) := by
  simp [onePointPushOut, ht]

@[simp]
private lemma onePointPushOut_zero (y : OnePoint (S × V)) : onePointPushOut 0 y = y := by
  induction y using OnePoint.rec with
  | infty => exact onePointPushOut_infty 0
  | coe z => simp [onePointPushOut_coe zero_ne_one]

/-- Pushing a point off the zero section keeps it off the zero section. -/
private lemma onePointPushOut_notMem_range_zeroSection {t : ℝ} {y : OnePoint (S × V)}
    (hy : y ∉ range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) :
    onePointPushOut t y ∉ range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)) := by
  rintro ⟨x, hx⟩
  by_cases ht : t = 1
  · rw [ht, onePointPushOut_one] at hx
    exact coe_ne_infty _ hx
  induction y using OnePoint.rec with
  | infty => exact coe_ne_infty _ (hx.trans (onePointPushOut_infty t))
  | coe z =>
    rw [onePointPushOut_coe ht, coe_eq_coe, Prod.ext_iff] at hx
    refine hy ⟨x, ?_⟩
    have h2 : z.2 = 0 := by
      simpa [sub_eq_zero, Ne.symm ht] using hx.2.symm
    rw [coe_eq_coe, Prod.ext_iff]
    exact ⟨hx.1, h2.symm⟩

/-- The radial push of a point `z` of `S × V` at a time `t ∈ [0, 1]` lands at `∞` or outside a set
`K` as soon as, for `t < 1`, the rescaled point `(z.1, (1 - t)⁻¹ • z.2)` is outside `K`. -/
private lemma onePointPushOut_mem_image_compl_union {K : Set (S × V)} {t : I} {z : S × V}
    (h : 0 < 1 - (t : ℝ) → (z.1, (1 - (t : ℝ))⁻¹ • z.2) ∉ K) :
    onePointPushOut (t : ℝ) (z : OnePoint (S × V)) ∈ (↑) '' Kᶜ ∪ {∞} := by
  by_cases ht : (t : ℝ) = 1
  · rw [ht, onePointPushOut_one]
    exact Or.inr rfl
  exact Or.inl ⟨_, h (sub_pos.2 (lt_of_le_of_ne (le_one t) ht)), (onePointPushOut_coe ht _).symm⟩

variable [TopologicalSpace S]

/-- The radial push at time `1`, near a point `(x₀, v₀)` with `v₀ ≠ 0`, lands outside every compact
set: the push of `(x, v)` at a time `t` close to `1` has norm `(1 - t)⁻¹ ‖v‖`, which is large. -/
private lemma tendsto_onePointPushOut_coe_one {z₀ : S × V} (hz₀ : z₀.2 ≠ 0) :
    Tendsto (fun q : I × (S × V) ↦ onePointPushOut (q.1 : ℝ) (q.2 : OnePoint (S × V)))
      (𝓝 (1, z₀)) (𝓝 ∞) := by
  rw [Tendsto, le_nhds_infty]
  intro K _ hK
  rw [mem_map]
  obtain ⟨R, hR⟩ := (hK.image continuous_snd).isBounded.exists_norm_le
  set a := ‖z₀.2‖ / 2 with ha
  have ha₀ : 0 < a := by positivity
  have h₁ : ∀ᶠ q : I × (S × V) in 𝓝 (1, z₀), a < ‖q.2.2‖ :=
    (continuous_norm.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually
      (lt_mem_nhds (by simp only [comp_apply, ha]; linarith [norm_pos_iff.2 hz₀]))
  have h₂ : ∀ᶠ q : I × (S × V) in 𝓝 (1, z₀), 1 - (q.1 : ℝ) < a / (|R| + 1) := by
    refine ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).continuousAt
      (x := ((1 : I), z₀))).eventually (gt_mem_nhds ?_)
    simpa using div_pos ha₀ (by positivity : (0 : ℝ) < |R| + 1)
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  refine onePointPushOut_mem_image_compl_union fun hpos hmem ↦ ?_
  have hbound := hR _ ⟨_, hmem, rfl⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos] at hbound
  have hlt : |R| + 1 < (1 - (q.1 : ℝ))⁻¹ * ‖q.2.2‖ := by
    rw [lt_inv_mul_iff₀ hpos]
    calc (1 - (q.1 : ℝ)) * (|R| + 1) < a / (|R| + 1) * (|R| + 1) := by gcongr
      _ = a := div_mul_cancel₀ a (by positivity)
      _ < ‖q.2.2‖ := hq₁
  linarith [le_abs_self R]

variable [T2Space S]

/-- Near `∞`, the radial push at any time stays near `∞`: a point outside the compact set of
the rescalings `(x, λ • v)`, `λ ∈ [0, 1]`, of the points of a compact set `K` is pushed outside
`K`. -/
private lemma tendsto_onePointPushOut_infty (t₀ : I) :
    Tendsto (fun q : I × OnePoint (S × V) ↦ onePointPushOut (q.1 : ℝ) q.2) (𝓝 (t₀, ∞)) (𝓝 ∞) := by
  rw [Tendsto, le_nhds_infty]
  intro K _ hK
  rw [mem_map]
  set C := (fun p : ℝ × (S × V) ↦ (p.2.1, p.1 • p.2.2)) '' (Icc 0 1 ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image (by fun_prop)
  rw [nhds_prod_eq]
  refine mem_of_superset (prod_mem_prod univ_mem
    (hasBasis_nhds_infty.mem_of_mem ⟨hC.isClosed, hC⟩)) ?_
  rintro ⟨t, y⟩ ⟨-, hy⟩
  obtain ⟨z, hz, rfl⟩ | rfl := hy
  · refine onePointPushOut_mem_image_compl_union fun hpos hmem ↦ hz ?_
    refine ⟨(1 - (t : ℝ), (z.1, (1 - (t : ℝ))⁻¹ • z.2)), ⟨⟨hpos.le, by linarith [nonneg t]⟩, hmem⟩,
      ?_⟩
    simp [smul_smul, hpos.ne']
  · simp only [mem_preimage, onePointPushOut_infty]
    exact Or.inr rfl

/-- **The radial push to infinity is continuous** at every point except the points of the zero
section at time `1`. -/
private theorem continuousAt_onePointPushOut {t : I} {y : OnePoint (S × V)}
    (h : y ∉ (range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) ∨ (t : ℝ) ≠ 1) :
    ContinuousAt (fun q : I × OnePoint (S × V) ↦ onePointPushOut (q.1 : ℝ) q.2) (t, y) := by
  induction y using OnePoint.rec with
  | infty =>
    rw [ContinuousAt, onePointPushOut_infty]
    exact tendsto_onePointPushOut_infty t
  | coe z =>
    -- Read through the open embedding `I × (S × V) → I × OnePoint (S × V)`.
    have he : IsOpenEmbedding (Prod.map id ((↑) : S × V → OnePoint (S × V))) :=
      (IsOpenEmbedding.id (X := I)).prodMap isOpenEmbedding_coe
    change ContinuousAt _ (Prod.map id ((↑) : S × V → OnePoint (S × V)) (t, z))
    rw [← he.isInducing.continuousAt_iff' (he.isOpen_range.mem_nhds (mem_range_self _))]
    by_cases ht : (t : ℝ) = 1
    · have hz : z.2 ≠ 0 := by
        rintro hz
        refine (h.resolve_right (not_not.2 ht)) ⟨z.1, ?_⟩
        rw [coe_eq_coe, Prod.ext_iff]
        exact ⟨rfl, hz.symm⟩
      rw [ContinuousAt, comp_apply, Prod.map_apply, id_eq, ht, onePointPushOut_one]
      obtain rfl : t = 1 := Subtype.ext ht
      exact tendsto_onePointPushOut_coe_one hz
    · -- Away from time `1` the push is `(x, v) ↦ (x, (1 - t)⁻¹ • v)`.
      have hopen : IsOpen {q : I × (S × V) | (q.1 : ℝ) ≠ 1} :=
        isOpen_ne_fun (continuous_subtypeVal.comp continuous_fst) continuous_const
      refine ContinuousAt.congr (f := fun q : I × (S × V) ↦
          (((q.2.1, (1 - (q.1 : ℝ))⁻¹ • q.2.2) : S × V) : OnePoint (S × V))) ?_ ?_
      · refine continuous_coe.continuousAt.comp ?_
        have h1t : (1 : ℝ) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
        exact (continuous_snd.fst.continuousAt).prodMk
          (((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).continuousAt.inv₀
            h1t).smul continuous_snd.snd.continuousAt)
      · filter_upwards [hopen.mem_nhds (show ((t, z).1 : ℝ) ≠ 1 from ht)] with q hq
        exact (onePointPushOut_coe hq q.2).symm

/-- The radial push to infinity, as a homotopy from the identity of the complement of the zero
section to the constant map at `∞`. -/
private def onePointPushOutHomotopy :
    ContinuousMap.Homotopy
      (ContinuousMap.id ↥(range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ)
      (ContinuousMap.const ↥(range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ
        ⟨∞, fun ⟨_, h⟩ ↦ coe_ne_infty _ h⟩) where
  toFun q :=
    ⟨onePointPushOut (q.1 : ℝ) q.2, onePointPushOut_notMem_range_zeroSection q.2.property⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun q ↦ ?_) _
    have hf : ContinuousAt (fun q : I × ↥(range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ ↦
        (q.1, (q.2 : OnePoint (S × V)))) q := by fun_prop
    exact ContinuousAt.comp (x := q) (continuousAt_onePointPushOut (Or.inl q.2.property)) hf
  map_zero_left y := Subtype.ext (onePointPushOut_zero (y : OnePoint (S × V)))
  map_one_left y := Subtype.ext (onePointPushOut_one (y : OnePoint (S × V)))

/-- **The complement of the zero section of `OnePoint (S × V)` is contractible**: the radial push
`(x, v) ↦ (x, (1 - t)⁻¹ • v)` contracts it onto `∞`. -/
theorem contractibleSpace_compl_range_onePoint_zeroSection :
    ContractibleSpace ↥(range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ :=
  (contractible_iff_id_nullhomotopic _).2 ⟨_, ⟨onePointPushOutHomotopy⟩⟩

end TauCeti
