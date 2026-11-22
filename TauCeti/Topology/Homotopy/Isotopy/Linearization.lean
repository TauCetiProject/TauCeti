/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.UnitInterval
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Isotopy of a map of `S × V` to its linearization along the zero section

Let `S` be a topological space and `V` a real normed space. A map `h : S × V → S × V` fixing the
zero section is rescaled along it by `h_t (x, w) = ((h (x, t w)).1, t⁻¹ (h (x, t w)).2)` for
`t ∈ (0, 1]`, extended at `t = 0` by a family `L` of linear maps, `(x, w) ↦ (x, L x w)`
(`TauCeti.zeroSectionRescale`). At `t = 1` it is `h`. If `h` is continuous on an open set
`U ⊇ S × {0}` and has fibre derivative `L` along the zero section uniformly in `x`, with `L`
continuous, the family is continuous on the open set of `(t, x, w)` with `(x, t w) ∈ U`, also at
`t = 0` (`TauCeti.continuousOn_zeroSectionRescale`); for `U = S × V` it is continuous.

For an open embedding `g` of `S × V` fixing the zero section, with `S` compact and fibre
derivative a continuous family `A` of linear automorphisms of `V`, the rescalings form an isotopy
of open embeddings from the linearization `(x, w) ↦ (x, A x w)` to `g`
(`TauCeti.isOpenEmbedding_zeroSectionRescale`). Its inverse is the rescaling of the inverse of
`g`, which has fibre derivative `(A x)⁻¹` along the zero section by compactness of `S`
(`TauCeti.exists_norm_snd_inverse_sub_le`). This is the rescaling step in the proof that tubular
neighbourhoods are unique up to isotopy.

## Main definitions

* `TauCeti.zeroSectionRescale h L`: the rescalings of `h` along the zero section, with limit
  `L` at `t = 0`.

## Main results

* `TauCeti.zeroSectionRescale_zero`, `TauCeti.zeroSectionRescale_one`: the endpoints.
* `TauCeti.continuousOn_zeroSectionRescale`: the rescaling is continuous on the open set of
  `(t, x, w)` with `(x, t w) ∈ U` when `h` is continuous on an open set `U ⊇ S × {0}` and has fibre
  derivative a continuous family `L` along the zero section.
* `TauCeti.exists_norm_snd_inverse_sub_le`: the inverse of an open embedding with fibre derivative
  `A` has fibre derivative `A⁻¹`.
* `TauCeti.isOpenEmbedding_zeroSectionRescale`: the rescalings of an open embedding form an
  isotopy of open embeddings to its linearization.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5 (uniqueness of tubular neighbourhoods, through the rescaling of an embedding to
  its derivative along the zero section).
-/

public section

open Function Set Topology Filter Metric

namespace TauCeti

variable {S V W : Type*} [TopologicalSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Rescaling a map of `S × V` along the zero section -/

/-- The rescaling of a map `h : S × V → S × W` along the zero section, with limit `L` at `t = 0`:
at `(t, x, w)` it is `(h (x, t w)).1, t⁻¹ (h (x, t w)).2` for `t ≠ 0`, and `(x, L x w)` for
`t = 0`. For `t = 1` it is `h`. If `h` is continuous on an open set `U ⊇ S × {0}`, fixes the
zero section, and has fibre derivative a continuous family `L` along it, this is continuous on
`{(t, x, w) | (x, t w) ∈ U}` (`TauCeti.continuousOn_zeroSectionRescale`): it is the deformation
of `h` into its linearization along the zero section. -/
noncomputable def zeroSectionRescale (h : S × V → S × W) (L : S → V →L[ℝ] W)
    (q : unitInterval × (S × V)) : S × W :=
  if (q.1 : ℝ) = 0 then (q.2.1, L q.2.1 q.2.2)
  else ((h (q.2.1, (q.1 : ℝ) • q.2.2)).1, (q.1 : ℝ)⁻¹ • (h (q.2.1, (q.1 : ℝ) • q.2.2)).2)

omit [TopologicalSpace S] in
theorem zeroSectionRescale_of_eq_zero {h : S × V → S × W} {L : S → V →L[ℝ] W}
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) = 0) :
    zeroSectionRescale h L q = (q.2.1, L q.2.1 q.2.2) := by
  simp [zeroSectionRescale, hq]

omit [TopologicalSpace S] in
theorem zeroSectionRescale_of_ne_zero {h : S × V → S × W} {L : S → V →L[ℝ] W}
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) ≠ 0) :
    zeroSectionRescale h L q = ((h (q.2.1, (q.1 : ℝ) • q.2.2)).1,
      (q.1 : ℝ)⁻¹ • (h (q.2.1, (q.1 : ℝ) • q.2.2)).2) := by
  simp [zeroSectionRescale, hq]

omit [TopologicalSpace S] in
/-- At `t = 0` the rescaling is the linearization `(x, w) ↦ (x, L x w)`. -/
@[simp]
theorem zeroSectionRescale_zero (h : S × V → S × W) (L : S → V →L[ℝ] W) (p : S × V) :
    zeroSectionRescale h L (0, p) = (p.1, L p.1 p.2) :=
  zeroSectionRescale_of_eq_zero rfl

omit [TopologicalSpace S] in
/-- At `t = 1` the rescaling is the map itself. -/
@[simp]
theorem zeroSectionRescale_one (h : S × V → S × W) (L : S → V →L[ℝ] W) (p : S × V) :
    zeroSectionRescale h L (1, p) = h p := by
  simp [zeroSectionRescale_of_ne_zero (q := (1, p)) one_ne_zero]

omit [TopologicalSpace S] in
/-- Away from `t = 0`, rescaling back by `t` recovers the value of `h`. -/
private theorem zeroSectionRescale_smul_eq {h : S × V → S × W} (L : S → V →L[ℝ] W)
    {q : unitInterval × (S × V)} (hq : (q.1 : ℝ) ≠ 0) :
    ((zeroSectionRescale h L q).1, (q.1 : ℝ) • (zeroSectionRescale h L q).2) =
      h (q.2.1, (q.1 : ℝ) • q.2.2) := by
  rw [zeroSectionRescale_of_ne_zero hq, smul_inv_smul₀ hq]

omit [TopologicalSpace S] in
/-- If `h` fixes the zero section, the first component of its rescaling at `(t, x, w)` is that of
`h (x, t w)`, also at `t = 0`. -/
theorem fst_zeroSectionRescale {h : S × V → S × W} (L : S → V →L[ℝ] W)
    (h0 : ∀ x, h (x, 0) = (x, 0)) (q : unitInterval × (S × V)) :
    (zeroSectionRescale h L q).1 = (h (q.2.1, (q.1 : ℝ) • q.2.2)).1 := by
  by_cases hq : (q.1 : ℝ) = 0
  · rw [zeroSectionRescale_of_eq_zero hq, hq, zero_smul, h0]
  · rw [zeroSectionRescale_of_ne_zero hq]

/-- **The rescaling is continuous.** Let `h` be continuous on an open set `U ⊇ S × {0}`, fixing
the zero section, with fibre derivative a continuous family `L` along it uniformly in `x`. Then
the rescaling of `h` is continuous on the open set of `(t, x, w)` with `(x, t w) ∈ U`. -/
theorem continuousOn_zeroSectionRescale {h : S × V → S × W}
    {L : S → V →L[ℝ] W} (hL : Continuous L) {U : Set (S × V)} (hU : IsOpen U)
    (hh : ContinuousOn h U) (h0 : ∀ x, h (x, 0) = (x, 0))
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, (x, v) ∈ U → ‖v‖ < δ → ‖(h (x, v)).2 - L x v‖ ≤ ε * ‖v‖) :
    ContinuousOn (zeroSectionRescale h L) {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} := by
  have hcU : Continuous fun q : unitInterval × (S × V) ↦ (q.2.1, (q.1 : ℝ) • q.2.2) := by fun_prop
  have hW : IsOpen {q : unitInterval × (S × V) | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} :=
    hU.preimage hcU
  have hhc : ContinuousOn (fun q : unitInterval × (S × V) ↦ h (q.2.1, (q.1 : ℝ) • q.2.2))
    {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ U} := hh.comp hcU.continuousOn fun _ hq ↦ hq
  refine hW.continuousOn_iff.2 fun q hq ↦ ?_
  -- The first component is the first component of `h (x, t w)`, also at `t = 0`.
  have h₁ : ContinuousAt (fun p ↦ (zeroSectionRescale h L p).1) q := by
    simp_rw [fst_zeroSectionRescale L h0]
    exact (continuous_fst.comp_continuousOn hhc).continuousAt (hW.mem_nhds hq)
  suffices h₂ : ContinuousAt (fun p ↦ (zeroSectionRescale h L p).2) q from h₁.prodMk h₂
  by_cases ht : (q.1 : ℝ) = 0
  · -- At `t = 0` the second component converges to `L x w` by the uniform estimate.
    rw [ContinuousAt, zeroSectionRescale_of_eq_zero ht]
    have hL' : ContinuousAt (fun p : unitInterval × (S × V) ↦ L p.2.1 p.2.2) q := by fun_prop
    suffices h₀ : Tendsto (fun p ↦ (zeroSectionRescale h L p).2 - L p.2.1 p.2.2) (𝓝 q) (𝓝 0) by
      simpa using h₀.add hL'
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hδε⟩ := hest (ε / 2 / (‖q.2.2‖ + 1)) (by positivity)
    have hδ' : (q.1 : ℝ) * ‖q.2.2‖ < δ := by simpa [ht] using hδ
    filter_upwards [hW.mem_nhds hq, (isOpen_lt (f := fun p : unitInterval × (S × V) ↦
        (p.1 : ℝ) * ‖p.2.2‖) (by fun_prop) continuous_const).mem_nhds hδ',
      (isOpen_lt (f := fun p : unitInterval × (S × V) ↦ ‖p.2.2‖) (by fun_prop)
        continuous_const).mem_nhds (lt_add_one ‖q.2.2‖)] with p hpU hpδ hpv
    rw [dist_zero_right]
    by_cases hp : (p.1 : ℝ) = 0
    · rwa [zeroSectionRescale_of_eq_zero hp, sub_self, norm_zero]
    have hp0 : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.property.1 (Ne.symm hp)
    rw [zeroSectionRescale_of_ne_zero hp]
    have := hδε p.2.1 _ hpU (by rwa [norm_smul, Real.norm_of_nonneg hp0.le])
    calc ‖(p.1 : ℝ)⁻¹ • (h (p.2.1, (p.1 : ℝ) • p.2.2)).2 - L p.2.1 p.2.2‖
        ≤ ε / 2 / (‖q.2.2‖ + 1) * ‖p.2.2‖ :=
          (L p.2.1).toLinearMap.norm_inv_smul_sub_le hp (by rwa [norm_smul] at this)
      _ ≤ ε / 2 / (‖q.2.2‖ + 1) * (‖q.2.2‖ + 1) := by gcongr
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
      _ < ε := half_lt_self hε
  · -- Away from `t = 0` the second component is given by its formula near `q`.
    have hev : (fun p ↦ (zeroSectionRescale h L p).2) =ᶠ[𝓝 q]
        fun p ↦ (p.1 : ℝ)⁻¹ • (h (p.2.1, (p.1 : ℝ) • p.2.2)).2 := by
      filter_upwards [(isOpen_ne_fun (f := fun p : unitInterval × (S × V) ↦ (p.1 : ℝ))
        (by fun_prop) continuous_const).mem_nhds ht] with p hp
      rw [zeroSectionRescale_of_ne_zero hp]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((continuous_subtypeVal.comp continuous_fst).continuousAt.inv₀ ht).smul
      ((continuous_snd.comp_continuousOn hhc).continuousAt (hW.mem_nhds hq))

/-! ### The isotopy of an open embedding to its linearization -/

/-- **The inverse has the inverse fibre derivative.** Let `g` be an open embedding of `S × V`
fixing the zero section, with fibre derivative `A x` along it uniformly in `x`, and let `g'` be an
inverse of `g` on its range. If `S` is compact, `g'` has fibre derivative `(A x)⁻¹` along the zero
section, uniformly in `x`. -/
theorem exists_norm_snd_inverse_sub_le [CompactSpace S] {g g' : S × V → S × V}
    (hg : IsOpenEmbedding g) (hg' : ContinuousOn g' (range g)) (hg'g : ∀ p, g' (g p) = p)
    (hgg' : ∀ q ∈ range g, g (g' q) = q) (h0 : ∀ x, g (x, 0) = (x, 0))
    {A : S → (V →L[ℝ] V)ˣ} (hA : Continuous A)
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ x u, (x, u) ∈ range g → ‖u‖ < δ →
      ‖(g' (x, u)).2 - (↑(A x)⁻¹ : V →L[ℝ] V) u‖ ≤ ε * ‖u‖ := by
  have hAi : Continuous fun x ↦ (↑(A x)⁻¹ : V →L[ℝ] V) := Units.continuous_coe_inv.comp hA
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hAi.continuousOn
  set K := max C 1
  have hK : 0 < K := lt_max_of_lt_right one_pos
  have hAK (x : S) : ‖(↑(A x)⁻¹ : V →L[ℝ] V)‖ ≤ K := (hC x (mem_univ x)).trans (le_max_left _ _)
  set ε' := min (1 / (2 * K)) (ε / (4 * K ^ 2))
  obtain ⟨δ₁, hδ₁, hδ₁ε⟩ := hest ε' (lt_min (by positivity) (by positivity))
  -- Near the zero section, `(A x)⁻¹` changes little between a point and its image under `g`.
  have hO₃ : IsOpen {p : S × V | ‖(↑(A (g p).1)⁻¹ : V →L[ℝ] V) - ↑(A p.1)⁻¹‖ < ε / 2} :=
    isOpen_lt ((hAi.comp (continuous_fst.comp hg.continuous)).sub
      (hAi.comp continuous_fst)).norm continuous_const
  obtain ⟨δ₃, hδ₃, hδ₃A⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (v : V) (x : S) ↦ ‖(↑(A (g (x, v)).1)⁻¹ : V →L[ℝ] V) - ↑(A x)⁻¹‖ < ε / 2)
    fun x _ ↦ (hO₃.preimage continuous_swap).mem_nhds (by simp [h0, hε])
  -- Near the zero section of the range, the inverse `g'` stays near the zero section.
  have hO₂ : IsOpen (range g ∩ g' ⁻¹' {p | ‖p.2‖ < min δ₁ δ₃}) :=
    hg'.isOpen_inter_preimage hg.isOpen_range (isOpen_lt continuous_snd.norm continuous_const)
  obtain ⟨δ₂, hδ₂, hδ₂g⟩ := isCompact_univ.exists_pos_forall_norm_lt
    (Q := fun (u : V) (x : S) ↦ (x, u) ∈ range g ∩ g' ⁻¹' {p | ‖p.2‖ < min δ₁ δ₃})
    fun x _ ↦ (hO₂.preimage continuous_swap).mem_nhds
      ⟨⟨(x, 0), h0 x⟩, by rw [mem_preimage, Prod.swap_prod_mk, ← h0 x, hg'g]; simp [hδ₁, hδ₃]⟩
  refine ⟨δ₂, hδ₂, fun x u hxu hu ↦ ?_⟩
  rcases hp : g' (x, u) with ⟨y, v⟩
  have hgp : g (y, v) = (x, u) := hp ▸ hgg' _ hxu
  have hv : ‖v‖ < min δ₁ δ₃ := by simpa [hp] using (hδ₂g hu x (mem_univ x)).2
  have h₁ := hδ₁ε y v (hv.trans_le (min_le_left _ _))
  have h₃ := hδ₃A (hv.trans_le (min_le_right _ _)) y (mem_univ y)
  simp only [hgp] at h₁
  simp only [hgp] at h₃
  have hBv : (↑(A y)⁻¹ : V →L[ℝ] V) ((A y : V →L[ℝ] V) v) = v := by
    simp [← mul_apply_eq_comp]
  have hKε : K * ε' ≤ 1 / 2 := by
    calc K * ε' ≤ K * (1 / (2 * K)) := by gcongr; exact min_le_left _ _
      _ = 1 / 2 := by field_simp
  have hε'K : 2 * K ^ 2 * ε' ≤ ε / 2 := by
    calc 2 * K ^ 2 * ε' ≤ 2 * K ^ 2 * (ε / (4 * K ^ 2)) := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp; ring
  calc ‖v - (↑(A x)⁻¹ : V →L[ℝ] V) u‖ ≤ (2 * K ^ 2 * ε' + ε / 2) * ‖u‖ :=
        ContinuousLinearMap.norm_sub_apply_le_of_apply_eq hBv (hAK y) hKε (by positivity) h₁ h₃.le
    _ ≤ ε * ‖u‖ := by nlinarith [norm_nonneg u]

/-- **The isotopy of an open embedding to its linearization.** Let `g` be an open embedding of
`S × V` fixing the zero section, with `S` compact and fibre derivative `A x` along it uniformly in
`x`, for a continuous family `A` of linear automorphisms of `V`. Then the rescalings of `g`, joined
at `t = 0` to its linearization `(x, v) ↦ (x, A x v)`, form an isotopy of open embeddings: the
total map `(t, x, v) ↦ (t, zeroSectionRescale g A (t, x, v))` is an open embedding. -/
theorem isOpenEmbedding_zeroSectionRescale [CompactSpace S] {g : S × V → S × V}
    (hg : IsOpenEmbedding g) (h0 : ∀ x, g (x, 0) = (x, 0)) {A : S → (V →L[ℝ] V)ˣ}
    (hA : Continuous A)
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x v, ‖v‖ < δ → ‖(g (x, v)).2 - (A x : V →L[ℝ] V) v‖ ≤ ε * ‖v‖) :
    IsOpenEmbedding fun q : unitInterval × (S × V) ↦
      (q.1, zeroSectionRescale g (fun x ↦ (A x : V →L[ℝ] V)) q) := by
  -- Over an empty `S` the domain is empty; otherwise `g` has an inverse on its range.
  cases isEmpty_or_nonempty S
  · exact .of_isEmpty _
  set g' := (hg.toOpenPartialHomeomorph g).symm
  have hg'g (p : S × V) : g' (g p) = p :=
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv g hg
  have hgg' (q : S × V) (hq : q ∈ range g) : g (g' q) = q :=
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv g hg hq
  have hg' : ContinuousOn g' (range g) := by
    simpa using (hg.toOpenPartialHomeomorph g).continuousOn_symm
  have hg'0 (x : S) : g' (x, 0) = (x, 0) := by simpa [h0] using hg'g (x, 0)
  have hcont := continuousOn_zeroSectionRescale (Units.continuous_val.comp hA) isOpen_univ
    hg.continuous.continuousOn h0 fun ε hε ↦ (hest ε hε).imp fun _ ⟨hδ, h⟩ ↦
      ⟨hδ, fun x v _ ↦ h x v⟩
  simp only [mem_univ, ofPred_true, continuousOn_univ] at hcont
  refine IsOpenEmbedding.of_continuousOn_inverse
    (W := {q | (q.2.1, (q.1 : ℝ) • q.2.2) ∈ range g})
    (g := fun q ↦ (q.1, zeroSectionRescale g' (fun x ↦ (↑(A x)⁻¹ : V →L[ℝ] V)) q))
    (continuous_fst.prodMk hcont) (hg.isOpen_range.preimage (by fun_prop))
    (continuous_fst.continuousOn.prodMk (continuousOn_zeroSectionRescale
      (Units.continuous_coe_inv.comp hA) hg.isOpen_range hg' hg'0 fun ε hε ↦
        exists_norm_snd_inverse_sub_le hg hg' hg'g hgg' h0 hA hest ε hε)) (fun q ↦ ?_)
    (fun q ↦ ?_) fun q hq ↦ ?_
  · -- The family stays in the domain of the inverse.
    by_cases ht : (q.1 : ℝ) = 0
    · simp only [mem_ofPred_eq, zeroSectionRescale_of_eq_zero ht, ht, zero_smul]
      exact ⟨(q.2.1, 0), h0 _⟩
    · exact ⟨_, (zeroSectionRescale_smul_eq _ ht).symm⟩
  · -- The inverse family undoes the family.
    refine Prod.ext rfl ?_
    dsimp only
    by_cases ht : (q.1 : ℝ) = 0
    · simp [zeroSectionRescale_of_eq_zero, ht, ← mul_apply_eq_comp]
    · simp [zeroSectionRescale_of_ne_zero, ht, hg'g]
  · -- The family undoes the inverse family on its domain.
    refine Prod.ext rfl ?_
    dsimp only
    by_cases ht : (q.1 : ℝ) = 0
    · simp [zeroSectionRescale_of_eq_zero, ht, ← mul_apply_eq_comp]
    · have hq' : (q.2.1, (q.1 : ℝ) • q.2.2) ∈ range g := hq
      simp [zeroSectionRescale_of_ne_zero, ht, hgg' _ hq']

end TauCeti
