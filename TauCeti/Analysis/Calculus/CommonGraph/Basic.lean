/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# Common local graph presentations of touching hypersurfaces

Let `E` and `F` be Banach spaces and `P = E × ℝ` with the `L²` product norm, the model of an
ambient chart split into a horizontal and a vertical direction. A map `f : F → P` which is
`Cᵏ`, for `k ≠ 0`, on an open set `U` and whose horizontal derivative
`v ↦ (df_a v).1` is bijective at `a ∈ U` is, near `a`, the graph of a `Cᵏ` height function
over an open set of `E`: the inverse function theorem applied to the horizontal component of `f`.

Two such parametrized hypersurfaces through a common point are then graphs over one common open
set of `E`. If the second one lies in `{0 ≤ ρ}` for a function `ρ` whose derivative at the
contact point is positive on the vertical direction, and the first one lies in `{ρ ≤ 0}`, the
heights are ordered: `u₁ ≤ u₂`. This turns one-sidedness of two touching hypersurfaces into the
order of two graph heights over a common domain, the form in which comparison principles apply.

## Main declarations

* `TauCeti.IsGraphPresentation`: `f` maps `V` bijectively onto the graph of `u` over `D`, with
  `TauCeti.isGraphPresentation_graph` for the graph map itself.
* `TauCeti.exists_isGraphPresentation`: a hypersurface with a non-vertical tangent plane is
  locally the graph of a `Cᵏ` height, for `k ≠ 0`.
* `TauCeti.eventually_le_of_hasStrictFDerivAt`: graph heights lying in `{ρ ≤ 0}` and in
  `{0 ≤ ρ}` are ordered near a contact point.
* `TauCeti.exists_common_isGraphPresentation_le`: two touching hypersurfaces, the first
  in `{ρ ≤ 0}` and the second in `{0 ≤ ρ}`, are graphs of ordered `Cᵏ` heights over a common
  open set, for `k ≠ 0`.
-/

public section

open Function Set Filter
open scoped Topology

namespace TauCeti

variable {E F : Type*}

/-- A graph presentation gives a bijective horizontal projection from `V` onto `D`.
The vertical component of `f` on `V` is the height `u` evaluated at the horizontal component. -/
structure IsGraphPresentation (f : F → WithLp 2 (E × ℝ)) (V : Set F) (D : Set E)
    (u : E → ℝ) : Prop where
  injOn : InjOn (fun x ↦ (WithLp.ofLp (f x)).1) V
  image_eq : (fun x ↦ (WithLp.ofLp (f x)).1) '' V = D
  snd_eq : ∀ x ∈ V, (WithLp.ofLp (f x)).2 = u (WithLp.ofLp (f x)).1

namespace IsGraphPresentation

variable {f : F → WithLp 2 (E × ℝ)} {V : Set F} {D : Set E} {u : E → ℝ}

/-- A graph presentation writes each point of `V` as the graph point of its horizontal
component. -/
theorem eq_toLp (h : IsGraphPresentation f V D u) {x : F} (hx : x ∈ V) :
    f x = WithLp.toLp 2 ((WithLp.ofLp (f x)).1, u (WithLp.ofLp (f x)).1) := by
  rw [← h.snd_eq x hx, Prod.mk.eta, WithLp.toLp_ofLp]

/-- Every graph point over `D` is attained in `V`. -/
theorem exists_eq_toLp (h : IsGraphPresentation f V D u) {y : E} (hy : y ∈ D) :
    ∃ x ∈ V, (WithLp.ofLp (f x)).1 = y ∧ f x = WithLp.toLp 2 (y, u y) := by
  rw [← h.image_eq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl, h.eq_toLp hx⟩

/-- A graph presentation restricts to every subset of its base. -/
theorem restrict (h : IsGraphPresentation f V D u) {D' : Set E} (hD' : D' ⊆ D) :
    IsGraphPresentation f (V ∩ (fun x ↦ (WithLp.ofLp (f x)).1) ⁻¹' D') D' u where
  injOn := h.injOn.mono inter_subset_left
  image_eq := by rw [image_inter_preimage, h.image_eq, inter_eq_right.mpr hD']
  snd_eq x hx := h.snd_eq x hx.1

/-- The horizontal component of a graph presentation maps `V` into `D`. -/
theorem mapsTo (h : IsGraphPresentation f V D u) :
    MapsTo (fun x ↦ (WithLp.ofLp (f x)).1) V D := fun _ hx ↦
  h.image_eq ▸ mem_image_of_mem _ hx

/-- The horizontal component of a graph presentation is a bijection from `V` onto `D`. -/
theorem bijOn (h : IsGraphPresentation f V D u) :
    BijOn (fun x ↦ (WithLp.ofLp (f x)).1) V D :=
  ⟨h.mapsTo, h.injOn, h.image_eq ▸ surjOn_image _ _⟩

/-- A graph presentation maps `V` onto the graph of `u` over `D`. -/
theorem image_eq_graph (h : IsGraphPresentation f V D u) :
    f '' V = (fun y ↦ WithLp.toLp 2 (y, u y)) '' D := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, h.mapsTo hx, (h.eq_toLp hx).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, -, hfx⟩ := h.exists_eq_toLp hy
    exact ⟨x, hx, hfx⟩

/-- The height of a graph presentation is determined on its base. -/
theorem eqOn {u' : E → ℝ} (h : IsGraphPresentation f V D u)
    (h' : IsGraphPresentation f V D u') : EqOn u u' D := by
  intro y hy
  obtain ⟨x, hx, hxy, -⟩ := h.exists_eq_toLp hy
  rw [← hxy, ← h.snd_eq x hx, h'.snd_eq x hx]

/-- A graph presentation restricts to every subset of its parameter domain, over the image of
that subset. -/
theorem mono (h : IsGraphPresentation f V D u) {V' : Set F} (hV' : V' ⊆ V) :
    IsGraphPresentation f V' ((fun x ↦ (WithLp.ofLp (f x)).1) '' V') u where
  injOn := h.injOn.mono hV'
  image_eq := rfl
  snd_eq x hx := h.snd_eq x (hV' hx)

end IsGraphPresentation

/-- The graph map `y ↦ (y, u y)` presents the graph of `u` over any set `D`. -/
@[simp] theorem isGraphPresentation_graph (u : E → ℝ) (D : Set E) :
    IsGraphPresentation (fun y ↦ WithLp.toLp 2 (y, u y)) D D u where
  injOn _ _ _ _ hxy := by simpa using hxy
  image_eq := by simp
  snd_eq _ _ := by simp

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Local graph presentation.** A map `f : F → E × ℝ`, `Cᵏ` for `k ≠ 0` on an open set
`U`, whose horizontal derivative is bijective at `a ∈ U`, maps an open neighbourhood `V ⊆ U` of `a`
bijectively onto the graph of a height `u`, `Cᵏ` on the open image `D` of `V` in `E`. -/
theorem exists_isGraphPresentation [CompleteSpace E] [CompleteSpace F]
    {f : F → WithLp 2 (E × ℝ)} {U : Set F} {a : F} {k : WithTop ℕ∞} (hk : k ≠ 0)
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ k f U)
    (hbij : Bijective fun v ↦ (WithLp.ofLp (fderiv ℝ f a v)).1) :
    ∃ V ⊆ U, IsOpen V ∧ a ∈ V ∧ ∃ D : Set E, IsOpen D ∧ ∃ u : E → ℝ,
      ContDiffOn ℝ k u D ∧ IsGraphPresentation f V D u := by
  let π := WithLp.fstL 2 ℝ E ℝ
  let ν := WithLp.sndL 2 ℝ E ℝ
  let g := π ∘ f
  have hg : ContDiffOn ℝ k g U := π.contDiff.comp_contDiffOn hf
  have hfd {x : F} (hx : x ∈ U) : HasFDerivAt g (π.comp (fderiv ℝ f x)) x :=
    π.hasFDerivAt.comp x ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt hk).hasFDerivAt
  let L₀ : F ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (π.comp (fderiv ℝ f a))
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hL₀ : HasFDerivAt g (L₀ : F →L[ℝ] E) a := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hfd ha
  have hk1 : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.mpr hk
  obtain ⟨φ, hφ, haφ, hφU, hφc⟩ := ContDiffOn.exists_openPartialHomeomorph hg hU ha hk1
    (e := L₀) hL₀.fderiv.symm
  refine ⟨φ.source, hφU, φ.open_source, haφ, φ.target, φ.open_target,
    fun y ↦ ν (f (φ.symm y)), ?_, ⟨?_, ?_, fun x hx ↦ ?_⟩⟩
  · exact (ν.contDiff.comp_contDiffOn hf).comp hφc (φ.mapsTo_symm.mono_right hφU)
  · intro x hx y hy hxy
    apply φ.injOn hx hy
    simpa [hφ, g, π] using hxy
  · simpa [hφ, g, π] using φ.image_source_eq_target
  · have hgx : (f x).fst = φ x := by simp [hφ, g, π]
    simp [hgx, φ.left_inv hx, ν]

/-- **One-sidedness gives ordered heights.** Let `ρ` be strictly differentiable at
`(x₀, t₀)`, with derivative positive on the vertical direction. If the graph of `u₂` lies in
`{0 ≤ ρ}` and the graph of `u₁` in `{ρ ≤ 0}` near `x₀`, both heights being continuous at `x₀`
with value `t₀`, then `u₁ ≤ u₂` near `x₀`. -/
theorem eventually_le_of_hasStrictFDerivAt {ρ : WithLp 2 (E × ℝ) → ℝ}
    {ρ' : WithLp 2 (E × ℝ) →L[ℝ] ℝ} {x₀ : E} {t₀ : ℝ}
    (hρ : HasStrictFDerivAt ρ ρ' (WithLp.toLp 2 (x₀, t₀)))
    (hρv : 0 < ρ' (WithLp.toLp 2 (0, 1))) {u₁ u₂ : E → ℝ}
    (hu₁ : ContinuousAt u₁ x₀) (hu₂ : ContinuousAt u₂ x₀) (hu₁₀ : u₁ x₀ = t₀)
    (hu₂₀ : u₂ x₀ = t₀) (hρ₁ : ∀ᶠ y in 𝓝 x₀, ρ (WithLp.toLp 2 (y, u₁ y)) ≤ 0)
    (hρ₂ : ∀ᶠ y in 𝓝 x₀, 0 ≤ ρ (WithLp.toLp 2 (y, u₂ y))) :
    ∀ᶠ y in 𝓝 x₀, u₁ y ≤ u₂ y := by
  let e : WithLp 2 (E × ℝ) := WithLp.toLp 2 (0, 1)
  have he0 : e ≠ 0 := by
    intro h
    have := congrArg (fun q : WithLp 2 (E × ℝ) ↦ (WithLp.ofLp q).2) h
    simp [e] at this
  have hne : 0 < ‖e‖ := norm_pos_iff.mpr he0
  have hc : 0 < ρ' e / (2 * ‖e‖) := div_pos hρv (mul_pos two_pos hne)
  have hsmall := hρ.isLittleO.def hc
  let G : E → WithLp 2 (E × ℝ) × WithLp 2 (E × ℝ) :=
    fun y ↦ (WithLp.toLp 2 (y, u₁ y), WithLp.toLp 2 (y, u₂ y))
  have hG : ContinuousAt G x₀ := by
    apply ContinuousAt.prodMk
    · exact (WithLp.prod_continuous_toLp 2 E ℝ).continuousAt.comp
        (continuousAt_id.prodMk hu₁)
    · exact (WithLp.prod_continuous_toLp 2 E ℝ).continuousAt.comp
        (continuousAt_id.prodMk hu₂)
  have hG₀ : G x₀ = (WithLp.toLp 2 (x₀, t₀), WithLp.toLp 2 (x₀, t₀)) := by
    simp [G, hu₁₀, hu₂₀]
  have hnear := hG.eventually (hG₀ ▸ hsmall)
  filter_upwards [hnear, hρ₁, hρ₂] with y hy hy₁ hy₂
  by_contra hlt
  replace hlt := not_le.mp hlt
  let d := u₁ y - u₂ y
  have hdpos : 0 < d := sub_pos.mpr hlt
  have hdiff : WithLp.toLp 2 (y, u₁ y) - WithLp.toLp 2 (y, u₂ y) = d • e := by
    apply WithLp.ofLp_injective
    ext <;> simp [e, d]
  simp only [G, hdiff, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hdpos] at hy
  have hle := (neg_le_abs _).trans hy
  have hcalc : ρ' e / (2 * ‖e‖) * (d * ‖e‖) = d * ρ' e / 2 := by
    field_simp
  linarith [mul_pos hdpos hρv]

/-- **Common graph presentation of two touching hypersurfaces.** Let `f₁` and `f₂` be maps into
`E × ℝ`, `Cᵏ` for `k ≠ 0` on open sets `U₁` and `U₂`, with bijective horizontal derivatives
at `a₁ ∈ U₁` and `a₂ ∈ U₂`, and `f₁ a₁ = f₂ a₂ = p`. Assume that `f₂` takes values in `{0 ≤ ρ}`
for a function `ρ` strictly differentiable at `p` with derivative positive on the vertical
direction, and that `f₁` takes values in `{ρ ≤ 0}`. Then there are an open set `D` containing
the base point of `p` and open neighbourhoods `Vᵢ ⊆ Uᵢ` of `aᵢ` such that `fᵢ` maps `Vᵢ` bijectively
onto the graph of a `Cᵏ` height `uᵢ` over `D`, and `u₁ ≤ u₂` on `D`. -/
theorem exists_common_isGraphPresentation_le [CompleteSpace E] [CompleteSpace F]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [CompleteSpace F₂]
    {f₁ : F → WithLp 2 (E × ℝ)} {f₂ : F₂ → WithLp 2 (E × ℝ)} {U₁ : Set F} {U₂ : Set F₂}
    {a₁ : F} {a₂ : F₂}
    {k : WithTop ℕ∞} (hk : k ≠ 0) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (ha₁ : a₁ ∈ U₁)
    (ha₂ : a₂ ∈ U₂) (hf₁ : ContDiffOn ℝ k f₁ U₁) (hf₂ : ContDiffOn ℝ k f₂ U₂)
    (hbij₁ : Bijective fun v ↦ (WithLp.ofLp (fderiv ℝ f₁ a₁ v)).1)
    (hbij₂ : Bijective fun v ↦ (WithLp.ofLp (fderiv ℝ f₂ a₂ v)).1) (hp : f₁ a₁ = f₂ a₂)
    {ρ : WithLp 2 (E × ℝ) → ℝ} {ρ' : WithLp 2 (E × ℝ) →L[ℝ] ℝ}
    (hρ : HasStrictFDerivAt ρ ρ' (f₁ a₁)) (hρv : 0 < ρ' (WithLp.toLp 2 (0, 1)))
    (hρ₁ : ∀ x ∈ U₁, ρ (f₁ x) ≤ 0) (hρ₂ : ∀ x ∈ U₂, 0 ≤ ρ (f₂ x)) :
    ∃ D : Set E, IsOpen D ∧ (WithLp.ofLp (f₁ a₁)).1 ∈ D ∧
      ∃ V₁ ⊆ U₁, IsOpen V₁ ∧ a₁ ∈ V₁ ∧ ∃ V₂ ⊆ U₂, IsOpen V₂ ∧ a₂ ∈ V₂ ∧
      ∃ u₁ u₂ : E → ℝ, ContDiffOn ℝ k u₁ D ∧ ContDiffOn ℝ k u₂ D ∧
        IsGraphPresentation f₁ V₁ D u₁ ∧ IsGraphPresentation f₂ V₂ D u₂ ∧
        ∀ y ∈ D, u₁ y ≤ u₂ y := by
  obtain ⟨V₁, hV₁U, hV₁, haV₁, D₁, hD₁, u₁, hu₁, hG₁⟩ :=
    exists_isGraphPresentation hk hU₁ ha₁ hf₁ hbij₁
  obtain ⟨V₂, hV₂U, hV₂, haV₂, D₂, hD₂, u₂, hu₂, hG₂⟩ :=
    exists_isGraphPresentation hk hU₂ ha₂ hf₂ hbij₂
  set x₀ : E := (WithLp.ofLp (f₁ a₁)).1 with hx₀
  set t₀ : ℝ := (WithLp.ofLp (f₁ a₁)).2 with ht₀
  have hx₀₂ : (WithLp.ofLp (f₂ a₂)).1 = x₀ := by rw [hx₀, hp]
  have hx₀D₁ : x₀ ∈ D₁ := hG₁.mapsTo haV₁
  have hx₀D₂ : x₀ ∈ D₂ := hx₀₂ ▸ hG₂.mapsTo haV₂
  have hu₁₀ : u₁ x₀ = t₀ := (hG₁.snd_eq a₁ haV₁).symm
  have hu₂₀ : u₂ x₀ = t₀ := by
    rw [← hx₀₂, ← hG₂.snd_eq a₂ haV₂, ht₀, hp]
  have hD : IsOpen (D₁ ∩ D₂) := hD₁.inter hD₂
  have hx₀D : x₀ ∈ D₁ ∩ D₂ := ⟨hx₀D₁, hx₀D₂⟩
  have hρ₁' : ∀ y ∈ D₁, ρ (WithLp.toLp 2 (y, u₁ y)) ≤ 0 := by
    intro y hy
    obtain ⟨x, hx, -, hfx⟩ := hG₁.exists_eq_toLp hy
    exact hfx ▸ hρ₁ x (hV₁U hx)
  have hρ₂' : ∀ y ∈ D₂, 0 ≤ ρ (WithLp.toLp 2 (y, u₂ y)) := by
    intro y hy
    obtain ⟨x, hx, -, hfx⟩ := hG₂.exists_eq_toLp hy
    exact hfx ▸ hρ₂ x (hV₂U hx)
  have hρp : HasStrictFDerivAt ρ ρ' (WithLp.toLp 2 (x₀, t₀)) := by
    rwa [hx₀, ht₀, Prod.mk.eta, WithLp.toLp_ofLp]
  have hle := eventually_le_of_hasStrictFDerivAt hρp hρv
    ((hu₁.continuousOn.continuousAt (hD₁.mem_nhds hx₀D₁)))
    ((hu₂.continuousOn.continuousAt (hD₂.mem_nhds hx₀D₂))) hu₁₀ hu₂₀
    (eventually_of_mem (hD₁.mem_nhds hx₀D₁) hρ₁') (eventually_of_mem (hD₂.mem_nhds hx₀D₂) hρ₂')
  obtain ⟨O, hOle, hO, hx₀O⟩ := eventually_nhds_iff.mp hle
  let D := (D₁ ∩ D₂) ∩ O
  have hDo : IsOpen D := hD.inter hO
  have hcont₁ : ContinuousOn (fun x ↦ (WithLp.ofLp (f₁ x)).1) V₁ :=
    (WithLp.fstL 2 ℝ E ℝ).continuous.comp_continuousOn (hf₁.continuousOn.mono hV₁U)
  have hcont₂ : ContinuousOn (fun x ↦ (WithLp.ofLp (f₂ x)).1) V₂ :=
    (WithLp.fstL 2 ℝ E ℝ).continuous.comp_continuousOn (hf₂.continuousOn.mono hV₂U)
  refine ⟨D, hDo, ⟨hx₀D, hx₀O⟩,
    V₁ ∩ (fun x ↦ (WithLp.ofLp (f₁ x)).1) ⁻¹' D, fun x hx ↦ hV₁U hx.1,
    hcont₁.isOpen_inter_preimage hV₁ hDo, ⟨haV₁, hx₀D, hx₀O⟩,
    V₂ ∩ (fun x ↦ (WithLp.ofLp (f₂ x)).1) ⁻¹' D, fun x hx ↦ hV₂U hx.1,
    hcont₂.isOpen_inter_preimage hV₂ hDo, ⟨haV₂, by rw [mem_preimage, hx₀₂]; exact ⟨hx₀D, hx₀O⟩⟩,
    u₁, u₂, hu₁.mono fun y hy ↦ hy.1.1, hu₂.mono fun y hy ↦ hy.1.2,
    hG₁.restrict fun y hy ↦ hy.1.1, hG₂.restrict fun y hy ↦ hy.1.2,
    fun y hy ↦ hOle y hy.2⟩

end TauCeti
