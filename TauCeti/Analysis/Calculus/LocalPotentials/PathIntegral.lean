/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.Homotopy.Path

/-!
# Integrating one-forms with local potentials along continuous paths

A covector field `φ` with local potentials (`TauCeti.HasLocalPotentials`) can be integrated along
a merely continuous path, with no derivative of the path: near each time, the increments of the
integral are the increments of a local potential evaluated along the path. No subdivision of the
path enters the definition, so the integral is independent of the chosen discs, potentials and
subdivisions by construction; subdivisions only appear in the proof that primitives along paths
exist.

We formalize this through primitives along maps. For `f : X → E`, a function `G : X → F` is a
primitive of `φ` along `f` (`TauCeti.IsPrimitiveAlong φ f G`) if near every `x`, the increments
of `G` are the increments of `g ∘ f` for some potential `g` of `φ` near `f x`.

## Main definitions and results

* `TauCeti.IsPrimitiveAlong φ f G`: `G` is a primitive of `φ` along `f`.
* `TauCeti.IsPrimitiveAlong.isLocallyConstant_sub`: two primitives along a continuous map differ
  by a locally constant function, so by a constant on a preconnected domain
  (`TauCeti.IsPrimitiveAlong.sub_eq_sub`).
* `TauCeti.HasLocalPotentials.exists_isPrimitiveAlong`: a field with local potentials on `s`
  has a primitive along every continuous map `[0, 1] → s`.
* `TauCeti.potentialIntegral φ γ`: the integral of `φ` along a path `γ`, the difference of the
  endpoint values of a primitive along `γ` (and `0` if there is none).
* `TauCeti.potentialIntegral_eq_sub_of_hasFDerivAt`: a global potential `g` gives the
  integral `g b - g a`; in particular a constant covector `L` integrates to `L (b - a)`.
* `TauCeti.potentialIntegral_refl`, `TauCeti.potentialIntegral_symm`,
  `TauCeti.potentialIntegral_trans`, `TauCeti.potentialIntegral_reparam`: the integral vanishes
  on constant paths, changes sign under reversal, is additive under concatenation and invariant
  under reparametrization.

## References

* Serge Lang, *Complex Analysis*, 4th ed., Graduate Texts in Mathematics 103, Springer, 1999,
  Chapter III, §4, primitives along continuous curves and the integral they define.
-/

public section

open Set Filter Metric unitInterval
open scoped Topology

namespace TauCeti

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X] [TopologicalSpace Y]
  {φ : E → E →L[ℝ] F} {f : X → E} {G G₁ G₂ : X → F} {s : Set E}

/-- A function `G : X → F` is a primitive of the covector field `φ` along `f : X → E` if near
every point `x`, the increments of `G` are the increments along `f` of a potential of `φ`
defined near `f x`. -/
def IsPrimitiveAlong (φ : E → E →L[ℝ] F) (f : X → E) (G : X → F) : Prop :=
  ∀ x, ∃ g : E → F, (∀ᶠ y in 𝓝 (f x), HasFDerivAt g (φ y) y) ∧
    ∀ᶠ x' in 𝓝 x, G x' - G x = g (f x') - g (f x)

/-- The local criterion for primitives along a map. -/
theorem isPrimitiveAlong_iff : IsPrimitiveAlong φ f G ↔
    ∀ x, ∃ g : E → F, (∀ᶠ y in 𝓝 (f x), HasFDerivAt g (φ y) y) ∧
      ∀ᶠ x' in 𝓝 x, G x' - G x = g (f x') - g (f x) := Iff.rfl

/-- Two potentials of the same field near `z` have the same increments near `z`. -/
private theorem eventually_sub_eq_sub_of_hasFDerivAt {g₁ g₂ : E → F} {z : E}
    (h₁ : ∀ᶠ y in 𝓝 z, HasFDerivAt g₁ (φ y) y) (h₂ : ∀ᶠ y in 𝓝 z, HasFDerivAt g₂ (φ y) y) :
    ∀ᶠ y in 𝓝 z, g₁ y - g₁ z = g₂ y - g₂ z := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h₁.and h₂)
  have hd : ∀ w ∈ ball z r, HasFDerivAt (g₁ - g₂) 0 w := fun w hw ↦ by
    simpa using (hball w hw).1.sub (hball w hw).2
  filter_upwards [ball_mem_nhds z hr] with y hy
  have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z r).isPreconnected
    (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w hw).fderiv) hy (mem_ball_self hr)
  rw [Pi.sub_apply, Pi.sub_apply] at this
  rw [sub_eq_sub_iff_sub_eq_sub, this]

/-- A potential of `φ` on an open set containing the image of `f` gives the primitive `g ∘ f`
along `f`. -/
theorem isPrimitiveAlong_comp_of_hasFDerivAt {U : Set E} {g : E → F} (hU : IsOpen U)
    (hg : ∀ y ∈ U, HasFDerivAt g (φ y) y) (hf : ∀ x, f x ∈ U) :
    IsPrimitiveAlong φ f (g ∘ f) :=
  fun x ↦ ⟨g, eventually_of_mem (hU.mem_nhds (hf x)) hg, .of_forall fun _ ↦ rfl⟩

/-- Adding a constant to a primitive gives a primitive. -/
theorem IsPrimitiveAlong.add_const (hG : IsPrimitiveAlong φ f G) (c : F) :
    IsPrimitiveAlong φ f (fun x ↦ G x + c) := by
  intro x
  obtain ⟨g, hg, hGx⟩ := hG x
  exact ⟨g, hg, hGx.mono fun x' hx' ↦ by rw [add_sub_add_right_eq_sub, hx']⟩

/-- A primitive along `f` restricts to a primitive along `f ∘ h` for a continuous `h`. -/
theorem IsPrimitiveAlong.comp (hG : IsPrimitiveAlong φ f G) {h : Y → X} (hh : Continuous h) :
    IsPrimitiveAlong φ (f ∘ h) (G ∘ h) := by
  intro y
  obtain ⟨g, hg, hGx⟩ := hG (h y)
  exact ⟨g, hg, hh.continuousAt.eventually hGx⟩

/-- A primitive along a continuous map is continuous. -/
theorem IsPrimitiveAlong.continuous (hG : IsPrimitiveAlong φ f G) (hf : Continuous f) :
    Continuous G := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨g, hg, hGx⟩ := hG x
  have hgf : ContinuousAt (g ∘ f) x :=
    hg.self_of_nhds.continuousAt.comp hf.continuousAt
  have hc : ContinuousAt (fun x' ↦ G x + (g (f x') - g (f x))) x :=
    continuousAt_const.add (hgf.sub continuousAt_const)
  exact hc.congr_of_eventuallyEq (hGx.mono fun x' hx' ↦ eq_add_of_sub_eq' hx')

/-- Two primitives along a continuous map differ by a locally constant function. -/
theorem IsPrimitiveAlong.isLocallyConstant_sub (hf : Continuous f)
    (h₁ : IsPrimitiveAlong φ f G₁) (h₂ : IsPrimitiveAlong φ f G₂) :
    IsLocallyConstant (G₁ - G₂) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_
  obtain ⟨g₁, hg₁, hG₁⟩ := h₁ x
  obtain ⟨g₂, hg₂, hG₂⟩ := h₂ x
  filter_upwards [hG₁, hG₂, hf.continuousAt.eventually
    (eventually_sub_eq_sub_of_hasFDerivAt hg₁ hg₂)] with x' hx₁ hx₂ hx
  rw [Pi.sub_apply, Pi.sub_apply, sub_eq_sub_iff_sub_eq_sub, hx₁, hx₂, hx]

/-- On a preconnected domain, two primitives along a continuous map have the same increments. -/
theorem IsPrimitiveAlong.sub_eq_sub [PreconnectedSpace X] (hf : Continuous f)
    (h₁ : IsPrimitiveAlong φ f G₁) (h₂ : IsPrimitiveAlong φ f G₂) (x y : X) :
    G₁ x - G₁ y = G₂ x - G₂ y := by
  have := (h₁.isLocallyConstant_sub hf h₂).apply_eq_of_preconnectedSpace x y
  rw [Pi.sub_apply, Pi.sub_apply] at this
  rw [sub_eq_sub_iff_sub_eq_sub, this]

/-! ### Existence of primitives along paths -/

section Existence

/-- The defining condition of `IsPrimitiveAlong` at a single point. -/
private def IsPrimitiveAlongAt (φ : E → E →L[ℝ] F) (f : X → E) (G : X → F) (x : X) : Prop :=
  ∃ g : E → F, (∀ᶠ y in 𝓝 (f x), HasFDerivAt g (φ y) y) ∧
    ∀ᶠ x' in 𝓝 x, G x' - G x = g (f x') - g (f x)

private theorem isPrimitiveAlong_iff_forall_isPrimitiveAlongAt :
    IsPrimitiveAlong φ f G ↔ ∀ x, IsPrimitiveAlongAt φ f G x := Iff.rfl

/-- The pointwise condition only sees the increments of `G` near the point. -/
private theorem IsPrimitiveAlongAt.congr {G' : X → F} {x : X}
    (hG : IsPrimitiveAlongAt φ f G x) (h : ∀ᶠ x' in 𝓝 x, G' x' - G' x = G x' - G x) :
    IsPrimitiveAlongAt φ f G' x := by
  obtain ⟨g, hg, hGx⟩ := hG
  exact ⟨g, hg, (h.and hGx).mono fun _ hx' ↦ hx'.1.trans hx'.2⟩

/-- Glue a primitive on `{t ≤ c}` and a primitive on a set `W ∋ c` at the point `c`. -/
private theorem exists_isPrimitiveAlongAt_of_le_or_mem {f : I → E} (hf : Continuous f)
    {G₁ G₂ : I → F} {c : I} {W : Set I} (h₁ : ∀ t ≤ c, IsPrimitiveAlongAt φ f G₁ t)
    (h₂ : ∀ t ∈ W, IsPrimitiveAlongAt φ f G₂ t) (hc : c ∈ W) :
    ∃ G : I → F, ∀ t, t ≤ c ∨ t ∈ W → IsPrimitiveAlongAt φ f G t := by
  refine ⟨fun u ↦ if u ≤ c then G₁ u else G₂ u + (G₁ c - G₂ c), fun t ht ↦ ?_⟩
  rcases lt_trichotomy t c with htc | rfl | htc
  · refine (h₁ t htc.le).congr ?_
    filter_upwards [Iio_mem_nhds htc] with u (hu : u < c)
    simp only [hu.le, htc.le, ↓reduceIte]
  · obtain ⟨g₁, hg₁, hG₁⟩ := h₁ t le_rfl
    obtain ⟨g₂, hg₂, hG₂⟩ := h₂ t hc
    refine ⟨g₁, hg₁, ?_⟩
    filter_upwards [hG₁, hG₂, hf.continuousAt.eventually
      (eventually_sub_eq_sub_of_hasFDerivAt hg₁ hg₂)] with u hu₁ hu₂ hu
    by_cases hut : u ≤ t
    · simpa only [hut, le_refl, ↓reduceIte] using hu₁
    · simp only [hut, le_refl, ↓reduceIte]
      rw [hu, ← hu₂]
      abel
  · refine (h₂ t (ht.resolve_left htc.not_ge)).congr ?_
    filter_upwards [Ioi_mem_nhds htc] with u (hu : c < u)
    simp only [hu.not_ge, htc.not_ge, ↓reduceIte]
    abel

/-- A field with local potentials on `s` has a primitive along every continuous map from the
unit interval into `s`. -/
theorem HasLocalPotentials.exists_isPrimitiveAlong (hφ : HasLocalPotentials s φ) {f : I → E}
    (hf : Continuous f) (hfs : ∀ t, f t ∈ s) : ∃ G : I → F, IsPrimitiveAlong φ f G := by
  -- Near each time, a potential at the image point composed with `f` is a primitive.
  have hloc : ∀ c : I, ∃ V ∈ 𝓝 c, ∃ G : I → F, ∀ t ∈ V, IsPrimitiveAlongAt φ f G t := by
    intro c
    obtain ⟨r, hr, -, g, -, hg⟩ := hasLocalPotentials_iff.mp hφ (f c) (hfs c)
    exact ⟨f ⁻¹' ball (f c) r, hf.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr), g ∘ f,
      fun t ht ↦ ⟨g, eventually_of_mem (isOpen_ball.mem_nhds ht) hg, .of_forall fun _ ↦ rfl⟩⟩
  -- The times up to which a primitive exists form a clopen set.
  let S : Set I := {c | ∃ G : I → F, ∀ t ≤ c, IsPrimitiveAlongAt φ f G t}
  have hkey : ∀ c : I, ∃ J ∈ 𝓝 c, ∀ c' ∈ J, c' ∈ S → J ⊆ S := by
    intro c
    obtain ⟨V, hV, G₂, hG₂⟩ := hloc c
    obtain ⟨b, d, -, hJ, hJV⟩ := exists_Icc_mem_subset_of_mem_nhds hV
    refine ⟨Icc b d, hJ, fun c' hc' ⟨G₁, hG₁⟩ e he ↦ ?_⟩
    obtain ⟨G, hG⟩ := exists_isPrimitiveAlongAt_of_le_or_mem hf hG₁ hG₂ (hJV hc')
    refine ⟨G, fun t hte ↦ hG t ?_⟩
    rcases le_or_gt t c' with htc | htc
    · exact .inl htc
    · exact .inr (hJV ⟨hc'.1.trans htc.le, hte.trans he.2⟩)
  have hopen : IsOpen S := isOpen_iff_mem_nhds.mpr fun c hc ↦ by
    obtain ⟨J, hJ, hJS⟩ := hkey c
    exact mem_of_superset hJ (hJS c (mem_of_mem_nhds hJ) hc)
  have hclosed : IsClosed S := isClosed_of_closure_subset fun c hc ↦ by
    obtain ⟨J, hJ, hJS⟩ := hkey c
    obtain ⟨c', hc'J, hc'S⟩ := mem_closure_iff_nhds.mp hc J hJ
    exact hJS c' hc'J hc'S (mem_of_mem_nhds hJ)
  have hzero : (0 : I) ∈ S := by
    obtain ⟨V, hV, G, hG⟩ := hloc 0
    exact ⟨G, fun t ht ↦ le_antisymm ht nonneg' ▸ hG 0 (mem_of_mem_nhds hV)⟩
  obtain ⟨G, hG⟩ : (1 : I) ∈ S := by
    rw [IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, hzero⟩]
    exact mem_univ _
  exact ⟨G, isPrimitiveAlong_iff_forall_isPrimitiveAlongAt.mpr fun t ↦ hG t le_one'⟩

end Existence

/-! ### The integral along a path -/

variable {a b c : E} {γ : Path a b}

open scoped Classical in
/-- The integral of a covector field `φ` along a continuous path `γ`: the difference of the
endpoint values of a primitive of `φ` along `γ`. It is `0` when there is no such primitive;
for fields with local potentials on a set containing the path, primitives exist by
`TauCeti.HasLocalPotentials.exists_isPrimitiveAlong`. -/
noncomputable def potentialIntegral (φ : E → E →L[ℝ] F) (γ : Path a b) : F :=
  if h : ∃ G : I → F, IsPrimitiveAlong φ γ G then h.choose 1 - h.choose 0 else 0

/-- The integral is computed by any primitive along the path. -/
theorem IsPrimitiveAlong.potentialIntegral_eq {G : I → F} (hG : IsPrimitiveAlong φ γ G) :
    potentialIntegral φ γ = G 1 - G 0 := by
  have h : ∃ G : I → F, IsPrimitiveAlong φ γ G := ⟨G, hG⟩
  rw [potentialIntegral, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.sub_eq_sub γ.continuous hG 1 0

/-- The integral is `0` when there is no primitive along the path. -/
theorem potentialIntegral_of_not_exists (h : ¬∃ G : I → F, IsPrimitiveAlong φ γ G) :
    potentialIntegral φ γ = 0 := by
  rw [potentialIntegral, dite_eq_right_of_eq_false (eq_false h)]

/-- A potential `g` of `φ` on an open set containing the path gives the integral
`g b - g a`. -/
theorem potentialIntegral_eq_sub_of_hasFDerivAt {U : Set E} {g : E → F} (hU : IsOpen U)
    (hg : ∀ y ∈ U, HasFDerivAt g (φ y) y) (hγ : ∀ t, γ t ∈ U) :
    potentialIntegral φ γ = g b - g a := by
  rw [(isPrimitiveAlong_comp_of_hasFDerivAt hU hg hγ).potentialIntegral_eq]
  simp

/-- A constant covector field integrates to its value on the displacement. -/
@[simp]
theorem potentialIntegral_const (L : E →L[ℝ] F) (γ : Path a b) :
    potentialIntegral (fun _ ↦ L) γ = L (b - a) := by
  rw [potentialIntegral_eq_sub_of_hasFDerivAt isOpen_univ (fun y _ ↦ L.hasFDerivAt)
    (fun _ ↦ mem_univ _), map_sub]

/-- The integral along a constant path vanishes. -/
@[simp]
theorem potentialIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    potentialIntegral φ (.refl a) = 0 := by
  by_cases h : ∃ G : I → F, IsPrimitiveAlong φ (Path.refl a) G
  · obtain ⟨G, hG⟩ := h
    rw [hG.potentialIntegral_eq, sub_eq_zero]
    -- A primitive along a constant path is locally constant.
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace
      ((IsLocallyConstant.iff_eventually_eq G).mpr fun t ↦ ?_) 1 0
    obtain ⟨g, -, hGt⟩ := hG t
    exact hGt.mono fun u hu ↦ sub_eq_zero.mp (by simpa using hu)
  · exact potentialIntegral_of_not_exists h

/-- The integral of `φ` along the reversed path is the negative of the integral. -/
@[simp]
theorem potentialIntegral_symm (φ : E → E →L[ℝ] F) (γ : Path a b) :
    potentialIntegral φ γ.symm = -potentialIntegral φ γ := by
  by_cases h : ∃ G : I → F, IsPrimitiveAlong φ γ G
  · obtain ⟨G, hG⟩ := h
    rw [(hG.comp continuous_symm).potentialIntegral_eq, hG.potentialIntegral_eq]
    simp
  · have h' : ¬∃ G : I → F, IsPrimitiveAlong φ γ.symm G := fun ⟨G, hG⟩ ↦
      h ⟨G ∘ σ, by simpa [Function.comp_def] using hG.comp continuous_symm⟩
    rw [potentialIntegral_of_not_exists h, potentialIntegral_of_not_exists h', neg_zero]

/-- The integral does not see a change of the endpoints' names. -/
@[simp]
theorem potentialIntegral_cast (φ : E → E →L[ℝ] F) (γ : Path a b) {a' b' : E} (ha : a' = a)
    (hb : b' = b) : potentialIntegral φ (γ.cast ha hb) = potentialIntegral φ γ := by
  by_cases h : ∃ G : I → F, IsPrimitiveAlong φ γ G
  · obtain ⟨G, hG⟩ := h
    rw [hG.potentialIntegral_eq,
      IsPrimitiveAlong.potentialIntegral_eq (γ := γ.cast ha hb) (by rwa [Path.cast_coe])]
  · rw [potentialIntegral_of_not_exists h,
      potentialIntegral_of_not_exists (γ := γ.cast ha hb) (by rwa [Path.cast_coe])]

/-- For a field with local potentials on a set containing the path, the integral is invariant
under reparametrization. -/
theorem potentialIntegral_reparam (hφ : HasLocalPotentials s φ) (hγ : ∀ t, γ t ∈ s)
    {h : I → I} (hh : Continuous h) (h₀ : h 0 = 0) (h₁ : h 1 = 1) :
    potentialIntegral φ (γ.reparam h hh h₀ h₁) = potentialIntegral φ γ := by
  obtain ⟨G, hG⟩ := hφ.exists_isPrimitiveAlong γ.continuous hγ
  rw [(hG.comp hh).potentialIntegral_eq, hG.potentialIntegral_eq, Function.comp_apply,
    Function.comp_apply, h₀, h₁]

/-- For a field with local potentials on a set containing two paths, the integral along their
concatenation is the sum of the integrals. -/
theorem potentialIntegral_trans (hφ : HasLocalPotentials s φ) {δ : Path b c}
    (hγ : ∀ t, γ t ∈ s) (hδ : ∀ t, δ t ∈ s) :
    potentialIntegral φ (γ.trans δ) = potentialIntegral φ γ + potentialIntegral φ δ := by
  have hγδ : ∀ t, (γ.trans δ) t ∈ s := fun t ↦ by
    rcases Path.trans_range γ δ ▸ mem_range_self (f := γ.trans δ) t with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact hu ▸ hγ u
    · exact hu ▸ hδ u
  obtain ⟨G, hG⟩ := hφ.exists_isPrimitiveAlong (γ.trans δ).continuous hγδ
  -- Restrict the primitive to the two halves of the unit interval.
  let h₁ : I → I := fun t ↦ ⟨t / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  let h₂ : I → I := fun t ↦ ⟨(1 + t) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hG₁ : IsPrimitiveAlong φ γ (G ∘ h₁) := by
    have e : (γ.trans δ) ∘ h₁ = γ :=
      funext fun t ↦ Path.trans_apply_of_eq_two_mul γ δ t (by simp [h₁]; ring)
    simpa only [e] using hG.comp (by fun_prop : Continuous h₁)
  have hG₂ : IsPrimitiveAlong φ δ (G ∘ h₂) := by
    have e : (γ.trans δ) ∘ h₂ = δ :=
      funext fun t ↦ Path.trans_apply_of_eq_two_mul_sub_one γ δ t (by simp [h₂]; ring)
    simpa only [e] using hG.comp (by fun_prop : Continuous h₂)
  have e₀ : h₁ 0 = 0 := by ext; simp [h₁]
  have e₁ : h₁ 1 = h₂ 0 := by ext; simp [h₁, h₂]
  have e₂ : h₂ 1 = 1 := by ext; simp [h₂]
  rw [hG.potentialIntegral_eq, hG₁.potentialIntegral_eq, hG₂.potentialIntegral_eq,
    Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply, e₀, e₁,
    e₂, sub_add_sub_cancel']

end TauCeti
