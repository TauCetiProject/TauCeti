/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import TauCeti.Analysis.Complex.UpperHalfPlane.StripDoubleCover
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Topology.Separation.InvFunOn

/-!
# Holomorphic double covers of the strip by a Jordan rectangle

Let `Ω` be a bounded domain of `ℂ` whose frontier is a Jordan curve, with four distinct frontier
points `x₁`, `y₁`, `x₂`, `y₂` in cyclic order: `x₁` and `x₂` separate `y₁` from `y₂` on the
frontier. They cut the frontier into four arcs, and `Ω` is a *rectangle* with corners `x₁`, `y₁`,
`x₂`, `y₂`. This file shows that there is a holomorphic map `u` of `Ω` into the strip
`0 < z.im < 1` which is a branched double cover with one branch point, extends continuously to
`closure Ω` away from the corners, maps the four arcs to the two boundary lines of the strip, and
whose real part tends to `-∞` at `x₁` and `x₂` and to `+∞` at `y₁` and `y₂`. Any two holomorphic
maps of `Ω` into the strip that are continuous up to the boundary away from finitely many points
and send each boundary point to the same boundary line differ by a real translation.

These are the holomorphic strips of Heegaard Floer homology whose domain is an embedded
rectangle, in the cylindrical formulation: a holomorphic disc in `Sym²(Σ)` from the generator
`{x₁, x₂}` to `{y₁, y₂}` whose domain is the rectangle corresponds to the inclusion of `Ω` into
`Σ` together with the double cover `u` of the strip, the two preimages of a point `ζ` being the
two points of the disc at `ζ`. In the bigon case the corresponding map is the inverse of a
biholomorphic strip parametrization of `Ω`
(`TauCeti.exists_continuousOn_bijOn_strip_of_isJordanCurve_frontier`); here it has degree two.

## Main results

* `TauCeti.exists_mapsTo_strip_ncard_inter_preimage_of_isJordanCurve_frontier`: **existence**.
  There is a map `u`, holomorphic on `Ω` and continuous on `closure Ω` away from the corners, which
  maps `Ω` into the open strip and the frontier away from the corners into the two boundary lines,
  whose real part tends to `-∞` at `x₁` and `x₂` and to `+∞` at `y₁` and `y₂`, and for which there
  is a point `b ∈ Ω` such that every point of the strip other than `u b` has exactly two
  preimages in `Ω` and `u b` has exactly one.
* `TauCeti.exists_eqOn_add_of_mapsTo_strip`: **uniqueness up to translation**. Two holomorphic maps
  of a bounded domain into the strip, continuous on the closure away from a finite set, whose
  imaginary parts agree on the frontier away from that set, differ by a real translation on the
  closure away from that set.

The map is obtained from Carathéodory's theorem on the closed upper half-plane,
`TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier`, with `∞` sent to
`y₂`: if `a₁`, `c` and `a₂` are the real prevertices of `x₁`, `y₁` and `x₂`, the separation
hypothesis says that `c` lies between `a₁` and `a₂`, and `u` is the inverse of the Carathéodory
map followed by the upper half-plane model `w ↦ log ((w - a₁) * (w - a₂) / (w - c)) / π` of
`TauCeti.ncard_inter_preimage_log_sub_mul_sub_div_sub_div_pi`. Uniqueness is the maximum principle
with finitely many exceptional boundary points,
`Complex.exists_eqOn_add_ofReal_of_forall_mem_frontier_im_eq`, applied to the bounded imaginary
parts.

The uniqueness statement assumes that the two maps send each boundary point to the same boundary
line. Two maps with the same corners at the two ends always do, by an orientation argument which is
not formalized here; for the same reason the existence statement does not say which arcs go to
which line.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), 1027--1158.
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. 10 (2006),
  955--1097.
* L. Ahlfors, *Complex Analysis*, Ch. 6.
-/

public section

open Bornology Complex Filter Function Set Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Real

namespace TauCeti

/-! ### Uniqueness up to translation -/

/-- **Strip maps with the same boundary lines are unique up to translation.** Let `Ω` be a bounded,
preconnected open set and `F` a finite set, and let `u` and `v` be holomorphic maps of `Ω` into the
strip `0 < z.im < 1`, continuous on `closure Ω` away from `F`. If `u` and `v` send each point of
`frontier Ω \ F` to the same boundary line of the strip, that is `(u z).im = (v z).im` there, then
`u` and `v` differ by a real translation on `closure Ω \ F`. -/
theorem exists_eqOn_add_of_mapsTo_strip {Ω F : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hΩb : IsBounded Ω) (hF : F.Finite) {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u Ω)
    (hv : DifferentiableOn ℂ v Ω) (huc : ContinuousOn u (closure Ω \ F))
    (hvc : ContinuousOn v (closure Ω \ F)) (huΩ : MapsTo u Ω {z | z.im ∈ Ioo 0 1})
    (hvΩ : MapsTo v Ω {z | z.im ∈ Ioo 0 1})
    (him : ∀ z ∈ frontier Ω \ F, (u z).im = (v z).im) :
    ∃ c : ℝ, EqOn u (fun z => v z + c) (closure Ω \ F) := by
  refine Complex.exists_eqOn_add_ofReal_of_forall_mem_frontier_im_eq hΩo hΩc hΩb hF hu hv huc hvc
    (Metric.isBounded_Ioo (-1 : ℝ) 1 |>.subset ?_) him
  rintro _ ⟨z, hz, rfl⟩
  have h₁ := huΩ hz
  have h₂ := hvΩ hz
  simp only [mem_ofPred_eq, mem_Ioo] at h₁ h₂
  exact ⟨by linarith, by linarith⟩

/-! ### Existence -/

/-- **The separation hypothesis interlaces the prevertices.** Let `f` be continuous and injective
on the closed upper half-plane, mapping the real line into a set `T` and tending to `y₂` at
infinity. If `f a₁ = x₁`, `f a₂ = x₂` and `f c = y₁` for real `a₁`, `a₂`, `c` with `c ≠ a₁, a₂`, and
`x₁` and `x₂` separate `y₁` from `y₂ ∈ T` in `T`, then `c` lies strictly between `a₁` and `a₂`:
otherwise the image of a real half-line, together with its limit `y₂`, would join `y₁` to `y₂` in
`T \ {x₁, x₂}`. -/
private theorem mul_pos_of_notMem_connectedComponentIn {T : Set ℂ} {f : ℂ → ℂ}
    {x₁ x₂ y₁ y₂ : ℂ} {a₁ a₂ c : ℝ} (hfc : ContinuousOn f {z | 0 ≤ z.im})
    (hinj : InjOn f {z | 0 ≤ z.im}) (hfT : ∀ t : ℝ, f t ∈ T)
    (hfy : Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 y₂)) (hy₂ : y₂ ∈ T \ {x₁, x₂})
    (hfa₁ : f a₁ = x₁) (hfa₂ : f a₂ = x₂) (hfc₁ : f c = y₁) (ha₁c : a₁ ≠ c) (ha₂c : a₂ ≠ c)
    (hsep : y₂ ∉ connectedComponentIn (T \ {x₁, x₂}) y₁) : 0 < (c - a₁) * (a₂ - c) := by
  have hreal (t : ℝ) : (t : ℂ) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  set fr : ℝ → ℂ := fun t => f t
  have hfrc : Continuous fr := hfc.comp_continuous continuous_ofReal hreal
  -- a preconnected set of reals containing `c` but not `a₁`, `a₂`, with `y₂` as a limit point
  have hsepI (I : Set ℝ) (hI : IsPreconnected I) (hcI : c ∈ I) (h₁ : a₁ ∉ I) (h₂ : a₂ ∉ I)
      (hcl : y₂ ∈ closure (fr '' I)) : False := by
    have hC : IsPreconnected (insert y₂ (fr '' I)) :=
      (hI.image fr hfrc.continuousOn).subset_closure (subset_insert _ _)
        (insert_subset_iff.mpr ⟨hcl, subset_closure⟩)
    have hfx (t a : ℝ) (ht : t ∈ I) (ha : a ∉ I) : fr t ≠ f a := fun h =>
      ha (ofReal_injective (hinj (hreal t) (hreal a) h) ▸ ht)
    have hCsub : insert y₂ (fr '' I) ⊆ T \ {x₁, x₂} := by
      refine insert_subset_iff.mpr ⟨hy₂, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨hfT t, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hfa₁ ▸ hfx t a₁ ht h₁, hfa₂ ▸ hfx t a₂ ht h₂⟩
    exact hsep (hC.subset_connectedComponentIn (mem_insert_of_mem _ ⟨c, hcI, hfc₁⟩) hCsub
      (mem_insert _ _))
  have hend (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => (t : ℂ)) l (cobounded ℂ)) :
      Tendsto fr l (𝓝 y₂) :=
    hfy.comp (tendsto_inf.mpr ⟨hl, tendsto_principal.mpr (Eventually.of_forall hreal)⟩)
  rcases ha₁c.lt_or_gt with h₁ | h₁ <;> rcases ha₂c.lt_or_gt with h₂ | h₂
  · refine (hsepI (Ioi (max a₁ a₂)) isPreconnected_Ioi (max_lt h₁ h₂) (by simp) (by simp)
      (mem_closure_of_tendsto (hend _ ?_)
        ((eventually_gt_atTop _).mono fun t ht => mem_image_of_mem fr ht))).elim
    exact tendsto_norm_atTop_iff_cobounded.mp (by simpa using tendsto_abs_atTop_atTop)
  · exact mul_pos (by linarith) (by linarith)
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · refine (hsepI (Iio (min a₁ a₂)) isPreconnected_Iio (lt_min h₁ h₂) (by simp) (by simp)
      (mem_closure_of_tendsto (hend _ ?_)
        ((eventually_lt_atBot _).mono fun t ht => mem_image_of_mem fr ht))).elim
    exact tendsto_norm_atTop_iff_cobounded.mp (by simpa using tendsto_abs_atBot_atTop)

/-- Real prevertices `a₁`, `a₂` and `c` of the corners `x₁`, `x₂` and `y₁` under a Carathéodory map
`f` sending infinity to `y₂`, with `c` strictly between `a₁` and `a₂`. -/
private theorem exists_prevertices_mul_pos {Ω : Set ℂ} {f : ℂ → ℂ} {x₁ y₁ x₂ y₂ : ℂ}
    (hfc : ContinuousOn f {z | 0 ≤ z.im}) (hinj : InjOn f {z | 0 ≤ z.im})
    (hfR : BijOn f {z | z.im = 0} (frontier Ω \ {y₂}))
    (hfy : Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 y₂)) (hx₁ : x₁ ∈ frontier Ω)
    (hx₂ : x₂ ∈ frontier Ω) (hy₁ : y₁ ∈ frontier Ω \ {x₁, x₂}) (hy₂ : y₂ ∈ frontier Ω \ {x₁, x₂})
    (hsep : y₂ ∉ connectedComponentIn (frontier Ω \ {x₁, x₂}) y₁) :
    ∃ a₁ a₂ c : ℝ, f a₁ = x₁ ∧ f a₂ = x₂ ∧ f c = y₁ ∧ a₁ ≠ c ∧ a₂ ≠ c ∧
      0 < (c - a₁) * (a₂ - c) := by
  have hy₁y₂ : y₁ ≠ y₂ := fun h => hsep (h ▸ mem_connectedComponentIn hy₁)
  have hy₂' := hy₂
  simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at hy₁ hy₂
  have hpre (z : ℂ) (hz : z ∈ frontier Ω) (hzy : z ≠ y₂) : ∃ a : ℝ, f a = z := by
    obtain ⟨w, hw, hfw⟩ := hfR.surjOn ⟨hz, hzy⟩
    exact ⟨w.re, by rw [← hfw]; congr 1; exact Complex.ext (by simp) (by simpa using hw.symm)⟩
  obtain ⟨a₁, hfa₁⟩ := hpre x₁ hx₁ (Ne.symm hy₂.2.1)
  obtain ⟨a₂, hfa₂⟩ := hpre x₂ hx₂ (Ne.symm hy₂.2.2)
  obtain ⟨c, hfc₁⟩ := hpre y₁ hy₁.1 hy₁y₂
  have hne {s t : ℝ} (h : f s ≠ f t) : s ≠ t := fun hst => h (by rw [hst])
  have ha₁c : a₁ ≠ c := hne (by rw [hfa₁, hfc₁]; exact Ne.symm hy₁.2.1)
  have ha₂c : a₂ ≠ c := hne (by rw [hfa₂, hfc₁]; exact Ne.symm hy₁.2.2)
  exact ⟨a₁, a₂, c, hfa₁, hfa₂, hfc₁, ha₁c, ha₂c, mul_pos_of_notMem_connectedComponentIn hfc hinj
    (fun t => (hfR.mapsTo (show (t : ℂ) ∈ {z : ℂ | z.im = 0} by simp)).1) hfy hy₂' hfa₁ hfa₂
    hfc₁ ha₁c ha₂c hsep⟩

/-- The inverse `invFunOn f {z | 0 ≤ z.im}` of a Carathéodory map `f` of the closed upper
half-plane onto `closure Ω \ {y₂}`, with `f` tending to `y₂` at infinity, is continuous on
`closure Ω \ {y₂}`, tends to infinity at `y₂`, is holomorphic on `Ω` with values in the upper
half-plane, maps the frontier to the real line, and inverts `f` on both sides. -/
private theorem invFunOn_caratheodory {Ω : Set ℂ} {f : ℂ → ℂ} {y₂ : ℂ}
    (hfc : ContinuousOn f {z | 0 ≤ z.im})
    (hfd : DifferentiableOn ℂ f upperHalfPlaneSet) (hfH : BijOn f upperHalfPlaneSet Ω)
    (hfcl : BijOn f {z | 0 ≤ z.im} (closure Ω \ {y₂}))
    (hfR : BijOn f {z | z.im = 0} (frontier Ω \ {y₂}))
    (hfy : Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 y₂)) :
    ContinuousOn (invFunOn f {z | 0 ≤ z.im}) (closure Ω \ {y₂}) ∧
      Tendsto (invFunOn f {z | 0 ≤ z.im}) (𝓝[closure Ω \ {y₂}] y₂) (cobounded ℂ) ∧
      DifferentiableOn ℂ (invFunOn f {z | 0 ≤ z.im}) Ω ∧
      MapsTo (invFunOn f {z | 0 ≤ z.im}) Ω upperHalfPlaneSet ∧
      MapsTo (invFunOn f {z | 0 ≤ z.im}) (frontier Ω \ {y₂}) {z | z.im = 0} ∧
      MapsTo (invFunOn f {z | 0 ≤ z.im}) (closure Ω \ {y₂}) {z | 0 ≤ z.im} ∧
      (∀ z ∈ closure Ω \ {y₂}, f (invFunOn f {z | 0 ≤ z.im} z) = z) ∧
      ∀ w ∈ {z : ℂ | 0 ≤ z.im}, invFunOn f {z | 0 ≤ z.im} (f w) = w := by
  have hH₀ : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have himage : f '' {z | 0 ≤ z.im} = closure Ω \ {y₂} := hfcl.image_eq
  have hφf : ∀ w ∈ {z : ℂ | 0 ≤ z.im}, invFunOn f {z | 0 ≤ z.im} (f w) = w :=
    fun w hw => hfcl.injOn.leftInvOn_invFunOn hw
  have hHsub (w : ℂ) (hw : w ∈ upperHalfPlaneSet) : w ∈ {z : ℂ | 0 ≤ z.im} :=
    le_of_lt (α := ℝ) hw
  have hφH : MapsTo (invFunOn f {z | 0 ≤ z.im}) Ω upperHalfPlaneSet := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hfH.surjOn hz
    rw [hφf w (hHsub w hw)]
    exact hw
  rw [Metric.cobounded_eq_cocompact] at hfy ⊢
  refine ⟨himage ▸ hfc.continuousOn_invFunOn_image_of_tendsto_cocompact hH₀ hfcl.injOn hfy
      (by simp [himage]), himage ▸ hfc.tendsto_invFunOn_cocompact hH₀ (by simp [himage]), ?_,
    hφH, fun z hz => ?_, fun z hz => hfcl.surjOn.mapsTo_invFunOn hz,
    fun z hz => hfcl.surjOn.rightInvOn_invFunOn hz, hφf⟩
  · -- on `Ω` the inverse agrees with the holomorphic inverse of `f` on the upper half-plane
    have hinv := hfd.invFunOn UpperHalfPlane.isOpen_upperHalfPlaneSet hfH.injOn
    rw [hfH.image_eq] at hinv
    refine hinv.congr fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hfH.surjOn hz
    rw [hφf w (hHsub w hw), hfH.injOn.leftInvOn_invFunOn hw]
  · obtain ⟨w, hw, rfl⟩ := hfR.surjOn hz
    rw [hφf w (le_of_eq (α := ℝ) hw.symm)]
    exact hw

/-- For `φ` an inverse of a bijection `f` of the upper half-plane onto `Ω`, the fibres of `Λ ∘ φ`
on `Ω` are the images under `f` of the fibres of `Λ` on the upper half-plane, and have the same
cardinality. -/
private theorem ncard_inter_preimage_comp {Ω : Set ℂ} {f φ Λ : ℂ → ℂ}
    (hfH : BijOn f upperHalfPlaneSet Ω) (hφH : MapsTo φ Ω upperHalfPlaneSet)
    (hfφ : ∀ z ∈ Ω, f (φ z) = z) (hφf : ∀ w ∈ upperHalfPlaneSet, φ (f w) = w) (ζ : ℂ) :
    (Ω ∩ (Λ ∘ φ) ⁻¹' {ζ}).ncard = (upperHalfPlaneSet ∩ Λ ⁻¹' {ζ}).ncard := by
  have hfib : Ω ∩ (Λ ∘ φ) ⁻¹' {ζ} = f '' (upperHalfPlaneSet ∩ Λ ⁻¹' {ζ}) := by
    ext z
    constructor
    · rintro ⟨hz, hζz⟩
      exact ⟨φ z, ⟨hφH hz, hζz⟩, hfφ z hz⟩
    · rintro ⟨w, ⟨hw, hζw⟩, rfl⟩
      exact ⟨hfH.mapsTo hw, by simpa [comp_apply, hφf w hw] using hζw⟩
  rw [hfib, (hfH.injOn.mono inter_subset_left).ncard_image]

/-- **A Jordan rectangle is a branched double cover of the strip.** Let `Ω` be a bounded, connected
open subset of `ℂ` whose frontier is a Jordan curve, and let `x₁`, `y₁`, `x₂` and `y₂` be points
of that frontier, with `y₁` and `y₂` different from `x₁` and `x₂` and separated from each other by
them on the frontier (so that the four points are distinct). Then there is a map `u`,
holomorphic on `Ω` and continuous on `closure Ω` away from the four corners, which maps `Ω` into
the open strip `0 < z.im < 1` and the frontier away from the corners into the two boundary lines,
whose real part tends to `-∞` at `x₁` and `x₂` and to `+∞` at `y₁` and `y₂` within the closure,
and which is a double cover with one branch point: for some `b ∈ Ω`, every point of the strip
other than `u b` has exactly two preimages in `Ω`, and `u b` has exactly one. -/
theorem exists_mapsTo_strip_ncard_inter_preimage_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω) (hΩJ : IsJordanCurve (frontier Ω))
    {x₁ y₁ x₂ y₂ : ℂ} (hx₁ : x₁ ∈ frontier Ω) (hx₂ : x₂ ∈ frontier Ω)
    (hy₁ : y₁ ∈ frontier Ω \ {x₁, x₂}) (hy₂ : y₂ ∈ frontier Ω \ {x₁, x₂})
    (hsep : y₂ ∉ connectedComponentIn (frontier Ω \ {x₁, x₂}) y₁) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u Ω ∧ ContinuousOn u (closure Ω \ {x₁, y₁, x₂, y₂}) ∧
      MapsTo u Ω {z | z.im ∈ Ioo 0 1} ∧
      MapsTo u (frontier Ω \ {x₁, y₁, x₂, y₂}) {z | z.im = 0 ∨ z.im = 1} ∧
      Tendsto u (𝓝[closure Ω \ {x₁, y₁, x₂, y₂}] x₁) (comap re atBot) ∧
      Tendsto u (𝓝[closure Ω \ {x₁, y₁, x₂, y₂}] x₂) (comap re atBot) ∧
      Tendsto u (𝓝[closure Ω \ {x₁, y₁, x₂, y₂}] y₁) (comap re atTop) ∧
      Tendsto u (𝓝[closure Ω \ {x₁, y₁, x₂, y₂}] y₂) (comap re atTop) ∧
      ∃ b ∈ Ω, ∀ ζ ∈ {z : ℂ | z.im ∈ Ioo 0 1},
        (Ω ∩ u ⁻¹' {ζ}).ncard = if ζ = u b then 1 else 2 := by
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfy⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ hy₂.1
  obtain ⟨a₁, a₂, c, hfa₁, hfa₂, hfc₁, ha₁c, ha₂c, hq⟩ :=
    exists_prevertices_mul_pos hfc hfcl.injOn hfR hfy hx₁ hx₂ hy₁ hy₂ hsep
  -- the inverse `φ` of `f`, and its behaviour at the corners
  obtain ⟨hφc, hφy, hφd, hφH, hφR, hφH₀, hfφ, hφf⟩ :=
    invFunOn_caratheodory hfc hfd hfH hfcl hfR hfy
  set φ := invFunOn f {z : ℂ | 0 ≤ z.im}
  set corners : Set ℂ := {x₁, y₁, x₂, y₂}
  have hsub : closure Ω \ corners ⊆ closure Ω \ {y₂} :=
    sdiff_subset_sdiff_right (by simp [corners])
  have hφa (z : ℂ) (hz : z ∈ closure Ω \ corners) (a : ℝ) (ha : f a ∈ corners) : φ z ≠ a :=
    fun h => hz.2 (by rw [← hfφ z (hsub hz), h]; exact ha)
  have hmaps : MapsTo φ (closure Ω \ corners) ({z | 0 ≤ z.im} \ {(a₁ : ℂ), (c : ℂ), (a₂ : ℂ)}) :=
    fun z hz => ⟨hφH₀ (hsub hz), by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hφa z hz a₁ (by simp [corners, hfa₁]), hφa z hz c (by simp [corners, hfc₁]),
        hφa z hz a₂ (by simp [corners, hfa₂])⟩⟩
  have hcorner (a : ℝ) (ha : f a ∈ corners) :
      Tendsto φ (𝓝[closure Ω \ corners] (f a)) (𝓝[≠] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
      hφa w hw a ha⟩
    have := ((hφc _ (hfcl.mapsTo (show (a : ℂ) ∈ {z : ℂ | 0 ≤ z.im} by simp))).mono hsub).tendsto
    rwa [hφf a (by simp)] at this
  -- the map `u` is the model double cover composed with `φ`; `f bH` is the branch point
  set bH : ℂ := (c : ℂ) + (√((c - a₁) * (a₂ - c)) : ℝ) * I
  have hbH : bH ∈ upperHalfPlaneSet := by simp [bH, upperHalfPlaneSet, Real.sqrt_pos.mpr hq]
  refine ⟨_ ∘ φ, (differentiableOn_log_sub_mul_sub_div_sub_div_pi hq).comp hφd hφH,
    (continuousOn_log_sub_mul_sub_div_sub_div_pi hq).comp (hφc.mono hsub) hmaps,
    (mapsTo_log_sub_mul_sub_div_sub_div_pi hq).comp hφH, fun z hz => ?_,
    (tendsto_log_sub_mul_sub_div_sub_div_pi_comap_re_atBot (.inl rfl) ha₁c).comp
      (hfa₁ ▸ hcorner a₁ (by simp [corners, hfa₁])),
    (tendsto_log_sub_mul_sub_div_sub_div_pi_comap_re_atBot (.inr rfl) ha₂c).comp
      (hfa₂ ▸ hcorner a₂ (by simp [corners, hfa₂])),
    (tendsto_log_sub_mul_sub_div_sub_div_pi_comap_re_atTop ha₁c ha₂c.symm).comp
      (hfc₁ ▸ hcorner c (by simp [corners, hfc₁])),
    (tendsto_log_sub_mul_sub_div_sub_div_pi_cobounded a₁ c a₂).comp
      (hφy.mono_left (nhdsWithin_mono _ hsub)), f bH, hfH.mapsTo hbH, fun ζ hζ => ?_⟩
  · exact mapsTo_log_sub_mul_sub_div_sub_div_pi_boundary a₁ c a₂
      ⟨hφR ⟨hz.1, fun h => hz.2 (by simp [corners, h])⟩,
        (hmaps ⟨frontier_subset_closure hz.1, hz.2⟩).2⟩
  · rw [ncard_inter_preimage_comp hfH hφH (fun z hz => hfφ z ⟨subset_closure hz, fun h =>
      hΩo.inter_frontier_eq.subset ⟨hz, h ▸ hy₂.1⟩⟩) (fun w hw => hφf w (le_of_lt (α := ℝ) hw)),
      ncard_inter_preimage_log_sub_mul_sub_div_sub_div_pi hq hζ, comp_apply,
      hφf bH (le_of_lt (α := ℝ) hbH)]

end TauCeti
