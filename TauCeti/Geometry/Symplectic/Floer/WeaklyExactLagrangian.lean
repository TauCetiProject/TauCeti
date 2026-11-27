/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExactBubble
public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd

/-!
# Weak exactness of the diagonal and of graphs, by doubling discs

A two-form `ω` on a manifold `M` is **weakly exact relative to** a subset `L ⊆ M`
(`TauCeti.IsWeaklyExactRel`) when its integral over every disc with boundary on `L` vanishes: for
every cap `u` (`TauCeti.IsCap`) of a loop `γ` lying in `L`, `∫ u^* ω = 0`. For a symplectic form
and a Lagrangian `L` this is the condition `ω(π₂(M, L)) = 0` of a weakly exact Lagrangian, under
which Lagrangian Floer theory has no disc bubbles: a pseudoholomorphic disc with boundary on `L`
is constant (`TauCeti.SmoothTwoForm.IsNondegenerate.apply_eq_apply_zero_of_isWeaklyExactRel`),
since its symplectic area is minus the integral over its polar cap, which is a cap of its boundary
loop. For a continuous weakly exact form, weak exactness relative to `L` says that every loop in
`L` has cap area `0` (`TauCeti.capArea`,
`TauCeti.IsWeaklyExact.isWeaklyExactRel_iff_capArea_eq_zero`).

The Floer theory of a symplectomorphism folds its seamed cylinders into strips in `M × M` with
boundary on the diagonal and on a graph, for the twisted product form `pr₁^* σ - pr₂^* σ`
(`TauCeti.Floer.fold`). These Lagrangians are weakly exact as soon as `σ` is weakly exact, that is
as soon as `σ` vanishes on spheres; no condition on discs in `M` is needed. The argument doubles a
disc: a disc `u = (u₁, u₂)` in `M × N` has integral

`∫ u^* (pr₁^* σ - pr₂^* τ) = ∫ u₁^* σ - ∫ u₂^* τ`

(`TauCeti.SmoothTwoForm.rectangleIntegral_twistedProd`). If its boundary lies on the graph
`{(x, φ x)}` of a map `φ : M → N` with `φ^* τ = σ`, then `φ ∘ u₁` and `u₂` are two discs in `N` with
the same boundary loop, and `∫ u₁^* σ = ∫ (φ ∘ u₁)^* τ`. Glued along their common boundary, they
form a sphere in `N`, so their integrals agree when `τ` is weakly exact
(`TauCeti.IsWeaklyExact.rectangleIntegral_eq_of_isCap`), and the integral over `u` vanishes
(`TauCeti.IsWeaklyExact.isWeaklyExactRel_twistedProd_graph`). Conversely, a sphere
`w` in `M` gives the disc `(w, φ x)` with boundary on the graph and integral `∫ w^* σ`, so weak
exactness relative to the graph forces `σ` to be weakly exact
(`TauCeti.IsWeaklyExactRel.isWeaklyExact_of_twistedProd_graph`). For the diagonal,
the graph of the identity, the two conditions coincide
(`TauCeti.SmoothTwoForm.isWeaklyExactRel_twistedProd_diagonal_iff`).

The boundary of a folded strip lies on the diagonal and on the set of pairs `(φ y, y)`, which is
the graph of `φ⁻¹` for a diffeomorphism `φ`, with `(φ⁻¹)^* σ = σ` when `φ` preserves `σ`.

## Main definitions

* `TauCeti.IsWeaklyExactRel ω L`: the integral of `ω` over every disc with boundary on `L`
  vanishes.

## Main results

* `TauCeti.SmoothTwoForm.rectangleIntegral_twistedProd`: the integral of a twisted product form
  over a map of the plane into `M × N` is the difference of the integrals over its components.
* `TauCeti.IsWeaklyExact.isWeaklyExactRel_twistedProd_graph`: the graph of a map
  `φ` with `φ^* τ = σ` is weakly exact for `pr₁^* σ - pr₂^* τ` when `τ` is weakly exact.
* `TauCeti.IsWeaklyExactRel.isWeaklyExact_of_twistedProd_graph`: conversely, `σ` is
  then weakly exact.
* `TauCeti.SmoothTwoForm.isWeaklyExactRel_twistedProd_diagonal_iff`: the diagonal is weakly exact
  for `pr₁^* σ - pr₂^* σ` exactly when `σ` is weakly exact.
* `TauCeti.SmoothTwoForm.IsNondegenerate.apply_eq_apply_zero_of_isWeaklyExactRel`: a
  pseudoholomorphic disc with boundary on a set relative to which the form is weakly exact is
  constant.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547 (Lagrangians with `ω(π₂(M, L)) = 0`).
* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611 (the Floer theory of a symplectomorphism through the diagonal and its graph).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 9.1 (the graph of a symplectomorphism and the
  diagonal as Lagrangians of `M × M⁻`).
-/

public section

noncomputable section

open Set Real
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Weak exactness relative to a subset -/

variable (I) in
/-- A two-form `φ` is **weakly exact relative to** a subset `L` when its integral over every disc
with boundary on `L` vanishes: `∫ u^* φ = 0` for every cap `u` (`TauCeti.IsCap`) of a loop `γ`
with values in `L`. For a symplectic form and a Lagrangian `L` this is the condition
`ω(π₂(M, L)) = 0` of a weakly exact Lagrangian. -/
def IsWeaklyExactRel (φ : RoughForm I M F 2) (L : Set M) : Prop :=
  ∀ ⦃u : ℝ × ℝ → M⦄ ⦃γ : ℝ → M⦄, IsCap I u γ → (∀ t, γ t ∈ L) →
    rectangleIntegral φ u (0, 0) (1, 1) = 0

/-- Unfolding `TauCeti.IsWeaklyExactRel`. -/
theorem isWeaklyExactRel_iff {φ : RoughForm I M F 2} {L : Set M} :
    IsWeaklyExactRel I φ L ↔ ∀ ⦃u : ℝ × ℝ → M⦄ ⦃γ : ℝ → M⦄, IsCap I u γ → (∀ t, γ t ∈ L) →
      rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

namespace IsWeaklyExactRel

variable {φ : RoughForm I M F 2} {L L' : Set M}

/-- **Weak exactness relative to a subset is antitone in the subset**: a disc with boundary on
`L'` has boundary on every `L ⊇ L'`. -/
theorem mono (h : IsWeaklyExactRel I φ L) (hL : L' ⊆ L) : IsWeaklyExactRel I φ L' :=
  fun _ _ hu hγ ↦ h hu fun t ↦ hL (hγ t)

end IsWeaklyExactRel

/-- **Weak exactness relative to a subset through the cap area.** A continuous weakly exact form
is weakly exact relative to `L` exactly when every loop in `L` has cap area `0`: the integral over
every cap of a loop is its cap area. -/
theorem IsWeaklyExact.isWeaklyExactRel_iff_capArea_eq_zero [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) (hw : IsWeaklyExact φ) {L : Set M} :
    IsWeaklyExactRel I φ L ↔ ∀ γ : ℝ → M, (∀ t, γ t ∈ L) → capArea φ γ = 0 :=
  ⟨fun h γ hγ ↦ by
    by_cases hc : ∃ u, IsCap I u γ
    · exact (hw.capArea_eq hφ hc.choose_spec).trans (h hc.choose_spec hγ)
    · exact capArea_of_not_exists_isCap hc,
    fun h _ _ hu hγ ↦ (hw.capArea_eq hφ hu).symm.trans (h _ hγ)⟩

section TwistedProd

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

namespace SmoothTwoForm

/-! ### The integral of a twisted product form -/

/-- **The integral of a twisted product form splits.** For a `C¹` map `u` of the plane into
`M × N`, the integral of `pr₁^* σ - pr₂^* τ` over `u` is the integral of `σ` over its first
component minus the integral of `τ` over its second component. -/
theorem rectangleIntegral_twistedProd (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N)
    {u : ℝ × ℝ → M × N} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) (I.prod J) 1 u) (a b : ℝ × ℝ) :
    rectangleIntegral (twistedProd σ τ).val u a b =
      rectangleIntegral σ.val (Prod.fst ∘ u) a b - rectangleIntegral τ.val (Prod.snd ∘ u) a b := by
  -- The two pulled-back forms are continuous, so their integrands over `u` are integrable.
  have hint {θ : RoughForm (I.prod J) (M × N) ℝ 2} (hθ : IsSmoothForm (I.prod J) 0 θ) :
      (∀ s ∈ [[a.1, b.1]], IntervalIntegrable
        (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) (I.prod J) u θ (s, t) ![(1, 0), (0, 1)])
        MeasureTheory.volume a.2 b.2) ∧
      IntervalIntegrable (fun s ↦ ∫ t in a.2..b.2,
        mpullback 𝓘(ℝ, ℝ × ℝ) (I.prod J) u θ (s, t) ![(1, 0), (0, 1)])
        MeasureTheory.volume a.1 b.1 :=
    ⟨fun s _ ↦ ((hθ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]).comp
      (Continuous.prodMk_right s)).intervalIntegrable _ _,
      (continuous_integral_mpullback hθ hu a.2 b.2).intervalIntegrable _ _⟩
  have h₁ := hint ((SmoothForm.mpullback Prod.fst contMDiff_fst σ).isSmoothForm.of_le (by simp))
  have h₂ := hint ((SmoothForm.mpullback Prod.snd contMDiff_snd τ).isSmoothForm.of_le (by simp))
  have hu' (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (I.prod J) u z :=
    hu.mdifferentiable one_ne_zero z
  rw [twistedProd_def, Submodule.coe_sub, rectangleIntegral_sub h₁.1 h₂.1 h₁.2 h₂.2,
    SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    rectangleIntegral_mpullback _ (fun z _ ↦ contMDiffAt_fst.mdifferentiableAt one_ne_zero)
      fun z _ ↦ hu' z,
    rectangleIntegral_mpullback _ (fun z _ ↦ contMDiffAt_snd.mdifferentiableAt one_ne_zero)
      fun z _ ↦ hu' z]

end SmoothTwoForm

/-! ### Graphs and the diagonal -/

/-- **Graphs are weakly exact, by doubling discs.** Let `φ : M → N` be a smooth map with
`φ^* τ = σ`, so that its graph `{(x, φ x)}` is isotropic for the twisted product form
`pr₁^* σ - pr₂^* τ`. If `τ` is weakly exact, the twisted product form is weakly exact relative to
the graph: a disc `(u₁, u₂)` with boundary on the graph has integral `∫ (φ ∘ u₁)^* τ - ∫ u₂^* τ`,
and `φ ∘ u₁` and `u₂` cap the same loop of `N`. -/
theorem IsWeaklyExact.isWeaklyExactRel_twistedProd_graph {σ : SmoothTwoForm I M}
    {τ : SmoothTwoForm J N} (hτ : IsWeaklyExact τ.val) {φ : M → N} (hφ : ContMDiff I J ∞ φ)
    (hφστ : SmoothForm.mpullback φ hφ τ = σ) :
    IsWeaklyExactRel (I.prod J) (SmoothTwoForm.twistedProd σ τ).val
      {p : M × N | p.2 = φ p.1} := by
  intro u γ hu hγ
  obtain ⟨x, hu⟩ := isCap_iff.1 hu
  have hu₁ := hu.comp (contMDiff_fst (n := 2))
  have hu₂ := hu.comp (contMDiff_snd (n := 2))
  -- `φ ∘ u₁` caps the loop `φ ∘ γ₁`, which is the second component `γ₂` of the boundary.
  have hφu₁ : IsCap J (φ ∘ Prod.fst ∘ u) (Prod.snd ∘ γ) := by
    have h := hu₁.comp (hφ.of_le (by simp))
    rw [show φ ∘ Prod.fst ∘ γ = Prod.snd ∘ γ from funext fun t ↦ (hγ t).symm] at h
    exact isCap_iff.2 ⟨φ x.1, h⟩
  rw [SmoothTwoForm.rectangleIntegral_twistedProd σ τ (hu.contMDiff.of_le one_le_two), ← hφστ,
    SmoothForm.coe_mpullback, rectangleIntegral_mpullback _
      (fun z _ ↦ (hφ.mdifferentiable (by simp)) _)
      fun z _ ↦ hu₁.contMDiff.mdifferentiable two_ne_zero z,
    hτ.rectangleIntegral_eq_of_isCap (τ.isSmoothForm.of_le (by simp)) hφu₁
      (isCap_iff.2 ⟨x.2, hu₂⟩), sub_self]

/-- **Weak exactness relative to a graph forces weak exactness.** If the twisted product form
`pr₁^* σ - pr₂^* τ` is weakly exact relative to the graph of a map `φ : M → N`, then `σ` is weakly
exact: a sphere `w` in `M` gives the disc `(w, φ x)` in `M × N`, with boundary on the graph and
the same integral as `w`. -/
theorem IsWeaklyExactRel.isWeaklyExact_of_twistedProd_graph {σ : SmoothTwoForm I M}
    {τ : SmoothTwoForm J N} {φ : M → N}
    (h : IsWeaklyExactRel (I.prod J) (SmoothTwoForm.twistedProd σ τ).val
      {p : M × N | p.2 = φ p.1}) :
    IsWeaklyExact σ.val := by
  rw [isWeaklyExact_iff]
  intro w x y hw
  have hcyl : IsLoopCylinder (I.prod J) (fun z ↦ (w z, φ x)) (fun _ ↦ (x, φ x))
      fun _ ↦ (y, φ x) :=
    ⟨hw.contMDiff.prodMk contMDiff_const, fun z ↦ by rw [hw.apply_add_one],
      fun t ↦ by rw [hw.apply_zero], fun t ↦ by rw [hw.apply_one]⟩
  have h0 := h hcyl.isCap fun _ ↦ rfl
  rwa [SmoothTwoForm.rectangleIntegral_twistedProd σ τ (hcyl.contMDiff.of_le one_le_two),
    show Prod.snd ∘ (fun z ↦ (w z, φ x)) = fun _ ↦ φ x from rfl, rectangleIntegral_const,
    sub_zero] at h0

namespace SmoothTwoForm

/-- **The diagonal is weakly exact exactly when the form is.** The twisted product form
`pr₁^* σ - pr₂^* σ` on `M × M` is weakly exact relative to the diagonal exactly when `σ` is weakly
exact. This is the case of the graph of the identity. -/
theorem isWeaklyExactRel_twistedProd_diagonal_iff {σ : SmoothTwoForm I M} :
    IsWeaklyExactRel (I.prod I) (twistedProd σ σ).val (diagonal M) ↔ IsWeaklyExact σ.val := by
  have hdiag : diagonal M = {p : M × M | p.2 = id p.1} := Set.ext fun _ ↦ eq_comm
  have hid : SmoothForm.mpullback (id : M → M) contMDiff_id σ = σ := by
    rw [SmoothForm.mpullback_id, LinearMap.id_apply]
  rw [hdiag]
  exact ⟨IsWeaklyExactRel.isWeaklyExact_of_twistedProd_graph,
    fun hσ ↦ hσ.isWeaklyExactRel_twistedProd_graph contMDiff_id hid⟩

end SmoothTwoForm

end TwistedProd

/-! ### No disc bubbles -/

namespace SmoothTwoForm

variable [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {u : ℝ × ℝ → M}

/-- **No disc bubbles on a weakly exact boundary.** Let `σ` be a nondegenerate two-form, weakly
exact relative to `L` (`TauCeti.IsWeaklyExactRel`), for instance the twisted product form on
`M × M` relative to the diagonal or to the graph of a symplectomorphism of a weakly exact manifold.
A `C²` map `u` of the plane solving the Cauchy–Riemann equation `∂_t u = J ∂_s u` on the open unit
disc, for almost complex structures `J z` on `T_{u z} M` tamed by `σ`, whose boundary loop
`t ↦ u (cos 2πt, sin 2πt)` lies in `L`, is constant on the closed unit disc. -/
theorem IsNondegenerate.apply_eq_apply_zero_of_isWeaklyExactRel (hσ : σ.IsNondegenerate)
    {L : Set M} (hL : IsWeaklyExactRel I σ.val L) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hσ.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    (hbd : ∀ t : ℝ, u (cos (2 * π * t), sin (2 * π * t)) ∈ L) {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) : u z = u 0 :=
  (hσ.rectangleIntegral_comp_polar_eq_zero_iff (hu.of_le one_le_two) J hJ hhol).1
    (hL (isLoopCylinder_comp_polar hu).isCap hbd) z hz

end SmoothTwoForm

end TauCeti
