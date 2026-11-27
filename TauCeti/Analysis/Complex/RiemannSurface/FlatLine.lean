/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FiberMultiset
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.Complex
import TauCeti.Analysis.Complex.QuasiPeriodic.Basic
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import TauCeti.RingTheory.Polynomial.Vieta
import TauCeti.Topology.Discrete

/-!
# Compact holomorphic curves in a flat line over a complex torus

Let `L ⊆ ℂ` be a full lattice and `ψ : L → S¹` a unitary character. The flat line `N` of holonomy
`ψ` over the complex torus `ℂ / L` is the orbit space of `ℂ × ℂ` under the free, properly
discontinuous action `ω +ᵥ (z, v) = (z + ω, ψ ω v)` of `L` (`TauCeti.FlatLine`; the action is
carried by the type synonym `TauCeti.FlatLineLattice ψ` of `L`). It is a complex manifold of
dimension two, the orbit projection `ℂ × ℂ → N` is a local biholomorphism
(`TauCeti.isLocalDiffeomorph_addQuotientMk`), and `[(z, v)] ↦ [z]` is a holomorphic projection
`N → ℂ / L` (`TauCeti.FlatLine.proj`, `TauCeti.FlatLine.contMDiff_proj`) with zero section
`{[(z, 0)]}`. Two representatives give the same point exactly when they differ by the action
(`TauCeti.FlatLine.mk_eq_mk_iff`).

The main result is that when `ψ` has infinite order, so that no positive power `N ^ j` is a trivial
line, every nonconstant holomorphic map `u` from a compact connected Riemann surface into `N` lies
on the zero section (`TauCeti.FlatLine.exists_eq_mk_zero_of_mdifferentiable`). The projection `f` of
`u` to the torus is either constant, and then `u` lies in one fibre `ℂ` and is constant by the
maximum principle, or a branched covering of some degree `m`. In the second case, choose a lift
`z ∈ ℂ` of a point of the torus; every point `x` of the fibre of `f` over `[z]` has a fibre
coordinate `v` with `u x = [(z, v)]`. The elementary symmetric functions `e_j(z)` of these
coordinates, counted with the local multiplicities of `f`, are holomorphic in `z`, also across the
branch values of `f`
(`TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`). Moving the lift by a lattice vector
`ω` multiplies every coordinate by `ψ ω`, so `e_j(z + ω) = ψ(ω) ^ j e_j(z)`: each `e_j` is a
holomorphic section of the nontrivial flat line `N ^ j`, hence vanishes
(`Differentiable.eq_zero_of_add_eq_smul`). Then `∏ (W - v) = Wᵐ`, and every fibre coordinate is `0`.

The hypothesis holds as soon as one holonomy `ψ ω₀` has infinite order, for instance for the
holonomy `exp (2π i c ω)` of a homomorphism `c : L → ℝ` taking an irrational value. A flat line
with such holonomy is the model of the normal bundle of an embedded square-zero torus in
Taubes's count of pseudoholomorphic curves in symplectic four-manifolds, with an integrable
complex structure on a neighbourhood of the torus. In that model the theorem says that the only
compact holomorphic curves near the torus are the torus itself and its branched covers. Some
condition on `ψ` is needed: if `ψ ^ k = 1`, the curves `{vᵏ = c}`, `c ≠ 0`, are compact and miss
the zero section.

## Main definitions

* `TauCeti.FlatLine ψ`: the total space of the flat line of holonomy `ψ` over `ℂ / L`.
* `TauCeti.FlatLine.proj`: its projection to the torus.

## Main results

* `TauCeti.FlatLine.contMDiff_proj`: the projection is holomorphic.
* `TauCeti.FlatLine.exists_eq_mk_zero_of_mdifferentiable`: compact holomorphic curves in a flat
  line of infinite order lie on the zero section.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8 (elementary symmetric functions of the values of a function along the fibres of a branched
  covering).
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 (flat line bundles
  on complex tori and their sections).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (square-zero tori and the flat model of their normal bundles).
-/

public section

noncomputable section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti

variable {L : Submodule ℤ ℂ} (ψ : AddChar L Circle)

/-- The lattice `L`, acting on `ℂ × ℂ` through the unitary character `ψ` by
`ω +ᵥ (z, v) = (z + ω, ψ ω v)`. The orbit space of this action is the total space of the flat
line of holonomy `ψ` over the torus `ℂ / L` (`TauCeti.FlatLine`). -/
def FlatLineLattice (_ψ : AddChar L Circle) : Type := L

namespace FlatLineLattice

instance : AddCommGroup (FlatLineLattice ψ) := inferInstanceAs (AddCommGroup L)

/-- The lattice vector underlying an element of `FlatLineLattice ψ`. -/
def toLattice : FlatLineLattice ψ ≃+ L := AddEquiv.refl _

instance : AddAction (FlatLineLattice ψ) (ℂ × ℂ) where
  vadd ω p := (p.1 + (toLattice ψ ω : ℂ), (ψ (toLattice ψ ω) : ℂ) * p.2)
  zero_vadd p := by
    -- Unfold the action field to expose the translation and the multiplier.
    change (p.1 + ((toLattice ψ 0 : L) : ℂ), (ψ (toLattice ψ 0) : ℂ) * p.2) = p
    simp
  add_vadd ω ω' p := by
    -- Unfold the action field to expose the translation and the multiplier.
    change (p.1 + ((toLattice ψ (ω + ω') : L) : ℂ), (ψ (toLattice ψ (ω + ω')) : ℂ) * p.2) =
      (p.1 + (toLattice ψ ω' : ℂ) + (toLattice ψ ω : ℂ),
        (ψ (toLattice ψ ω) : ℂ) * ((ψ (toLattice ψ ω') : ℂ) * p.2))
    simp only [map_add, Submodule.coe_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    exact Prod.ext (by ring) (by ring)

@[simp]
theorem vadd_def (ω : FlatLineLattice ψ) (p : ℂ × ℂ) :
    ω +ᵥ p = (p.1 + (toLattice ψ ω : ℂ), (ψ (toLattice ψ ω) : ℂ) * p.2) :=
  (rfl)

/-- The action is free: already its first coordinate, a translation by `ω`, determines `ω`. -/
instance : IsCancelVAdd (FlatLineLattice ψ) (ℂ × ℂ) :=
  isCancelVAdd_iff_eq_zero_of_vadd_eq.2 fun ω p h ↦ (toLattice ψ).injective <| by
    simpa [Prod.ext_iff] using congrArg Prod.fst h

instance : ContinuousConstVAdd (FlatLineLattice ψ) (ℂ × ℂ) :=
  ⟨fun ω ↦ by
    simp only [vadd_def]
    fun_prop⟩

instance (n : WithTop ℕ∞) : ContMDiffConstVAdd 𝓘(ℂ, ℂ × ℂ) n (FlatLineLattice ψ) (ℂ × ℂ) :=
  ⟨fun ω ↦ by
    rw [contMDiff_iff_contDiff]
    simp only [vadd_def]
    fun_prop⟩

/-- The action is also real smooth, so the flat line is a real manifold with the orbit projection a
real local diffeomorphism, on which real differential forms live. -/
instance (n : WithTop ℕ∞) : ContMDiffConstVAdd 𝓘(ℝ, ℂ × ℂ) n (FlatLineLattice ψ) (ℂ × ℂ) :=
  ⟨fun ω ↦ by
    rw [contMDiff_iff_contDiff]
    simp only [vadd_def]
    fun_prop⟩

/-- The action is properly discontinuous because its first coordinate is the translation action
of the discrete lattice `L` on `ℂ`. -/
instance [DiscreteTopology L] : ProperlyDiscontinuousVAdd (FlatLineLattice ψ) (ℂ × ℂ) := by
  refine ⟨fun {K₁ K₂} hK₁ hK₂ ↦ ?_⟩
  refine ((ProperlyDiscontinuousVAdd.finite_disjoint_inter_image (Γ := L)
    (hK₁.image continuous_fst) (hK₂.image continuous_fst)).preimage
    (toLattice ψ).injective.injOn).subset ?_
  rintro ω hω
  obtain ⟨_, ⟨p, hp, rfl⟩, hq⟩ := hω
  refine ⟨p.1 + (toLattice ψ ω : ℂ), ⟨p.1, mem_image_of_mem _ hp, ?_⟩, ⟨_, hq, rfl⟩⟩
  simp [Submodule.vadd_def, add_comm]

end FlatLineLattice

/-- The total space of the flat unitary line of holonomy `ψ` over the complex torus `ℂ / L`: the
orbit space of `ℂ × ℂ` under `ω +ᵥ (z, v) = (z + ω, ψ ω v)`. For a full lattice `L` it is a
complex manifold of dimension two, and the orbit projection is a local biholomorphism
(`TauCeti.instIsManifoldAddQuotient`, `TauCeti.isLocalDiffeomorph_addQuotientMk`). -/
abbrev FlatLine := AddAction.orbitRel.Quotient (FlatLineLattice ψ) (ℂ × ℂ)

namespace FlatLine

variable {ψ}

/-- Two points `p` and `q` of `ℂ × ℂ` represent the same point of the flat line exactly when
`p = (q.1 + ω, ψ ω q.2)` for a lattice vector `ω`. -/
theorem mk_eq_mk_iff {p q : ℂ × ℂ} :
    (Quotient.mk _ p : FlatLine ψ) = Quotient.mk _ q ↔
      ∃ ω : L, p.1 = q.1 + ω ∧ p.2 = (ψ ω : ℂ) * q.2 := by
  rw [Quotient.eq]
  refine ⟨fun ⟨ω, h⟩ ↦ ⟨FlatLineLattice.toLattice ψ ω, ?_⟩, fun ⟨ω, h⟩ ↦
    ⟨(FlatLineLattice.toLattice ψ).symm ω, ?_⟩⟩
  · simpa [Prod.ext_iff, eq_comm] using h
  · simpa [Prod.ext_iff, eq_comm] using h

/-- The point `(z + ω, ψ ω v)` represents the same point of the flat line as `(z, v)`. -/
theorem mk_add_mul (z v : ℂ) (ω : L) :
    (Quotient.mk _ (z + ω, (ψ ω : ℂ) * v) : FlatLine ψ) = Quotient.mk _ (z, v) :=
  mk_eq_mk_iff.2 ⟨ω, rfl, rfl⟩

/-- The projection of the flat line to the torus `ℂ / L`, induced by `(z, v) ↦ z`. -/
def proj : FlatLine ψ → AddAction.orbitRel.Quotient L ℂ :=
  Quotient.lift (fun p ↦ Quotient.mk _ p.1) fun p q ⟨ω, h⟩ ↦
    L.orbitRelQuotient_mk_eq_mk_iff.2 (by simp [← h])

@[simp]
theorem proj_mk (p : ℂ × ℂ) :
    proj (Quotient.mk _ p : FlatLine ψ) = Quotient.mk (AddAction.orbitRel L ℂ) p.1 :=
  (rfl)

variable [DiscreteTopology L]

/-- The projection of the flat line to the torus is holomorphic. -/
theorem contMDiff_proj (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) n (proj (ψ := ψ)) := by
  refine ((isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ) (M := ℂ × ℂ)
    (I := 𝓘(ℂ, ℂ × ℂ)) (n := ⊤)).contMDiff_comp_iff Quotient.mk_surjective le_top).1 ?_
  have h : proj ∘ (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) =
      Quotient.mk (AddAction.orbitRel L ℂ) ∘ Prod.fst := rfl
  rw [h]
  exact ((isLocalDiffeomorph_addQuotientMk (G := L) (M := ℂ) (I := 𝓘(ℂ)) (n := ⊤)).contMDiff.of_le
    le_top).comp (contMDiff_iff_contDiff.2 contDiff_fst)

/-! ### The fibre coordinate over a lift of the base point -/

open Classical in
/-- The fibre coordinate of a point `x` of the flat line over a lift `z ∈ ℂ` of its base point: the
unique `v` with `x = [(z, v)]`, and `0` if `x` does not lie over `[z]`. -/
private def fiberCoord (z : ℂ) (x : FlatLine ψ) : ℂ :=
  if h : ∃ v, x = Quotient.mk _ (z, v) then h.choose else 0

omit [DiscreteTopology L] in
private theorem fiberCoord_mk (z v : ℂ) :
    fiberCoord z (Quotient.mk _ (z, v) : FlatLine ψ) = v := by
  have h : ∃ v', (Quotient.mk _ (z, v) : FlatLine ψ) = Quotient.mk _ (z, v') := ⟨v, rfl⟩
  rw [fiberCoord, dite_eq_left h]
  obtain ⟨ω, h₁, h₂⟩ := mk_eq_mk_iff.1 h.choose_spec.symm
  have hω : ω = 0 := Subtype.ext (by simpa using h₁)
  simpa [hω] using h₂

omit [DiscreteTopology L] in
private theorem mk_fiberCoord {z : ℂ} {x : FlatLine ψ}
    (hx : proj x = Quotient.mk (AddAction.orbitRel L ℂ) z) :
    Quotient.mk _ (z, fiberCoord z x) = x := by
  obtain ⟨⟨z', v'⟩, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨γ, hγ⟩ : ∃ γ : L, (γ : ℂ) = z' - z :=
    ⟨⟨_, L.orbitRelQuotient_mk_eq_mk_iff.1 hx⟩, rfl⟩
  have h : ∃ v, (Quotient.mk _ (z', v') : FlatLine ψ) = Quotient.mk _ (z, v) := by
    refine ⟨(ψ γ : ℂ)⁻¹ * v', ?_⟩
    rw [← mk_add_mul z _ γ, mul_inv_cancel_left₀ (Circle.coe_ne_zero _), hγ, add_sub_cancel]
  rw [fiberCoord, dite_eq_left h]
  exact h.choose_spec.symm

omit [DiscreteTopology L] in
private theorem fiberCoord_add_mk (z v : ℂ) (ω : L) :
    fiberCoord (z + ω) (Quotient.mk _ (z, v) : FlatLine ψ) = ψ ω * v := by
  rw [← mk_add_mul z v ω, fiberCoord_mk]

omit [DiscreteTopology L] in
/-- Moving the lift of the base point by a lattice vector `ω` multiplies the fibre coordinate by the
holonomy `ψ ω`. -/
private theorem fiberCoord_add {z : ℂ} {x : FlatLine ψ}
    (hx : proj x = Quotient.mk (AddAction.orbitRel L ℂ) z) (ω : L) :
    fiberCoord (z + ω) x = ψ ω * fiberCoord z x := by
  conv_lhs => rw [← mk_fiberCoord hx]
  rw [fiberCoord_add_mk]

/-- **The fibre coordinate is holomorphic over a chart of the torus.** Let `u` be a map into the
flat line, holomorphic at `x`, and let `e` be a chart of the torus whose source contains the base
point of `u x`. Then the fibre coordinate of `u` over the lift `e (proj (u x'))` of the base point
is holomorphic at `x`: near `x` it is `ψ ω` times the second coordinate of a holomorphic lift of
`u` to `ℂ × ℂ`, for a fixed lattice vector `ω`. -/
private theorem mdifferentiableAt_fiberCoord {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → FlatLine ψ} {x : X} (hu : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u x)
    {e : OpenPartialHomeomorph (AddAction.orbitRel.Quotient L ℂ) ℂ}
    (he : e ∈ atlas ℂ (AddAction.orbitRel.Quotient L ℂ)) (hx : proj (u x) ∈ e.source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x' ↦ fiberCoord (e (proj (u x'))) (u x')) x := by
  -- A holomorphic lift `c ∘ u` of `u` near `x`, through the chart `c` of the flat line at `u x`.
  set c := chartAt (ℂ × ℂ) (u x)
  have hlift : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) (fun x' ↦ c (u x')) x :=
    (mdifferentiableAt_atlas (chart_mem_atlas _ _) (mem_chart_source _ _)).comp x hu
  have hmk : ∀ᶠ x' in 𝓝 x, Quotient.mk _ (c (u x')) = u x' :=
    (hu.continuousAt.eventually_mem (c.open_source.mem_nhds (mem_chart_source _ _))).mono
      fun x' h ↦ addQuotientMk_apply_of_mem_atlas_addQuotient (chart_mem_atlas _ _) h
  have hproj : ContinuousAt (fun x' ↦ proj (u x')) x :=
    (contMDiff_proj ⊤).continuous.continuousAt.comp hu.continuousAt
  have hsrc : ∀ᶠ x' in 𝓝 x, proj (u x') ∈ e.source :=
    hproj.preimage_mem_nhds (e.open_source.mem_nhds hx)
  -- The lift `e (proj (u x'))` of the base point differs from `(c (u x')).1` by a lattice vector,
  -- constant near `x`.
  have hδ : ∀ᶠ x' in 𝓝 x, e (proj (u x')) - (c (u x')).1 ∈ L := by
    filter_upwards [hmk, hsrc] with x' h₁ h₂
    have h₄ : proj (u x') = Quotient.mk _ (c (u x')).1 := by conv_lhs => rw [← h₁, proj_mk]
    rw [h₄] at h₂ ⊢
    exact L.orbitRelQuotient_mk_eq_mk_iff.1
      (addQuotientMk_apply_of_mem_atlas_addQuotient he h₂)
  have hδc : ContinuousAt (fun x' ↦ e (proj (u x')) - (c (u x')).1) x :=
    (ContinuousAt.comp (f := fun x' ↦ proj (u x')) (e.continuousAt hx) hproj).sub
      hlift.continuousAt.fst
  obtain ⟨ω, hω⟩ : ∃ ω : L, (ω : ℂ) = e (proj (u x)) - (c (u x)).1 := ⟨⟨_, hδ.self_of_nhds⟩, rfl⟩
  have heq : (fun x' ↦ fiberCoord (e (proj (u x'))) (u x')) =ᶠ[𝓝 x]
      fun x' ↦ (ψ ω : ℂ) * (c (u x')).2 := by
    filter_upwards [hmk, hδc.tendsto.eventually_eq_of_isDiscrete hδ.self_of_nhds hδ
      (isDiscrete_iff_discreteTopology.2 (inferInstanceAs (DiscreteTopology L)))] with x' h₁ h₂
    rw [← hω, sub_eq_iff_eq_add'] at h₂
    generalize c (u x') = p at h₁ h₂ ⊢
    rw [h₂, ← h₁, fiberCoord_add_mk]
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact (DifferentiableAt.mdifferentiableAt ((differentiableAt_const _).mul
    differentiableAt_snd)).comp (f := fun x' ↦ c (u x')) (g := fun p : ℂ × ℂ ↦ (ψ ω : ℂ) * p.2)
    x hlift

/-! ### Compact holomorphic curves lie on the zero section -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] {u : X → FlatLine ψ}

omit [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X] [ConnectedSpace X] in
private theorem mdifferentiable_proj_comp (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun x ↦ proj (u x) := fun x ↦
  ((contMDiff_proj ⊤).mdifferentiable (by simp) _).comp x (hu x)

omit [T2Space X] in
/-- A nonconstant holomorphic map from a compact connected Riemann surface to the flat line has a
projection to the torus which is constant near no point: otherwise the projection is constant,
the fibre coordinate of `u` over a fixed lift of its value is a holomorphic function on the compact
surface `X`, hence constant, and so is `u`. -/
private theorem not_eventuallyConst_proj_comp (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u)
    (hne : ∃ x x', u x ≠ u x') (x₁ : X) : ¬EventuallyConst (fun x ↦ proj (u x)) (𝓝 x₁) := by
  intro hx₁
  have hconst : ∀ x', proj (u x') = proj (u x₁) := RiemannSurface.apply_eq_of_eventuallyConst
    (mdifferentiable_proj_comp hu) hx₁
  set e := chartAt ℂ (proj (u x₁))
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun x' ↦ fiberCoord (e (proj (u x'))) (u x') := fun x' ↦
    mdifferentiableAt_fiberCoord (hu x') (chart_mem_atlas _ _)
      (mem_of_eq_of_mem (hconst x') (mem_chart_source ℂ _))
  have hmk : ∀ x', Quotient.mk _ (e (proj (u x₁)), fiberCoord (e (proj (u x'))) (u x')) = u x' :=
    fun x' ↦ by
      rw [hconst x']
      exact mk_fiberCoord ((hconst x').trans (addQuotientMk_chartAt_self _).symm)
  obtain ⟨x, x', hxx'⟩ := hne
  exact hxx' (by rw [← hmk x, ← hmk x', hg.apply_eq_of_compactSpace x x'])

/-- The `j`-th elementary symmetric function of the fibre coordinates over `z` of the points of `u`
lying over `[z]`, counted with the local multiplicities of the projection of `u` to the torus. -/
private def fiberEsymm (u : X → FlatLine ψ) (j : ℕ) (z : ℂ) : ℂ :=
  ((RiemannSurface.fiberMultiset (fun x ↦ proj (u x)) (Quotient.mk _ z)).map
    fun x ↦ fiberCoord z (u x)).esymm j

omit [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X] [ConnectedSpace X] in
/-- The symmetric functions of the fibre coordinates are quasi-periodic with multiplier `ψ ^ j`:
they are holomorphic sections of the `j`-th power of the flat line. -/
private theorem fiberEsymm_add (hfin : ∀ y, ((fun x ↦ proj (u x)) ⁻¹' {y}).Finite) (j : ℕ)
    (z : ℂ) (ω : L) : fiberEsymm u j (z + ω) = (ψ ω : ℂ) ^ j * fiberEsymm u j z := by
  have hz : (Quotient.mk (AddAction.orbitRel L ℂ) (z + ω)) = Quotient.mk _ z :=
    L.orbitRelQuotient_mk_eq_mk_iff.2 (by simp)
  rw [fiberEsymm, fiberEsymm, hz, ← smul_eq_mul, Multiset.pow_smul_esymm, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x hx ↦ ?_
  exact fiberCoord_add ((RiemannSurface.mem_fiberMultiset (hfin _)).1 hx).1 ω

/-- The symmetric functions of the fibre coordinates are entire. Near the coordinate of a chart of
the torus at `[z₀]`, they are the elementary symmetric functions of a holomorphic function along the
fibres of the projection of `u`, which are holomorphic across branch values; the coordinate is a
translate of `z₀` by a lattice vector, and quasi-periodicity moves the conclusion to `z₀`. -/
private theorem differentiable_fiberEsymm (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u)
    (hne : ∃ x x', u x ≠ u x') (j : ℕ) : Differentiable ℂ (fiberEsymm u j) := by
  intro z₀
  have hf := mdifferentiable_proj_comp hu
  have hnc := not_eventuallyConst_proj_comp hu hne
  have hfin := RiemannSurface.finite_preimage_singleton hf hnc
  set e := chartAt ℂ (Quotient.mk (AddAction.orbitRel L ℂ) z₀)
  have hg : ∀ x ∈ (fun x ↦ proj (u x)) ⁻¹' {Quotient.mk _ z₀}, ∀ᶠ x' in 𝓝 x,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x' ↦ fiberCoord (e (proj (u x'))) (u x')) x' := by
    intro x hx
    filter_upwards [(hf x).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds
      (mem_of_eq_of_mem hx (mem_chart_source _ _)))] with x' hx'
    exact mdifferentiableAt_fiberCoord (hu x') (chart_mem_atlas _ _) hx'
  have heq : (fun w ↦ ((RiemannSurface.fiberMultiset (fun x ↦ proj (u x)) (e.symm w)).map
      fun x' ↦ fiberCoord (e (proj (u x'))) (u x')).esymm j) =ᶠ[𝓝 (e (Quotient.mk _ z₀))]
      fiberEsymm u j := by
    filter_upwards [e.open_target.mem_nhds (e.map_source (mem_chart_source _ _))] with w hw
    rw [chartAt_addQuotient_symm_eq_addQuotientMk _ hw, fiberEsymm]
    congr 1
    refine Multiset.map_congr rfl fun x' hx' ↦ ?_
    rw [((RiemannSurface.mem_fiberMultiset (hfin _)).1 hx').1,
      ← chartAt_addQuotient_symm_eq_addQuotientMk _ hw, e.right_inv hw]
  -- The coordinate of the chart is a translate `z₀ + γ` of `z₀` by a lattice vector.
  obtain ⟨γ, hγ⟩ : ∃ γ : L, (γ : ℂ) = e (Quotient.mk _ z₀) - z₀ :=
    ⟨⟨_, L.orbitRelQuotient_mk_eq_mk_iff.1 (addQuotientMk_chartAt_self _)⟩, rfl⟩
  have hd : DifferentiableAt ℂ (fiberEsymm u j) (z₀ + γ) := by
    rw [hγ, add_sub_cancel]
    exact (RiemannSurface.analyticAt_esymm_map_fiberMultiset hf hnc
      (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source _ _) hg j).congr heq
      |>.differentiableAt
  have hE : fiberEsymm u j = fun z ↦ ((ψ γ : ℂ) ^ j)⁻¹ * fiberEsymm u j (z + γ) :=
    funext fun z ↦ by
      rw [fiberEsymm_add hfin, inv_mul_cancel_left₀ (pow_ne_zero _ (Circle.coe_ne_zero _))]
  rw [hE]
  exact (differentiableAt_const _).mul (DifferentiableAt.comp (g := fiberEsymm u j)
    (f := fun z ↦ z + (γ : ℂ)) z₀ hd (differentiableAt_id.add_const _))

/-- **A compact holomorphic curve in a flat line of infinite order lies on the zero section.** Let
`ψ` be a unitary character of a full lattice `L` of infinite order, so that no positive power of
the flat line `N` of `ψ` over the torus `ℂ / L` is trivial; this holds as soon as one holonomy
`ψ ω₀` has infinite order. Let `u : X → N` be a nonconstant holomorphic map from a compact
connected Riemann surface. Then every point of `u` lies on the zero section `{[(z, 0)]}`. -/
theorem exists_eq_mk_zero_of_mdifferentiable [IsZLattice ℝ L]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) u) (hne : ∃ x x', u x ≠ u x') (hψ : ¬IsOfFinOrder ψ)
    (x : X) :
    ∃ z : ℂ, u x = Quotient.mk _ (z, 0) := by
  have hf := mdifferentiable_proj_comp hu
  have hnc := not_eventuallyConst_proj_comp hu hne
  have hfin := RiemannSurface.finite_preimage_singleton hf hnc
  -- A flat line with no trivial positive power has no nonzero holomorphic section.
  have hzero : ∀ j, j ≠ 0 → fiberEsymm u j = 0 := fun j hj ↦
    (differentiable_fiberEsymm hu hne j).eq_zero_of_add_eq_smul (ψ := ψ ^ j)
      (fun h ↦ hψ (isOfFinOrder_iff_pow_eq_one.2 ⟨j, Nat.pos_of_ne_zero hj, h⟩))
      fun z ω ↦ by simpa using fiberEsymm_add hfin j z ω
  obtain ⟨z, hz⟩ := Quotient.mk_surjective (proj (u x))
  have hmem : x ∈ RiemannSurface.fiberMultiset (fun x ↦ proj (u x)) (Quotient.mk _ z) :=
    (RiemannSurface.mem_fiberMultiset (hfin _)).2 ⟨hz.symm,
      (RiemannSurface.localMultiplicity_pos_iff (.of_forall hf)).2 (hnc x)⟩
  have h0 := Multiset.eq_zero_of_mem_of_forall_esymm_eq_zero
    (fun j hj ↦ congrFun (hzero j hj) z)
    (Multiset.mem_map_of_mem (fun x' ↦ fiberCoord z (u x')) hmem)
  exact ⟨z, by rw [← h0]; exact (mk_fiberCoord hz.symm).symm⟩

end FlatLine

end TauCeti
