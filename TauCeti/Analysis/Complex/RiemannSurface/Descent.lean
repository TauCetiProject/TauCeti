/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.GermFactorization
import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
import TauCeti.Analysis.Complex.RiemannSurface.OpenMapping
import TauCeti.Analysis.Complex.RiemannSurface.Ramification
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Holomorphic descent along finite holomorphic maps

Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface to a connected one
(`TauCeti.RiemannSurface.FiniteHolomorphicMap`). This file shows that `f` behaves like a quotient
map in the holomorphic category, and records how germs of maps behave under precomposition with
`f` at its unramified points.

* **Descent.** A holomorphic map `g : X → Z` to a Riemann surface which is constant on the fibres
  of `f` is `h ∘ f` for a holomorphic `h : Y → Z`
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.exists_mdifferentiable_comp_eq`). The map `h` is
  continuous because `f` is an open surjection, hence a quotient map. Near a point `f x` at which
  `f` is a local biholomorphism, `h` is `g` composed with a local inverse of `f`, and the finitely
  many remaining points, images of ramification points, are removable singularities.
* **Fibres agreeing off a finite set.** If a continuous map `g` to a Hausdorff space is constant
  on the fibres of `f` as soon as these fibres are taken off a finite set, then it is constant on
  all fibres of `f`
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.apply_eq_of_apply_eq_of_finite`). Near any two
  points of a fibre, the open mapping theorem provides pairs of points with the same image that
  avoid the finite set.
* **Maps with the same fibres.** Two finite holomorphic maps `f₁ : X → Y₁` and `f₂ : X → Y₂` with
  the same fibres differ by exactly one biholomorphism `a : Y₁ → Y₂`, with `a ∘ f₁ = f₂`
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.existsUnique_biholomorph_comp_eq`).
* **Germs at unramified points.** If `π : X → Y` is a local biholomorphism at `a` and at `b`, the
  germ of `v ∘ π` at `b` factors holomorphically through its germ at `a` exactly when the germ of
  `v` at `π b` factors through its germ at `π a`
  (`TauCeti.RiemannSurface.germFactorsThrough_comp_iff`): a holomorphic change of coordinate
  upstairs is pushed down through local inverses of `π`, and conversely lifted through them.

These are the steps in which the factorization of a closed pseudoholomorphic curve through a
simple curve (McDuff–Salamon, Proposition 2.5.1) is compared across two branched covers.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §§2 and 4.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 2.5.1.
-/

public section

open Filter Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

/-! ### Germs under precomposition with a local biholomorphism -/

section Germ

variable {N : Type*} {π : X → Y} {v : Y → N} {a b : X}

/-- **Germs at unramified points.** Let `π : X → Y` be holomorphic near `a` and `b`, with local
multiplicity `1` at both points, so that it is a local biholomorphism there. Then the germ of
`v ∘ π` at `b` factors holomorphically through the germ of `v ∘ π` at `a` exactly when the germ of
`v` at `π b` factors holomorphically through the germ of `v` at `π a`. -/
theorem germFactorsThrough_comp_iff (hπa : ∀ᶠ x in 𝓝 a, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x)
    (hπb : ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x) (ha : localMultiplicity π a = 1)
    (hb : localMultiplicity π b = 1) :
    GermFactorsThrough (v ∘ π) b (v ∘ π) a ↔ GermFactorsThrough v (π b) v (π a) := by
  constructor
  · -- Push the change of coordinate `φ` down through a local inverse `s` of `π` at `b`.
    intro h
    obtain ⟨φ, hφb, hφd, hφu⟩ := germFactorsThrough_iff.1 h
    have hL := (localMultiplicity_eq_one_iff_isLocalDiffeomorphAt hπb).1 hb
    have hsb := hL.localInverse_left_inv hL.localInverse_mem_target
    have hs := hsb ▸ hL.continuousAt_localInverse.tendsto
    have hφ : Tendsto φ (𝓝 b) (𝓝 a) := by
      simpa only [hφb] using hφd.self_of_nhds.continuousAt.tendsto
    have hsd : ∀ᶠ w in 𝓝 (π b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) hL.localInverse w :=
      hL.localInverse_isLocalDiffeomorphAt.eventually.mono fun _ h ↦ h.mdifferentiableAt one_ne_zero
    refine germFactorsThrough_iff.2
      ⟨π ∘ φ ∘ hL.localInverse, by simp only [comp_apply, hsb, hφb], ?_, ?_⟩
    · filter_upwards [hsd, hs.eventually hφd, hs.eventually (hφ.eventually hπa)]
        with w hsw hφw hπw
      exact hπw.comp w (hφw.comp w hsw)
    · filter_upwards [hL.localInverse_eventuallyEq_right, hs.eventually hφu] with w hw hφw
      simp only [comp_apply, id_eq] at hw hφw ⊢
      rw [← hφw, hw]
  · -- Lift the change of coordinate `ψ` through a local inverse `s` of `π` at `a`.
    intro h
    obtain ⟨ψ, hψb, hψd, hψv⟩ := germFactorsThrough_iff.1 h
    have hL := (localMultiplicity_eq_one_iff_isLocalDiffeomorphAt hπa).1 ha
    have hπ : Tendsto π (𝓝 b) (𝓝 (π b)) := hπb.self_of_nhds.continuousAt.tendsto
    have hψ : Tendsto ψ (𝓝 (π b)) (𝓝 (π a)) := by
      simpa only [hψb] using hψd.self_of_nhds.continuousAt.tendsto
    have hsd : ∀ᶠ w in 𝓝 (π a), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) hL.localInverse w :=
      hL.localInverse_isLocalDiffeomorphAt.eventually.mono fun _ h ↦ h.mdifferentiableAt one_ne_zero
    refine germFactorsThrough_iff.2 ⟨hL.localInverse ∘ ψ ∘ π, ?_, ?_, ?_⟩
    · simp only [comp_apply, hψb]
      exact hL.localInverse_left_inv hL.localInverse_mem_target
    · filter_upwards [hπb, hπ.eventually hψd, hπ.eventually (hψ.eventually hsd)]
        with x hπx hψx hsx
      exact hsx.comp x (hψx.comp x hπx)
    · filter_upwards [hπ.eventually hψv, hπ.eventually (hψ.eventually
        hL.localInverse_eventuallyEq_right)] with x hψx hsx
      simp only [comp_apply, id_eq] at hψx hsx ⊢
      rw [hsx, ← hψx]

end Germ

/-! ### Descent along finite holomorphic maps -/

namespace FiniteHolomorphicMap

variable (f : FiniteHolomorphicMap X Y)

/-- **Holomorphic descent.** Let `f : X → Y` be a finite holomorphic map from a compact Riemann
surface to a connected one. A holomorphic map `g : X → Z` to a Riemann surface which takes the same
value at any two points with the same image under `f` is `h ∘ f` for a holomorphic map
`h : Y → Z`. -/
theorem exists_mdifferentiable_comp_eq [CompactSpace X] [T2Space Y] [PreconnectedSpace Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) 1 Z] {g : X → Z}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hfg : ∀ x x', f x = f x' → g x = g x') :
    ∃ h : Y → Z, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h ∧ h ∘ f = g := by
  set h : Y → Z := g ∘ surjInv f.surjective
  have hhf : h ∘ f = g := funext fun x ↦ hfg _ _ (surjInv_eq f.surjective (f x))
  refine ⟨h, ?_, hhf⟩
  -- `f` is an open surjection, hence a quotient map, so `h` is continuous.
  have hq : IsQuotientMap f :=
    (isOpenMap_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst).isQuotientMap
      f.holomorphic.continuous f.surjective
  have hc : Continuous h := hq.continuous_iff.2 (hhf ▸ hg.continuous)
  -- Off the images of the finitely many ramification points, `h` is `g` composed with a local
  -- inverse of `f`; the remaining points are removable singularities.
  refine f.finite_branchValues.mdifferentiable_of_continuous_of_compl hc fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hL := (localMultiplicity_eq_one_iff_isLocalDiffeomorphAt
    (.of_forall fun z ↦ f.holomorphic z)).1 ((f.notMem_branchValues_iff _).1 hy x rfl)
  exact ((hL.mdifferentiableAt_comp_iff one_ne_zero).1 (hhf ▸ hg x)).mdifferentiableWithinAt

/-- **Fibres agreeing off a finite set.** Let `f : X → Y` be a finite holomorphic map. If a
continuous map `g` to a Hausdorff space takes the same value at any two points outside a finite set
`F` which have the same image under `f`, then it takes the same value at any two points with the
same image under `f`. -/
theorem apply_eq_of_apply_eq_of_finite {W : Type*} [TopologicalSpace W] [T2Space W] {g : X → W}
    (hg : Continuous g) {F : Set X} (hF : F.Finite)
    (hfg : ∀ x ∉ F, ∀ x' ∉ F, f x = f x' → g x = g x') {x x' : X} (hxx' : f x = f x') :
    g x = g x' := by
  have := ChartedSpace.perfectSpace (H := ℂ) (X := X)
  have := ChartedSpace.t1Space ℂ X
  -- The points whose fibre meets `F` form a finite set `F'`.
  have hF' : (f ⁻¹' (f '' F)).Finite := (hF.image f).preimage' fun y _ ↦ f.finite_fiber y
  by_contra hne
  obtain ⟨A, B, hA, hB, hxA, hx'B, hAB⟩ := t2_separation hne
  -- Near `x` there is a point `z ∉ F'` whose fibre meets the neighbourhood `g ⁻¹' B` of `x'`.
  have hV : f '' (g ⁻¹' B) ∈ 𝓝 (f x) := hxx' ▸ nhds_le_map_nhds_of_not_eventuallyConst
    (.of_forall fun z ↦ f.holomorphic z) (f.not_eventuallyConst x')
    (image_mem_map (hg.continuousAt.preimage_mem_nhds (hB.mem_nhds hx'B)))
  have hW : g ⁻¹' A ∩ f ⁻¹' (f '' (g ⁻¹' B)) ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (inter_mem (hg.continuousAt.preimage_mem_nhds (hA.mem_nhds hxA))
      (f.holomorphic.continuous.continuousAt.preimage_mem_nhds hV))
  obtain ⟨z, ⟨hzA, hzV⟩, hzF⟩ := Filter.nonempty_of_mem
    (inter_mem hW (mem_codiscrete_iff_forall_mem_nhdsNE.1 hF'.compl_mem_codiscrete x))
  obtain ⟨z', hz'B, hz'z⟩ := mem_preimage.1 hzV
  rw [mem_compl_iff, mem_preimage, mem_image, not_exists] at hzF
  have hz : z ∉ F := fun h ↦ hzF z ⟨h, rfl⟩
  have hz' : z' ∉ F := fun h ↦ hzF z' ⟨h, hz'z⟩
  exact hAB.ne_of_mem hzA hz'B (hfg z hz z' hz' hz'z.symm)

/-- **Finite holomorphic maps with the same fibres differ by a biholomorphism.** Let
`f₁ : X → Y₁` and `f₂ : X → Y₂` be finite holomorphic maps from a compact Riemann surface to
connected ones. If two points have the same image under `f₁` exactly when they have the same image
under `f₂`, there is exactly one biholomorphism `a : Y₁ → Y₂` with `a ∘ f₁ = f₂`. -/
theorem existsUnique_biholomorph_comp_eq [CompactSpace X] {Y₁ Y₂ : Type*} [TopologicalSpace Y₁]
    [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) 1 Y₁] [T2Space Y₁] [PreconnectedSpace Y₁]
    [TopologicalSpace Y₂] [ChartedSpace ℂ Y₂] [IsManifold 𝓘(ℂ) 1 Y₂] [T2Space Y₂]
    [PreconnectedSpace Y₂] (f₁ : FiniteHolomorphicMap X Y₁) (f₂ : FiniteHolomorphicMap X Y₂)
    (h : ∀ x x', f₁ x = f₁ x' ↔ f₂ x = f₂ x') :
    ∃! a : Y₁ ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y₂, a ∘ f₁ = f₂ := by
  obtain ⟨a, ha, haf⟩ := f₁.exists_mdifferentiable_comp_eq f₂.holomorphic fun x x' ↦ (h x x').1
  obtain ⟨b, hb, hbf⟩ := f₂.exists_mdifferentiable_comp_eq f₁.holomorphic fun x x' ↦ (h x x').2
  have hba : LeftInverse b a := fun y ↦ by
    obtain ⟨x, rfl⟩ := f₁.surjective y
    rw [← comp_apply (f := a), haf, ← comp_apply (f := b), hbf]
  have hab : RightInverse b a := fun y ↦ by
    obtain ⟨x, rfl⟩ := f₂.surjective y
    rw [← comp_apply (f := b), hbf, ← comp_apply (f := a), haf]
  refine ⟨{ toEquiv := ⟨a, b, hba, hab⟩
            contMDiff_toFun := ha.contMDiff
            contMDiff_invFun := hb.contMDiff }, haf, fun a' ha' ↦ ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := f₁.surjective y
  exact (congrFun ha' x).trans (congrFun haf x).symm

end FiniteHolomorphicMap

end TauCeti.RiemannSurface

end
