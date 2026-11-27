/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Descent
public import TauCeti.Analysis.Complex.RiemannSurface.SomewhereInjective
public import TauCeti.Geometry.Symplectic.JHolomorphic.BranchDegree
import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
import TauCeti.Analysis.Complex.RiemannSurface.Ramification

/-!
# Uniqueness of the simple curve underlying a closed pseudoholomorphic curve

Let `N` be a Hausdorff manifold with a smooth almost complex structure `J`. A nonconstant closed
pseudoholomorphic curve `u : S → N` factors as `u = v ∘ π` through a finite holomorphic map
`π : S → S'` onto a compact connected Riemann surface and a somewhere injective pseudoholomorphic
curve `v : S' → N` (McDuff–Salamon, Proposition 2.5.1). This file proves that such a factorization
is unique up to a unique biholomorphism of the factor surfaces
(`TauCeti.existsUnique_biholomorph_of_isSomewhereInjective`): if
`v₁ ∘ π₁ = v₂ ∘ π₂`, with `v₁` and `v₂` somewhere injective, there is exactly one biholomorphism
`a : S₁ → S₂` with `a ∘ π₁ = π₂` and `v₂ ∘ a = v₁`. So the simple curve underlying `u`, its genus
and the degree of the cover are determined by `u`. Nothing is assumed of `J` beyond smoothness,
and the curves `vᵢ` need only be of class `C²`.

The proof compares the fibres of `π₁` and `π₂` through the germs of `u`.

* **Somewhere injective curves have no coincident branches.** Let `v : S' → N` be a `C²`
  pseudoholomorphic curve on a compact connected Riemann surface, with an injective point `w₀`.
  Off the finite set `B = v⁻¹(v(Crit v))`, the number of points `w` such that the branch of `v` at
  `w'` factors holomorphically through the branch of `v` at `w` is the same for every `w'`
  (`TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq`). At `w₀` this number is `1`, so
  for `w' ∉ B` the branch of `v` at `w'` factors through the branch at `w` only for `w = w'`
  (`TauCeti.IsSomewhereInjective.germFactorsThrough_iff`).
* **Branches of a multiple cover.** For `u = v ∘ π`, at two points `z`, `z'` of `S` where `π` is
  unramified and with `π z' ∉ B`, the branch of `u` at `z'` factors holomorphically through its
  branch at `z` exactly when `π z' = π z`
  (`TauCeti.IsSomewhereInjective.germFactorsThrough_comp_iff`), by pushing changes of coordinate
  down through local inverses of `π` (`TauCeti.RiemannSurface.germFactorsThrough_comp_iff`).
* **The fibres coincide.** Off a finite subset of `S`, the fibres of `π₁` and of `π₂` are therefore
  both described by the germs of `u`, so they coincide; by the open mapping theorem they coincide
  everywhere (`TauCeti.RiemannSurface.FiniteHolomorphicMap.apply_eq_of_apply_eq_of_finite`).
  Two finite holomorphic maps with the same fibres differ by a unique biholomorphism
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.existsUnique_biholomorph_comp_eq`).

## Main results

* `TauCeti.IsSomewhereInjective.germFactorsThrough_iff`: a somewhere injective curve has no
  coincident branches off the preimage of its critical values.
* `TauCeti.IsSomewhereInjective.germFactorsThrough_comp_iff`: the coincident branches of
  `v ∘ π` at unramified points lie over the same point of the somewhere injective curve `v`.
* `TauCeti.existsUnique_biholomorph_of_isSomewhereInjective`: uniqueness of the factorization of
  a closed pseudoholomorphic curve through a somewhere injective one.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 2.5.1.
* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*, arXiv:1011.1690,
  Proposition 4.3.
-/

public section

open Function Set
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure RiemannSurface

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {J : SmoothAlmostComplexStructure I N}
  {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  [CompactSpace S] [ConnectedSpace S] [T2Space S] {v : S → N}

/-- **A somewhere injective curve has no coincident branches.** Let `v` be a `C²`
pseudoholomorphic, somewhere injective curve on a compact connected Riemann surface, and let `w'`
be a point outside the preimage `v⁻¹(v(Crit v))` of the critical values. Then the branch of `v` at
`w'` factors holomorphically through the branch of `v` at `w` only for `w = w'`. -/
theorem IsSomewhereInjective.germFactorsThrough_iff (hv : ContMDiff 𝓘(ℝ, ℂ) I 2 v)
    (hJv : IsPseudoholomorphic (ofComplexManifold ℂ S) J v)
    (hi : IsSomewhereInjective 𝓘(ℝ, ℂ) I v) {w w' : S}
    (hw' : w' ∉ criticalValuePreimage I v) :
    GermFactorsThrough v w' v w ↔ w' = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ .refl v w'⟩
  obtain ⟨w₀, hw₀⟩ := isSomewhereInjective_iff.1 hi
  obtain ⟨d, -, hd⟩ := exists_pos_forall_ncard_setOf_germFactorsThrough_eq hv hJv hi.exists_apply_ne
  -- The injective point `w₀` is immersed and alone in its fibre, so it lies outside the preimage of
  -- the critical values and only `w₀` itself is related to it: the common count is `1`.
  have hw₀B : w₀ ∉ criticalValuePreimage I v := by
    rw [mem_criticalValuePreimage]
    rintro ⟨c, hc, hcv⟩
    rw [hw₀.eq_of_apply_eq hcv] at hc
    exact (hJv.isPseudoholomorphicAt w₀).injective_mfderiv_iff_ne_zero.1 hw₀.injective_mfderiv hc
  have h₀ : {ζ | GermFactorsThrough v w₀ v ζ} = {w₀} := by
    ext ζ
    rw [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun h ↦ hw₀.eq_of_apply_eq h.apply_eq.symm, fun h ↦ h ▸ .refl v w₀⟩
  have hd₁ : d = 1 := by rw [← hd w₀ hw₀B, h₀, ncard_singleton]
  -- So the class of `w'`, which contains `w'` and `w`, is a singleton.
  obtain ⟨c, hc⟩ := ncard_eq_one.1 ((hd w' hw').trans hd₁)
  have hw'c : w' ∈ ({c} : Set S) := hc ▸ GermFactorsThrough.refl v w'
  have hwc : w ∈ ({c} : Set S) := hc ▸ h
  exact (mem_singleton_iff.1 hw'c).trans (mem_singleton_iff.1 hwc).symm

/-- **Coincident branches of a multiple cover lie over one point.** Let `v` be a `C²`
pseudoholomorphic, somewhere injective curve on a compact connected Riemann surface and `π` a
map to it, holomorphic near `z` and `z'` and unramified there, with `π z'` outside the preimage
of the critical values of `v`. Then the branch of `v ∘ π` at `z'` factors holomorphically
through its branch at `z` exactly when `π z' = π z`. -/
theorem IsSomewhereInjective.germFactorsThrough_comp_iff (hv : ContMDiff 𝓘(ℝ, ℂ) I 2 v)
    (hJv : IsPseudoholomorphic (ofComplexManifold ℂ S) J v)
    (hi : IsSomewhereInjective 𝓘(ℝ, ℂ) I v) {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {π : X → S} {z z' : X}
    (hπz : ∀ᶠ x in nhds z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x)
    (hπz' : ∀ᶠ x in nhds z', MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x)
    (hz : localMultiplicity π z = 1) (hz' : localMultiplicity π z' = 1)
    (hz'B : π z' ∉ criticalValuePreimage I v) :
    GermFactorsThrough (v ∘ π) z' (v ∘ π) z ↔ π z' = π z :=
  (RiemannSurface.germFactorsThrough_comp_iff hπz hπz' hz hz').trans
    (hi.germFactorsThrough_iff hv hJv hz'B)

omit [IsManifold 𝓘(ℂ) ∞ S] [ConnectedSpace S] [T2Space S] in
/-- **Uniqueness of the simple curve underlying a closed pseudoholomorphic curve.** Let `S` be a
compact Riemann surface, `π₁ : S → S₁` and `π₂ : S → S₂` finite holomorphic maps onto compact
connected Riemann surfaces, and `v₁ : S₁ → N`, `v₂ : S₂ → N` somewhere injective `C²`
pseudoholomorphic curves with `v₁ ∘ π₁ = v₂ ∘ π₂`. Then there is exactly one biholomorphism
`a : S₁ → S₂` with `a ∘ π₁ = π₂` and `v₂ ∘ a = v₁`. -/
theorem existsUnique_biholomorph_of_isSomewhereInjective {S₁ S₂ : Type*} [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ∞ S₁] [ConnectedSpace S₁] [T2Space S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ∞ S₂] [ConnectedSpace S₂]
    [T2Space S₂] [IsManifold 𝓘(ℂ) 1 S] (π₁ : FiniteHolomorphicMap S S₁)
    (π₂ : FiniteHolomorphicMap S S₂) {v₁ : S₁ → N} {v₂ : S₂ → N} (hv₁ : ContMDiff 𝓘(ℝ, ℂ) I 2 v₁)
    (hv₂ : ContMDiff 𝓘(ℝ, ℂ) I 2 v₂) (hJv₁ : IsPseudoholomorphic (ofComplexManifold ℂ S₁) J v₁)
    (hJv₂ : IsPseudoholomorphic (ofComplexManifold ℂ S₂) J v₂)
    (hi₁ : IsSomewhereInjective 𝓘(ℝ, ℂ) I v₁) (hi₂ : IsSomewhereInjective 𝓘(ℝ, ℂ) I v₂)
    (h : v₁ ∘ π₁ = v₂ ∘ π₂) :
    ∃! a : S₁ ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ S₂, a ∘ π₁ = π₂ ∧ v₂ ∘ a = v₁ := by
  have := π₁.compactSpace_codomain
  have := π₂.compactSpace_codomain
  -- Off a finite set `F`, both covers are unramified and avoid the preimages of the critical
  -- values of the two curves.
  set B₁ := criticalValuePreimage I v₁
  set B₂ := criticalValuePreimage I v₂
  set F := π₁ ⁻¹' (π₁.branchValues ∪ B₁) ∪ π₂ ⁻¹' (π₂.branchValues ∪ B₂)
  have hF : F.Finite :=
    ((π₁.finite_branchValues.union
      (finite_criticalValuePreimage (hv₁.of_le one_le_two)
        hJv₁ hi₁.exists_apply_ne)).preimage' fun y _ ↦ π₁.finite_fiber y).union
    ((π₂.finite_branchValues.union
      (finite_criticalValuePreimage (hv₂.of_le one_le_two)
        hJv₂ hi₂.exists_apply_ne)).preimage' fun y _ ↦ π₂.finite_fiber y)
  have hlm₁ : ∀ z ∉ F, localMultiplicity π₁ z = 1 := fun z hz ↦
    (π₁.notMem_branchValues_iff _).1 (fun h ↦ hz (.inl (.inl h))) z rfl
  have hlm₂ : ∀ z ∉ F, localMultiplicity π₂ z = 1 := fun z hz ↦
    (π₂.notMem_branchValues_iff _).1 (fun h ↦ hz (.inr (.inl h))) z rfl
  -- There, the fibres of both covers are the classes of coincident branches of `v₁ ∘ π₁`.
  have hfib : ∀ z ∉ F, ∀ z' ∉ F, π₁ z = π₁ z' ↔ π₂ z = π₂ z' := fun z hz z' hz' ↦ by
    rw [eq_comm (a := π₁ z), eq_comm (a := π₂ z),
      ← hi₁.germFactorsThrough_comp_iff hv₁ hJv₁ (.of_forall fun x ↦ π₁.holomorphic x)
        (.of_forall fun x ↦ π₁.holomorphic x) (hlm₁ z hz) (hlm₁ z' hz')
        fun h ↦ hz' (.inl (.inr h)), h,
      hi₂.germFactorsThrough_comp_iff hv₂ hJv₂ (.of_forall fun x ↦ π₂.holomorphic x)
        (.of_forall fun x ↦ π₂.holomorphic x) (hlm₂ z hz) (hlm₂ z' hz')
        fun h ↦ hz' (.inr (.inr h))]
  -- By the open mapping theorem the fibres coincide everywhere.
  have hfib' : ∀ z z', π₁ z = π₁ z' ↔ π₂ z = π₂ z' := fun z z' ↦
    ⟨π₁.apply_eq_of_apply_eq_of_finite π₂.holomorphic.continuous hF
      (fun x hx x' hx' ↦ (hfib x hx x' hx').1),
     π₂.apply_eq_of_apply_eq_of_finite π₁.holomorphic.continuous hF
      (fun x hx x' hx' ↦ (hfib x hx x' hx').2)⟩
  obtain ⟨a, ha, huniq⟩ := π₁.existsUnique_biholomorph_comp_eq π₂ hfib'
  refine ⟨a, ⟨ha, funext fun y ↦ ?_⟩, fun a' ha' ↦ huniq a' ha'.1⟩
  obtain ⟨x, rfl⟩ := π₁.surjective y
  rw [comp_apply, ← comp_apply (f := a), ha]
  exact (congrFun h x).symm

end TauCeti

end
