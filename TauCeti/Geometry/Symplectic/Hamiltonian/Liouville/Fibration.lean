/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Fibration
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Submersion

/-!
# The fibres of a regular Lagrangian torus fibration are tori

Let `σ` be a symplectic form on a boundaryless manifold `M` and let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`): a
proper smooth submersion with connected Lagrangian fibres, onto a Hausdorff manifold `B` of
dimension `n`. This file proves that every fibre `π⁻¹(b)` is homeomorphic to the torus
`(ℝ / ℤ)ⁿ` (`IsLagrangianTorusFibration.nonempty_homeomorph_unitAddTorus`), which justifies the
name of the notion.

The proof reduces to the topological Liouville–Arnold theorem for `n` Poisson-commuting functions
(`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`). A smooth map
`κ : B → ℝⁿ` which near `b` is a chart of `B` (localized by a bump function) pulls back to the
family `F = κ ∘ π`. Its components Poisson-commute because the fibres are Lagrangian
(`IsLagrangianFibration.poissonBracket_comp_eq_zero`); `F` is regular along
`π⁻¹(b)` because `dκ_b` is invertible and `π` is a submersion; and since `κ` is injective near `b`,
the connected compact fibre `π⁻¹(b)` is exactly the connected component of the level
`F⁻¹(F x)` through any of its points `x`. These coordinates around a fibre are
`IsLagrangianTorusFibration.exists_coordinates`.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
-/

public section

open Function Set Module
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [FiniteDimensional ℝ F] [IsManifold J ∞ B] in
/-- If a map `κ` on the base is injective near `b`, each point `x` of the fibre over `b` has this
fibre as its connected component in the level `(κ ∘ π)⁻¹(κ (π x))`: the level splits into the
closed sets over `b` and over the complement of a neighbourhood of `b` on which `κ` is
injective. -/
private theorem connectedComponentIn_comp_preimage_eq (h : hσ.IsLagrangianTorusFibration J π)
    {X : Type*} {κ : B → X} {b : B} {W : Set B} (hWo : IsOpen W) (hbW : b ∈ W)
    (hinj : ∀ c ∈ W, κ c = κ b → c = b) {x : M} (hx : x ∈ π ⁻¹' {b}) :
    connectedComponentIn ((κ ∘ π) ⁻¹' {κ (π x)}) x = π ⁻¹' {b} := by
  rw [mem_preimage, mem_singleton_iff] at hx
  refine Subset.antisymm ?_ ((h.isConnected_preimage_singleton b).isPreconnected
    |>.subset_connectedComponentIn (by simp [hx]) fun y hy ↦ ?_)
  · have hcover : connectedComponentIn ((κ ∘ π) ⁻¹' {κ (π x)}) x ⊆ π ⁻¹' {b} ∪ π ⁻¹' Wᶜ := by
      intro y hy
      have hyG : κ (π y) = κ b := by
        simpa only [mem_preimage, mem_singleton_iff, comp_apply, hx] using
          connectedComponentIn_subset _ _ hy
      by_cases hyW : π y ∈ W
      · exact Or.inl (hinj _ hyW hyG)
      · exact Or.inr hyW
    have hdisj : connectedComponentIn ((κ ∘ π) ⁻¹' {κ (π x)}) x ∩
        (π ⁻¹' {b} ∩ π ⁻¹' Wᶜ) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff,
        mem_empty_iff_false, iff_false, not_and, not_not]
      intro _ hyb
      exact hyb ▸ hbW
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
      (π ⁻¹' {b}) (π ⁻¹' Wᶜ) (isClosed_singleton.preimage h.contMDiff.continuous)
      (hWo.isClosed_compl.preimage h.contMDiff.continuous) hcover hdisj with hb | hW
    · exact hb
    · exact absurd (hW (mem_connectedComponentIn (by simp))) (by simpa [hx] using hbW)
  · simp only [mem_preimage, mem_singleton_iff] at hy
    simp [hy, hx]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
/-- **Coordinates around a fibre.** For every `b : B` there are a smooth map
`κ : B → ℝⁿ`, `n = dim B`, whose differential at `b` is a linear isomorphism `e`, such that the
components of `κ ∘ π` are regular along the fibre `π⁻¹(b)`, and this fibre is the connected
component of each of its points `x` in the level `(κ ∘ π)⁻¹(κ (π x))`. For instance, `κ` can be
taken to be a chart of `B` at `b`, localized by a bump function and composed with a linear
isomorphism. -/
theorem exists_coordinates (h : hσ.IsLagrangianTorusFibration J π) (b : B) :
    ∃ (κ : B → Fin (finrank ℝ F) → ℝ) (e : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ)),
      ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ κ ∧
      mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) κ b = (e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∧
      (∀ y ∈ π ⁻¹' {b}, IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (κ ∘ π) y) ∧
      ∀ x ∈ π ⁻¹' {b}, connectedComponentIn ((κ ∘ π) ⁻¹' {κ (π x)}) x = π ⁻¹' {b} := by
  -- A smooth map `κ₀ : B → F` with the germ of the chart at `b`, and coordinates on `F`.
  obtain ⟨κ₀, hκ₀⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := J) b
  let e : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  set κ : B → Fin (finrank ℝ F) → ℝ := fun c ↦ e (κ₀ c)
  have hκ : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) ∞ κ :=
    e.contDiff.comp_contMDiff κ₀.contMDiff
  -- `dκ₀_b` is the derivative of the chart at `b`, the identity.
  have hκ₀b : mfderiv J 𝓘(ℝ, F) κ₀ b = ContinuousLinearMap.id ℝ F := by
    rw [hκ₀.mfderiv_eq, mfderiv_extChartAt_self]
    -- The identity of the tangent space `T_b B` is the identity of its model space `F`.
    rfl
  have hdκ : mfderiv J 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) κ b =
      (e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) := by
    have h1 := mfderiv_comp b e.mdifferentiableAt (κ₀.contMDiff.mdifferentiableAt (by simp))
    rw [hκ₀b, e.mfderiv_eq] at h1
    exact h1
  -- `κ` is injective near `b`: it agrees there with the chart, up to `e`.
  obtain ⟨W, hWsub, hWo, hbW⟩ := mem_nhds_iff.1
    (hκ₀.and (extChartAt_source_mem_nhds (I := J) b))
  have hinj (c : B) (hc : c ∈ W) (hcb : κ c = κ b) : c = b := by
    have h1 := hWsub hc
    have h2 := hWsub hbW
    refine (extChartAt J b).injOn h1.2 h2.2 ?_
    rw [← h1.1, ← h2.1]
    exact e.injective hcb
  have hreg (y : M) (hy : y ∈ π ⁻¹' {b}) :
      IsRegularPoint I 𝓘(ℝ, Fin (finrank ℝ F) → ℝ) (κ ∘ π) y := by
    rw [mem_preimage, mem_singleton_iff] at hy
    -- `κ` is `e ∘ κ₀` by its definition above.
    have hκπ : κ ∘ π = (e : F →L[ℝ] Fin (finrank ℝ F) → ℝ) ∘ (κ₀ ∘ π) :=
      congrArg (· ∘ (κ₀ ∘ π)) (ContinuousLinearEquiv.coe_coe e).symm
    rw [hκπ]
    refine isRegularPoint_iff_surjective_mvfderiv.2 (mvfderiv_comp_surjective ?_ _ e.surjective)
    -- `d(κ₀ ∘ π)_y = dκ₀_b ∘ dπ_y`, and `dκ₀_b` is the identity.
    rw [mfderiv_comp y (κ₀.contMDiff.mdifferentiableAt (by simp)) (h.mdifferentiableAt y), hy,
      hκ₀b]
    exact h.surjective_mfderiv y
  exact ⟨κ, e, hκ, hdκ, hreg, fun x hx ↦
    h.connectedComponentIn_comp_preimage_eq hWo hbW hinj hx⟩

/-- **The fibres of a regular Lagrangian torus fibration are tori.** If `σ` is closed, so
symplectic, every fibre of a regular Lagrangian torus fibration `π : M → B` over a Hausdorff
manifold of dimension `n` is homeomorphic to the torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus (h : hσ.IsLagrangianTorusFibration J π)
    (hσc : σ.IsClosed) (b : B) :
    Nonempty (π ⁻¹' {b} ≃ₜ UnitAddTorus (Fin (finrank ℝ F))) := by
  obtain ⟨x, hx⟩ := (h.isConnected_preimage_singleton b).nonempty
  have : Nonempty M := ⟨x⟩
  obtain ⟨κ, -, hκ, -, hreg, hcomp⟩ := h.exists_coordinates b
  have hσS : σ.IsSymplectic := ⟨hσc, hσ⟩
  obtain ⟨φ⟩ := hσS.nonempty_homeomorph_unitAddTorus (hκ.comp h.contMDiff)
    (fun i j _ ↦ h.poissonBracket_comp_apply_eq_zero ((hκ _).mdifferentiableAt (by simp)) i j)
    (fun y hy ↦ hreg y (hcomp x hx ▸ hy)) h.two_mul_card_fin_finrank
    (hcomp x hx ▸ h.isCompact_preimage_singleton b)
  exact ⟨(Homeomorph.setCongr (hcomp x hx).symm).trans φ⟩

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
