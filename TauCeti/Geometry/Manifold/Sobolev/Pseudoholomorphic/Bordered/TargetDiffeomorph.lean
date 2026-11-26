/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Bordered
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.TargetDiffeomorph

/-!
# Weak pseudoholomorphic maps up to the boundary under diffeomorphisms of the target

Let `X` be a Riemann surface with boundary and `g : M → N` a smooth diffeomorphism between
manifolds modelled on the same boundaryless model `I`. A map `g ∘ u : X → N` is weakly
pseudoholomorphic up to the boundary for a domain-dependent structure `J` on `N` and an
inhomogeneous term `ν` exactly when `u : X → M` is weakly pseudoholomorphic up to the boundary for
the pulled-back structure `g^* J` and term `g^* ν`
(`TauCeti.isWeakPseudoholomorphicOnBordered_diffeomorph_comp_iff`). The boundary condition is
transported along `ι ↦ g ∘ ι`: `g ∘ u` maps the boundary into `L` along `g ∘ ι` exactly when `u`
maps it into `L` along `ι` (`TauCeti.mapsBoundaryInto_comp_iff`), and the two statements combine
into the invariance of the boundary value problem
(`TauCeti.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_diffeomorph_comp_iff`).

The proof is that of `TauCeti.isWeakPseudoholomorphicOn_diffeomorph_comp_iff` for surfaces without
boundary. The predicate tests every bordered holomorphic chart `φ` of `X`, every chart `ψ` of the
maximal atlas of `M` and every chart `χ` of that of `N`, and `ψ ↦ g⁻¹ ≫ ψ`, `χ ↦ g ≫ χ` match the
charts of `M` and `N` so that `ψ = χ ∘ g`. In matched charts the two coordinate equations on the
extended target of `φ` are the same: the coordinate expressions agree, and `g^* J` and `g^* ν`
read in `ψ` are `J` and `ν` read in `χ`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_pullback`,
`TauCeti.InhomogeneousTerm.chartTermExtend_pullback`). The Sobolev class follows from continuity
and the coordinate equations
(`TauCeti.isWeakPseudoholomorphicOnBordered_iff_continuousOn_isWeakCauchyRiemannOn`), so `s` need
not be open.

## Main results

* `TauCeti.isWeakPseudoholomorphicOnBordered_diffeomorph_comp_iff`,
  `TauCeti.isWeakPseudoholomorphicBordered_diffeomorph_comp_iff`: **invariance under
  diffeomorphisms of the target**, transporting `J` and `ν`.
* `TauCeti.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_diffeomorph_comp_iff`,
  `TauCeti.isWeakPseudoholomorphicBordered_and_mapsBoundaryInto_diffeomorph_comp_iff`: the same
  for the boundary value problem, transporting `J`, `ν` and `ι`.
* Check: the map `z ↦ 2 z` of the closed upper half-plane into `ℂ` is weakly pseudoholomorphic up
  to the boundary for the structure `i` and maps the boundary into the real line
  (`TauCeti.isWeakPseudoholomorphicBordered_two_mul_coe_and_mapsBoundaryInto`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.2 and 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I N closedUpperHalfPlaneModel X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- The coordinate equations of `g ∘ u` for `(J, ν)` in the charts `φ` and `χ` and of `u` for
`(g^* J, g^* ν)` in the charts `φ` and `ψ` agree when `ψ = χ ∘ g`. -/
private theorem isWeakCauchyRiemannOn_chart_bordered_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N)
    {ψ : OpenPartialHomeomorph M H} {χ : OpenPartialHomeomorph N H}
    (hsrc : ψ.source = g ⁻¹' χ.source) (hfun : ∀ x, ψ x = χ (g x))
    (hsymm : ∀ w, ψ.symm w = g.symm (χ.symm w))
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) :
    IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ (g ∘ u) ⁻¹' χ.source))
        (J.chartField φ (χ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
        (ν.chartTermExtend φ (χ.extendTrans I (Homeomorph.refl E)))
        (χ.extendTrans I (Homeomorph.refl E) ∘ (g ∘ u) ∘
          (φ.extend closedUpperHalfPlaneModel).symm) ↔
      IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        ((J.pullback g le_top).chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘
          closedUpperHalfPlaneModel.symm)
        ((ν.pullback g le_top).chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  have hfun' : ⇑(ψ.extendTrans I (Homeomorph.refl E)) = χ.extendTrans I (Homeomorph.refl E) ∘ g :=
    funext fun x ↦ by simp [OpenPartialHomeomorph.extendTrans_apply, hfun]
  have hsymm' : ⇑(ψ.extendTrans I (Homeomorph.refl E)).symm =
      g.symm ∘ (χ.extendTrans I (Homeomorph.refl E)).symm :=
    funext fun w ↦ by simp [OpenPartialHomeomorph.extendTrans_symm_apply, hsymm]
  rw [J.chartField_pullback g le_top φ hfun' hsymm',
    ν.chartTermExtend_pullback g le_top φ hfun' hsymm', hfun', hsrc, preimage_comp]
  rfl

/-- **Invariance under diffeomorphisms of the target.** For a diffeomorphism `g : M → N`, the
map `g ∘ u` is weakly pseudoholomorphic up to the boundary on `s` for `J` and `ν` exactly when
`u` is weakly pseudoholomorphic up to the boundary on `s` for the pulled-back structure `g^* J`
and term `g^* ν`. -/
theorem isWeakPseudoholomorphicOnBordered_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphicOnBordered J ν p (g ∘ u) s ↔
      IsWeakPseudoholomorphicOnBordered (J.pullback g le_top) (ν.pullback g le_top) p u s := by
  simp only [isWeakPseudoholomorphicOnBordered_iff_continuousOn_isWeakCauchyRiemannOn]
  refine and_congr (g.toHomeomorph.comp_continuousOn_iff u s)
    ⟨fun h φ hφ ψ hψ ↦ ?_, fun h φ hφ χ hχ ↦ ?_⟩
  · -- Test `g ∘ u` in the chart `g⁻¹ ≫ ψ` of `N`.
    refine (isWeakCauchyRiemannOn_chart_bordered_diffeomorph_comp_iff g ?_ (fun x ↦ ?_)
      (fun w ↦ ?_) φ).1 (h φ hφ _ (g.symm.toPartialDiffeomorph.trans_mem_maximalAtlas hψ))
    · ext x
      simp
    · simp
    · simp
  · -- Test `u` in the chart `g ≫ χ` of `M`.
    refine (isWeakCauchyRiemannOn_chart_bordered_diffeomorph_comp_iff g ?_ (fun x ↦ ?_)
      (fun w ↦ ?_) φ).2 (h φ hφ _ (g.toPartialDiffeomorph.trans_mem_maximalAtlas hχ))
    · ext x
      simp
    · simp
    · simp

/-- **Invariance under diffeomorphisms of the target.** For a diffeomorphism `g : M → N`, the
map `g ∘ u` is weakly pseudoholomorphic up to the boundary for `J` and `ν` exactly when `u` is
weakly pseudoholomorphic up to the boundary for the pulled-back structure `g^* J` and term
`g^* ν`. -/
theorem isWeakPseudoholomorphicBordered_diffeomorph_comp_iff (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphicBordered J ν p (g ∘ u) ↔
      IsWeakPseudoholomorphicBordered (J.pullback g le_top) (ν.pullback g le_top) p u := by
  simp only [← isWeakPseudoholomorphicOnBordered_univ,
    isWeakPseudoholomorphicOnBordered_diffeomorph_comp_iff g]

/-- **Invariance of the boundary value problem under diffeomorphisms of the target.** For a
diffeomorphism `g : M → N` and a map `ι : L → M`, the map `g ∘ u` is weakly pseudoholomorphic up
to the boundary on `s` for `J` and `ν` and maps the boundary into `L` along `g ∘ ι` exactly when
`u` is weakly pseudoholomorphic up to the boundary on `s` for `g^* J` and `g^* ν` and maps the
boundary into `L` along `ι`. -/
theorem isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_diffeomorph_comp_iff
    {L : Type*} (ι : L → M) (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphicOnBordered J ν p (g ∘ u) s ∧
        MapsBoundaryInto closedUpperHalfPlaneModel (g ∘ u) (g ∘ ι) ↔
      IsWeakPseudoholomorphicOnBordered (J.pullback g le_top) (ν.pullback g le_top) p u s ∧
        MapsBoundaryInto closedUpperHalfPlaneModel u ι := by
  rw [isWeakPseudoholomorphicOnBordered_diffeomorph_comp_iff g,
    mapsBoundaryInto_comp_iff (g := g) g.injective]

/-- **Invariance of the boundary value problem under diffeomorphisms of the target.** For a
diffeomorphism `g : M → N` and a map `ι : L → M`, the map `g ∘ u` is weakly pseudoholomorphic up
to the boundary for `J` and `ν` and maps the boundary into `L` along `g ∘ ι` exactly when `u` is
weakly pseudoholomorphic up to the boundary for `g^* J` and `g^* ν` and maps the boundary into `L`
along `ι`. -/
theorem isWeakPseudoholomorphicBordered_and_mapsBoundaryInto_diffeomorph_comp_iff
    {L : Type*} (ι : L → M) (g : M ≃ₘ⟮I, I⟯ N) :
    IsWeakPseudoholomorphicBordered J ν p (g ∘ u) ∧
        MapsBoundaryInto closedUpperHalfPlaneModel (g ∘ u) (g ∘ ι) ↔
      IsWeakPseudoholomorphicBordered (J.pullback g le_top) (ν.pullback g le_top) p u ∧
        MapsBoundaryInto closedUpperHalfPlaneModel u ι := by
  rw [isWeakPseudoholomorphicBordered_diffeomorph_comp_iff g,
    mapsBoundaryInto_comp_iff (g := g) g.injective]

/-! ### Checks -/

/-- **Check.** On the closed upper half-plane, with the structure `i` of `ℂ`, the map `z ↦ 2 z`
into `ℂ` is weakly pseudoholomorphic up to the boundary and maps the boundary into the real line
along `x ↦ 2 x`. It is `g ∘ (↑)` for the diffeomorphism `g = (2 ·)` of `ℂ`, along which `i` pulls
back to itself, and the inclusion `(↑)` solves the problem with the boundary condition along
`ℝ ⊆ ℂ`, so this is the transport of `TauCeti.isWeakPseudoholomorphicBordered_coe` and
`TauCeti.mapsBoundaryInto_coe_ofReal` along `g = TauCeti.twoSMulDiffeomorph`, with `ι` transported
to `g ∘ ι`. -/
theorem isWeakPseudoholomorphicBordered_two_mul_coe_and_mapsBoundaryInto {ℓ : ℕ∞}
    {p : ENNReal} :
    IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const
        ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ)) 0 p
        (fun z : ClosedUpperHalfPlane ↦ 2 * (z : ℂ)) ∧
      MapsBoundaryInto closedUpperHalfPlaneModel (fun z : ClosedUpperHalfPlane ↦ 2 * (z : ℂ))
        (fun x : ℝ ↦ ((2 * x : ℝ) : ℂ)) := by
  have hJ :=
    ContMDiffAlmostComplexStructureFamily.const_ofComplexManifold_eq_pullback_twoSMulDiffeomorph
      (IP := closedUpperHalfPlaneModel) (P := ClosedUpperHalfPlane) (ℓ := ℓ)
  have hcoe := (isWeakPseudoholomorphicBordered_ofEq (ν := 0) rfl hJ).2
    (isWeakPseudoholomorphicBordered_coe (ℓ := ℓ) (p := p))
  rw [InhomogeneousTerm.ofEq_zero,
    ← InhomogeneousTerm.pullback_zero twoSMulDiffeomorph le_top] at hcoe
  have h := (isWeakPseudoholomorphicBordered_and_mapsBoundaryInto_diffeomorph_comp_iff
    ((↑) : ℝ → ℂ) twoSMulDiffeomorph).2 ⟨hcoe, mapsBoundaryInto_coe_ofReal⟩
  convert h using 2 <;> funext z <;> simp

end TauCeti
