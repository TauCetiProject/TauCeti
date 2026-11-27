/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.MaximalAtlas
public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Bordered
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Comp
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.SourceDiffeomorph

/-!
# Weak pseudoholomorphic maps up to the boundary under biholomorphisms of the domain

Let `f : X' → X` be a biholomorphism of Riemann surfaces with boundary, that is a structomorphism
for `TauCeti.borderedHolomorphicGroupoid`. It is smooth up to the boundary
(`Structomorph.contMDiff_borderedHolomorphic`) and its differential is complex linear, also at
boundary points (`Structomorph.mfderiv_ofBorderedHolomorphic_apply`). A domain-dependent almost
complex structure `J` on `M` parametrized by `X` reparametrizes to `J ∘ f`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.compStructomorph`), and an inhomogeneous term `ν`
to `f^* ν`, `(x, y) ↦ ν(f x, y) ∘ df_x` (`TauCeti.InhomogeneousTerm.compStructomorph`). The weak
pseudoholomorphic equation up to the boundary is invariant: `u` is weakly pseudoholomorphic up to
the boundary on `s` for `(J, ν)` exactly when `u ∘ f` is on `f ⁻¹' s` for `(J ∘ f, f^* ν)`
(`Structomorph.isWeakPseudoholomorphicOnBordered_comp_iff`). Since `f` maps the boundary of `X'`
onto the boundary of `X`, the boundary condition `u(∂X) ⊆ ι(L)` is unchanged, with the same `ι`
(`Structomorph.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_iff`).

The proof is that of `Diffeomorph.isWeakPseudoholomorphicOn_comp_diffeomorph_iff` for surfaces
without boundary. The bordered holomorphic charts of `X'` are exactly the charts `f ≫ φ` for
bordered holomorphic charts `φ` of `X`. In such a pair of charts the extended charts satisfy
`f ∘ (φ'.extend)⁻¹ = φ.extend⁻¹`, so the coordinate expressions of `u` and `u ∘ f` coincide, and
so do the structures and the terms read in the charts
(`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_comp`,
`TauCeti.InhomogeneousTerm.chartTermExtend_comp`). No change of variables in the plane is needed.

## Main results

* `TauCeti.ContMDiffAlmostComplexStructureFamily.compStructomorph`,
  `TauCeti.InhomogeneousTerm.compStructomorph`: the transported structure `J ∘ f` and term `f^* ν`,
  the latter linear in `ν`.
* `Structomorph.isWeakPseudoholomorphicOnBordered_comp_iff`,
  `Structomorph.isWeakPseudoholomorphicBordered_comp_iff`: **invariance under biholomorphisms of
  the domain**, transporting `J` and `ν`.
* `Structomorph.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_iff`,
  `Structomorph.isWeakPseudoholomorphicBordered_and_mapsBoundaryInto_comp_iff`: the same for the
  boundary value problem.
* `TauCeti.isWeakPseudoholomorphicOnBordered_const_zero_comp_iff`: for a structure independent of
  the domain point and the zero term, nothing needs to be transported.
* Check: on the closed upper half-plane, `u` and `z ↦ u (2 z)` are weak solutions of the same
  autonomous homogeneous boundary value problem together
  (`TauCeti.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_twoMul_iff`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1 and 3.1 and Appendix B.4.
-/

public section

open Set Filter MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ClosedUpperHalfPlane X']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}

namespace ContMDiffAlmostComplexStructureFamily

/-- The reparametrization `J ∘ f` of a domain-dependent almost complex structure along a
biholomorphism `f : X' → X` of Riemann surfaces with boundary. -/
def compStructomorph
    (J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ)
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X' ℓ :=
  J.comp ⟨f.toHomeomorph, f.contMDiff_borderedHolomorphic (by exact_mod_cast le_top)⟩

/-- The reparametrized structure at `(x, y)` is the structure at `(f x, y)`. -/
@[simp]
theorem compStructomorph_toEndomorphism_apply
    (J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ)
    (f : Structomorph borderedHolomorphicGroupoid X' X) (q : X' × M) :
    (J.compStructomorph f).toEndomorphism q = J.toEndomorphism (f.toHomeomorph q.1, q.2) :=
  comp_toEndomorphism_apply J _ q

/-- A structure independent of the domain point is unchanged by reparametrization. -/
@[simp]
theorem const_compStructomorph (K : ContMDiffAlmostComplexStructure I ℓ M)
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (const (IP := closedUpperHalfPlaneModel) (P := X) K).compStructomorph f = const K :=
  comp_const K _

end ContMDiffAlmostComplexStructureFamily

variable [HasGroupoid X borderedHolomorphicGroupoid] [HasGroupoid X' borderedHolomorphicGroupoid]

namespace InhomogeneousTerm

variable {J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ}

/-- The reparametrization `f^* ν` of an inhomogeneous term along a biholomorphism `f : X' → X` of
Riemann surfaces with boundary: at `(x, y)` it is `ν(f x, y) ∘ df_x`, an inhomogeneous term for
the structure of `X'` and the reparametrized family `J ∘ f`. -/
def compStructomorph
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (f : Structomorph borderedHolomorphicGroupoid X' X) :
    InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X').toContMDiff ℓ)
      (J.compStructomorph f) :=
  ν.comp _ _ (f.contMDiff_borderedHolomorphic (by exact_mod_cast le_top)) fun x v ↦ by
    simpa only [SmoothAlmostComplexStructure.toContMDiff_apply, ContMDiffMap.coeFn_mk] using
      f.mfderiv_ofBorderedHolomorphic_apply x v

/-- The reparametrized term at `(x, y)`, evaluated on a tangent vector `v`, is
`ν(f x, y)(df_x v)`. -/
@[simp]
theorem compStructomorph_val_tangentHom_apply
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (f : Structomorph borderedHolomorphicGroupoid X' X) (q : X' × M)
    (v : TangentSpace closedUpperHalfPlaneModel q.1) :
    (ν.compStructomorph f).val.tangentHom q v =
      ν.val.tangentHom (f.toHomeomorph q.1, q.2)
        (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel f.toHomeomorph q.1 v) :=
  comp_val_tangentHom_apply _ _ _ _ _ q v

/-- The reparametrization of the zero term is zero. -/
@[simp]
theorem compStructomorph_zero (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (0 : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J).compStructomorph f = 0 :=
  comp_zero _ _ _ _

/-- Reparametrization is additive. -/
@[simp]
theorem compStructomorph_add
    (ν μ : InhomogeneousTerm
      ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ) J)
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (ν + μ).compStructomorph f = ν.compStructomorph f + μ.compStructomorph f :=
  comp_add _ _ _ _ _ _

/-- Reparametrization commutes with scalar multiplication. -/
@[simp]
theorem compStructomorph_smul (c : ℝ)
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (c • ν).compStructomorph f = c • ν.compStructomorph f :=
  comp_smul _ _ _ _ _ c

/-- Reparametrization commutes with negation. -/
@[simp]
theorem compStructomorph_neg
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ)
      J) (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (-ν).compStructomorph f = -ν.compStructomorph f :=
  comp_neg _ _ _ _ _

/-- Reparametrization commutes with subtraction. -/
@[simp]
theorem compStructomorph_sub
    (ν μ : InhomogeneousTerm
      ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ) J)
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    (ν - μ).compStructomorph f = ν.compStructomorph f - μ.compStructomorph f :=
  comp_sub _ _ _ _ _ _

end InhomogeneousTerm

variable [I.Boundaryless]
  {J : ContMDiffAlmostComplexStructureFamily I M closedUpperHalfPlaneModel X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofBorderedHolomorphic X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- **Invariance in one pair of charts.** Let `φ'` be a bordered holomorphic chart of `X'` and `φ`
a chart of `X` with `f ∘ φ'⁻¹ = φ⁻¹` and the same target, such as `φ' = f ≫ φ`. In `φ'` and a
chart `ψ` of `M`, the coordinate equation of `u ∘ f` for the reparametrized data is the coordinate
equation of `u` in `φ` and `ψ`. -/
private theorem _root_.Structomorph.isWeakCauchyRiemannOn_chart_comp_iff
    (f : Structomorph borderedHolomorphicGroupoid X' X)
    {φ' : OpenPartialHomeomorph X' ClosedUpperHalfPlane}
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X')
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane} (hsymm : f.toHomeomorph ∘ φ'.symm = φ.symm)
    (htarget : φ'.target = φ.target) (ψ : OpenPartialHomeomorph M H) :
    IsWeakCauchyRiemannOn p ((φ'.extend closedUpperHalfPlaneModel).target ∩
          (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹'
            (f.toHomeomorph ⁻¹' s ∩ (u ∘ f.toHomeomorph) ⁻¹' ψ.source))
        ((J.compStructomorph f).chartField φ' (ψ.extendTrans I (Homeomorph.refl E)) ∘
          closedUpperHalfPlaneModel.symm)
        ((ν.compStructomorph f).chartTermExtend φ' (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ (u ∘ f.toHomeomorph) ∘
          (φ'.extend closedUpperHalfPlaneModel).symm) ↔
      IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)) ∘ closedUpperHalfPlaneModel.symm)
        (ν.chartTermExtend φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  set ψ' := ψ.extendTrans I (Homeomorph.refl E)
  have hsymmE : f.toHomeomorph ∘ (φ'.extend closedUpperHalfPlaneModel).symm =
      (φ.extend closedUpperHalfPlaneModel).symm := by
    rw [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe_symm, ← hsymm,
      Function.comp_assoc]
  have htargetE : (φ'.extend closedUpperHalfPlaneModel).target =
      (φ.extend closedUpperHalfPlaneModel).target := by
    rw [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.extend_target, htarget]
  have hset : (φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹'
          (f.toHomeomorph ⁻¹' s ∩ (u ∘ f.toHomeomorph) ⁻¹' ψ.source) =
      (φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
    rw [htargetE, ← hsymmE]
    -- A preimage under a composite is the iterated preimage, by definition.
    rfl
  have hfun : ψ' ∘ (u ∘ f.toHomeomorph) ∘ (φ'.extend closedUpperHalfPlaneModel).symm =
      ψ' ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm := by
    rw [← hsymmE, Function.comp_assoc]
  have hJ : (J.compStructomorph f).chartField φ' ψ' = J.chartField φ ψ' :=
    J.chartField_comp _ hsymm ψ'
  rw [hJ, hfun]
  -- The terms read in the extended charts agree on the extended target of `φ'`, where the inverse
  -- extended chart is differentiable within the closed upper half-plane.
  refine (isWeakCauchyRiemannOn_congr_ae (η' := ν.chartTermExtend φ ψ') (ae_of_all _ fun _ ↦ rfl)
    ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_interior).2 (ae_of_all _ fun z hz ↦ ?_)
    have hz' : z ∈ (φ'.extend closedUpperHalfPlaneModel).target := (interior_subset hz).1
    exact congrFun (ν.chartTermExtend_comp _ _ _ _ hsymmE ψ'
      (mdifferentiableWithinAt_extend_symm
        (borderedHolomorphicGroupoid_maximalAtlas_subset (by exact_mod_cast le_top) hφ') hz')
      (OpenPartialHomeomorph.extend_target_subset_range _ hz')) _
  · rw [hset]

/-- **Invariance under biholomorphisms of the domain.** For a biholomorphism `f : X' → X` of
Riemann surfaces with boundary, a map `u : X → M` is weakly pseudoholomorphic up to the boundary on
`s` for `(J, ν)` exactly when `u ∘ f` is weakly pseudoholomorphic up to the boundary on `f ⁻¹' s`
for the reparametrized structure `J ∘ f` and term `f^* ν`. -/
theorem _root_.Structomorph.isWeakPseudoholomorphicOnBordered_comp_iff
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    IsWeakPseudoholomorphicOnBordered (J.compStructomorph f) (ν.compStructomorph f) p
        (u ∘ f.toHomeomorph) (f.toHomeomorph ⁻¹' s) ↔
      IsWeakPseudoholomorphicOnBordered J ν p u s := by
  rw [isWeakPseudoholomorphicOnBordered_iff, isWeakPseudoholomorphicOnBordered_iff]
  refine and_congr f.memWkpLocMapOnGroupoid_comp_iff
    ⟨fun h φ hφ ψ hψ ↦ ?_, fun h φ' hφ' ψ hψ ↦ ?_⟩
  · -- Test `u` in `φ` through the chart `f ≫ φ` of `X'`.
    obtain ⟨φ', hφ', htarget, hsymm⟩ := f.symm.exists_mem_maximalAtlas_symm_eq_comp hφ
    have hsymm' : f.toHomeomorph ∘ φ'.symm = φ.symm := by
      rw [hsymm]
      funext z
      simp
    exact (f.isWeakCauchyRiemannOn_chart_comp_iff hφ' hsymm' htarget ψ).1 (h φ' hφ' ψ hψ)
  · -- Test `u ∘ f` in `φ'` through the chart `f⁻¹ ≫ φ'` of `X`.
    obtain ⟨φ, hφ, htarget, hsymm⟩ := f.exists_mem_maximalAtlas_symm_eq_comp hφ'
    exact (f.isWeakCauchyRiemannOn_chart_comp_iff hφ' hsymm.symm htarget.symm ψ).2
      (h φ hφ ψ hψ)

/-- **Invariance under biholomorphisms of the domain.** For a biholomorphism `f : X' → X` of
Riemann surfaces with boundary, a map `u : X → M` is weakly pseudoholomorphic up to the boundary
for `(J, ν)` exactly when `u ∘ f` is weakly pseudoholomorphic up to the boundary for the
reparametrized structure `J ∘ f` and term `f^* ν`. -/
theorem _root_.Structomorph.isWeakPseudoholomorphicBordered_comp_iff
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    IsWeakPseudoholomorphicBordered (J.compStructomorph f) (ν.compStructomorph f) p
        (u ∘ f.toHomeomorph) ↔
      IsWeakPseudoholomorphicBordered J ν p u := by
  simpa only [preimage_univ, isWeakPseudoholomorphicOnBordered_univ] using
    f.isWeakPseudoholomorphicOnBordered_comp_iff (ν := ν) (p := p) (u := u) (s := univ)

/-- **Invariance of the boundary value problem under biholomorphisms of the domain.** For a
biholomorphism `f : X' → X` of Riemann surfaces with boundary and a map `ι : L → M`, the map
`u ∘ f` is weakly pseudoholomorphic up to the boundary on `f ⁻¹' s` for `J ∘ f` and `f^* ν` and
maps the boundary of `X'` into `L` along `ι` exactly when `u` is weakly pseudoholomorphic up to the
boundary on `s` for `J` and `ν` and maps the boundary of `X` into `L` along `ι`: `f` maps the
boundary of `X'` onto that of `X`, so `ι` is unchanged. -/
theorem _root_.Structomorph.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_iff
    {L : Type*} (ι : L → M) (f : Structomorph borderedHolomorphicGroupoid X' X) :
    IsWeakPseudoholomorphicOnBordered (J.compStructomorph f) (ν.compStructomorph f) p
          (u ∘ f.toHomeomorph) (f.toHomeomorph ⁻¹' s) ∧
        MapsBoundaryInto closedUpperHalfPlaneModel (u ∘ f.toHomeomorph) ι ↔
      IsWeakPseudoholomorphicOnBordered J ν p u s ∧
        MapsBoundaryInto closedUpperHalfPlaneModel u ι := by
  rw [f.isWeakPseudoholomorphicOnBordered_comp_iff, ← Structomorph.coe_toDiffeomorph
    borderedHolomorphicGroupoid_le_contDiffGroupoid f,
    mapsBoundaryInto_comp_diffeomorph_iff (by simp)]

/-- **Invariance of the boundary value problem under biholomorphisms of the domain.** For a
biholomorphism `f : X' → X` of Riemann surfaces with boundary and a map `ι : L → M`, the map
`u ∘ f` is weakly pseudoholomorphic up to the boundary for `J ∘ f` and `f^* ν` and maps the
boundary into `L` along `ι` exactly when `u` is weakly pseudoholomorphic up to the boundary for `J`
and `ν` and maps the boundary into `L` along `ι`. -/
theorem _root_.Structomorph.isWeakPseudoholomorphicBordered_and_mapsBoundaryInto_comp_iff
    {L : Type*} (ι : L → M) (f : Structomorph borderedHolomorphicGroupoid X' X) :
    IsWeakPseudoholomorphicBordered (J.compStructomorph f) (ν.compStructomorph f) p
          (u ∘ f.toHomeomorph) ∧
        MapsBoundaryInto closedUpperHalfPlaneModel (u ∘ f.toHomeomorph) ι ↔
      IsWeakPseudoholomorphicBordered J ν p u ∧
        MapsBoundaryInto closedUpperHalfPlaneModel u ι := by
  simpa only [preimage_univ, isWeakPseudoholomorphicOnBordered_univ] using
    f.isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_iff (ν := ν) (p := p) (u := u)
      (s := univ) ι

/-- **Reparametrizing solutions of an autonomous homogeneous equation.** For a structure `K` on `M`
independent of the domain point and the zero term, a map `u : X → M` is weakly pseudoholomorphic
up to the boundary on `s` exactly when `u ∘ f` is on `f ⁻¹' s`, for every biholomorphism
`f : X' → X` of Riemann surfaces with boundary: no data has to be transported. -/
theorem isWeakPseudoholomorphicOnBordered_const_zero_comp_iff
    (K : ContMDiffAlmostComplexStructure I ℓ M)
    (f : Structomorph borderedHolomorphicGroupoid X' X) :
    IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const K) 0 p
        (u ∘ f.toHomeomorph) (f.toHomeomorph ⁻¹' s) ↔
      IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const K) 0 p
        u s := by
  rw [← f.isWeakPseudoholomorphicOnBordered_comp_iff,
    ← isWeakPseudoholomorphicOnBordered_ofEq rfl
      (ContMDiffAlmostComplexStructureFamily.const_compStructomorph K f),
    InhomogeneousTerm.compStructomorph_zero, InhomogeneousTerm.ofEq_zero]

/-! ### Check: dilations of the closed upper half-plane -/

/-- **Check: dilation by `2`.** On the closed upper half-plane, for a structure `K` on `M`
independent of the domain point and the zero term, a map `u` is weakly pseudoholomorphic up to the
boundary on `s` and maps the boundary into `L` along `ι` exactly when `z ↦ u (2 z)` is weakly
pseudoholomorphic up to the boundary on `{z | 2 z ∈ s}` and maps the boundary into `L` along the
same `ι`. -/
theorem isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_twoMul_iff
    (K : ContMDiffAlmostComplexStructure I ℓ M) {L : Type*} (ι : L → M)
    {u : ClosedUpperHalfPlane → M} {s : Set ClosedUpperHalfPlane} :
    IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const K) 0 p
          (u ∘ twoMul) (twoMul ⁻¹' s) ∧
        MapsBoundaryInto closedUpperHalfPlaneModel (u ∘ twoMul) ι ↔
      IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const K) 0 p u s ∧
        MapsBoundaryInto closedUpperHalfPlaneModel u ι := by
  have h := (Structomorph.ofMemGroupoid twoMul twoMul_mem_borderedHolomorphicGroupoid
    ).isWeakPseudoholomorphicOnBordered_and_mapsBoundaryInto_comp_iff
    (J := ContMDiffAlmostComplexStructureFamily.const K) (ν := 0) (p := p) (u := u) (s := s) ι
  rwa [← isWeakPseudoholomorphicOnBordered_ofEq rfl
      (ContMDiffAlmostComplexStructureFamily.const_compStructomorph K _),
    InhomogeneousTerm.compStructomorph_zero, InhomogeneousTerm.ofEq_zero,
    Structomorph.ofMemGroupoid_toHomeomorph] at h

end TauCeti
