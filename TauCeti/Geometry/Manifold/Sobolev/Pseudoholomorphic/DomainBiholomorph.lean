/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Comp
import TauCeti.Geometry.Manifold.Diffeomorph.MaximalAtlas
import TauCeti.Geometry.Manifold.Diffeomorph.RestrictScalars
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.SourceDiffeomorph

/-!
# Weak pseudoholomorphic maps under biholomorphisms of the domain

Let `f : X' → X` be a biholomorphism of Riemann surfaces without boundary. A domain-dependent
almost complex structure `J` on `M` parametrized by `X` reparametrizes to `J ∘ f`
(`TauCeti.ContMDiffAlmostComplexStructureFamily.compBiholomorph`), and an inhomogeneous term `ν`
for `J` to `f^* ν`, `(x, y) ↦ ν(f x, y) ∘ df_x` (`TauCeti.InhomogeneousTerm.compBiholomorph`),
which is again complex antilinear because `df` is complex linear. The weak pseudoholomorphic
equation is invariant: `u` is weakly pseudoholomorphic on `s` for `(J, ν)` exactly when `u ∘ f`
is on `f ⁻¹' s` for `(J ∘ f, f^* ν)` (`Diffeomorph.isWeakPseudoholomorphicOn_comp_diffeomorph_iff`).

The holomorphic charts of `X'` are exactly the charts `f ≫ φ` for holomorphic charts `φ` of `X`.
In a pair of such charts the coordinate expressions of `u` and `u ∘ f` coincide, and so do the
structures and the terms read in the charts, since `(J ∘ f)(f⁻¹ (φ⁻¹ z)) = J(φ⁻¹ z)` and
`df (d(f⁻¹ ∘ φ⁻¹) 1) = dφ⁻¹ 1`. So the invariance needs no change of variables in the plane.

## Main results

* `TauCeti.InhomogeneousTerm.compBiholomorph`: the transported term `f^* ν`, linear in `ν`.
* `Diffeomorph.isWeakPseudoholomorphicOn_comp_diffeomorph_iff`,
  `Diffeomorph.isWeakPseudoholomorphic_comp_diffeomorph_iff`: **invariance under biholomorphisms
  of the domain**, transporting `J` and `ν`.
* `TauCeti.isWeakPseudoholomorphicOn_const_zero_comp_diffeomorph_iff`: for a structure independent
  of the domain point and the zero term, nothing needs to be transported, so reparametrizing a
  solution by a biholomorphism gives a solution of the same equation.
* Example on `X = ℂ`: the maps `u` and `z ↦ u (2 z)` are weak solutions of the same homogeneous
  equation together (`TauCeti.isWeakPseudoholomorphicOn_comp_two_mul_iff`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1 and 3.1 and Appendix B.4.
-/

public section

open Set Filter MeasureTheory
open scoped Manifold ContDiff TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ∞ X']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}

namespace ContMDiffAlmostComplexStructureFamily

/-- The reparametrization `J ∘ f` of a domain-dependent almost complex structure along a
biholomorphism `f : X' → X` of the domains. -/
def compBiholomorph (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X' ℓ :=
  J.comp ⟨f, (f.contMDiff_modelWithCornersSelf_restrictScalars ℝ).of_le
    (by exact_mod_cast le_top)⟩

omit [IsManifold 𝓘(ℂ) ∞ X] [IsManifold 𝓘(ℂ) ∞ X'] in
/-- The reparametrized structure at `(x, y)` is the structure at `(f x, y)`. -/
@[simp]
theorem compBiholomorph_toEndomorphism_apply
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ) (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X)
    (q : X' × M) : (J.compBiholomorph f).toEndomorphism q = J.toEndomorphism (f q.1, q.2) :=
  comp_toEndomorphism_apply J _ q

omit [IsManifold 𝓘(ℂ) ∞ X] [IsManifold 𝓘(ℂ) ∞ X'] in
/-- A structure independent of the domain point is unchanged by reparametrization. -/
@[simp]
theorem const_compBiholomorph (K : ContMDiffAlmostComplexStructure I ℓ M)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    (const (IP := 𝓘(ℝ, ℂ)) (P := X) K).compBiholomorph f = const K :=
  comp_const K _

end ContMDiffAlmostComplexStructureFamily

namespace InhomogeneousTerm

variable {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}

/-- The reparametrization `f^* ν` of an inhomogeneous term along a biholomorphism
`f : X' → X` of the domains: at `(x, y)` it is `ν(f x, y) ∘ df_x`, an inhomogeneous term for the
structure of `X'` and the reparametrized family `J ∘ f`. -/
def compBiholomorph
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X').toContMDiff ℓ)
      (J.compBiholomorph f) :=
  ν.comp _ _ ((f.contMDiff_modelWithCornersSelf_restrictScalars ℝ).of_le
      (by exact_mod_cast le_top))
    fun x v ↦ by
      simpa only [SmoothAlmostComplexStructure.toContMDiff_apply, ContMDiffMap.coeFn_mk] using
        ((f.contMDiff x).mdifferentiableAt (by simp)).mfderiv_ofComplexManifold_apply v

/-- The reparametrized term at `(x, y)`, evaluated on a tangent vector `v`, is
`ν(f x, y)(df_x v)`. -/
@[simp]
theorem compBiholomorph_val_tangentHom_apply
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (q : X' × M) (v : TangentSpace 𝓘(ℝ, ℂ) q.1) :
    (ν.compBiholomorph f).val.tangentHom q v =
      ν.val.tangentHom (f q.1, q.2) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f q.1 v) :=
  comp_val_tangentHom_apply _ _ _ _ _ q v

/-- The reparametrization of the zero term is zero. -/
@[simp]
theorem compBiholomorph_zero (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    (0 : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)
      J).compBiholomorph f = 0 :=
  comp_zero _ _ _ _

/-- Reparametrization is additive. -/
@[simp]
theorem compBiholomorph_add
    (ν μ : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)
      J) (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    (ν + μ).compBiholomorph f = ν.compBiholomorph f + μ.compBiholomorph f :=
  comp_add _ _ _ _ _ _

/-- Reparametrization commutes with scalar multiplication. -/
@[simp]
theorem compBiholomorph_smul (c : ℝ)
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) : (c • ν).compBiholomorph f = c • ν.compBiholomorph f :=
  comp_smul _ _ _ _ _ c

/-- Reparametrization commutes with negation. -/
@[simp]
theorem compBiholomorph_neg
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) : (-ν).compBiholomorph f = -ν.compBiholomorph f :=
  comp_neg _ _ _ _ _

/-- Reparametrization commutes with subtraction. -/
@[simp]
theorem compBiholomorph_sub
    (ν μ : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)
      J) (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    (ν - μ).compBiholomorph f = ν.compBiholomorph f - μ.compBiholomorph f :=
  comp_sub _ _ _ _ _ _

end InhomogeneousTerm

variable {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

section Invariance

variable [I.Boundaryless]

/-- **Invariance in one pair of charts.** Let `φ'` be a holomorphic chart of `X'` and `φ` a chart
of `X` with `f ∘ φ'⁻¹ = φ⁻¹` and the same target, such as `φ' = f ≫ φ`. In `φ'` and a chart `ψ`
of `M`, the coordinate equation of `u ∘ f` for the reparametrized data is the coordinate equation
of `u` in `φ` and `ψ`. -/
private theorem _root_.Diffeomorph.isWeakCauchyRiemannOn_chart_comp_iff (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X)
    {φ' : OpenPartialHomeomorph X' ℂ} (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X')
    {φ : OpenPartialHomeomorph X ℂ} (hsymm : f ∘ φ'.symm = φ.symm)
    (htarget : φ'.target = φ.target) (ψ : OpenPartialHomeomorph M H) :
    IsWeakCauchyRiemannOn p (φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' s ∩ (u ∘ f) ⁻¹' ψ.source))
        ((J.compBiholomorph f).chartField φ' (ψ.extendTrans I (Homeomorph.refl E)))
        ((ν.compBiholomorph f).chartTerm φ' (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ (u ∘ f) ∘ φ'.symm) ↔
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  set ψ' := ψ.extendTrans I (Homeomorph.refl E)
  have hset : φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' s ∩ (u ∘ f) ⁻¹' ψ.source) =
      φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
    rw [← htarget, ← hsymm]
    rfl
  have hfun : ψ' ∘ (u ∘ f) ∘ φ'.symm = ψ' ∘ u ∘ φ.symm := by
    rw [← hsymm]
    rfl
  have hJ : (J.compBiholomorph f).chartField φ' ψ' = J.chartField φ ψ' :=
    J.chartField_comp _ hsymm ψ'
  rw [hJ, hfun]
  -- The terms read in the charts agree on the target of `φ'`, where `φ'⁻¹` is differentiable.
  refine (isWeakCauchyRiemannOn_congr_ae (η' := ν.chartTerm φ ψ') (ae_of_all _ fun _ ↦ rfl)
    ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_interior).2 (ae_of_all _ fun z hz ↦ ?_)
    have hz' : z ∈ φ'.target := (interior_subset hz).1
    exact congrFun (ν.chartTerm_comp _ _ _ _ hsymm ψ'
      ((contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X') hφ') hz').mdifferentiableAt
          one_ne_zero)) _
  · rw [hset]

/-- **Invariance under biholomorphisms of the domain.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is weakly pseudoholomorphic on `s` for `(J, ν)` exactly when `u ∘ f` is weakly
pseudoholomorphic on `f ⁻¹' s` for the reparametrized structure `J ∘ f` and term `f^* ν`. -/
theorem _root_.Diffeomorph.isWeakPseudoholomorphicOn_comp_diffeomorph_iff
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    IsWeakPseudoholomorphicOn (J.compBiholomorph f) (ν.compBiholomorph f) p (u ∘ f) (f ⁻¹' s) ↔
      IsWeakPseudoholomorphicOn J ν p u s := by
  have hn : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [isWeakPseudoholomorphicOn_iff, isWeakPseudoholomorphicOn_iff,
    f.memWkpLocMapOn_comp_diffeomorph_iff hn]
  refine and_congr_right fun _ ↦ ⟨fun h φ hφ ψ hψ ↦ ?_, fun h φ' hφ' ψ hψ ↦ ?_⟩
  · -- Test `u` in `φ` through the chart `f ≫ φ` of `X'`.
    obtain ⟨φ', hφ', htarget, hsymm⟩ := f.exists_mem_maximalAtlas_comp_symm_eq hn hφ
    exact (f.isWeakCauchyRiemannOn_chart_comp_iff hφ' hsymm htarget ψ).1 (h φ' hφ' ψ hψ)
  · -- Test `u ∘ f` in `φ'` through a chart `φ` of `X` with `φ⁻¹ = f ∘ φ'⁻¹`.
    obtain ⟨φ, hφ, htarget, hsymm⟩ := f.exists_mem_maximalAtlas_symm_eq_comp hn hφ'
    exact (f.isWeakCauchyRiemannOn_chart_comp_iff hφ' hsymm.symm htarget.symm ψ).2 (h φ hφ ψ hψ)

/-- **Invariance under biholomorphisms of the domain.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is weakly pseudoholomorphic for `(J, ν)` exactly when `u ∘ f` is weakly
pseudoholomorphic for the reparametrized structure `J ∘ f` and term `f^* ν`. -/
theorem _root_.Diffeomorph.isWeakPseudoholomorphic_comp_diffeomorph_iff
    (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    IsWeakPseudoholomorphic (J.compBiholomorph f) (ν.compBiholomorph f) p (u ∘ f) ↔
      IsWeakPseudoholomorphic J ν p u := by
  simpa only [preimage_univ, isWeakPseudoholomorphicOn_univ] using
    f.isWeakPseudoholomorphicOn_comp_diffeomorph_iff (ν := ν) (p := p) (u := u) (s := univ)

/-- **Reparametrizing solutions of an autonomous homogeneous equation.** For a structure `K` on `M`
independent of the domain point and the zero term, a map `u : X → M` is weakly pseudoholomorphic
on `s` exactly when `u ∘ f` is on `f ⁻¹' s`, for every biholomorphism `f : X' → X`: no data has
to be transported. -/
theorem isWeakPseudoholomorphicOn_const_zero_comp_diffeomorph_iff
    (K : ContMDiffAlmostComplexStructure I ℓ M) (f : X' ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const K) 0 p (u ∘ f)
        (f ⁻¹' s) ↔
      IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const K) 0 p u s := by
  rw [← f.isWeakPseudoholomorphicOn_comp_diffeomorph_iff,
    ← isWeakPseudoholomorphicOn_ofEq rfl
      (ContMDiffAlmostComplexStructureFamily.const_compBiholomorph K f),
    InhomogeneousTerm.compBiholomorph_zero, InhomogeneousTerm.ofEq_zero]

/-! ### Example: dilations of the plane -/

omit [IsManifold 𝓘(ℂ) ∞ X] in
/-- **Dilation by `2`.** On `X = ℂ`, for a structure `K` on `M` independent of the domain
point and the zero term, a map `u : ℂ → M` is weakly pseudoholomorphic on `s` exactly when
`z ↦ u (2 z)` is weakly pseudoholomorphic on `{z | 2 z ∈ s}`. -/
theorem isWeakPseudoholomorphicOn_comp_two_mul_iff (K : ContMDiffAlmostComplexStructure I ℓ M)
    {u : ℂ → M} {s : Set ℂ} :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const K) 0 p
        (fun z ↦ u (2 * z)) ((2 * ·) ⁻¹' s) ↔
      IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const K) 0 p u s := by
  let e : ℂ ≃L[ℂ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ 2 two_ne_zero).toContinuousLinearEquiv
  have he : ⇑e.toDiffeomorph = (2 * ·) := by
    funext z
    simp [e, smul_eq_mul]
  have h := isWeakPseudoholomorphicOn_const_zero_comp_diffeomorph_iff (p := p) (u := u) (s := s)
    K e.toDiffeomorph
  rwa [he] at h

end Invariance

end TauCeti
