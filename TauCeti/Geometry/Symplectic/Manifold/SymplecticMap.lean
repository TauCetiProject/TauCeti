/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Symplectic maps and symplectomorphisms

Let `σ` and `σ'` be smooth two-forms on manifolds `M` and `M'`, modelled on possibly different
real normed spaces. A map `φ : M → M'` is a **symplectic map** from `σ` to `σ'` when its
differential preserves the forms, `σ'_{φ x}(dφ v, dφ w) = σ_x(v, w)` for every point `x` and
tangent vectors `v`, `w` at `x` (`TauCeti.SmoothTwoForm.IsSymplecticMap`). The condition is
pointwise and asks no regularity of `φ` and no nondegeneracy of the forms; for a smooth map it is
the equation `φ^* σ' = σ` of the pullback of forms
(`TauCeti.SmoothTwoForm.isSymplecticMap_iff_mpullback_eq`). In particular every smooth map is a
symplectic map from the pullback form, such as the inclusion of an open submanifold with the
restricted form (`TauCeti.SmoothTwoForm.isSymplecticMap_mpullback`).

The condition can also be imposed only at the points of a set `s`
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn`); on an open set it depends only on the map there.

The identity is a symplectic map, composites of differentiable symplectic maps are symplectic
maps, and out of a nondegenerate form the differential of a symplectic map is injective at every
point, since a vector in its kernel pairs to zero with every vector.

A **symplectomorphism** is a diffeomorphism, of any order of differentiability, that is a
symplectic map (`TauCeti.SmoothTwoForm.IsSymplectomorphism`). The identity is one, and for
diffeomorphisms of nonzero order inverses and composites of symplectomorphisms are
symplectomorphisms. A linear equivalence of finite-dimensional symplectic vector spaces is a
symplectomorphism of the constant forms exactly when it is a linear symplectomorphism
(`TauCeti.SymplecticForm.isSymplectomorphism_constSmooth_toDiffeomorph_iff`).

These are the maps along which Hamiltonian vector fields, Poisson brackets and Hamiltonian
dynamics are transported, and the maps whose fixed points fixed-point Floer theory counts.

## Main declarations

* `TauCeti.SmoothTwoForm.IsSymplecticMap`: maps whose differential preserves the forms.
* `TauCeti.SmoothTwoForm.isSymplecticMap_iff_mpullback_eq`: for smooth maps, `φ^* σ' = σ`.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.comp`: composites of differentiable symplectic maps.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_injective`: the differential of a symplectic map
  out of a nondegenerate form is injective.
* `TauCeti.SmoothTwoForm.IsSymplecticMap.flat_apply`: the flat map of `σ` is that of `σ'` read
  through the differential.
* `TauCeti.SmoothTwoForm.IsSymplecticMapOn`: maps whose differential preserves the forms at the
  points of a set, such as partial diffeomorphisms pulling one form back to the other on their
  sources, with `TauCeti.SmoothTwoForm.IsSymplecticMapOn.comp` and
  `TauCeti.SmoothTwoForm.IsSymplecticMapOn.congr`.
* `TauCeti.SmoothTwoForm.IsSymplectomorphism`: diffeomorphisms that are symplectic maps, with
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.symm` and
  `TauCeti.SmoothTwoForm.IsSymplectomorphism.trans`.
* `TauCeti.SymplecticForm.isSymplectomorphism_constSmooth_toDiffeomorph_iff`: linear
  symplectomorphisms as symplectomorphisms of constant forms.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M E' H' M' E'' H'' M'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' ∞ M'']
  {σ : SmoothTwoForm I M} {σ' : SmoothTwoForm I' M'} {σ'' : SmoothTwoForm I'' M''}
  {φ : M → M'} {ψ : M' → M''}

/-! ### Symplectic maps -/

/-- A map `φ : M → M'` is a **symplectic map** from `σ` to `σ'` when its differential preserves
the forms: `σ'_{φ x}(dφ v, dφ w) = σ_x(v, w)` for every point `x` and tangent vectors `v`, `w`.
No regularity of `φ` is assumed; where `φ` is not differentiable its differential is zero, so the
condition forces `σ` to vanish there. -/
def IsSymplecticMap (σ : SmoothTwoForm I M) (σ' : SmoothTwoForm I' M') (φ : M → M') : Prop :=
  ∀ x (v w : TangentSpace I x),
    σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w

/-- A map is symplectic exactly when its differential preserves the forms at every point. -/
theorem isSymplecticMap_iff :
    σ.IsSymplecticMap σ' φ ↔
      ∀ x (v w : TangentSpace I x),
        σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w :=
  Iff.rfl

/-- Apply a symplectic map hypothesis at a point and two tangent vectors. -/
theorem IsSymplecticMap.apply (h : σ.IsSymplecticMap σ' φ) (x : M) (v w : TangentSpace I x) :
    σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w :=
  h x v w

/-- **Symplectic maps are pullbacks.** A smooth map is a symplectic map from `σ` to `σ'` exactly
when it pulls `σ'` back to `σ`. -/
theorem isSymplecticMap_iff_mpullback_eq (hφ : ContMDiff I I' ∞ φ) :
    σ.IsSymplecticMap σ' φ ↔ SmoothForm.mpullback φ hφ σ' = σ := by
  simp only [isSymplecticMap_iff, SmoothBundleForm.ext_eval₂_iff, SmoothForm.eval₂_mpullback]

/-- Every smooth map is a symplectic map from the pullback form. For the inclusion of an open
submanifold, this says that the inclusion is a symplectic map from the restricted form. -/
@[simp]
theorem isSymplecticMap_mpullback (σ' : SmoothTwoForm I' M') (hφ : ContMDiff I I' ∞ φ) :
    IsSymplecticMap (SmoothForm.mpullback φ hφ σ') σ' φ :=
  (isSymplecticMap_iff_mpullback_eq hφ).2 rfl

/-- The identity is a symplectic map. -/
@[simp]
theorem isSymplecticMap_id (σ : SmoothTwoForm I M) : σ.IsSymplecticMap σ id := fun x v w ↦ by
  rw [mfderiv_id]
  rfl

/-- **The flat map through a symplectic map.** For a symplectic map `φ`, the flat map of `σ` at
`x` sends `v` to the flat of `dφ v` for `σ'`, precomposed with `dφ`. -/
theorem IsSymplecticMap.flat_apply (h : σ.IsSymplecticMap σ' φ) (x : M) (v : TangentSpace I x) :
    σ.flat x v = (σ'.flat (φ x) (mfderiv I I' φ x v)).comp (mfderiv I I' φ x) :=
  ContinuousLinearMap.ext fun w ↦ by
    rw [SmoothTwoForm.flat_apply, ContinuousLinearMap.comp_apply, SmoothTwoForm.flat_apply,
      h x v w]

/-- **Symplectic maps have injective differentials.** Out of a nondegenerate form, the
differential of a symplectic map is injective at every point: a vector in its kernel pairs to zero
with every tangent vector. -/
theorem IsSymplecticMap.mfderiv_injective (h : σ.IsSymplecticMap σ' φ) (hσ : σ.IsNondegenerate)
    (x : M) : Function.Injective (mfderiv I I' φ x) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦
    (isNondegenerate_iff_separatingLeft.1 hσ) x v fun w ↦ ?_
  rw [← h x v w, hv, SmoothBundleForm.eval₂_zero_left]

/-! ### Symplectic maps on a set -/

/-- A map `φ : M → M'` is a **symplectic map on `s`** from `σ` to `σ'` when its differential
preserves the forms at every point of `s`: `σ'_{φ x}(dφ v, dφ w) = σ_x(v, w)` for `x ∈ s` and
tangent vectors `v`, `w` at `x`. For a partial diffeomorphism on its source, this says that it
pulls `σ'` back to `σ` there. -/
def IsSymplecticMapOn (σ : SmoothTwoForm I M) (σ' : SmoothTwoForm I' M') (φ : M → M')
    (s : Set M) : Prop :=
  ∀ x ∈ s, ∀ v w : TangentSpace I x,
    σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w

/-- A map is symplectic on `s` exactly when its differential preserves the forms at every point
of `s`. -/
theorem isSymplecticMapOn_iff {s : Set M} :
    σ.IsSymplecticMapOn σ' φ s ↔
      ∀ x ∈ s, ∀ v w : TangentSpace I x,
        σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w :=
  Iff.rfl

/-- Apply a symplectic-map-on-a-set hypothesis at a point of the set and two tangent vectors. -/
theorem IsSymplecticMapOn.apply {s : Set M} (h : σ.IsSymplecticMapOn σ' φ s) {x : M} (hx : x ∈ s)
    (v w : TangentSpace I x) :
    σ'.eval₂ (φ x) (mfderiv I I' φ x v) (mfderiv I I' φ x w) = σ.eval₂ x v w :=
  h x hx v w

/-- A map is a symplectic map on the whole space exactly when it is a symplectic map. -/
@[simp]
theorem isSymplecticMapOn_univ : σ.IsSymplecticMapOn σ' φ Set.univ ↔ σ.IsSymplecticMap σ' φ :=
  ⟨fun h x ↦ h x (Set.mem_univ x), fun h x _ ↦ h x⟩

/-- A symplectic map is a symplectic map on every set. -/
theorem IsSymplecticMap.isSymplecticMapOn (h : σ.IsSymplecticMap σ' φ) (s : Set M) :
    σ.IsSymplecticMapOn σ' φ s :=
  fun x _ ↦ h x

/-- A symplectic map on `s` is a symplectic map on every subset of `s`. -/
theorem IsSymplecticMapOn.mono {s t : Set M} (h : σ.IsSymplecticMapOn σ' φ s) (hts : t ⊆ s) :
    σ.IsSymplecticMapOn σ' φ t :=
  fun x hx ↦ h x (hts hx)

/-- **Composites of symplectic maps on sets.** If `φ` is a symplectic map on `s`, differentiable
there, mapping `s` into `t`, and `ψ` is a symplectic map on `t`, differentiable at the images of
the points of `s`, then `ψ ∘ φ` is a symplectic map on `s`. -/
theorem IsSymplecticMapOn.comp {s : Set M} {t : Set M'} (hψ : σ'.IsSymplecticMapOn σ'' ψ t)
    (hφ : σ.IsSymplecticMapOn σ' φ s) (hst : Set.MapsTo φ s t)
    (hψd : ∀ x ∈ s, MDifferentiableAt I' I'' ψ (φ x)) (hφd : ∀ x ∈ s, MDifferentiableAt I I' φ x) :
    σ.IsSymplecticMapOn σ'' (ψ ∘ φ) s := fun x hx v w ↦ by
  rw [mfderiv_comp x (hψd x hx) (hφd x hx)]
  exact (hψ (φ x) (hst hx) _ _).trans (hφ x hx v w)

/-- **Composites of symplectic maps.** If `φ` is a differentiable symplectic map from `σ` to `σ'`
and `ψ`, differentiable on the image of `φ`, is a symplectic map from `σ'` to `σ''`, then `ψ ∘ φ`
is a symplectic map from `σ` to `σ''`. -/
theorem IsSymplecticMap.comp (hψ : σ'.IsSymplecticMap σ'' ψ) (hφ : σ.IsSymplecticMap σ' φ)
    (hψd : ∀ x, MDifferentiableAt I' I'' ψ (φ x)) (hφd : MDifferentiable I I' φ) :
    σ.IsSymplecticMap σ'' (ψ ∘ φ) :=
  isSymplecticMapOn_univ.1 ((hψ.isSymplecticMapOn _).comp (hφ.isSymplecticMapOn _)
    (Set.mapsTo_univ _ _) (fun x _ ↦ hψd x) (fun x _ ↦ hφd x))

/-- **Symplectic maps on open sets depend only on the map there.** If `φ` is a symplectic map on
an open set `s` and `φ'` agrees with `φ` on `s`, then `φ'` is a symplectic map on `s`. -/
theorem IsSymplecticMapOn.congr {s : Set M} {φ' : M → M'} (h : σ.IsSymplecticMapOn σ' φ s)
    (hs : IsOpen s) (hφ : Set.EqOn φ φ' s) : σ.IsSymplecticMapOn σ' φ' s := fun x hx v w ↦ by
  have hφx : φ' =ᶠ[nhds x] φ := (hφ.symm.eventuallyEq_of_mem (hs.mem_nhds hx))
  rw [hφx.mfderiv_eq, ← hφ hx]
  exact h x hx v w

/-! ### Symplectomorphisms -/

variable {n : ℕ∞ω}

/-- A diffeomorphism `φ : M ≃ₘ^n⟮I, I'⟯ M'` is a **symplectomorphism** from `σ` to `σ'` when it
is a symplectic map. -/
def IsSymplectomorphism (σ : SmoothTwoForm I M) (σ' : SmoothTwoForm I' M')
    (φ : M ≃ₘ^n⟮I, I'⟯ M') : Prop :=
  σ.IsSymplecticMap σ' φ

/-- A diffeomorphism is a symplectomorphism exactly when its underlying map is a symplectic map. -/
theorem isSymplectomorphism_iff {φ : M ≃ₘ^n⟮I, I'⟯ M'} :
    σ.IsSymplectomorphism σ' φ ↔ σ.IsSymplecticMap σ' φ :=
  Iff.rfl

/-- A symplectomorphism is a symplectic map. -/
theorem IsSymplectomorphism.isSymplecticMap {φ : M ≃ₘ^n⟮I, I'⟯ M'}
    (h : σ.IsSymplectomorphism σ' φ) : σ.IsSymplecticMap σ' φ :=
  h

/-- A smooth diffeomorphism is a symplectomorphism exactly when it pulls `σ'` back to `σ`. -/
theorem isSymplectomorphism_iff_mpullback_eq {φ : M ≃ₘ⟮I, I'⟯ M'} :
    σ.IsSymplectomorphism σ' φ ↔ SmoothForm.mpullback φ φ.contMDiff σ' = σ :=
  isSymplecticMap_iff_mpullback_eq φ.contMDiff

/-- The identity is a symplectomorphism. -/
@[simp]
theorem isSymplectomorphism_refl (σ : SmoothTwoForm I M) :
    σ.IsSymplectomorphism σ (Diffeomorph.refl I M n) := by
  rw [isSymplectomorphism_iff, Diffeomorph.coe_refl]
  exact isSymplecticMap_id σ

/-- **The inverse of a symplectomorphism is a symplectomorphism**, for diffeomorphisms of nonzero
order. -/
theorem IsSymplectomorphism.symm {φ : M ≃ₘ^n⟮I, I'⟯ M'} (h : σ.IsSymplectomorphism σ' φ)
    (hn : n ≠ 0) : σ'.IsSymplectomorphism σ φ.symm := by
  intro y v w
  obtain ⟨x, rfl⟩ : ∃ x, φ x = y := ⟨φ.symm y, φ.apply_symm_apply y⟩
  -- Write `v` and `w` as differentials of their images under the inverse differential.
  conv_rhs => rw [← φ.mfderiv_apply_mfderiv_symm_apply hn x v,
    ← φ.mfderiv_apply_mfderiv_symm_apply hn x w]
  refine Eq.trans ?_ (h x _ _).symm
  -- The base points `φ⁻¹ (φ x)` and `x` agree; the tangent spaces at both are the model space.
  rw [φ.symm_apply_apply]

/-- A diffeomorphism of nonzero order is a symplectomorphism exactly when its inverse is. -/
theorem isSymplectomorphism_symm_iff {φ : M ≃ₘ^n⟮I, I'⟯ M'} (hn : n ≠ 0) :
    σ'.IsSymplectomorphism σ φ.symm ↔ σ.IsSymplectomorphism σ' φ :=
  ⟨fun h ↦ h.symm hn, fun h ↦ h.symm hn⟩

/-- **Composites of symplectomorphisms are symplectomorphisms**, for diffeomorphisms of nonzero
order. -/
theorem IsSymplectomorphism.trans {φ : M ≃ₘ^n⟮I, I'⟯ M'} {ψ : M' ≃ₘ^n⟮I', I''⟯ M''}
    (hφ : σ.IsSymplectomorphism σ' φ) (hψ : σ'.IsSymplectomorphism σ'' ψ) (hn : n ≠ 0) :
    σ.IsSymplectomorphism σ'' (φ.trans ψ) := by
  rw [isSymplectomorphism_iff, Diffeomorph.coe_trans]
  exact IsSymplecticMap.comp hψ hφ (fun x ↦ ψ.mdifferentiable hn (φ x)) (φ.mdifferentiable hn)

end SmoothTwoForm

namespace SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Linear symplectomorphisms are symplectomorphisms.** A continuous linear equivalence of
finite-dimensional symplectic vector spaces is a symplectomorphism of the constant forms exactly
when it is a linear symplectomorphism. -/
theorem isSymplectomorphism_constSmooth_toDiffeomorph_iff {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm W} {e : V ≃L[ℝ] W} :
    ω₁.constSmooth.IsSymplectomorphism ω₂.constSmooth e.toDiffeomorph ↔
      IsSymplectomorphism ω₁ ω₂ e := by
  simp only [SmoothTwoForm.isSymplectomorphism_iff, SmoothTwoForm.isSymplecticMap_iff,
    isSymplectomorphism_iff, ContinuousLinearEquiv.coe_toDiffeomorph,
    ContinuousLinearEquiv.mfderiv_eq, fromTangentSpace_constSmooth_apply]
  exact ⟨fun h v w ↦ h 0 v w, fun h _ v w ↦ h v w⟩

end SymplecticForm

end TauCeti
