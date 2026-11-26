/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder
import TauCeti.Geometry.Symplectic.ConleyZehnder.Lagrangian
import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
import TauCeti.Geometry.Symplectic.WittExtension

/-!
# The Conley–Zehnder index in frames adapted to a Lagrangian distribution

Let `σ` be a smooth two-form on a manifold `M`, `γ : [0, 1] → M` a path and `Φ(t)` a family of
linear isomorphisms along `γ` preserving `σ`, such as the linearized flow along a periodic orbit of
a Hamiltonian. Its Conley–Zehnder index read in a symplectic frame `χ` along `γ`
(`TauCeti.SmoothTwoForm.frameConleyZehnderIndex`) depends on the frame: changing the frame by a
loop `g` of linear symplectic maps of the model adds `2 μ(g)`
(`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_add_maslovIndex`).

Fix a Lagrangian subspace `L₀` of the model `(W, ω₀)`, and suppose that the frames carry `L₀` onto
prescribed subspaces `Λ(t)` of the tangent spaces along `γ`, for instance the vertical tangent
spaces of a cotangent bundle. Two such frames differ by a loop preserving `L₀`, whose Maslov index
vanishes (`TauCeti.SymplecticForm.maslovIndex_eq_zero_of_mapsTo`). So all frames adapted to `Λ`
give the same index:

* for frames with the same model whose change of frame is a loop
  (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_of_map_eq`);
* for frames with arbitrary models `(W, ω₀, L₀)` and `(W', ω', L₀')` whose change of frame is a
  loop (`TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_of_map_eq_of_map_eq`): a linear
  symplectomorphism `W ≃ W'` carrying `L₀` onto `L₀'`
  (`TauCeti.SymplecticForm.exists_isSymplectomorphism_map_eq`) moves both frames to one model.

So the Conley–Zehnder index of a periodic orbit in a cotangent bundle, read in frames that send
the vertical tangent spaces to a fixed Lagrangian of the model, does not depend on the choice among
such frames whose change of frame is a loop. This file constructs no such frame; their existence,
and the twisted frames needed along loops whose pulled-back tangent bundle is not orientable, are
not covered here. Without the Lagrangian condition the index does depend on the frame: along the
constant loop at a point, a frame rotating once in a symplectic plane of the model changes the
index by `2`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplecticFrame.isLagrangian_map_iff`: a symplectic frame carries a
  subspace of the model onto a Lagrangian subspace exactly when the subspace is Lagrangian.
* `TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_of_map_eq`: two symplectic frames with the same
  model whose change of frame is a loop, carrying a Lagrangian of the model to the same subspaces
  along `γ`, give the same index.
* `TauCeti.SmoothTwoForm.frameConleyZehnderIndex_eq_of_map_eq_of_map_eq`: two symplectic frames,
  with any models and with a loop as change of frame, adapted to the same subspaces along `γ`
  through Lagrangians of their models, give the same index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of Floer
  homology of cotangent bundles).
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. **24**, EMS, 2015, §1.4 (gradings from trivializations
  of the vertical distribution).
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
  {ω₀ : SymplecticForm W} {ω' : SymplecticForm W'} {L₀ : Submodule ℝ W} {L₀' : Submodule ℝ W'}
  {γ : unitInterval → M} {Φ : ∀ t, TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t)}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] in
/-- **Symplectic frames match Lagrangian subspaces.** For a symplectic frame `φ` along `f` and a
point `y`, a subspace `L₀` of the model is Lagrangian exactly when its image under `φ(y)` is a
Lagrangian subspace of the tangent space at `f y`, for the symplectic form that the nondegenerate
two-form `σ` induces there. -/
theorem IsSymplecticFrame.isLagrangian_map_iff {Y : Type*} [TopologicalSpace Y] {f : Y → M}
    {φ : ∀ y, W ≃L[ℝ] TangentSpace I (f y)} (hφ : IsSymplecticFrame σ ω₀ f φ)
    (h : σ.IsNondegenerate) (y : Y) :
    (h.symplecticFormAt (f y)).IsLagrangian (L₀.map (φ y : W →ₗ[ℝ] TangentSpace I (f y))) ↔
      ω₀.IsLagrangian L₀ :=
  SymplecticForm.IsSymplectomorphism.isLagrangian_map_iff (e := (φ y).toLinearEquiv) <|
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦
      (h.symplecticFormAt_apply (f y) _ _).trans (hφ.apply_apply y v w)

/-- **Frames adapted to a Lagrangian give the same Conley–Zehnder index.** Let `χ` and `χ'` be
symplectic frames along `γ` with model `(W, ω₀)` whose change of frame `t ↦ χ(t)⁻¹ ∘ χ'(t)` is a
loop, for instance periodic frames along a loop. If they carry a Lagrangian subspace `L₀` of the
model to the same subspaces of the tangent spaces along `γ`, then the Conley–Zehnder index of `Φ`
read in `χ'` equals its index read in `χ`. -/
theorem frameConleyZehnderIndex_eq_of_map_eq {χ χ' : ∀ t, W ≃L[ℝ] TangentSpace I (γ t)}
    (hχ : IsSymplecticFrame σ ω₀ γ χ) (hχ' : IsSymplecticFrame σ ω₀ γ χ')
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm) (hL₀ : ω₀.IsLagrangian L₀)
    (hL : ∀ t, L₀.map (χ' t : W →ₗ[ℝ] TangentSpace I (γ t)) =
      L₀.map (χ t : W →ₗ[ℝ] TangentSpace I (γ t)))
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω₀ hχ' hΦ hΦσ = frameConleyZehnderIndex ω₀ hχ hΦ hΦσ := by
  -- The change of frame `χ(t)⁻¹ ∘ χ'(t)` maps `L₀` into itself, so its Maslov index vanishes.
  rw [frameConleyZehnderIndex_eq_add_maslovIndex hχ hχ' hper hΦ hΦσ,
    SymplecticForm.maslovIndex_eq_zero_of_mapsTo hL₀ _ _ fun t v hv ↦ ?_, Int.cast_zero,
    mul_zero, add_zero]
  obtain ⟨w, hw, hwv⟩ : χ' t v ∈ L₀.map (χ t : W →ₗ[ℝ] TangentSpace I (γ t)) :=
    hL t ▸ Submodule.mem_map_of_mem hv
  rw [transitionLoop_apply, ← hwv]
  simpa using hw

/-- **The Conley–Zehnder index in frames adapted to a distribution of subspaces.** Let `Λ(t)` be
subspaces of the tangent spaces along `γ`, and let `χ` and `χ'` be symplectic frames along `γ`,
with models `(W, ω₀)` and `(W', ω')`, whose change of frame `t ↦ χ(t)⁻¹ ∘ χ'(t)` is a loop, for
instance periodic frames along a loop. If `χ` carries a Lagrangian subspace `L₀` of `W` onto `Λ`,
and `χ'` a subspace `L₀'` of `W'` onto `Λ`, then the Conley–Zehnder index of `Φ` is the same in both
frames. (Then `L₀'` is Lagrangian too.) -/
theorem frameConleyZehnderIndex_eq_of_map_eq_of_map_eq
    {χ : ∀ t, W ≃L[ℝ] TangentSpace I (γ t)} {χ' : ∀ t, W' ≃L[ℝ] TangentSpace I (γ t)}
    (hχ : IsSymplecticFrame σ ω₀ γ χ) (hχ' : IsSymplecticFrame σ ω' γ χ')
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm) (hL₀ : ω₀.IsLagrangian L₀)
    {Λ : ∀ t, Submodule ℝ (TangentSpace I (γ t))}
    (hL : ∀ t, L₀.map (χ t : W →ₗ[ℝ] TangentSpace I (γ t)) = Λ t)
    (hL' : ∀ t, L₀'.map (χ' t : W' →ₗ[ℝ] TangentSpace I (γ t)) = Λ t)
    (hΦ : Continuous fun q : unitInterval × TangentSpace I (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle I M))
    (hΦσ : ∀ t u v, σ.eval₂ (γ t) (Φ t u) (Φ t v) = σ.eval₂ (γ 0) u v) :
    frameConleyZehnderIndex ω' hχ' hΦ hΦσ = frameConleyZehnderIndex ω₀ hχ hΦ hΦσ := by
  -- At time `0` the frames differ by the linear symplectomorphism `χ'(0)⁻¹ ∘ χ(0)`, which carries
  -- `L₀` onto `L₀'`; so `L₀'` is Lagrangian.
  have hL₀' : ω'.IsLagrangian L₀' := by
    have hψ : SymplecticForm.IsSymplectomorphism ω₀ ω'
        ((χ 0).toLinearEquiv.trans (χ' 0).toLinearEquiv.symm) :=
      SymplecticForm.isSymplectomorphism_iff.2 fun u v ↦ by
        rw [← hχ'.apply_apply 0, ← hχ.apply_apply 0]
        simp
    have hψL : L₀.map ((χ 0).toLinearEquiv.trans (χ' 0).toLinearEquiv.symm).toLinearMap = L₀' := by
      rw [LinearEquiv.coe_trans, Submodule.map_comp, Submodule.map_symm_eq_iff]
      exact (hL' 0).trans (hL 0).symm
    exact hψL ▸ hψ.isLagrangian_map_iff.2 hL₀
  -- Move the model of `χ'` to `(W, ω₀)` by a linear symplectomorphism carrying `L₀` onto `L₀'`.
  have hdim : finrank ℝ W = finrank ℝ W' :=
    ((χ 0).toLinearEquiv.finrank_eq).trans (χ' 0).toLinearEquiv.finrank_eq.symm
  obtain ⟨e, he, heL⟩ := SymplecticForm.exists_isSymplectomorphism_map_eq ω₀ ω' hdim hL₀ hL₀'
  have he' : ∀ v w, ω' (e.toContinuousLinearEquiv v) (e.toContinuousLinearEquiv w) = ω₀ v w :=
    he.apply
  rw [← frameConleyZehnderIndex_trans hχ' e.toContinuousLinearEquiv he' hΦ hΦσ]
  -- Composing with `e` keeps the change of frame a loop.
  have hper_e : ((e.toContinuousLinearEquiv.trans (χ' 0)).trans (χ 0).symm) =
      ((e.toContinuousLinearEquiv.trans (χ' 1)).trans (χ 1).symm) :=
    ContinuousLinearEquiv.ext <| funext fun v ↦ DFunLike.congr_fun hper (e v)
  refine frameConleyZehnderIndex_eq_of_map_eq hχ (hχ'.trans _ he') hper_e hL₀ (fun t ↦ ?_) hΦ hΦσ
  -- Both sides are the image of `L₀` under `v ↦ χ'(t) (e v)`.
  rw [hL, ← hL', ← heL, ← Submodule.map_comp]
  exact congrArg L₀.map (LinearMap.ext fun v ↦ ContinuousLinearEquiv.trans_apply _ _ v)

end TauCeti.SmoothTwoForm
