/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder
import TauCeti.Geometry.Symplectic.Manifold.ConleyZehnder.Lagrangian

/-!
# The Conley–Zehnder index in vertical frames of a cotangent bundle

Let `T*M` be the cotangent bundle of a finite-dimensional manifold `M`, with its canonical
symplectic form `ω = -dλ` (`TauCeti.CotangentBundle.symplecticForm`), and let `π : T*M → M` be the
projection. The *vertical* tangent space at a covector `z` is the kernel of `dπ_z`, the tangent
space of the fibre through `z`; it is a Lagrangian subspace
(`TauCeti.CotangentBundle.isLagrangian_ker_mfderiv_proj`).

A *vertical frame* along a path `γ` in `T*M` is a symplectic frame `χ` along `γ`
(`TauCeti.SmoothTwoForm.IsSymplecticFrame`) that carries a fixed subspace `L₀` of its model onto the
vertical tangent spaces. Such an `L₀` is automatically Lagrangian, since `χ` is symplectic. This
file shows that a family `Φ` of linear symplectic maps along a loop, such as the linearized flow
of a Hamiltonian along a periodic orbit, has the same Conley–Zehnder index in any two vertical
frames whose change of frame is a loop, such as two periodic vertical frames, whatever their models
(`TauCeti.CotangentBundle.frameConleyZehnderIndex_eq_of_map_eq_ker_mfderiv_proj`): two such
frames differ by a loop preserving a Lagrangian, which has Maslov index zero. This is the
independence among vertical frames that the canonical grading of Floer homology of cotangent
bundles uses; the existence of vertical frames, and the twisted frames needed along loops whose
pulled-back tangent bundle is not orientable, are not covered here.

A periodic vertical frame along a loop `γ` trivializes the vertical tangent spaces along `γ`, the
fibres of `T*M` along `π ∘ γ`, so it exists only when the pullback of `TM` along `π ∘ γ` is
orientable. Along the other loops, the comparison above still applies to vertical frames whose
change of frame is a loop, but no such frame is constructed here.

## Main results

* `TauCeti.CotangentBundle.frameConleyZehnderIndex_eq_of_map_eq_ker_mfderiv_proj`: vertical
  frames whose change of frame is a loop give the same Conley–Zehnder index.

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

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
  {ω₀ : SymplecticForm W} {ω' : SymplecticForm W'} {L₀ : Submodule ℝ W} {L₀' : Submodule ℝ W'}

/-- **The Conley–Zehnder index in vertical frames.** Let `γ` be a path in `T*M` and `Φ` a family
of linear maps along `γ` preserving the canonical symplectic form. Let `χ` and `χ'` be symplectic
frames along `γ`, with models `(W, ω₀)` and `(W', ω')`, whose change of frame
`t ↦ χ(t)⁻¹ ∘ χ'(t)` is a loop, for instance periodic frames along a loop, and carrying subspaces
`L₀` of `W` and `L₀'` of `W'` onto the vertical tangent spaces `ker dπ` along `γ`. Then the
Conley–Zehnder index of `Φ` is the same in both frames. -/
theorem frameConleyZehnderIndex_eq_of_map_eq_ker_mfderiv_proj
    {γ : unitInterval → CotangentBundle I M}
    {Φ : ∀ t, TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ 0) ≃L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ t)}
    {χ : ∀ t, W ≃L[ℝ] TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ t)}
    {χ' : ∀ t, W' ≃L[ℝ] TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ t)}
    (hχ : SmoothTwoForm.IsSymplecticFrame (symplecticForm I M) ω₀ γ χ)
    (hχ' : SmoothTwoForm.IsSymplecticFrame (symplecticForm I M) ω' γ χ')
    (hper : (χ' 0).trans (χ 0).symm = (χ' 1).trans (χ 1).symm)
    (hL : ∀ t, L₀.map (χ t : W →ₗ[ℝ] TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ t)) =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) (γ t)).ker)
    (hL' : ∀ t, L₀'.map (χ' t : W' →ₗ[ℝ] TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ t)) =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) (γ t)).ker)
    (hΦ : Continuous fun q : unitInterval × TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (γ 0) ↦
      (⟨γ q.1, Φ q.1 q.2⟩ : TangentBundle (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M)))
    (hΦσ : ∀ t u v, (symplecticForm I M).eval₂ (γ t) (Φ t u) (Φ t v) =
      (symplecticForm I M).eval₂ (γ 0) u v) :
    SmoothTwoForm.frameConleyZehnderIndex ω' hχ' hΦ hΦσ =
      SmoothTwoForm.frameConleyZehnderIndex ω₀ hχ hΦ hΦσ := by
  -- The model subspace `L₀` is Lagrangian, since `χ` carries it onto the vertical tangent spaces,
  -- which are.
  have hL₀ : ω₀.IsLagrangian L₀ :=
    (hχ.isLagrangian_map_iff isSymplectic_symplecticForm.isNondegenerate 0).1
      (hL 0 ▸ isLagrangian_ker_mfderiv_proj (γ 0))
  exact SmoothTwoForm.frameConleyZehnderIndex_eq_of_map_eq_of_map_eq hχ hχ' hper hL₀ hL hL' hΦ
    hΦσ

end TauCeti.CotangentBundle
