/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic

/-!
# Transverse slices through a critical submanifold

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold`), and let `γ : X → M` be a `C²` map from a real
normed space with `γ 0 = i s`. Then `f ∘ γ` has a critical point at `0`, and its Hessian there is
the normal Hessian of the submanifold
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`) read through the **normal
derivative** `u ↦ [dγ₀ u]` of `γ`, the derivative of `γ` at `0` followed by the quotient map onto
the normal space `TangentSpace I (i s) ⧸ range (di)`. This is the second-order chain rule at a
critical point (`TauCeti.criticalHessian_comp_apply`) together with the fact that the tangent
directions of the submanifold lie in the kernel of the critical Hessian.

When the normal derivative is bijective, `γ` is a **transverse slice** through the submanifold at
`s`: a copy of the normal space, as for the fibres of a tubular neighbourhood or of the normal
exponential. Then `f ∘ γ` has a nondegenerate critical point at `0` exactly when the normal
Hessian is nondegenerate at `s`, and its Morse index at `0` is the Morse index of `f` at `i s`. In
particular, along a Morse–Bott critical submanifold every transverse slice has a nondegenerate
critical point on the submanifold, of the index of the submanifold. This is Bott's description of
a nondegenerate critical manifold through its normal slices, and it is the input of the Morse–Bott
lemma on the normal bundle, where `f` is read along the fibres of a tubular neighbourhood.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.fderiv_comp_eq_zero`: `f ∘ γ` is critical at `0`.
* `IsCriticalSubmanifold.fderiv_fderiv_comp_apply`: its Hessian at `0` is the normal Hessian on
  normal derivatives.
* `IsCriticalSubmanifold.isNondegenerateCriticalPoint_comp_iff`: for a transverse slice, `0` is a
  nondegenerate critical point of `f ∘ γ` exactly when the normal Hessian at `s` is nondegenerate.
* `IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp`: along a Morse–Bott
  submanifold every transverse slice has a nondegenerate critical point at `0`.
* `IsCriticalSubmanifold.morseIndex_comp`: the Morse index of a transverse slice at `0` is the
  Morse index of `f` at `i s`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public noncomputable section

open Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {γ : X → M} {s : S}

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (hγ0 : γ 0 = i s) (hγ : ContMDiffAt 𝓘(ℝ, X) I 2 γ 0)
include h hγ0 hγ

omit [I.Boundaryless] [IsManifold I 2 M] in
/-- A `C²` map through a critical submanifold composes with `f` to a `C²` function at `0`. -/
theorem contDiffAt_comp : ContDiffAt ℝ 2 (f ∘ γ) 0 := by
  have hf : ContMDiffAt I 𝓘(ℝ) 2 f (γ 0) := hγ0 ▸ h.contMDiffAt s
  exact (hf.comp 0 hγ).contDiffAt

omit [I.Boundaryless] [IsManifold I 2 M] in
/-- A map through a point of a critical submanifold composes with `f` to a function with a
critical point at `0`. -/
theorem fderiv_comp_eq_zero : fderiv ℝ (f ∘ γ) 0 = 0 := by
  have hf : MDifferentiableAt I 𝓘(ℝ) f (γ 0) :=
    hγ0 ▸ (h.contMDiffAt s).mdifferentiableAt two_ne_zero
  have hcrit : γ 0 ∈ criticalPoints I f := hγ0 ▸ h.mem_criticalPoints s
  have hcomp := mfderiv_comp (0 : X) hf (hγ.mdifferentiableAt two_ne_zero)
  rw [mem_criticalPoints_iff_mfderiv_eq_zero.mp hcrit, ContinuousLinearMap.zero_comp,
    mfderiv_eq_fderiv] at hcomp
  exact hcomp

/-- **The Hessian of `f` along a map through a critical submanifold.** If `γ 0 = i s`, the Hessian
at `0` of `f ∘ γ` is the normal Hessian at `s` evaluated on the normal classes of the derivatives
of `γ` at `0`. -/
theorem fderiv_fderiv_comp_apply (u w : X) :
    fderiv ℝ (fderiv ℝ (f ∘ γ)) 0 u w =
      h.normalHessian hn s (i.normalClass s hn (mfderiv 𝓘(ℝ, X) I γ 0 u))
        (i.normalClass s hn (mfderiv 𝓘(ℝ, X) I γ 0 w)) := by
  have key := criticalHessian_comp_apply hγ0 (h.contMDiffAt s) hγ (h.mem_criticalPoints s) u w
  rw [criticalHessian_modelSpace] at key
  exact key.trans (h.normalHessian_normalClass hn s _ _).symm

variable (hL : Bijective fun u : X ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, X) I γ 0 u))
include hL

/-- The normal derivative of a transverse slice, as a linear equivalence onto the normal space. -/
private def normalDerivEquiv : X ≃ₗ[ℝ] i.NormalSpace s hn :=
  LinearEquiv.ofBijective
    ((i.normalClass s hn).comp (mfderiv 𝓘(ℝ, X) I γ 0 : X →L[ℝ] TangentSpace I (i s)).toLinearMap)
    hL

omit [I.Boundaryless] [IsManifold I 2 M] h hγ0 hγ in
private theorem normalDerivEquiv_apply (u : X) :
    normalDerivEquiv hn hL u = i.normalClass s hn (mfderiv 𝓘(ℝ, X) I γ 0 u) := rfl

/-- **Bott's criterion along a transverse slice.** If the normal derivative of `γ` at `0` is
bijective, then `f ∘ γ` has a nondegenerate critical point at `0` exactly when the normal Hessian
of the critical submanifold at `s` is nondegenerate. -/
theorem isNondegenerateCriticalPoint_comp_iff [FiniteDimensional ℝ X] :
    IsNondegenerateCriticalPoint (f ∘ γ) 0 ↔ LinearMap.ker (h.normalHessian hn s) = ⊥ := by
  set L := normalDerivEquiv hn hL
  have hQ (u w : X) : fderiv ℝ (fderiv ℝ (f ∘ γ)) 0 u w = h.normalHessian hn s (L u) (L w) := by
    rw [h.fderiv_fderiv_comp_apply hn hγ0 hγ, normalDerivEquiv_apply, normalDerivEquiv_apply]
  constructor
  · intro hN
    refine (Submodule.eq_bot_iff _).mpr fun p hp ↦ ?_
    obtain ⟨u, rfl⟩ := L.surjective p
    -- A normal class in the kernel pairs to zero with every normal class, so its preimage lies in
    -- the kernel of the invertible slice Hessian.
    have hu : fderiv ℝ (fderiv ℝ (f ∘ γ)) 0 u = 0 := by
      ext w
      rw [hQ, LinearMap.mem_ker.mp hp, LinearMap.zero_apply,
        zero_apply]
    rw [hN.isInvertible.injective (hu.trans (map_zero _).symm), map_zero]
  · intro hker
    refine ⟨h.contDiffAt_comp hγ0 hγ, h.fderiv_comp_eq_zero hγ0 hγ,
      ContinuousLinearMap.isInvertible_of_injective <|
        (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_⟩
    -- The normal class of `u` pairs to zero with every normal class, so it vanishes.
    have hLu : L u ∈ LinearMap.ker (h.normalHessian hn s) := by
      rw [LinearMap.mem_ker]
      ext p
      obtain ⟨w, rfl⟩ := L.surjective p
      rw [← hQ, hu, zero_apply, LinearMap.zero_apply]
    rwa [hker, Submodule.mem_bot, map_eq_zero_iff _ L.injective] at hLu

/-- **The index of a transverse slice.** If the normal derivative of `γ` at `0` is bijective, the
Morse index of `f ∘ γ` at `0` is the Morse index of `f` at `i s`. -/
theorem morseIndex_comp [FiniteDimensional ℝ E] :
    morseIndex (f ∘ γ) 0 = manifoldMorseIndex I f (i s) := by
  set L := normalDerivEquiv hn hL
  have hQ : hessianQuadraticForm (f ∘ γ) 0 =
      (h.normalHessian hn s).toQuadraticMap.comp L.toLinearMap := by
    ext u
    rw [hessianQuadraticForm_apply, h.fderiv_fderiv_comp_apply hn hγ0 hγ]
    rfl
  rw [morseIndex_def, hQ, ← h.sigNeg_normalHessian hn s]
  exact QuadraticMap.Equivalent.sigNeg_eq
    ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv (h.normalHessian hn s).toQuadraticMap L).symm⟩

end IsCriticalSubmanifold

/-- **Transverse slices of a Morse–Bott submanifold are nondegenerate.** If `i` is a Morse–Bott
critical submanifold of `f` and `γ` is a `C²` map with `γ 0 = i s` whose normal derivative at `0`
is bijective, then `f ∘ γ` has a nondegenerate critical point at `0`. -/
theorem IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_comp
    [FiniteDimensional ℝ X] (h : i.IsNondegenerateCriticalSubmanifold f) (hγ0 : γ 0 = i s)
    (hγ : ContMDiffAt 𝓘(ℝ, X) I 2 γ 0)
    (hL : Bijective fun u : X ↦ i.normalClass s hn (mfderiv 𝓘(ℝ, X) I γ 0 u)) :
    IsNondegenerateCriticalPoint (f ∘ γ) 0 :=
  (h.toIsCriticalSubmanifold.isNondegenerateCriticalPoint_comp_iff hn hγ0 hγ hL).mpr
    (h.ker_normalHessian hn s)

end TauCeti.SmoothEmbedding
