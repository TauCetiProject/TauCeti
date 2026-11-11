/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Wirtinger.Polydisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Local exactness for smooth forms of type `(0,1)`

On a complex vector space, the Dolbeault differential of a smooth function is its conjugate
Wirtinger derivative. For a smooth `(0,1)`-form `η`, its differential on `v,w` is
`∂bar η(v,w) = ∂bar(η(w))(v) - ∂bar(η(v))(w)`. Thus closedness gives the symmetry of
coordinate derivatives needed by the coordinate Dolbeault lemma.

An ambient smooth `(0,1)`-form whose Dolbeault differential vanishes on a finite product of
planar domains has a smooth primitive near every compact subproduct. Both the input and the
primitive use
`SmoothForm`; the coordinate solver supplies a function, which is extended smoothly before
being bundled as a zero-form. Exactness is asserted near the compact product, with no claim
of exactness on the whole original domain.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 2.1.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §2.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold ComplexConjugate

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On a complex model space the Dolbeault differential of a smooth zero-form is the conjugate
Wirtinger derivative of its value function. -/
theorem delBar_apply_eq_conjWirtingerDeriv (f : SmoothForm 𝓘(ℝ, E) E F 0) (z v : E) :
    ((ofComplexManifold E E).delBar f).1 z ![v] =
      conjWirtingerDeriv (fun y ↦ f.1 y 0) z v := by
  have h := delBar_apply_apply (ofComplexManifold E E) f z v
  -- Identify the model-space tangent fibre and its identity comparison with `E`.
  simp only [ofComplexManifold_apply, mvfderiv_eq_fderiv] at h
  rw [conjWirtingerDeriv_apply]
  convert h using 1; rfl

variable {η : SmoothForm 𝓘(ℝ, E) E F 1}

/-- Read the type equation of a one-form in the model tangent fibre. -/
private theorem IsOfType.modelSpace (hη : η.IsOfType (ofComplexManifold E E) 0 1) (z : E) :
    (η.1 z : E [⋀^Fin 1]→L[ℝ] F).IsOfType (I • ContinuousLinearMap.id ℝ E) 0 1 := by
  have h := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h
  -- The manifold tangent and coefficient fibres here are the underlying model spaces.
  convert h using 1

/-- On a smooth `(0,1)`-form the Dolbeault differential is the alternating conjugate Wirtinger
derivative of its evaluations on constant tangent vectors. -/
theorem IsOfType.delBar_apply_pair (hη : η.IsOfType (ofComplexManifold E E) 0 1)
    (z v w : E) :
    ((ofComplexManifold E E).delBar η).1 z ![v, w] =
      conjWirtingerDeriv (fun y ↦ η.1 y ![w]) z v -
        conjWirtingerDeriv (fun y ↦ η.1 y ![v]) z w := by
  let Θ : E → E [⋀^Fin 1]→L[ℝ] F := η.1
  let β : E [⋀^Fin 2]→L[ℝ] F := (mextDerivₗ 𝓘(ℝ, E) 1 η).1 z
  -- Express tangent-fibre evaluations through the model-space field `Θ`.
  change ((ofComplexManifold E E).delBar η).1 z ![v, w] =
    conjWirtingerDeriv (fun y ↦ Θ y ![w]) z v -
      conjWirtingerDeriv (fun y ↦ Θ y ![v]) z w
  have hd : ContDiff ℝ ∞ Θ := isSmoothForm_modelSpace_iff.1 η.isSmoothForm
  have heval (u : E) : DifferentiableAt ℝ (fun y ↦ Θ y ![u]) z :=
    (ContinuousAlternatingMap.apply ℝ E F ![u]).differentiableAt.comp z
      (hd.differentiable (by simp) z)
  have hI (u : E) : (fun y ↦ Θ y ![I • u]) = fun y ↦ -I • Θ y ![u] := by
    funext y
    have ht : (Θ y).IsOfType (I • ContinuousLinearMap.id ℝ E) 0 1 := hη.modelSpace y
    simpa only [conj_I] using ht.map_smul_conj I u
  have hβ (a b : E) : β ![a, b] =
      fderiv ℝ (fun y ↦ Θ y ![b]) z a - fderiv ℝ (fun y ↦ Θ y ![a]) z b := by
    have hflat : β = extDeriv Θ z := by
      have h := mextDeriv_eq_extDeriv η.1 z
      rw [← mextDerivₗ_apply] at h
      -- Only the model tangent and trivial coefficient fibres differ in this comparison.
      convert h using 1; rfl
    rw [hflat]
    simpa only [Matrix.vec_single_eq_const] using
      extDeriv_apply_pair_of_differentiableAt (hd.differentiable (by simp) z) a b
  have hδ : ((ofComplexManifold E E).delBar η).1 z =
      (I • ContinuousLinearMap.id ℝ E).typeProjection 0 2 β := by
    rw [hη.delBar_eq, coe_typeProjection]
    exact congrArg (fun A : E →L[ℝ] E ↦ A.typeProjection 0 2 β)
      (toEndomorphism_ofComplexManifold (E := E) z)
  rw [hδ]
  -- Evaluation now takes place entirely in `E`, rather than its opaque tangent-space synonym.
  change ((I • ContinuousLinearMap.id ℝ E).typeProjection 0 2 β : E [⋀^Fin 2]→L[ℝ] F)
    ![v, w] = conjWirtingerDeriv (fun y ↦ Θ y ![w]) z v -
      conjWirtingerDeriv (fun y ↦ Θ y ![v]) z w
  rw [ContinuousLinearMap.typeProjection_zero_two_apply (by simp [smul_smul])]
  simp only [smul_apply, ContinuousLinearMap.id_apply, hβ, hI,
    fderiv_fun_const_smul (heval _) _, conjWirtingerDeriv_apply]
  simp only [smul_sub, smul_add, smul_smul, mul_neg, I_mul_I]
  module

section Coordinates

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {η : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F 1}

/-- A closed smooth `(0,1)`-form satisfies the symmetry of conjugate coordinate derivatives. -/
theorem IsOfType.conjWirtingerDeriv_apply_single_eq
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 1) {z : ι → ℂ}
    (hz : ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).1 z = 0) (i j : ι) :
    conjWirtingerDeriv (fun y ↦ η.1 y ![Pi.single j 1]) z (Pi.single i 1) =
      conjWirtingerDeriv (fun y ↦ η.1 y ![Pi.single i 1]) z (Pi.single j 1) := by
  apply sub_eq_zero.mp
  rw [← hη.delBar_apply_pair, hz]
  rfl

variable [CompleteSpace F]

omit [DecidableEq ι] in
/-- A smooth `(0,1)`-form closed on a product of planar domains is Dolbeault-exact near every
compact subproduct, with a globally smooth zero-form as a representative of the primitive. -/
theorem IsOfType.exists_delBar_eventually_eq_of_pi
    (hη : η.IsOfType (ofComplexManifold (ι → ℂ) (ι → ℂ)) 0 1)
    {U K : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i)
    (hclosed : ∀ z ∈ univ.pi U,
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar η).1 z = 0) :
    ∃ f : SmoothForm 𝓘(ℝ, ι → ℂ) (ι → ℂ) F 0, ∀ᶠ z in 𝓝ˢ (univ.pi K),
      ((ofComplexManifold (ι → ℂ) (ι → ℂ)).delBar f).1 z = η.1 z := by
  classical
  have hd : ContDiff ℝ ∞ (fun y : ι → ℂ ↦ η.1 y) :=
    isSmoothForm_modelSpace_iff.1 η.isSmoothForm
  obtain ⟨u, hu⟩ := exists_contDiffAt_conjWirtingerDeriv_apply_single_eventually_eq_of_pi hU
    (f := fun j y ↦ η.1 y ![Pi.single j 1])
    (fun j ↦ ((ContinuousAlternatingMap.apply ℝ (ι → ℂ) F ![Pi.single j 1]).contDiff.comp
      hd).contDiffOn)
    (fun z hz i j ↦ hη.conjWirtingerDeriv_apply_single_eq (hclosed z hz) i j) hK hKU
  obtain ⟨V, hV, hKV, hVu⟩ := eventually_nhdsSet_iff_exists.1 hu
  have huV : ContDiffOn ℝ ∞ u V := fun z hz ↦ (hVu z hz).1.contDiffWithinAt
  obtain ⟨g, hg, -, -, -, hgu⟩ :=
    huV.exists_contDiff_eventuallyEq_on_isCompact (isCompact_univ_pi hK) hV hKV
  let f := ofFunction (I := 𝓘(ℝ, ι → ℂ)) ⟨g, hg.contMDiff⟩
  refine ⟨f, eventually_nhdsSet_iff_forall.2 fun z hz ↦ ?_⟩
  filter_upwards [hV.mem_nhds (hKV hz), (hgu z hz).eventuallyEq_nhds] with y hyV hgy
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv]
  have hf := delBar_apply_eq_conjWirtingerDeriv f y (v 0)
  have hfg : (fun y ↦ f.1 y 0) = g := ofFunction_apply_zero _
  rw [hfg] at hf
  refine hf.trans ?_
  -- Expand both conjugate-linear covectors in the same complex coordinate basis.
  have heq (i : ι) : conjWirtingerDeriv g y (Pi.single i 1) = η.1 y ![Pi.single i 1] := by
    rw [hgy.conjWirtingerDeriv_eq]
    exact (hVu y hyV).2 i
  have hηsum := (hη.modelSpace y).apply_eq_sum_conj_smul (ι := ι) (v 0)
  refine Eq.trans ?_ hηsum.symm
  let w : ι → ℂ := v 0
  have hsum : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    simp [← Pi.single_smul, Finset.univ_sum_single]
  calc
    conjWirtingerDeriv g y w = conjWirtingerDeriv g y (∑ i, w i • Pi.single i (1 : ℂ)) :=
      congrArg (conjWirtingerDeriv g y) hsum
    _ = _ := by
      simp only [map_sum, map_smulₛₗ, starRingEnd_apply, heq]
      rfl

end Coordinates

end TauCeti.SmoothForm
