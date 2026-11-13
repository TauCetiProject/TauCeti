/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Analysis.Complex.Wirtinger.Polydisc
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace

/-!
# Local exactness for smooth forms of type `(0,1)`

On a complex vector space, the Dolbeault differential of a smooth `(0,1)`-form `η` on `v,w` is
`∂bar η(v,w) = ∂bar(η(w))(v) - ∂bar(η(v))(w)` (`SmoothForm.IsOfType.delBar_apply_pair`). Thus
closedness gives the symmetry of coordinate derivatives needed by the coordinate Dolbeault lemma.

An ambient smooth `(0,1)`-form whose Dolbeault differential vanishes on a finite product of
planar domains has a smooth primitive near every compact subproduct. Both the input and the
primitive use
`SmoothForm`; the coordinate solver supplies a function, which is extended smoothly before
being bundled as a zero-form. Exactness is asserted near the compact product, with no claim
of exactness on the whole original domain.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.conjWirtingerDeriv_apply_single_eq`: the symmetry of conjugate
  coordinate derivatives of a closed `(0,1)`-form.
* `TauCeti.SmoothForm.IsOfType.exists_delBar_eventually_eq_of_pi`: local exactness of closed
  `(0,1)`-forms on products of planar domains.

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
  have hηsum := (hη.apply_modelSpace y).apply_eq_sum_conj_smul (ι := ι) (v 0)
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
