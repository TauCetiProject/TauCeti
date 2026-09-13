/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Basic
public import TauCeti.Analysis.Normed.Operator.Splitting
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# The tangent space of a regular level set away from its base point

`TauCeti.levelSetChart` parametrizes the level set `{x | f x = c}` near a regular point `a` by the
kernel of the derivative `f'` there, and `TauCeti.hasStrictFDerivAt_coe_levelSetChart_symm`
computes the derivative of that parametrization **at the chart origin**: it is the inclusion of
`ker f'` into the ambient space. At any other point of the chart the derivative need not be that
inclusion, because the level set may have turned: its tangent space there is the kernel of the
derivative of `f` at that point, which need not be the kernel at `a`.

This file computes the derivative at those other points. At a chart point `k` whose image `z` lies
in `HasStrictFDerivAt.implicitCoordSource`, the neighbourhood on which the implicit-function
coordinate map keeps an invertible derivative, the inverse chart is differentiable with derivative
`ContinuousLinearMap.kerSection A P`, where `A` is the derivative of `f` at `z` and `P` is the
projection chosen by the complementation hypothesis. That map is injective with range exactly
`ker A`: the chart identifies the fixed model space `ker f'` with the moving tangent space of the
level set, linearly and isomorphically.

Two consequences deserve naming on their own. The derivative of `f` is automatically surjective at
every point of that neighbourhood (`HasStrictFDerivAt.surjective_of_mem_implicitCoordSource`), so
"regular point" is not an extra hypothesis nearby; and the tangent space is therefore
complemented, being the range of a section.

This is the pointwise input that turns a statement proved at one point of a Fredholm level set
into a statement about a neighbourhood of it, which is what the parametric transversality package
of McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3, needs:
there the conclusion must hold at every nearby solution, not only at the one the chart is centred
on.

## Main results

* `TauCeti.hasFDerivAt_coe_levelSetChart_symm_of_mem`: the derivative of the inverse chart at a
  point of the coordinate neighbourhood is the kernel section of the derivative there.
* `TauCeti.range_fderiv_coe_levelSetChart_symm_of_mem`: its range is the kernel of that
  derivative, the tangent space of the level set.
* `TauCeti.fderiv_coe_levelSetChart_symm_injective_of_mem`: it is injective, so the chart is an
  immersion.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {K E F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[K] F} {a : E} {c : F}

/-- **The derivative of the inverse regular-level-set chart away from its origin.** At a chart
point `k` whose image lies in the neighbourhood `HasStrictFDerivAt.implicitCoordSource`, the
inverse chart is differentiable, with derivative the section
`ContinuousLinearMap.kerSection A (Classical.choose hker)` of the derivative `A` of `f` there.

`TauCeti.hasStrictFDerivAt_coe_levelSetChart_symm` is the case `k = 0`, where `A` may be taken to
be `f'` and the section is the inclusion of `ker f'`. -/
theorem hasFDerivAt_coe_levelSetChart_symm_of_mem (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : k ∈ (levelSetChart hf hf' hker ha).target)
    (hmem : (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E) ∈
      hf.implicitCoordSource hf' hker)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) :
    HasFDerivAt (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E))
      (A.kerSection (Classical.choose hker)) k := by
  subst c
  set Φ := hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker with hΦ
  have hval : (((levelSetChart hf hf' hker rfl).symm k : ↥{x | f x = f a}) : E) = Φ.symm (f a, k) :=
    levelSetChart_symm_apply hf hf' hker rfl hk
  have hktarget : (f a, k) ∈ Φ.target := by
    have hk' := hk
    rwa [levelSetChart_target, Set.mem_preimage] at hk'
  have hfun : ⇑Φ = fun x ↦ (f x, Classical.choose hker (x - a)) :=
    funext (hf.implicitToOpenPartialHomeomorphOfComplemented_apply hf' hker)
  have hcoord : HasFDerivAt Φ (A.prod (Classical.choose hker)) (Φ.symm (f a, k)) := by
    rw [hfun]
    exact (hval ▸ hA).prodMk
      ((Classical.choose hker).hasFDerivAt.comp _ ((hasFDerivAt_id _).sub_const a))
  obtain ⟨e, he⟩ :=
    hf.isInvertible_prod_of_mem_implicitCoordSource hf' hker (hval ▸ hmem) (hval ▸ hA)
  have hsymm : HasFDerivAt Φ.symm ((A.prod (Classical.choose hker)).inverse) (f a, k) := by
    have hd : HasFDerivAt Φ (e : E →L[K] F × ↥f'.ker) (Φ.symm (f a, k)) := by rwa [he]
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact Φ.hasFDerivAt_symm hktarget hd
  have hslice : HasFDerivAt (fun k' : ↥f'.ker ↦ ((f a, k') : F × ↥f'.ker))
      (ContinuousLinearMap.inr K F ↥f'.ker) k :=
    (hasFDerivAt_const (f a) k).prodMk (hasFDerivAt_id k)
  have hcomp := hsymm.comp k hslice
  have hsec : (A.prod (Classical.choose hker)).inverse ∘L ContinuousLinearMap.inr K F ↥f'.ker =
      A.kerSection (Classical.choose hker) :=
    ContinuousLinearMap.eq_kerSection ⟨e, he⟩ fun v ↦ by rw [← he]; simp
  rw [← hsec]
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(levelSetChart hf hf' hker rfl).open_target.mem_nhds hk] with k' hk'
  exact levelSetChart_symm_apply hf hf' hker rfl hk'

/-- The Fréchet derivative of the inverse regular-level-set chart at a point of the coordinate
neighbourhood. -/
theorem fderiv_coe_levelSetChart_symm_of_mem (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : k ∈ (levelSetChart hf hf' hker ha).target)
    (hmem : (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E) ∈
      hf.implicitCoordSource hf' hker)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) :
    fderiv K (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) k =
      A.kerSection (Classical.choose hker) :=
  (hasFDerivAt_coe_levelSetChart_symm_of_mem hf hf' hker ha hk hmem hA).fderiv

/-- **The tangent space of a regular level set.** The derivative of the inverse chart at a point of
the coordinate neighbourhood has range exactly the kernel of the derivative of `f` there. -/
theorem range_fderiv_coe_levelSetChart_symm_of_mem (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : k ∈ (levelSetChart hf hf' hker ha).target)
    (hmem : (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E) ∈
      hf.implicitCoordSource hf' hker)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) :
    (fderiv K (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) k).range =
      A.ker := by
  rw [fderiv_coe_levelSetChart_symm_of_mem hf hf' hker ha hk hmem hA]
  exact ContinuousLinearMap.range_kerSection
    (hf.isInvertible_prod_of_mem_implicitCoordSource hf' hker hmem hA)

/-- The inverse chart is an immersion: its derivative at a point of the coordinate neighbourhood
is injective. -/
theorem fderiv_coe_levelSetChart_symm_injective_of_mem (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (ha : f a = c) {k : ↥f'.ker}
    (hk : k ∈ (levelSetChart hf hf' hker ha).target)
    (hmem : (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E) ∈
      hf.implicitCoordSource hf' hker)
    {A : E →L[K] F}
    (hA : HasFDerivAt f A (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) :
    Function.Injective
      (fderiv K (fun k ↦ (((levelSetChart hf hf' hker ha).symm k : ↥{x | f x = c}) : E)) k) := by
  rw [fderiv_coe_levelSetChart_symm_of_mem hf hf' hker ha hk hmem hA]
  exact ContinuousLinearMap.kerSection_injective
    (hf.isInvertible_prod_of_mem_implicitCoordSource hf' hker hmem hA)

end TauCeti

end
