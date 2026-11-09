/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# First-jet coordinate transformations

The local first jet of a section with values in `F` is a pair in `F × (E →L[𝕜] F)`.
Under a change of base coordinates `h` and a varying linear fibre map `g`, the section
becomes `x ↦ g x (s (h x))`. Its value and derivative transform by

`(v, A) ↦ (g x v, (dg x).flip v + (g x).comp (A.comp (dh x)))`.

`ContinuousLinearMap.firstJetPullback` bundles this linear transformation. We prove its
composition law, invertibility when the value and base maps are invertible, agreement with
the derivative of an actual section, and smoothness for smoothly varying coefficients.
The open-set smoothness theorem applies to chart overlaps. These are local coordinate
results; no global jet bundle or connection is chosen here.

## References

* Kolář, Michor and Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17, for first jets of vector bundles and their coordinate transformations.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff

variable {𝕜 E E' E'' F G H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace ContinuousLinearMap

/-- The first-jet transformation with fibre map `a`, fibre derivative `b`, and
base derivative `c`. The latter points from the new base coordinates to the old ones. -/
def firstJetPullback (a : F →L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G) (c : E' →L[𝕜] E) :
    (F × (E →L[𝕜] F)) →L[𝕜] G × (E' →L[𝕜] G) :=
  (a.comp (fst 𝕜 F (E →L[𝕜] F))).prod
    (b.flip.comp (fst 𝕜 F (E →L[𝕜] F)) +
      (compL 𝕜 E' F G a).comp
        (((compL 𝕜 E' E F).flip c).comp (snd 𝕜 F (E →L[𝕜] F))))

@[simp]
theorem firstJetPullback_apply (a : F →L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G)
    (c : E' →L[𝕜] E) (j : F × (E →L[𝕜] F)) :
    a.firstJetPullback b c j = (a j.1, b.flip j.1 + a.comp (j.2.comp c)) :=
  (rfl)

/-- Constant identity coordinate changes act identically on first jets. -/
@[simp]
theorem firstJetPullback_id :
    (ContinuousLinearMap.id 𝕜 F).firstJetPullback (0 : E →L[𝕜] F →L[𝕜] F)
        (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (F × (E →L[𝕜] F)) := by
  apply ContinuousLinearMap.ext
  intro j
  simp

/-- Composition of first-jet transformations is the chain/product rule. -/
theorem firstJetPullback_comp (a : F →L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G)
    (c : E' →L[𝕜] E) (a' : G →L[𝕜] H) (b' : E'' →L[𝕜] G →L[𝕜] H)
    (c' : E'' →L[𝕜] E') :
    (a'.firstJetPullback b' c').comp (a.firstJetPullback b c) =
      (a'.comp a).firstJetPullback
        ((compL 𝕜 F G H a').comp (b.comp c') +
          ((compL 𝕜 F G H).flip a).comp b') (c.comp c') := by
  apply ContinuousLinearMap.ext
  intro j
  apply Prod.ext
  · simp
  · ext v
    simp [add_assoc, add_left_comm]

/-- The transformation of an actual first jet under a varying fibre map and a base map. -/
theorem _root_.HasFDerivAt.firstJetPullback {g : E' → F →L[𝕜] G} {g' : E' →L[𝕜] F →L[𝕜] G}
    {h : E' → E} {h' : E' →L[𝕜] E} {s : E → F} {s' : E →L[𝕜] F} {x : E'}
    (hg : HasFDerivAt g g' x) (hh : HasFDerivAt h h' x)
    (hs : HasFDerivAt s s' (h x)) :
    HasFDerivAt (fun y ↦ g y (s (h y)))
      ((g x).firstJetPullback g' h' (s (h x), s')).2 x := by
  simpa only [firstJetPullback_apply, Function.comp_apply, add_comm] using
    hg.clm_apply (hs.comp x hh)

/-- Smooth families of coefficients and jets give smooth transformed first jets. -/
theorem _root_.ContDiffOn.firstJetPullback {n : ℕ∞ω} {u : Set X}
    {a : X → F →L[𝕜] G} {b : X → E' →L[𝕜] F →L[𝕜] G} {c : X → E' →L[𝕜] E}
    {j : X → F × (E →L[𝕜] F)}
    (ha : ContDiffOn 𝕜 n a u) (hb : ContDiffOn 𝕜 n b u) (hc : ContDiffOn 𝕜 n c u)
    (hj : ContDiffOn 𝕜 n j u) :
    ContDiffOn 𝕜 n (fun x ↦ (a x).firstJetPullback (b x) (c x) (j x)) u := by
  have hterm : ContDiffOn 𝕜 n (fun x ↦ (b x).flip (j x).1) u := by
    refine (((ContinuousLinearMap.apply 𝕜 G).contDiff.comp_contDiffOn hj.fst).clm_comp
      hb).congr ?_
    intro x _
    ext v
    simp [flip_apply, apply_apply]
  simpa only [firstJetPullback_apply, Function.comp_apply] using
    (ha.clm_apply hj.fst).prodMk (hterm.add (ha.clm_comp (hj.snd.clm_comp hc)))

end ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- The first-jet coordinate equivalence for invertible fibre and base maps.
The off-diagonal coefficient `b` is arbitrary. -/
def firstJetPullback (a : F ≃L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G) (c : E' ≃L[𝕜] E) :
    (F × (E →L[𝕜] F)) ≃L[𝕜] G × (E' →L[𝕜] G) :=
  a.skewProd (c.symm.arrowCongr a) b.flip

@[simp]
theorem coe_firstJetPullback (a : F ≃L[𝕜] G)
    (b : E' →L[𝕜] F →L[𝕜] G) (c : E' ≃L[𝕜] E) :
    (a.firstJetPullback b c : _ →L[𝕜] _) =
      a.toContinuousLinearMap.firstJetPullback b c.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro j
  apply Prod.ext
  · rfl
  · ext v
    simp [firstJetPullback, skewProd_apply, add_comm]

@[simp]
theorem firstJetPullback_apply (a : F ≃L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G)
    (c : E' ≃L[𝕜] E) (j : F × (E →L[𝕜] F)) :
    a.firstJetPullback b c j =
      (a j.1, b.flip j.1 + a.toContinuousLinearMap.comp (j.2.comp c.toContinuousLinearMap)) := by
  simpa only [ContinuousLinearMap.firstJetPullback_apply, coe_coe] using
    congrArg (fun f ↦ f j) (coe_firstJetPullback a b c)

@[simp]
theorem firstJetPullback_symm_apply (a : F ≃L[𝕜] G) (b : E' →L[𝕜] F →L[𝕜] G)
    (c : E' ≃L[𝕜] E) (j : G × (E' →L[𝕜] G)) :
    (a.firstJetPullback b c).symm j =
      (a.symm j.1, a.symm.toContinuousLinearMap.comp
        ((j.2 - b.flip (a.symm j.1)).comp c.symm.toContinuousLinearMap)) :=
  (rfl)

end ContinuousLinearEquiv

namespace TauCeti

/-- On open chart domains, smooth fibre and base maps induce smooth transformations of
first jets. At finite regularity the transformation uses one derivative. -/
theorem contDiffOn_firstJetPullback_fderiv {n m : ℕ∞ω} {u : Set E'}
    {g : E' → F →L[𝕜] G} {h : E' → E} (hu : IsOpen u)
    (hg : ContDiffOn 𝕜 n g u) (hh : ContDiffOn 𝕜 n h u) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m
      (fun p : E' × (F × (E →L[𝕜] F)) ↦
        (g p.1).firstJetPullback (fderiv 𝕜 g p.1) (fderiv 𝕜 h p.1) p.2)
      (u ×ˢ Set.univ) := by
  have hfst : ContDiffOn 𝕜 m (fun p : E' × (F × (E →L[𝕜] F)) ↦ p.1) (u ×ˢ Set.univ) :=
    contDiff_fst.contDiffOn
  have hmem : Set.MapsTo (fun p : E' × (F × (E →L[𝕜] F)) ↦ p.1) (u ×ˢ Set.univ) u :=
    fun _ hp ↦ hp.1
  exact ((hg.of_le (le_trans le_self_add hmn)).comp hfst hmem).firstJetPullback
    ((hg.fderiv_of_isOpen hu hmn).comp hfst hmem)
    ((hh.fderiv_of_isOpen hu hmn).comp hfst hmem) contDiff_snd.contDiffOn

end TauCeti
