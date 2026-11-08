/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.FirstOrder

/-!
# Nonlinear first-jet coordinate changes

In local bundle coordinates a first jet is a value `v` and a derivative `A`.
If `h` changes the base coordinates and `g(x, v)` changes the fibre coordinates,
the new section is `x ↦ g(x, s(h(x)))`. The map `firstJetCoordChange` implements
its value and derivative, allowing nonlinear, base-dependent fibre changes.

We prove the chain rule on actual sections, the identity and cocycle laws, and
smoothness on open chart domains. For a fixed value the change in derivatives
is affine: differences transform by the vertical derivative of `g` and the
base derivative of `h`. In particular this does not select a zero derivative
independently of coordinates. These are local coordinate results, not a
construction of the global jet bundle.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A, for local jet coordinates.
* Kolář, Michor and Slovák, *Natural Operations in Differential Geometry*,
  Chapter 12, for jets of fibred manifolds and their coordinate transformations.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Topology

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

namespace TauCeti

/-- Pull back first jets by a base map and a possibly nonlinear, base-dependent
fibre map. Differentiability is required by the calculus lemmas, not by this definition. -/
def firstJetCoordChange (h : E' → E) (g : E' × F → G) (x : E')
    (j : F × (E →L[𝕜] F)) : G × (E' →L[𝕜] G) :=
  (g (x, j.1), (fderiv 𝕜 g (x, j.1)).comp
    ((ContinuousLinearMap.id 𝕜 E').prod (j.2.comp (fderiv 𝕜 h x))))

@[simp]
theorem firstJetCoordChange_fst (h : E' → E) (g : E' × F → G) (x : E')
    (j : F × (E →L[𝕜] F)) : (firstJetCoordChange h g x j).1 = g (x, j.1) :=
  (rfl)

@[simp]
theorem firstJetCoordChange_snd_apply (h : E' → E) (g : E' × F → G) (x : E')
    (j : F × (E →L[𝕜] F)) (w : E') :
    (firstJetCoordChange h g x j).2 w = fderiv 𝕜 g (x, j.1) (w, j.2 (fderiv 𝕜 h x w)) :=
  (rfl)

/-- First-jet changes depend only on the germs of the coordinate maps. -/
theorem firstJetCoordChange_congr {h h' : E' → E} {g g' : E' × F → G} {x : E'}
    (j : F × (E →L[𝕜] F)) (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 (x, j.1)] g') :
    firstJetCoordChange h g x j = firstJetCoordChange h' g' x j := by
  apply Prod.ext
  · exact hg.eq_of_nhds
  · ext w
    simp only [firstJetCoordChange_snd_apply, hh.fderiv_eq, hg.fderiv_eq]

/-- The nonlinear coordinate change gives the derivative of a transformed section. -/
theorem _root_.HasFDerivAt.firstJetCoordChange {h : E' → E} {g : E' × F → G}
    {s : E → F} {A : E →L[𝕜] F} {x : E'}
    (hs : HasFDerivAt s A (h x)) (hh : DifferentiableAt 𝕜 h x)
    (hg : DifferentiableAt 𝕜 g (x, s (h x))) :
    HasFDerivAt (fun y ↦ g (y, s (h y)))
      (firstJetCoordChange h g x (s (h x), A)).2 x :=
  hg.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hs.comp x hh.hasFDerivAt))

/-- A jet computed before or after a nonlinear coordinate change has the same coordinates. -/
theorem firstJetCoordChange_fderiv {h : E' → E} {g : E' × F → G} {s : E → F} {x : E'}
    (hh : DifferentiableAt 𝕜 h x) (hg : DifferentiableAt 𝕜 g (x, s (h x)))
    (hs : DifferentiableAt 𝕜 s (h x)) :
    firstJetCoordChange h g x (s (h x), fderiv 𝕜 s (h x)) =
      (g (x, s (h x)), fderiv 𝕜 (fun y ↦ g (y, s (h y))) x) := by
  exact Prod.ext rfl (hs.hasFDerivAt.firstJetCoordChange hh hg).fderiv.symm

/-- Identity base and fibre changes act identically. -/
@[simp]
theorem firstJetCoordChange_id (x : E) (j : F × (E →L[𝕜] F)) :
    firstJetCoordChange (id : E → E) (Prod.snd : E × F → F) x j = j := by
  apply Prod.ext
  · rfl
  · ext w
    simp [fderiv_snd]

/-- The cocycle law for nonlinear fibre-coordinate changes, with both base and
fibre derivatives evaluated at their actual intermediate points. -/
theorem firstJetCoordChange_comp {h : E' → E} {k : E'' → E'}
    {g : E' × F → G} {l : E'' × G → H} {y : E''} (j : F × (E →L[𝕜] F))
    (hh : DifferentiableAt 𝕜 h (k y)) (hk : DifferentiableAt 𝕜 k y)
    (hg : DifferentiableAt 𝕜 g (k y, j.1))
    (hl : DifferentiableAt 𝕜 l (y, g (k y, j.1))) :
    firstJetCoordChange k l y (firstJetCoordChange h g (k y) j) =
      firstJetCoordChange (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) y j := by
  have hkg : HasFDerivAt (fun p : E'' × F ↦ g (k p.1, p.2))
      ((fderiv 𝕜 g (k y, j.1)).comp
        (((fderiv 𝕜 k y).comp (fst 𝕜 E'' F)).prod (snd 𝕜 E'' F))) (y, j.1) :=
    hg.hasFDerivAt.comp (y, j.1)
      ((hk.hasFDerivAt.comp (y, j.1) hasFDerivAt_fst).prodMk hasFDerivAt_snd)
  have hd := (hl.hasFDerivAt.comp (y, j.1) (hasFDerivAt_fst.prodMk hkg)).fderiv
  dsimp only [Function.comp_def] at hd
  apply Prod.ext
  · rfl
  · ext w
    simp [firstJetCoordChange_snd_apply, hd, fderiv_comp y hh hk]

/-- Coordinate maps that are inverse as germs give inverse changes of first jets.
Both inverse identities follow by applying this statement in the two orders. -/
theorem firstJetCoordChange_inverse {h : E' → E} {k : E → E'}
    {g : E' × F → G} {l : E × G → F} {x : E} (j : F × (E →L[𝕜] F))
    (hh : DifferentiableAt 𝕜 h (k x)) (hk : DifferentiableAt 𝕜 k x)
    (hg : DifferentiableAt 𝕜 g (k x, j.1))
    (hl : DifferentiableAt 𝕜 l (x, g (k x, j.1)))
    (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, j.1)] Prod.snd) :
    firstJetCoordChange k l x (firstJetCoordChange h g (k x) j) = j := by
  rw [firstJetCoordChange_comp j hh hk hg hl]
  exact (firstJetCoordChange_congr j hbase hfibre).trans (firstJetCoordChange_id x j)

/-- At a fixed field value, derivative differences transform tensorially.
The base-dependent inhomogeneous term cancels. -/
theorem firstJetCoordChange_snd_sub (h : E' → E) (g : E' × F → G) (x : E')
    (v : F) (A B : E →L[𝕜] F) :
    (firstJetCoordChange h g x (v, A)).2 - (firstJetCoordChange h g x (v, B)).2 =
      ((fderiv 𝕜 g (x, v)).comp (inr 𝕜 E' F)).comp ((A - B).comp (fderiv 𝕜 h x)) := by
  ext w
  simpa only [firstJetCoordChange_snd_apply, sub_apply, comp_apply, inr_apply,
    Prod.mk_sub_mk, sub_self] using (fderiv 𝕜 g (x, v)).map_sub
      (w, A (fderiv 𝕜 h x w)) (w, B (fderiv 𝕜 h x w)) |>.symm

/-- If the base and vertical derivatives are invertible, the affine change on
derivatives over a fixed field value is bijective. -/
theorem firstJetCoordChange_snd_bijective (h : E' → E) (g : E' × F → G) (x : E')
    (v : F) (a : F ≃L[𝕜] G) (c : E' ≃L[𝕜] E)
    (ha : (fderiv 𝕜 g (x, v)).comp (inr 𝕜 E' F) = a.toContinuousLinearMap)
    (hc : fderiv 𝕜 h x = c.toContinuousLinearMap) :
    Function.Bijective (fun A : E →L[𝕜] F ↦ (firstJetCoordChange h g x (v, A)).2) := by
  have heq : (fun A : E →L[𝕜] F ↦ (firstJetCoordChange h g x (v, A)).2) =
      fun A ↦ (c.symm.arrowCongr a) A + (firstJetCoordChange h g x (v, 0)).2 := by
    funext A
    have hd := firstJetCoordChange_snd_sub h g x v A 0
    rw [sub_zero, ha, hc] at hd
    exact sub_eq_iff_eq_add.mp hd
  rw [heq]
  exact (Equiv.addRight _).bijective.comp (c.symm.arrowCongr a).bijective

/-- For fibre-linear changes, the nonlinear formula agrees with the linear
first-jet transformation. -/
theorem firstJetCoordChange_eq_firstJetPullback {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'}
    (j : F × (E →L[𝕜] F)) (hg : DifferentiableAt 𝕜 g x) :
    firstJetCoordChange h (fun p : E' × F ↦ g p.1 p.2) x j =
      (g x).firstJetPullback (fderiv 𝕜 g x) (fderiv 𝕜 h x) j := by
  have hgf : HasFDerivAt (fun p : E' × F ↦ g p.1)
      ((fderiv 𝕜 g x).comp (fst 𝕜 E' F)) (x, j.1) :=
    hg.hasFDerivAt.comp (x, j.1) hasFDerivAt_fst
  have hd := (hgf.clm_apply hasFDerivAt_snd).fderiv
  dsimp only [Function.comp_def] at hd
  apply Prod.ext
  · simp
  · ext w
    simp [firstJetCoordChange_snd_apply, firstJetPullback_apply, hd, add_comm]

/-- Smooth base and nonlinear fibre maps induce smooth first-jet transitions
on open chart domains. The transition consumes one derivative. -/
theorem contDiffOn_firstJetCoordChange {n m : ℕ∞ω} {u : Set E'} {v : Set (E' × F)}
    {h : E' → E} {g : E' × F → G} (hu : IsOpen u) (hv : IsOpen v)
    (hh : ContDiffOn 𝕜 n h u) (hg : ContDiffOn 𝕜 n g v) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m
      (fun p : E' × (F × (E →L[𝕜] F)) ↦ firstJetCoordChange h g p.1 p.2)
      {p | p.1 ∈ u ∧ (p.1, p.2.1) ∈ v} := by
  let S : Set (E' × (F × (E →L[𝕜] F))) := {p | p.1 ∈ u ∧ (p.1, p.2.1) ∈ v}
  have hx : ContDiffOn 𝕜 m (fun p : E' × (F × (E →L[𝕜] F)) ↦ p.1) S :=
    contDiff_fst.contDiffOn
  have hxv : ContDiffOn 𝕜 m (fun p : E' × (F × (E →L[𝕜] F)) ↦ (p.1, p.2.1)) S :=
    hx.prodMk contDiff_snd.fst.contDiffOn
  have hb := (hh.fderiv_of_isOpen hu hmn).comp hx (fun _ hp ↦ hp.1)
  have hf := (hg.fderiv_of_isOpen hv hmn).comp hxv (fun _ hp ↦ hp.2)
  have hA : ContDiffOn 𝕜 m (fun p : E' × (F × (E →L[𝕜] F)) ↦ p.2.2) S :=
    contDiff_snd.snd.contDiffOn
  have hgraph : ContDiffOn 𝕜 m
      (fun p : E' × (F × (E →L[𝕜] F)) ↦
        (ContinuousLinearMap.id 𝕜 E').prod (p.2.2.comp (fderiv 𝕜 h p.1))) S := by
    exact (prodₗᵢ 𝕜 : (E' →L[𝕜] E') × (E' →L[𝕜] F) ≃ₗᵢ[𝕜] E' →L[𝕜] E' × F).contDiff
      |>.comp_contDiffOn (contDiffOn_const.prodMk (hA.clm_comp hb))
  exact ((hg.of_le (le_trans le_self_add hmn)).comp hxv (fun _ hp ↦ hp.2)).prodMk
    (hf.clm_comp hgraph)

end TauCeti
