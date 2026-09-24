/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.RootSum
public import TauCeti.Topology.PiCurry.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-!
# Analytic coordinate changes across families of root blocks

An elementary-symmetric chart on a symmetric power of a complex surface separates a tuple into
points lying in finitely many disjoint coordinate patches. If the multiplicity in patch `i` is
`m i`, its coordinates form a block `Fin (m i) → ℂ`; a bijection
`(Σ i, Fin (m i)) ≃ Fin n` regroups those blocks into the model space `Fin n → ℂ`.

`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt` proves that changing a
holomorphic surface coordinate is analytic on one block, including where roots collide. This file
applies that result to a finite family of blocks and then conjugates the family by the possibly
different source and target regroupings. The multiplicity-free `RCLike` version remains in
`TauCeti/Analysis/Polynomial/SimpleRoots/Family.lean`; the assembled complex statement is
`TauCeti.Sym.analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm_of_analyticAt`.

Thus the blockwise coordinate-change expression used by elementary-symmetric charts is analytic
at every represented tuple. This supplies the transition-map calculation needed to assemble a
holomorphic atlas for symmetric powers. For background on the symmetric-power setting, see
Ozsváth--Szabó, [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Section 2.2. The
blockwise analytic statement and proof in this file are developed here, rather than attributed to
that section.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {ι : Type*} [Finite ι] {m : ι → ℕ} {n : ℕ}

attribute [local instance] Fintype.ofFinite

/-- **Coordinate changes on a finite family of root blocks are analytic.**

For each `i`, the coefficient tuple `c₀ i` determines a finite multiset of complex points. Applying
`φ i` to those points and returning to elementary-symmetric coordinates is analytic jointly in the
family of coefficient blocks, provided `φ i` is analytic at every represented point. -/
private theorem analyticAt_pi_coeffEquiv_map_coeffEquiv_symm
    {φ : ι → ℂ → ℂ} {c₀ : ∀ i, Fin (m i) → ℂ}
    (hφ : ∀ i z, z ∈ (coeffEquiv ℂ (m i)).symm (c₀ i) → AnalyticAt ℂ (φ i) z) :
    AnalyticAt ℂ
      (fun c i => coeffEquiv ℂ (m i)
        (_root_.Sym.map (φ i) ((coeffEquiv ℂ (m i)).symm (c i)))) c₀ := by
  refine AnalyticAt.pi fun i => ?_
  exact AnalyticAt.comp (f := fun c : (∀ i, Fin (m i) → ℂ) => c i)
    (analyticAt_coeffEquiv_map_coeffEquiv_symm_of_analyticAt (hφ i))
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun i => Fin (m i) → ℂ) i).analyticAt c₀)

/-- **A blockwise elementary-symmetric coordinate change is analytic after regrouping.**

The bijections `e` and `e'` are the independent choices used to identify the source and target
families of coefficient blocks with `Fin n → ℂ`. The transition first undoes `e`, changes the
underlying coordinate separately on each root block, and then regroups along `e'`. It is analytic
at every represented tuple, including tuples with repeated points. -/
theorem analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm_of_analyticAt
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    {φ : ι → ℂ → ℂ} {c₀ : ∀ i, Fin (m i) → ℂ}
    (hφ : ∀ i z, z ∈ (coeffEquiv ℂ (m i)).symm (c₀ i) → AnalyticAt ℂ (φ i) z) :
    AnalyticAt ℂ
      (fun c => piSigmaConstHomeomorph ℂ e' (fun i =>
        coeffEquiv ℂ (m i) (_root_.Sym.map (φ i)
          ((coeffEquiv ℂ (m i)).symm ((piSigmaConstHomeomorph ℂ e).symm c i)))))
      (piSigmaConstHomeomorph ℂ e c₀) := by
  have hin := analyticAt_piSigmaConstHomeomorph_symm e
    (piSigmaConstHomeomorph ℂ e c₀)
  have hblocks := analyticAt_pi_coeffEquiv_map_coeffEquiv_symm hφ
  have hblocks' : AnalyticAt ℂ
      (fun c => fun i => coeffEquiv ℂ (m i) (_root_.Sym.map (φ i)
        ((coeffEquiv ℂ (m i)).symm (c i))))
      ((piSigmaConstHomeomorph ℂ e).symm (piSigmaConstHomeomorph ℂ e c₀)) := by
    rw [Homeomorph.symm_apply_apply]
    exact hblocks
  have hmiddle := AnalyticAt.comp
    (f := (piSigmaConstHomeomorph ℂ e).symm) hblocks' hin
  have hmiddle' : AnalyticAt ℂ
      (fun c => fun i => coeffEquiv ℂ (m i) (_root_.Sym.map (φ i)
        ((coeffEquiv ℂ (m i)).symm ((piSigmaConstHomeomorph ℂ e).symm c i))))
      (piSigmaConstHomeomorph ℂ e c₀) := by
    convert hmiddle using 1
    all_goals rfl
  convert AnalyticAt.comp
    (f := fun c => fun i => coeffEquiv ℂ (m i) (_root_.Sym.map (φ i)
      ((coeffEquiv ℂ (m i)).symm ((piSigmaConstHomeomorph ℂ e).symm c i))))
    (analyticAt_piSigmaConstHomeomorph e' _) hmiddle' using 1
  all_goals rfl

end Sym

end TauCeti
