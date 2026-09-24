/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.RootSum.Family
public import TauCeti.Geometry.Manifold.SymmetricPower

/-!
# Holomorphic transitions between elementary-symmetric charts

An elementary-symmetric chart on `Sym^n X` separates a tuple into finitely many blocks lying in
coordinate patches. For two charts using the same block partition, a change from one chart to the
other applies, block by block, the transition between the two surface coordinates and then
regroups the elementary-symmetric coefficients. Charts with different partitions are not covered
here.

This file identifies that coefficient expression with the transition
`target ∘ source.symm` of the explicit partial homeomorphs from
`TauCeti.symOpenPartialHomeomorph`. The blockwise root theorem
`TauCeti.Sym.analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm_of_analyticAt`
then proves that the transition is analytic at the represented tuple. Repeated points are included.
The regularity claims below assume that, for every represented block `q i` and every `z ∈ q i`,
the surface coordinate change `fun w : ℂ => ψ i ((φ i).symm w)` is analytic at `φ i (z : α)`.
The whole-target claims require this hypothesis for every block represented in the target.

The construction follows Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds* ([arXiv:math/0101206](https://arxiv.org/abs/math/0101206)), §2.1.

## Main declarations

* `TauCeti.symOpenPartialHomeomorph_transition_apply`: the explicit blockwise coordinate
  expression equals the source-chart transition on its target.
* `TauCeti.analyticAt_symOpenPartialHomeomorph_transition`: the transition between two
  elementary-symmetric coordinate charts is analytic at the tuple represented by the source
  coefficients.
* `TauCeti.contDiffOn_symOpenPartialHomeomorph_transition`: the same coordinate transition is
  infinitely differentiable on the entire target of the source chart.
* `TauCeti.contDiffOn_symOpenPartialHomeomorph_trans`: the transition partial homeomorphism is
  infinitely differentiable on its source, in the form used by Mathlib's manifold atlas API.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The coefficient expression is the same-partition chart transition on the source target.** -/
theorem symOpenPartialHomeomorph_transition_apply
    (φ ψ : ι → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i))
    (hVsubφ : ∀ i, V i ⊆ (φ i).source)
    (hVsubψ : ∀ i, V i ⊆ (ψ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i)))
    (c : Fin n → ℂ)
    (hc : c ∈ (symOpenPartialHomeomorph
      φ V m hm hVo hVsubφ hVdisj e hp).target) :
    piSigmaConstHomeomorph ℂ e' (fun i =>
      Sym.coeffEquiv ℂ (m i)
        (Sym.map (fun w : ℂ => ψ i ((φ i).symm w))
          ((Sym.coeffEquiv ℂ (m i)).symm
            ((piSigmaConstHomeomorph ℂ e).symm c i)))) =
      symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
        ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).symm c) := by
  classical
  let C : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp
  let D : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
  have hrepr : ∃ q : ∀ i, Sym ↥(V i) (m i),
      C.symm c = Sym.sumSubtype V m hm q := by
    have hs : C.symm c ∈ C.source := C.map_target hc
    rw [symOpenPartialHomeomorph_source φ V m hm hVo hVsubφ hVdisj e hp] at hs
    rcases Set.mem_range.mp hs with ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  obtain ⟨q, hq⟩ := hrepr
  have hsq : Sym.sumSubtype V m hm q ∈ C.source := by
    rw [← hq]
    exact C.map_target hc
  have hc' : C (Sym.sumSubtype V m hm q) = c := by
    rw [← hq, C.right_inv hc]
  rw [← hc', C.left_inv hsq]
  have hCcoords : C (Sym.sumSubtype V m hm q) =
      piSigmaConstHomeomorph ℂ e (fun j =>
        Sym.coeffEquiv ℂ (m j)
          (Sym.map (fun z : ↥(V j) => φ j (z : α)) (q j))) := by
    exact symOpenPartialHomeomorph_apply φ V m hm hVo hVsubφ hVdisj e hp q
  rw [hCcoords]
  rw [symOpenPartialHomeomorph_apply ψ V m hm hVo hVsubψ hVdisj e' hp]
  apply congrArg (piSigmaConstHomeomorph ℂ e')
  funext i
  have hroot : (Sym.coeffEquiv ℂ (m i)).symm
        (((piSigmaConstHomeomorph ℂ e).symm
          (piSigmaConstHomeomorph ℂ e (fun j =>
            Sym.coeffEquiv ℂ (m j)
              (Sym.map (fun z : ↥(V j) => φ j (z : α)) (q j))))) i) =
      Sym.map (fun z : ↥(V i) => φ i (z : α)) (q i) := by
    simp
  rw [hroot]
  congr 1
  rw [Sym.map_map]
  congr 1
  funext z
  simp only [Function.comp_apply]
  have hzφ : (φ i).symm (φ i z) = z :=
    (φ i).left_inv (hVsubφ i z.2)
  rw [hzφ]

/-- **The same-partition elementary-symmetric chart transition is analytic at a represented tuple.**
The two charts use the common disjoint patch family `V` and multiplicities `m`; their surface
coordinate maps `φ`, `ψ` and regrouping bijections `e`, `e'` may differ. Repeated points in the
represented symmetric-power tuple are allowed. The hypothesis `hφ` requires the surface coordinate
change `ψ i ∘ (φ i).symm` to be analytic at `φ i (z : α)` for every `i` and `z ∈ p i`. -/
theorem analyticAt_symOpenPartialHomeomorph_transition
    (φ ψ : ι → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i))
    (hVsubφ : ∀ i, V i ⊆ (φ i).source)
    (hVsubψ : ∀ i, V i ⊆ (ψ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    (p : ∀ i, Sym ↥(V i) (m i))
    (hφ : ∀ i (z : ↥(V i)), z ∈ p i →
      AnalyticAt ℂ (fun w : ℂ => ψ i ((φ i).symm w)) (φ i (z : α))) :
    AnalyticAt ℂ
      (fun c : Fin n → ℂ =>
        symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' ⟨p⟩
          ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e ⟨p⟩).symm c))
      (symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e ⟨p⟩
        (Sym.sumSubtype V m hm p)) := by
  classical
  let hp : Nonempty (∀ i, Sym ↥(V i) (m i)) := ⟨p⟩
  let C : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp
  let D : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
  let cblocks : ∀ i, Fin (m i) → ℂ := fun i =>
    Sym.coeffEquiv ℂ (m i) (Sym.map (fun z : ↥(V i) => φ i (z : α)) (p i))
  let F : (Fin n → ℂ) → (Fin n → ℂ) := fun c =>
    piSigmaConstHomeomorph ℂ e' (fun i =>
      Sym.coeffEquiv ℂ (m i)
        (Sym.map (fun w : ℂ => ψ i ((φ i).symm w))
          ((Sym.coeffEquiv ℂ (m i)).symm ((piSigmaConstHomeomorph ℂ e).symm c i))))
  have hφ' : ∀ i z, z ∈ (Sym.coeffEquiv ℂ (m i)).symm (cblocks i) →
      AnalyticAt ℂ (fun w : ℂ => ψ i ((φ i).symm w)) z := by
    intro i z hz
    have hz' : z ∈ Sym.map (fun w : ↥(V i) => φ i (w : α)) (p i) := by
      simpa [cblocks] using hz
    rcases (Sym.mem_map).1 hz' with ⟨a, ha, hza⟩
    rw [← hza]
    exact hφ i a ha
  have hF : AnalyticAt ℂ F (piSigmaConstHomeomorph ℂ e cblocks) := by
    dsimp only [F]
    exact Sym.analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm_of_analyticAt
      e e' hφ'
  have hlocal : ∀ c : Fin n → ℂ, c ∈ C.target → F c = D (C.symm c) := by
    intro c hc
    simpa only [C, D, F] using
      (symOpenPartialHomeomorph_transition_apply
        φ ψ V m hm hVo hVsubφ hVsubψ hVdisj e e' hp c hc)
  have hbase : C (Sym.sumSubtype V m hm p) =
      piSigmaConstHomeomorph ℂ e cblocks := by
    simp [C, cblocks, symOpenPartialHomeomorph_apply]
  rw [hbase]
  have hs0 : Sym.sumSubtype V m hm p ∈ C.source := by
    rw [symOpenPartialHomeomorph_source φ V m hm hVo hVsubφ hVdisj e hp]
    exact ⟨p, rfl⟩
  have ht0 : C (Sym.sumSubtype V m hm p) ∈ C.target := C.map_source hs0
  refine hF.congr ?_
  have hev : ∀ᶠ c in 𝓝 (piSigmaConstHomeomorph ℂ e cblocks), c ∈ C.target := by
    simpa [hbase] using (C.open_target.mem_nhds ht0)
  filter_upwards [hev] with c hc
  exact hlocal c hc


/-- **The coordinate transition is infinitely differentiable on the source-chart target.**
Here `hφ` requires the surface coordinate change `ψ i ∘ (φ i).symm` to be analytic at
`φ i (z : α)` for every `i`, every represented block `q i`, and every `z ∈ q i`. No analyticity is
required for points outside the represented blocks. -/
theorem contDiffOn_symOpenPartialHomeomorph_transition
    (φ ψ : ι → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i))
    (hVsubφ : ∀ i, V i ⊆ (φ i).source)
    (hVsubψ : ∀ i, V i ⊆ (ψ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i)))
    (hφ : ∀ i (q : Sym ↥(V i) (m i)) (z : ↥(V i)), z ∈ q →
      AnalyticAt ℂ (fun w : ℂ => ψ i ((φ i).symm w)) (φ i (z : α))) :
    ContDiffOn ℂ ω
      (fun c : Fin n → ℂ =>
        symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
          ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).symm c))
      (symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).target := by
  let C : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp
  have ha : AnalyticOn ℂ
      (fun c : Fin n → ℂ =>
        symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp (C.symm c))
      C.target := by
    intro c hc
    have hs : C.symm c ∈ C.source := C.map_target hc
    rw [symOpenPartialHomeomorph_source φ V m hm hVo hVsubφ hVdisj e hp] at hs
    rcases Set.mem_range.mp hs with ⟨q, hq⟩
    have hqA := analyticAt_symOpenPartialHomeomorph_transition
      φ ψ V m hm hVo hVsubφ hVsubψ hVdisj e e' q
        (fun i z hz => hφ i (q i) z hz)
    have hc' : C (Sym.sumSubtype V m hm q) = c := by
      calc
        C (Sym.sumSubtype V m hm q) = C (C.symm c) := by rw [hq]
        _ = c := C.right_inv hc
    rw [hc'] at hqA
    exact hqA.analyticWithinAt
  exact ha.contDiffOn C.open_target.uniqueDiffOn

/-- **The transition partial homeomorphism is infinitely differentiable on its source.** This is
the source-and-target form consumed by `isManifold_of_contDiffOn`. Here `hφ` requires the surface
coordinate change `ψ i ∘ (φ i).symm` to be analytic at `φ i (z : α)` for every `i`, every
represented block `q i`, and every `z ∈ q i`; no analyticity is required for points outside the
represented blocks. -/
theorem contDiffOn_symOpenPartialHomeomorph_trans
    (φ ψ : ι → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i))
    (hVsubφ : ∀ i, V i ⊆ (φ i).source)
    (hVsubψ : ∀ i, V i ⊆ (ψ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i)))
    (hφ : ∀ i (q : Sym ↥(V i) (m i)) (z : ↥(V i)), z ∈ q →
      AnalyticAt ℂ (fun w : ℂ => ψ i ((φ i).symm w)) (φ i (z : α))) :
    ContDiffOn ℂ ω
      ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).symm.trans
        (symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp))
      ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).symm.trans
        (symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp)).source := by
  let C : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp
  let D : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
  have h : ContDiffOn ℂ ω
      (fun c : Fin n → ℂ => D (C.symm c)) C.target :=
    contDiffOn_symOpenPartialHomeomorph_transition
      φ ψ V m hm hVo hVsubφ hVsubψ hVdisj e e' hp hφ
  have hsub : (C.symm.trans D).source ⊆ C.target := by
    intro c hc
    rw [OpenPartialHomeomorph.trans_source] at hc
    simpa only [C.symm_source] using hc.1
  simpa [C, D, OpenPartialHomeomorph.coe_trans, Function.comp_def] using h.mono hsub

end TauCeti

end
