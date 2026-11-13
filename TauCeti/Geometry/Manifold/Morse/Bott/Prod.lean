/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Morse–Bott functions of the second factor of a product

A function `q` on a finite-dimensional normed space `V` pulls back to the function
`(x, v) ↦ q v` on a product `M × V`. Its critical set is `M` times the critical set of `q`
(`TauCeti.criticalPoints_comp_snd`), so over a critical point `y` of `q` it contains the slice
`M × {y}`. Whether this function is Morse–Bott along the slice is decided by `q` alone:

* if `y` is a nondegenerate critical point of `q`, the slice is a Morse–Bott critical submanifold
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd`), and if moreover `y` is
  the only critical point of `q` and `M` is connected, it is the only piece of a Morse–Bott family
  (`TauCeti.isMorseBottFamily_comp_snd`);
* conversely, a Morse–Bott critical submanifold whose second component is locally constant lies
  over a nondegenerate critical point of `q`
  (`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_snd`):
  a vector of `V` killed by the Hessian of `q` is a vertical vector in the kernel of the critical
  Hessian, so it must be tangent to the submanifold, whose tangent vectors are horizontal. Hence
  the slice is Morse–Bott exactly when `y` is nondegenerate
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd_iff`), and if `y` is an
  isolated degenerate critical point, no family of embeddings exhibits `(x, v) ↦ q v` as a
  Morse–Bott function (`TauCeti.not_isMorseBottFamily_comp_snd`).

The examples `(x, y) ↦ y²` and `(x, y) ↦ y⁴` on `M × ℝ` are worked out in
`TauCeti.Geometry.Manifold.Morse.Bott.Examples.Plane`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {q : V → ℝ} {y : V} {n : ℕ∞ω}

namespace SmoothEmbedding

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

/-- **A Morse–Bott submanifold of a function of the second factor whose second component is
locally constant lies over a nondegenerate critical point.** If `i` is a Morse–Bott critical
submanifold of `(x, v) ↦ q v` on `M × V` whose second component is constant near `s`, then that
component is a nondegenerate critical point of `q`. -/
theorem IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_snd
    [FiniteDimensional ℝ V] {i : SmoothEmbedding J (I.prod 𝓘(ℝ, V)) n S (M × V)}
    (h : i.IsNondegenerateCriticalSubmanifold (q ∘ Prod.snd)) {s : S}
    (hs : Prod.snd ∘ i =ᶠ[𝓝 s] fun _ ↦ (i s).2) :
    IsNondegenerateCriticalPoint q (i s).2 := by
  have hq : ContDiffAt ℝ 2 q (i s).2 := by
    have hslice : ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V)) 2 (fun w : V ↦ ((i s).1, w)) (i s).2 :=
      contMDiffAt_const.prodMk contMDiffAt_id
    exact contMDiffAt_iff_contDiffAt.1 ((h.contMDiffAt s).comp_of_eq hslice rfl)
  refine isNondegenerateCriticalPoint_iff_separatingLeft.2 ⟨hq, ?_, fun w hw ↦ ?_⟩
  · exact mem_criticalPoints_iff_fderiv_eq_zero.1 <|
      mem_criticalPoints_comp_snd_iff.1 (h.mem_criticalPoints s)
  -- The vertical vector `(0, w)` lies in the kernel of the critical Hessian, so it is tangent to
  -- `i`; but the second component of `i` is constant near `s`, so `w = 0`.
  have hker : criticalHessian (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) ((i s).1, (i s).2) ((0 : E), w) =
      0 := by
    ext z
    exact (criticalHessian_comp_snd_apply hq (i s).1 _ z).trans ((hw z.2).trans (zero_apply z).symm)
  obtain ⟨u, hu⟩ := h.ker_criticalHessian_le s (LinearMap.mem_ker.2 hker)
  rw [ContinuousLinearMap.coe_coe] at hu
  by_cases hi : MDifferentiableAt J (I.prod 𝓘(ℝ, V)) i s
  · have hd : mfderiv J 𝓘(ℝ, V) (fun t ↦ (i t).2) s = 0 := by
      rw [show (fun t ↦ (i t).2) = Prod.snd ∘ i from rfl, hs.mfderiv_eq, mfderiv_const,
        ContinuousLinearMap.comp_zero]
    have hsnd := hi.mfderiv_snd_apply u
    rw [hd, hu, zero_apply] at hsnd
    exact hsnd.symm
  · rw [mfderiv_zero_of_not_mdifferentiableAt hi, zero_apply] at hu
    exact (congrArg Prod.snd hu).symm

/-- **The slice `M × {y}` is Morse–Bott exactly over a nondegenerate critical point.** For
nonempty `M`, the slice is a Morse–Bott critical submanifold of `(x, v) ↦ q v` exactly when `y` is
a nondegenerate critical point of `q`. -/
theorem isNondegenerateCriticalSubmanifold_comp_snd_iff [Nonempty M] [FiniteDimensional ℝ V]
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, V)) n (fun x : M ↦ (x, y))) :
    (ofIsSmoothEmbedding _ h).IsNondegenerateCriticalSubmanifold (q ∘ Prod.snd) ↔
      IsNondegenerateCriticalPoint q y := by
  refine ⟨fun h' ↦ ?_, fun hq ↦ isNondegenerateCriticalSubmanifold_comp_snd hq h⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  have hsnd (z : M) : (ofIsSmoothEmbedding _ h z).2 = y := by
    rw [ofIsSmoothEmbedding_apply]
  simpa only [hsnd] using h'.isNondegenerateCriticalPoint_snd (s := x)
    (Eventually.of_forall fun z ↦ (hsnd z).trans (hsnd x).symm)

end SmoothEmbedding

/-- **The model Morse–Bott function.** Let `M` be a nonempty connected manifold without boundary
and let `q` be a smooth function on `V` whose only critical point is `y`, a nondegenerate one.
Then the slice `M × {y}`, the whole critical set of `(x, v) ↦ q v`, is the only piece of a
Morse–Bott family for this function. For `y = 0` the slice is a smooth embedding for instance by
`TauCeti.isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero`. -/
theorem isMorseBottFamily_comp_snd [BoundarylessManifold I M] [ConnectedSpace M]
    (hq : ContDiff ℝ ∞ q) (hy : IsNondegenerateCriticalPoint q y)
    (hcrit : criticalPoints 𝓘(ℝ, V) q ⊆ {y})
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, V)) n (fun x : M ↦ (x, y))) :
    IsMorseBottFamily (fun _ : Unit ↦ SmoothEmbedding.ofIsSmoothEmbedding _ h)
      (q ∘ Prod.snd) := by
  have hcrit' : criticalPoints (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) = range fun x : M ↦ (x, y) := by
    rw [criticalPoints_comp_snd, hcrit.antisymm
      (singleton_subset_iff.2 (mem_criticalPoints_iff_fderiv_eq_zero.2 hy.fderiv_eq_zero)),
      prod_singleton, image_univ]
  have hrange : range (SmoothEmbedding.ofIsSmoothEmbedding _ h) = range fun x : M ↦ (x, y) := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
  refine ⟨hq.contMDiff.comp contMDiff_snd,
    fun _ ↦ SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd hy h,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ x ↦ ?_, fun _ _ _ ↦ rfl, ?_,
    locallyFinite_of_finite _⟩
  · rw [hrange, hcrit', SmoothEmbedding.ofIsSmoothEmbedding_apply]
    exact ((isPreconnected_range (by fun_prop)).connectedComponentIn (mem_range_self x)).symm
  · rw [hcrit']
    exact subset_iUnion_of_subset () hrange.ge

/-- **An isolated degenerate critical point is not Morse–Bott on a product.** Let `M` be nonempty
and let `y` be an isolated critical point of `q` which is degenerate. Then no family of embeddings
exhibits `(x, v) ↦ q v` on `M × V` as a Morse–Bott function: near `M × {y}` its critical set is
that slice, and along it the kernel of the critical Hessian contains nonzero vertical vectors,
which are not tangent to the slice. -/
theorem not_isMorseBottFamily_comp_snd [Nonempty M] [FiniteDimensional ℝ V]
    {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
    {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
    {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
    (i : ∀ a, SmoothEmbedding (J a) (I.prod 𝓘(ℝ, V)) n (S a) (M × V))
    (hy : y ∈ criticalPoints 𝓘(ℝ, V) q)
    (hiso : ∀ᶠ z in 𝓝 y, z ∈ criticalPoints 𝓘(ℝ, V) q → z = y)
    (hq : ¬IsNondegenerateCriticalPoint q y) :
    ¬IsMorseBottFamily i (q ∘ Prod.snd) := by
  intro hf
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨a, s, hs⟩ := mem_iUnion.1 (hf.criticalPoints_subset_iUnion_range
    (mem_criticalPoints_comp_snd_iff.2 hy : (x, y) ∈ _))
  -- Near `s`, the second component of `i a` is a critical point of `q` close to `y`, so it is `y`.
  have hcont : Tendsto (fun t ↦ (i a t).2) (𝓝 s) (𝓝 y) := by
    simpa only [ContinuousAt, hs] using ((i a).contMDiff.continuous.continuousAt (x := s)).snd
  have hloc : Prod.snd ∘ i a =ᶠ[𝓝 s] fun _ ↦ (i a s).2 := by
    filter_upwards [hcont.eventually hiso] with t ht
    rw [hs]
    exact ht (mem_criticalPoints_comp_snd_iff.1
      (hf.range_subset_criticalPoints a (mem_range_self t)))
  refine hq ?_
  simpa only [hs] using
    (hf.isNondegenerateCriticalSubmanifold a).isNondegenerateCriticalPoint_snd hloc

end TauCeti
