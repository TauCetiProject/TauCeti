/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Prod

/-!
# Morse–Bott functions of the second factor of a product

A function `q` on a finite-dimensional normed space `V` pulls back to the function
`(x, v) ↦ q v` on a product `M × V`. Its critical set is `M` times the critical set of `q`
(`TauCeti.criticalPoints_comp_snd`), so when `0` is the only critical point of `q` the critical set
is the slice `M × {0}`. Whether this function is Morse–Bott is decided by `q` alone:

* if `0` is a nondegenerate critical point of `q`, the slice is a Morse–Bott critical submanifold
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd`), and for connected `M`
  it is the only piece of a Morse–Bott family (`TauCeti.isMorseBottFamily_comp_snd`);
* conversely, a Morse–Bott critical submanifold whose second component is locally constant lies
  over a nondegenerate critical point of `q`
  (`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_snd`):
  a vector of `V` killed by the Hessian of `q` is a vertical vector in the kernel of the critical
  Hessian, so it must be tangent to the submanifold, whose tangent vectors are horizontal. Hence
  the slice is Morse–Bott exactly when `0` is nondegenerate
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd_iff`), and if `0` is a
  degenerate critical point and the only one, no family of embeddings exhibits `(x, v) ↦ q v` as
  a Morse–Bott function (`TauCeti.not_isMorseBottFamily_comp_snd`).

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
  [NormedAddCommGroup V] [NormedSpace ℝ V] {q : V → ℝ} {n : ℕ∞ω}

namespace SmoothEmbedding

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

/-- **A Morse–Bott submanifold of a function of the second factor whose second component is
locally constant lies over a nondegenerate critical point.** If `i` is a Morse–Bott critical
submanifold of `(x, v) ↦ q v` on `M × V` whose second component is constant near `s`, then that
component is a nondegenerate critical point of `q`. -/
theorem IsNondegenerateCriticalSubmanifold.isNondegenerateCriticalPoint_snd
    [FiniteDimensional ℝ V] {i : SmoothEmbedding J (I.prod 𝓘(ℝ, V)) n S (M × V)} (hn : n ≠ 0)
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
  have hd : mfderiv J 𝓘(ℝ, V) (Prod.snd ∘ i) s = 0 := by
    rw [hs.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
  have hcomp := mfderiv_comp_apply s mdifferentiableAt_snd
    ((i.contMDiff s).mdifferentiableAt hn) u
  rw [hd, mfderiv_snd] at hcomp
  exact (congrArg Prod.snd hu).symm.trans (hcomp.symm.trans (zero_apply u))

/-- **The slice `M × {0}` is Morse–Bott exactly over a nondegenerate critical point.** For
nonempty `M`, the slice is a Morse–Bott critical submanifold of `(x, v) ↦ q v` exactly when `0` is
a nondegenerate critical point of `q`. -/
theorem isNondegenerateCriticalSubmanifold_comp_snd_iff [Nonempty M] [FiniteDimensional ℝ V]
    (hn : n ≠ 0) (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, V)) n (fun x : M ↦ (x, (0 : V)))) :
    (ofIsSmoothEmbedding _ h).IsNondegenerateCriticalSubmanifold (q ∘ Prod.snd) ↔
      IsNondegenerateCriticalPoint q 0 := by
  refine ⟨fun h' ↦ ?_, fun hq ↦ isNondegenerateCriticalSubmanifold_comp_snd hq h⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  have hsnd (y : M) : (ofIsSmoothEmbedding _ h y).2 = 0 := by
    rw [ofIsSmoothEmbedding_apply]
  simpa only [hsnd] using h'.isNondegenerateCriticalPoint_snd hn (s := x)
    (Eventually.of_forall fun y ↦ (hsnd y).trans (hsnd x).symm)

end SmoothEmbedding

/-- **The model Morse–Bott function.** Let `M` be a nonempty connected manifold without boundary
and let `q` be a smooth function on `V` whose only critical point is `0`, a nondegenerate one.
Then the slice `M × {0}`, the whole critical set of `(x, v) ↦ q v`, is the only piece of a
Morse–Bott family for this function. The slice is a smooth embedding for instance by
`TauCeti.isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero`. -/
theorem isMorseBottFamily_comp_snd [BoundarylessManifold I M] [ConnectedSpace M]
    (hq : ContDiff ℝ ∞ q) (hq₀ : IsNondegenerateCriticalPoint q 0)
    (hcrit : criticalPoints 𝓘(ℝ, V) q ⊆ {0})
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, V)) n (fun x : M ↦ (x, (0 : V)))) :
    IsMorseBottFamily (fun _ : Unit ↦ SmoothEmbedding.ofIsSmoothEmbedding _ h)
      (q ∘ Prod.snd) := by
  have hcrit' : criticalPoints (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) =
      range fun x : M ↦ (x, (0 : V)) := by
    rw [criticalPoints_comp_snd, hcrit.antisymm
      (singleton_subset_iff.2 (mem_criticalPoints_iff_fderiv_eq_zero.2 hq₀.fderiv_eq_zero)),
      prod_singleton, image_univ]
  have hrange : range (SmoothEmbedding.ofIsSmoothEmbedding _ h) =
      range fun x : M ↦ (x, (0 : V)) := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
  refine ⟨hq.contMDiff.comp contMDiff_snd,
    fun _ ↦ SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd hq₀ h,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ x ↦ ?_, fun _ _ _ ↦ rfl, ?_,
    locallyFinite_of_finite _⟩
  · rw [hrange, hcrit', SmoothEmbedding.ofIsSmoothEmbedding_apply]
    exact ((isPreconnected_range (by fun_prop)).connectedComponentIn (mem_range_self x)).symm
  · rw [hcrit']
    exact subset_iUnion_of_subset () hrange.ge

/-- **A unique degenerate critical point is not Morse–Bott on a product.** Let `M` be nonempty
and let `0` be the only critical point of `q`, a degenerate one. Then no family of embeddings
exhibits `(x, v) ↦ q v` on `M × V` as a Morse–Bott function: its critical set is the slice
`M × {0}`, and along it the kernel of the critical Hessian contains nonzero vertical vectors,
which are not tangent to the slice. -/
theorem not_isMorseBottFamily_comp_snd [Nonempty M] [FiniteDimensional ℝ V]
    {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
    {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
    {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
    (i : ∀ a, SmoothEmbedding (J a) (I.prod 𝓘(ℝ, V)) n (S a) (M × V)) (hn : n ≠ 0)
    (hcrit : criticalPoints 𝓘(ℝ, V) q = {0}) (hq : ¬IsNondegenerateCriticalPoint q 0) :
    ¬IsMorseBottFamily i (q ∘ Prod.snd) := by
  intro hf
  obtain ⟨x⟩ := ‹Nonempty M›
  have hcrit' : criticalPoints (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) = (univ : Set M) ×ˢ {0} := by
    rw [criticalPoints_comp_snd, hcrit]
  have hx : (x, (0 : V)) ∈ criticalPoints (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) := by
    rw [hcrit']
    exact ⟨mem_univ x, rfl⟩
  obtain ⟨a, s, -⟩ := mem_iUnion.1 (hf.criticalPoints_subset_iUnion_range hx)
  have hsnd (t : S a) : (i a t).2 = 0 := by
    have ht := hf.range_subset_criticalPoints a (mem_range_self t)
    rw [hcrit'] at ht
    exact ht.2
  refine hq ?_
  simpa only [hsnd] using (hf.isNondegenerateCriticalSubmanifold a).isNondegenerateCriticalPoint_snd
    hn (s := s) (Eventually.of_forall fun t ↦ (hsnd t).trans (hsnd s).symm)

end TauCeti
