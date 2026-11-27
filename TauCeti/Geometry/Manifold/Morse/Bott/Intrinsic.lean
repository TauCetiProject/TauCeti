/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
import TauCeti.Geometry.Manifold.RegularValue

/-!
# Morse–Bott functions, intrinsically

A smooth function `f` on a manifold `M` is **Morse–Bott** when its critical set is, near each of
its points, a smooth submanifold along which the kernel of the critical Hessian is exactly the
tangent space of the submanifold. This file states this condition intrinsically, with no choice
of critical submanifolds (`TauCeti.IsMorseBott`): every critical point `x` lies in the source of a
smooth chart `q : M → E` of `M` with smooth inverse which flattens the critical set onto a linear
subspace `V` of the model space, so that on the source of `q` a point is critical exactly when its
coordinates lie in `V`, and at every critical point `z` in the source of `q` the kernel of the
critical Hessian is `(dq_z)⁻¹ V`, the tangent space at `z` of the flattened critical set. The
condition is stated without any assumption on the dimension of the model space. Different
components of the critical set may have different dimensions.

The Morse–Bott theory of `TauCeti.Geometry.Manifold.Morse.Bott` runs on a family of smooth
embeddings `i a : S a → M` presenting the critical submanifolds (`TauCeti.IsMorseBottFamily`).
This file shows that the two notions agree, on a boundaryless manifold modelled on a
finite-dimensional space.

* **Families give the intrinsic condition** (`TauCeti.IsMorseBottFamily.isMorseBott`). Near a
  point of a nondegenerate critical submanifold `i : S → M`, the slice chart of the embedding
  (`TauCeti.exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement`) flattens
  the image of `i`, which near that point is the whole critical set
  (`IsNondegenerateCriticalSubmanifold.exists_isOpen_criticalPoints_inter_eq_range`). The
  kernel of the critical Hessian at each of its points is the tangent space of `S`, which the
  derivative of the chart carries into the slice, and both have the dimension of `S`
  (`IsCriticalSubmanifold.isNondegenerateCriticalSubmanifold_iff_finrank_ker`, both in the
  namespace `TauCeti.SmoothEmbedding`). This is
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_sliceChart`.
* **The intrinsic condition gives a family** (`TauCeti.IsMorseBott.exists_isMorseBottFamily`).
  The derivative of a slice chart is invertible, so the kernel of the critical Hessian has the
  dimension of the slice, which is therefore locally constant along the critical set
  (`TauCeti.IsMorseBott.eventually_finrank_ker_criticalHessian_eq`), hence constant on each of its
  connected components
  (`TauCeti.IsMorseBott.finrank_ker_criticalHessian_eq_of_mem_connectedComponentIn`). Near each
  of its points, a connected component is flattened by a slice chart of the critical set cut down to
  a convex coordinate ball (`TauCeti.IsMorseBott.exists_sliceChart_connectedComponentIn`), so it
  is an embedded submanifold modelled on a subspace of its dimension
  (`TauCeti.exists_isSmoothEmbedding_of_finrankSubspaceCharts`). Its inclusion is a critical
  submanifold along which the kernel of the critical Hessian has the dimension of the
  component, hence a nondegenerate one, and the connected components of the critical set,
  each with this embedding, form a Morse–Bott family
  (`TauCeti.IsMorseBottFamily.of_pairwise_disjoint`).

Together, `TauCeti.isMorseBott_iff_exists_isMorseBottFamily`: a function is Morse–Bott exactly
when some family of embedded submanifolds, each modelled on a subspace of the model space,
exhibits it as one. In particular Morse functions are Morse–Bott (`TauCeti.IsMorse.isMorseBott`),
as are constant functions (`TauCeti.isMorseBott_const`), and `f` is Morse–Bott exactly when `-f`
is (`TauCeti.isMorseBott_neg_iff`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 5 (slice charts of
  embedded submanifolds).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

universe u

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {x y : M}

/-- A function `f` on `M` is **Morse–Bott** when it is smooth and, near each critical point `x`,
a smooth chart `q : M → E` with smooth inverse flattens the critical set onto a linear subspace
`V` of the model space, such that at every critical point `z` in the source of `q` the kernel of
the critical Hessian is `(dq_z)⁻¹ V`, the tangent space of the critical set at `z`. On a
boundaryless manifold modelled on a finite-dimensional space, the equivalent description by a
family of critical submanifolds is `TauCeti.isMorseBott_iff_exists_isMorseBottFamily`. -/
structure IsMorseBott (I : ModelWithCorners ℝ E H) (f : M → ℝ) : Prop where
  /-- The function is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ) ∞ f
  /-- Near each critical point, a smooth chart flattens the critical set onto a linear subspace
  whose preimage under the derivative of the chart is the kernel of the critical Hessian at each
  critical point of the chart. -/
  exists_sliceChart (x : M) (hx : x ∈ criticalPoints I f) :
    ∃ (q : OpenPartialHomeomorph M E) (V : Submodule ℝ E), x ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(ℝ, E) ∞ q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(ℝ, E) I ∞ q.symm z) ∧
      (∀ z ∈ q.source, z ∈ criticalPoints I f ↔ q z ∈ V) ∧
      ∀ z ∈ q.source, z ∈ criticalPoints I f →
        (criticalHessian I f z).ker = V.comap (mfderiv I 𝓘(ℝ, E) q z).toLinearMap

/-- `f` is Morse–Bott exactly when `-f` is: the two functions have the same critical points, and
their critical Hessians are opposite, with the same kernels. -/
@[simp]
theorem isMorseBott_neg_iff : IsMorseBott I (-f) ↔ IsMorseBott I f := by
  have key {g : M → ℝ} (hg : IsMorseBott I g) : IsMorseBott I (-g) := by
    refine ⟨contDiff_neg.contMDiff.comp hg.contMDiff, fun x hx ↦ ?_⟩
    rw [criticalPoints_neg] at hx ⊢
    obtain ⟨q, V, hxq, hq, hqs, hcrit, hdim⟩ := hg.exists_sliceChart x hx
    refine ⟨q, V, hxq, hq, hqs, hcrit, fun z hz hzc ↦ ?_⟩
    rw [criticalHessian_neg, ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg,
      hdim z hz hzc]
  exact ⟨fun h ↦ by simpa only [neg_neg] using key h, key⟩

/-- If `f` is Morse–Bott, so is `-f`. -/
theorem IsMorseBott.neg (hf : IsMorseBott I f) : IsMorseBott I (-f) :=
  isMorseBott_neg_iff.2 hf

/-! ### Families of critical submanifolds give the intrinsic condition -/

section Family

variable [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}

/-- **A Morse–Bott critical submanifold is flattened by a slice chart of the critical set.** Near
each point of a smooth nondegenerate critical submanifold `i : S → M` modelled without boundary,
a smooth chart `q` of `M` with values in the model space flattens the critical set onto a linear
subspace `V`, whose preimage under the derivative of `q` at every critical point of the chart is the
kernel of the critical Hessian. -/
theorem SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_sliceChart
    (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : ∞ ≤ n) (s : S) :
    ∃ (q : OpenPartialHomeomorph M E) (V : Submodule ℝ E), i s ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(ℝ, E) ∞ q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(ℝ, E) I ∞ q.symm z) ∧
      (∀ z ∈ q.source, z ∈ criticalPoints I f ↔ q z ∈ V) ∧
      ∀ z ∈ q.source, z ∈ criticalPoints I f →
        (criticalHessian I f z).ker = V.comap (mfderiv I 𝓘(ℝ, E) q z).toLinearMap := by
  have hn0 : n ≠ 0 := ne_bot_of_le_ne_bot (by simp) hn
  -- The slice chart of `i` in `E' × F ≃ E`, and an open `U` cutting the critical set to `range i`.
  have hI := (i.isImmersion.isImmersionAt s).isImmersionAtOfComplement_complement
  set L := hI.equiv
  obtain ⟨Φ, hsΦ, hslice, hΦ, hΦs⟩ :=
    exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement i.isEmbedding hI
  obtain ⟨U, hUo, hU⟩ := hi.exists_isOpen_criticalPoints_inter_eq_range (le_trans (by simp) hn)
  set Ψ := Φ.restrOpen U hUo
  set q := Ψ.transHomeomorph L.toHomeomorph
  -- The slice `E' × {0}`, read in `E` through `L`, has dimension `dim E'`.
  have hVdim : Module.finrank ℝ (LinearMap.ker
      ((LinearMap.snd ℝ E' _).comp L.symm.toLinearEquiv.toLinearMap)) = Module.finrank ℝ E' := by
    rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
      LinearMap.ker_snd, LinearMap.finrank_range_of_inj LinearMap.inl_injective]
  set V : Submodule ℝ E :=
    LinearMap.ker ((LinearMap.snd ℝ E' _).comp L.symm.toLinearEquiv.toLinearMap)
  set π := (ContinuousLinearMap.snd ℝ E' _).comp L.symm.toContinuousLinearMap
  have hcrit (z : M) (hz : z ∈ Ψ.source) : z ∈ criticalPoints I f ↔ z ∈ range i :=
    ⟨fun h ↦ hU.le ⟨h, hz.2⟩, fun h ↦ (hU.ge h).1⟩
  -- The chart is `L ∘ Φ` on an open subset of the source of `Φ`, and its inverse is `Φ⁻¹ ∘ L⁻¹`.
  have hq (z : M) (hz : z ∈ q.source) : ContMDiffAt I 𝓘(ℝ, E) ∞ q z :=
    L.contDiff.contMDiff.contMDiffAt.comp z ((hΦ.contMDiffAt (Φ.open_source.mem_nhds
      (by simpa [q, Ψ] using hz.1))).of_le hn)
  have hqs (z : E) (hz : z ∈ q.target) : ContMDiffAt 𝓘(ℝ, E) I ∞ q.symm z :=
    ((hΦs.contMDiffAt (Φ.open_target.mem_nhds hz.1)).of_le hn).comp z
      L.symm.contDiff.contMDiff.contMDiffAt
  -- `L` carries the slice of `Φ` onto `V`, and `q` is `L ∘ Φ` on its source.
  have hslice_V (w : E' × _) : L w ∈ V ↔ w ∈ range J ×ˢ ({0} : Set _) := by
    simp [V, J.range_eq_univ]
  have hflat (z : M) (hz : z ∈ q.source) : z ∈ criticalPoints I f ↔ q z ∈ V :=
    (hcrit z hz).trans <| (isSliceChart_iff.1 hslice z hz.1).trans (hslice_V (Φ z)).symm
  refine ⟨q, V, ⟨hsΦ, (hU.ge (mem_range_self s)).2⟩, hq, hqs, hflat, fun z hz hzc ↦ ?_⟩
  -- Every critical point of the chart lies on the submanifold, whose tangent space is the kernel
  -- of the critical Hessian. The chart carries it into `V`, and both have dimension `dim E'`.
  obtain ⟨t, rfl⟩ := (hcrit z hz).1 hzc
  have hle : (criticalHessian I f (i t)).ker ≤ V.comap (mfderiv I 𝓘(ℝ, E) q (i t)).toLinearMap := by
    have hπ := range_mfderiv_le_ker_mfderiv_of_eventually_eq (K := J) (I := I)
      (J := 𝓘(ℝ, (i.isImmersion.isImmersionAt s).complement)) (f := π ∘ q) (g := i) (y := 0)
      (p := t) <| by
      filter_upwards [i.isEmbedding.continuous.continuousAt.preimage_mem_nhds
        (q.open_source.mem_nhds hz)] with r hr
      exact (hflat _ hr).1 (hi.mem_criticalPoints r)
    rw [mfderiv_comp _ π.mdifferentiableAt ((hq _ hz).mdifferentiableAt (by simp)),
      π.mfderiv_eq] at hπ
    exact fun v hv ↦ hπ ((hi.ker_criticalHessian hn0 t).le hv)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [OpenPartialHomeomorph.finrank_comap_mfderiv (by simp) hq hqs V hz, hVdim,
    (hi.toIsCriticalSubmanifold.isNondegenerateCriticalSubmanifold_iff_finrank_ker hn0).1 hi t]

variable {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)]
  [∀ a, NormedSpace ℝ (E' a)] {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)]
  {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)} [∀ a, (J a).Boundaryless] {S : ι → Type*}
  [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
  {i : ∀ a, SmoothEmbedding (J a) I n (S a) M}

/-- **A Morse–Bott family makes its function Morse–Bott.** If a family of smooth embeddings
modelled without boundary exhibits `f` as a Morse–Bott function, then `f` is Morse–Bott in the
intrinsic sense. -/
theorem IsMorseBottFamily.isMorseBott (h : IsMorseBottFamily i f) (hn : ∞ ≤ n) :
    IsMorseBott I f := by
  refine ⟨h.contMDiff, fun x hx ↦ ?_⟩
  obtain ⟨a, s, rfl⟩ := mem_iUnion.1 (h.criticalPoints_subset_iUnion_range hx)
  exact (h.isNondegenerateCriticalSubmanifold a).exists_sliceChart hn s

end Family

/-! ### The intrinsic condition gives a family of critical submanifolds -/

namespace IsMorseBott

variable (hf : IsMorseBott I f)
include hf

/-- **The nullity of the critical Hessian is locally constant along the critical set** of a
Morse–Bott function: it is the dimension of the critical set. -/
theorem eventually_finrank_ker_criticalHessian_eq (hx : x ∈ criticalPoints I f) :
    ∀ᶠ z in 𝓝[criticalPoints I f] x, Module.finrank ℝ (criticalHessian I f z).ker =
      Module.finrank ℝ (criticalHessian I f x).ker := by
  obtain ⟨q, V, hxq, hq, hqs, -, hker⟩ := hf.exists_sliceChart x hx
  filter_upwards [inter_mem_nhdsWithin _ (q.open_source.mem_nhds hxq)] with z hz
  rw [hker z hz.2 hz.1, hker x hxq hx,
    OpenPartialHomeomorph.finrank_comap_mfderiv (by simp) hq hqs V hz.2,
    OpenPartialHomeomorph.finrank_comap_mfderiv (by simp) hq hqs V hxq]

/-- **The nullity of the critical Hessian is constant on each connected component of the
critical set** of a Morse–Bott function. -/
theorem finrank_ker_criticalHessian_eq_of_mem_connectedComponentIn (hx : x ∈ criticalPoints I f)
    (hy : y ∈ connectedComponentIn (criticalPoints I f) x) :
    Module.finrank ℝ (criticalHessian I f y).ker = Module.finrank ℝ (criticalHessian I f x).ker :=
  isPreconnected_connectedComponentIn.constant
    (f := fun z ↦ Module.finrank ℝ (criticalHessian I f z).ker)
    (fun _ hz ↦ tendsto_const_nhds.congr' (EventuallyEq.symm
      (hf.eventually_finrank_ker_criticalHessian_eq (connectedComponentIn_subset _ _ hz))
      |>.filter_mono (nhdsWithin_mono _ (connectedComponentIn_subset _ _))))
    hy (mem_connectedComponentIn hx)

/-- **A connected component of the critical set is flattened by a slice chart.** Near each
critical point `x` of a Morse–Bott function, a smooth chart with values in the model space
flattens the connected component of `x` in the critical set onto a linear subspace whose
dimension is that of the kernel of the critical Hessian at `x`. -/
theorem exists_sliceChart_connectedComponentIn (hx : x ∈ criticalPoints I f) :
    ∃ (q : OpenPartialHomeomorph M E) (V : Submodule ℝ E), x ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(ℝ, E) ∞ q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(ℝ, E) I ∞ q.symm z) ∧
      (∀ z ∈ q.source, z ∈ connectedComponentIn (criticalPoints I f) x ↔ q z ∈ V) ∧
      Module.finrank ℝ V = Module.finrank ℝ (criticalHessian I f x).ker := by
  obtain ⟨q, V, hxq, hq, hqs, hcrit, hker⟩ := hf.exists_sliceChart x hx
  -- Cut the chart down to a coordinate ball, whose slice is convex, hence connected.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 q.open_target (q x) (q.map_source hxq)
  set N := q.source ∩ q ⁻¹' Metric.ball (q x) r
  have hNo : IsOpen N := q.isOpen_inter_preimage Metric.isOpen_ball
  have hsub : q.symm '' (Metric.ball (q x) r ∩ V) ⊆
      connectedComponentIn (criticalPoints I f) x := by
    refine ((convex_ball _ _).inter V.convex).isPreconnected.image _
      (q.continuousOn_symm.mono (inter_subset_left.trans hball))
      |>.subset_connectedComponentIn ⟨q x, ⟨Metric.mem_ball_self hr, (hcrit x hxq).1 hx⟩,
        q.left_inv hxq⟩ ?_
    rintro _ ⟨w, ⟨hwb, hwV⟩, rfl⟩
    exact (hcrit _ (q.map_target (hball hwb))).2 (by rwa [q.right_inv (hball hwb)])
  refine ⟨q.restrOpen N hNo, V, ⟨hxq, hxq, Metric.mem_ball_self hr⟩,
    fun z hz ↦ hq z hz.1, fun z hz ↦ hqs z ?_, fun z hz ↦ ?_, ?_⟩
  · exact hz.1
  · simp only [OpenPartialHomeomorph.coe_restrOpen]
    refine ⟨fun hz' ↦ (hcrit z hz.1).1 (connectedComponentIn_subset _ _ hz'), fun hzV ↦ ?_⟩
    exact hsub ⟨q z, ⟨hz.2.2, hzV⟩, q.left_inv hz.1⟩
  · rw [hker x hxq hx, OpenPartialHomeomorph.finrank_comap_mfderiv (by simp) hq hqs V hxq]

end IsMorseBott

/-- **The connected components of the critical set are embedded submanifolds.** On a boundaryless
manifold modelled on a finite-dimensional space, the connected component of a critical point `x`
of a Morse–Bott function in the critical set is a smooth manifold modelled on any subspace `L` of
the model space whose dimension is that of the kernel of the critical Hessian at `x`, and its
inclusion into `M` is a smooth embedding. -/
theorem IsMorseBott.exists_isSmoothEmbedding_connectedComponentIn [I.Boundaryless]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] (hf : IsMorseBott I f)
    (hx : x ∈ criticalPoints I f) (L : Submodule ℝ E)
    (hL : Module.finrank ℝ L = Module.finrank ℝ (criticalHessian I f x).ker) :
    ∃ C : ChartedSpace L (connectedComponentIn (criticalPoints I f) x), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (criticalPoints I f) x) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, L) I ∞
          (Subtype.val : connectedComponentIn (criticalPoints I f) x → M) := by
  refine exists_isSmoothEmbedding_of_finrankSubspaceCharts fun y hy ↦ ?_
  obtain ⟨q, V, hyq, hq, hqs, hV, hdim⟩ :=
    hf.exists_sliceChart_connectedComponentIn (connectedComponentIn_subset _ _ hy)
  refine ⟨q, V, hyq, hq, hqs, fun z hz ↦ ?_, ?_⟩
  · rw [connectedComponentIn_eq hy]
    exact hV z hz
  · rw [hdim, hL, hf.finrank_ker_criticalHessian_eq_of_mem_connectedComponentIn hx hy]

/-- **A Morse–Bott function has a Morse–Bott family.** On a boundaryless manifold modelled on a
finite-dimensional space, the connected components of the critical set of a Morse–Bott function,
each an embedded submanifold of `M` modelled on a subspace `L a` of the model space, form a
Morse–Bott family of `f`. -/
theorem IsMorseBott.exists_isMorseBottFamily [I.Boundaryless] [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] (hf : IsMorseBott I f) :
    ∃ (ι : Type u) (L : ι → Submodule ℝ E) (S : ι → Set M) (_ : ∀ a, ChartedSpace (L a) (S a))
      (i : ∀ a, SmoothEmbedding 𝓘(ℝ, L a) I ∞ (S a) M),
      (∀ a, ⇑(i a) = Subtype.val) ∧ IsMorseBottFamily i f := by
  have : IsManifold I 2 M := .of_le (n := ∞) (by simp)
  -- The pieces are the connected components of the critical set, each with a chosen point.
  let ι := {C : Set M // ∃ x ∈ criticalPoints I f, connectedComponentIn (criticalPoints I f) x = C}
  choose x hx hxC using fun a : ι ↦ a.property
  -- Each piece is modelled on a subspace of the dimension of the critical Hessian's kernel, such
  -- as the slice of a chart at its chosen point.
  choose L hL using fun a : ι ↦
    let ⟨_, V, _, _, _, _, hV⟩ := hf.exists_sliceChart_connectedComponentIn (hx a)
    (⟨V, hV⟩ : ∃ V : Submodule ℝ E,
      Module.finrank ℝ V = Module.finrank ℝ (criticalHessian I f (x a)).ker)
  choose C _ hemb using fun a ↦
    hf.exists_isSmoothEmbedding_connectedComponentIn (hx a) (L a) (hL a)
  let i (a : ι) :
      SmoothEmbedding 𝓘(ℝ, L a) I ∞ (connectedComponentIn (criticalPoints I f) (x a)) M :=
    letI := C a
    .ofIsSmoothEmbedding _ (hemb a)
  have hi (a : ι) : ⇑(i a) = Subtype.val := SmoothEmbedding.coe_ofIsSmoothEmbedding _ _
  have hrange (a : ι) : range (i a) = connectedComponentIn (criticalPoints I f) (x a) := by
    rw [hi, Subtype.range_coe]
  have (a : ι) : Nonempty (connectedComponentIn (criticalPoints I f) (x a)) :=
    ⟨⟨x a, mem_connectedComponentIn (hx a)⟩⟩
  have (a : ι) : PreconnectedSpace (connectedComponentIn (criticalPoints I f) (x a)) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  refine ⟨ι, L, _, C, i, hi, IsMorseBottFamily.of_pairwise_disjoint
    (by simp) hf.contMDiff (fun a ↦ ?_) (fun a b hab ↦ ?_) fun y hy ↦ ?_⟩
  · -- Each piece is a critical submanifold along which the Hessian's kernel has its dimension.
    let := C a
    have hcs : (i a).IsCriticalSubmanifold f :=
      ⟨fun s ↦ hf.contMDiff.contMDiffAt.of_le (by simp), fun s ↦ by
        rw [hi]
        exact connectedComponentIn_subset _ _ s.property⟩
    refine (hcs.isNondegenerateCriticalSubmanifold_iff_finrank_ker (by simp)).2 fun s ↦ ?_
    rw [hi, hf.finrank_ker_criticalHessian_eq_of_mem_connectedComponentIn (hx a) s.property, hL]
  · -- Distinct components are disjoint.
    rw [Function.onFun, hrange, hrange, Set.disjoint_left]
    refine fun z hza hzb ↦ hab (Subtype.ext ?_)
    rw [← hxC, ← hxC, connectedComponentIn_eq hza, connectedComponentIn_eq hzb]
  · refine mem_iUnion.2 ⟨⟨_, y, hy, rfl⟩, ?_⟩
    rw [hrange, hxC]
    exact mem_connectedComponentIn hy

/-- **Morse–Bott functions are those with a Morse–Bott family.** On a boundaryless manifold
modelled on a finite-dimensional space, a function is Morse–Bott exactly when some family of
smooth embeddings of subsets of `M`, each modelled on a subspace of the model space, exhibits it as
a Morse–Bott function. -/
theorem isMorseBott_iff_exists_isMorseBottFamily [I.Boundaryless] [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] :
    IsMorseBott I f ↔
      ∃ (ι : Type u) (L : ι → Submodule ℝ E) (S : ι → Set M) (_ : ∀ a, ChartedSpace (L a) (S a))
        (i : ∀ a, SmoothEmbedding 𝓘(ℝ, L a) I ∞ (S a) M), IsMorseBottFamily i f := by
  refine ⟨fun hf ↦ ?_, fun ⟨ι, L, S, C, i, h⟩ ↦ h.isMorseBott le_rfl⟩
  obtain ⟨ι, L, S, C, i, -, h⟩ := hf.exists_isMorseBottFamily
  exact ⟨ι, L, S, C, i, h⟩

/-- **Morse functions are Morse–Bott**: their critical submanifolds are their critical points. -/
theorem IsMorse.isMorseBott [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (hf : IsMorse I f) : IsMorseBott I f := by
  obtain ⟨i, -, h⟩ := hf.exists_isMorseBottFamily (n := ∞) (by simp) (Fin 0 → ℝ)
  exact h.isMorseBott le_rfl

/-- **A constant function is Morse–Bott**: every point is critical, the critical Hessian vanishes,
and the preferred extended chart at a point flattens the critical set onto the whole model space. -/
theorem isMorseBott_const [I.Boundaryless] [IsManifold I ∞ M] (c : ℝ) :
    IsMorseBott I (fun _ : M ↦ c) := by
  refine ⟨contMDiff_const, fun x _ ↦ ⟨(chartAt H x).transHomeomorph I.toHomeomorph, ⊤,
    by simp, fun z hz ↦ ?_, fun z hz ↦ ?_, by simp [criticalPoints_const], fun z _ _ ↦ ?_⟩⟩
  · exact contMDiffAt_extChartAt' (by simpa using hz)
  · refine (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds ?_)
    simpa [extChartAt_target, I.range_eq_univ] using hz
  · rw [criticalHessian_const, ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero]
    exact (Submodule.comap_top _).symm

end TauCeti
