/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
import TauCeti.Analysis.Convex.LocalToGlobal.Quadric
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
import TauCeti.Geometry.Manifold.Submersion.ConvexChart

/-!
# Connected levels of Morse–Bott functions

A Morse–Bott function whose critical points have neither Morse index nor coindex one has connected
level sets on a compact connected manifold. This is the lemma behind Atiyah's connectedness theorem
for the components of a moment map, whose indices and coindices are even.

The proof is local-to-global. Near a point `i s` of a nondegenerate critical submanifold, the
normalized Morse–Bott lemma
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_normalized_morseBott_chart`)
gives coordinates `(x, a, b)`, with `a` of dimension the index `λ` and `b` of dimension the coindex,
in which `f = f (i s) - ‖a‖² + ‖b‖²`. When neither `λ` nor the coindex is one, the product of a ball
in `x` with a ball in `(a, b)` is a convexity chart of this model
(`TauCeti.exists_isConvexChart_of_eqOn_norm_sq_sub_norm_sq`): its fibres are connected and the model
is open onto its image. So every point of a Morse–Bott critical submanifold lies in a convexity
chart of `f` (`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_isConvexChart`).
At regular points the submersion normal form supplies convexity charts, and the local-to-global
principle for convexity (`IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`) shows
that the levels of `f` are preconnected
(`TauCeti.isPreconnected_preimage_singleton_of_forall_mem_criticalPoints`,
`TauCeti.IsMorseBottFamily.isPreconnected_preimage_singleton`).

The hypothesis on the indices is needed: the height function of a circle has index zero and
coindex one at its minimum, and its levels between the two critical values are pairs of points.

## Main results

* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_isConvexChart`: a point of a
  Morse–Bott critical submanifold at which neither the index nor the coindex is one lies in a
  convexity chart.
* `TauCeti.isPreconnected_preimage_singleton_of_forall_mem_criticalPoints`: on a compact connected
  manifold, a `C¹` function with convexity charts at its critical points has preconnected levels.
* `TauCeti.IsMorseBottFamily.isPreconnected_preimage_singleton`: the levels of a Morse–Bott function
  without critical points of index or coindex one are preconnected.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the levels of a Morse–Bott function without index or coindex one are connected).
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Section 3 (the local-to-global principle).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
-/

public section

open Filter Function Manifold Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-- Splitting the coordinates of `ℝᵐ` into the first `l` and the remaining ones turns the signed sum
of squares `-Σ_{j < l} y_j² + Σ_{j ≥ l} y_j²` into `‖b‖² - ‖a‖²`. -/
private theorem sum_ite_mul_sq_eq {m l : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ∑ j, (if j.val < l then -1 else 1) * y j ^ 2 =
      ‖(WithLp.toLp 2 fun j : {j : Fin m // ¬ j.val < l} ↦ y j : EuclideanSpace ℝ _)‖ ^ 2 -
        ‖(WithLp.toLp 2 fun j : {j : Fin m // j.val < l} ↦ y j : EuclideanSpace ℝ _)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin m ↦ j.val < l)]
  have h₁ : ∀ j : {j : Fin m // j.val < l}, (if j.val.val < l then -1 else 1) * y j ^ 2 =
      -y j ^ 2 := fun j ↦ by simp [j.property]
  have h₂ : ∀ j : {j : Fin m // ¬ j.val < l}, (if j.val.val < l then -1 else 1) * y j ^ 2 =
      y j ^ 2 := fun j ↦ by simp [j.property]
  simp only [h₁, h₂, Finset.sum_neg_distrib]
  ring

/-- The homeomorphism of `ℝᵐ` splitting off its first `l` coordinates, which turns the normal form
of the Morse–Bott lemma into `‖b‖² - ‖a‖²` (`sum_ite_mul_sq_eq`). -/
private def splitHomeomorph (m l : ℕ) : EuclideanSpace ℝ (Fin m) ≃ₜ
    EuclideanSpace ℝ {j : Fin m // j.val < l} × EuclideanSpace ℝ {j : Fin m // ¬ j.val < l} :=
  (PiLp.homeomorph 2 _).trans ((Homeomorph.piEquivPiSubtypeProd (fun j : Fin m ↦ j.val < l)
    fun _ ↦ ℝ).trans ((PiLp.homeomorph 2 _).symm.prodCongr (PiLp.homeomorph 2 _).symm))

private theorem splitHomeomorph_apply {m l : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    splitHomeomorph m l y = (WithLp.toLp 2 fun j : {j : Fin m // j.val < l} ↦ y j,
      WithLp.toLp 2 fun j : {j : Fin m // ¬ j.val < l} ↦ y j) :=
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

omit [J.Boundaryless] in
/-- The Morse index and the coindex of `f` at a point of a Morse–Bott critical submanifold add up
to the dimension of a complement `F` of its tangent space in slice coordinates. -/
private theorem manifoldMorseIndex_add_manifoldMorseIndex_neg_eq_finrank
    (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : n ≠ 0) {s : S} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : IsImmersionAtOfComplement F J I n i s) :
    manifoldMorseIndex I f (i s) + manifoldMorseIndex I (-f) (i s) = Module.finrank ℝ F := by
  have : FiniteDimensional ℝ (E' × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ F :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' F) LinearMap.snd_surjective
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_surjective (LinearMap.fst ℝ E' F) LinearMap.fst_surjective
  have h₁ := hi.manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank hn s
  have h₂ : Module.finrank ℝ E' + Module.finrank ℝ F = Module.finrank ℝ E := by
    rw [← Module.finrank_prod, h.equiv.toLinearEquiv.finrank_eq]
  omega

/-- **The Morse–Bott lemma in a chart of `M`.** Near a point `i s` of a Morse–Bott critical
submanifold, with complement `F` in slice coordinates, there is a chart `e` of `M` onto an open
subset of `E' × ℝᵐ`, `m = dim F`, sending `i s` to the zero section, in which
`f = f (i s) - Σ_{j < λ} y_j² + Σ_{j ≥ λ} y_j²` for the Morse index `λ` of `f` at `i s`. -/
private theorem exists_openPartialHomeomorph_eqOn (hi : i.IsNondegenerateCriticalSubmanifold f)
    (hn : 3 ≤ n) {s : S} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : IsImmersionAtOfComplement F J I n i s) (hf : ∀ᶠ y in 𝓝 (i s), ContMDiffAt I 𝓘(ℝ) 3 f y) :
    ∃ e : OpenPartialHomeomorph M (E' × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))),
      i s ∈ e.source ∧ (e (i s)).2 = 0 ∧
        EqOn f (fun x ↦ f (i s) +
          ∑ j, (if j.val < manifoldMorseIndex I f (i s) then -1 else 1) * (e x).2 j ^ 2)
          e.source := by
  obtain ⟨ψ, U, V, -, -, haU, h0V, hsource, -, hUVξ, hsec, -, hψ0, -, -, -, hψg⟩ :=
    hi.exists_normalized_morseBott_chart h (k := 1) (by exact_mod_cast hn) one_ne_zero
      (by convert hf using 4; norm_num)
  -- The slice chart of `M` at `i s`, followed by the Morse–Bott chart `ψ`.
  refine ⟨(h.codChart.transHomeomorph (I.toHomeomorph.trans h.equiv.symm.toHomeomorph)).trans ψ,
    ?_, ?_, fun x hx ↦ ?_⟩
  rotate_right
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.transHomeomorph_source,
      mem_inter_iff, mem_preimage] at hx
    have hx' : (h.codChart.extend I).symm (I (h.codChart x)) = x :=
      h.codChart.extend_left_inv hx.1
    have := hψg _ hx.2
    simp only [comp_apply, OpenPartialHomeomorph.transHomeomorph_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.apply_symm_apply,
      ModelWithCorners.toHomeomorph_apply, hx'] at this
    simpa only [OpenPartialHomeomorph.coe_trans, comp_apply,
      OpenPartialHomeomorph.transHomeomorph_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, ModelWithCorners.toHomeomorph_apply] using this
  -- The slice chart sends `i s` to `(a, 0)`, which `ψ` fixes.
  all_goals
    set a := h.domChart.extend J s
    have hs : (h.domChart.extend J).symm a = s :=
      (h.domChart.extend J).left_inv (by simpa using h.mem_domChart_source)
    have hext : h.codChart.extend I (i s) = h.equiv (a, 0) := by
      have := hsec a haU
      rw [hs] at this
      rw [← this, (h.codChart.extend I).right_inv (hUVξ (mk_mem_prod haU h0V))]
    have hL : h.equiv.symm (I (h.codChart (i s))) = (a, 0) := by
      simpa using congr_arg h.equiv.symm hext
  · exact ⟨h.mem_codChart_source, by simp [hL, hsource, haU, h0V]⟩
  · simp [hL, hψ0]

/-- **Convexity charts at a Morse–Bott critical point.** Let `i : S → M` be a nondegenerate critical
submanifold of a function `f`, `C³` near `i s`, with `i` of class `C³`. If neither the Morse index
nor the coindex of `f` at `i s` is one, then `i s` lies in a convexity chart of `f`. -/
theorem exists_isConvexChart (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : 3 ≤ n) (s : S)
    (hf : ∀ᶠ y in 𝓝 (i s), ContMDiffAt I 𝓘(ℝ) 3 f y)
    (hidx : manifoldMorseIndex I f (i s) ≠ 1) (hco : manifoldMorseIndex I (-f) (i s) ≠ 1) :
    ∃ U, i s ∈ U ∧ IsConvexChart f U := by
  let F := i.isImmersion.complement
  have h : IsImmersionAtOfComplement F J I n i s :=
    i.isImmersion.isImmersionOfComplement_complement s
  have hl : manifoldMorseIndex I f (i s) + manifoldMorseIndex I (-f) (i s) =
      Module.finrank ℝ F :=
    hi.manifoldMorseIndex_add_manifoldMorseIndex_neg_eq_finrank
      (ne_of_gt (lt_of_lt_of_le (by norm_num) hn)) h
  obtain ⟨e, hsrc, he, hfe⟩ := hi.exists_openPartialHomeomorph_eqOn hn h hf
  -- Split `ℝᵐ` into its first `l` and its last `m - l` coordinates, turning the signed sum of
  -- squares into `‖b‖² - ‖a‖²`.
  refine exists_isConvexChart_of_eqOn_norm_sq_sub_norm_sq ?_ ?_
    (e := e.transHomeomorph ((Homeomorph.refl E').prodCongr
      (splitHomeomorph _ (manifoldMorseIndex I f (i s)))))
    (c := f (i s)) (fun x hx ↦ by
      have := hfe hx
      dsimp only at this
      rw [this, sum_ite_mul_sq_eq]
      simp only [comp_apply, OpenPartialHomeomorph.transHomeomorph_apply,
        Homeomorph.coe_prodCongr, Prod.map_snd, splitHomeomorph_apply]) hsrc ?_
  -- The two factors have dimensions the index `λ` and the coindex `m - λ`.
  · rw [Ne, Module.rank_eq_one_iff_finrank_eq_one, finrank_euclideanSpace, Fintype.card_subtype,
      Fin.card_filter_val_lt, min_eq_right (by omega)]
    exact hidx
  · rw [Ne, Module.rank_eq_one_iff_finrank_eq_one, finrank_euclideanSpace,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype, Fin.card_filter_val_lt,
      min_eq_right (by omega)]
    omega
  · simp only [OpenPartialHomeomorph.transHomeomorph_apply, Homeomorph.coe_prodCongr,
      comp_apply, Prod.map_snd, he, splitHomeomorph_apply]
    ext <;> simp

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### Connected levels -/

section Level

variable [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- **Connected levels from local convexity at the critical points.** Let `f` be a `C¹` function on
a compact connected boundaryless finite-dimensional manifold. If every critical point of `f` lies in
a convexity chart of `f`, then every level set of `f` is preconnected. At the regular points
convexity charts come from the submersion normal form, and the local-to-global principle for
convexity (`IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`) applies. -/
theorem isPreconnected_preimage_singleton_of_forall_mem_criticalPoints
    (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hloc : ∀ x ∈ criticalPoints I f, ∃ U, x ∈ U ∧ IsConvexChart f U) (c : ℝ) :
    IsPreconnected (f ⁻¹' {c}) := by
  refine hf.continuous.isProperMap.isPreconnected_preimage_singleton_of_isConvexChart
    (fun x ↦ ?_) c
  by_cases hx : x ∈ criticalPoints I f
  · exact hloc x hx
  -- At a regular point the differential is a nonzero functional, hence surjective.
  have hs : Surjective (mvfderiv I f x : TangentSpace I x →ₗ[ℝ] ℝ) :=
    LinearMap.surjective_of_ne_zero fun h0 ↦ hx (mem_criticalPoints.2
      (ContinuousLinearMap.coe_injective h0))
  have hs' : Surjective (mfderiv I 𝓘(ℝ) f x) := fun r ↦ by
    obtain ⟨w, hw⟩ := hs r
    exact ⟨w, by rw [← mvfderiv_apply_eq_mfderiv_apply]; exact hw⟩
  obtain ⟨U, -, hxU, hU⟩ := hf.contMDiffOn.exists_isConvexChart_subset_of_surjective_mfderiv
    isOpen_univ (mem_univ x) le_rfl hs' univ_mem
  exact ⟨U, hxU, hU⟩

/-- **The levels of a Morse–Bott function without index or coindex one are connected.** Let a
family of `C³` embeddings exhibit `f` as a Morse–Bott function on a compact connected boundaryless
finite-dimensional manifold. If at no critical point is the Morse index or the coindex of `f` equal
to one, then every level set of `f` is preconnected. -/
theorem IsMorseBottFamily.isPreconnected_preimage_singleton {ι : Type*} {E' : ι → Type*}
    [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)] {H' : ι → Type*}
    [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
    [∀ a, (J a).Boundaryless] {S : ι → Type*} [∀ a, TopologicalSpace (S a)]
    [∀ a, ChartedSpace (H' a) (S a)] {i : ∀ a, SmoothEmbedding (J a) I n (S a) M}
    (h : IsMorseBottFamily i f) (hn : 3 ≤ n)
    (hidx : ∀ a s, manifoldMorseIndex I f (i a s) ≠ 1)
    (hco : ∀ a s, manifoldMorseIndex I (-f) (i a s) ≠ 1) (c : ℝ) :
    IsPreconnected (f ⁻¹' {c}) := by
  refine isPreconnected_preimage_singleton_of_forall_mem_criticalPoints
    (h.contMDiff.of_le (by simp)) (fun x hx ↦ ?_) c
  obtain ⟨a, s, rfl⟩ := h.mem_criticalPoints_iff.1 hx
  exact (h.isNondegenerateCriticalSubmanifold a).exists_isConvexChart hn s
    (Eventually.of_forall fun y ↦ (h.contMDiff y).of_le (by simp)) (hidx a s) (hco a s)

end Level

end TauCeti
