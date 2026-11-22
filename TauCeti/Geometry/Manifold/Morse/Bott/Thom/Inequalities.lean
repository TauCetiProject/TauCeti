/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Class
public import TauCeti.Geometry.Manifold.Morse.Bott.Count
public import TauCeti.Geometry.Manifold.Morse.Generic.Inequalities

/-!
# The Morse–Bott inequalities from Thom classes of the negative normal bundles

Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`)
on a compact boundaryless manifold `M`, and let `λ_j` be the index of the piece `S j`
(`TauCeti.IsMorseBottFamily.index`). A smooth fibre metric `g j` on the normal bundle of `S j`
selects the negative normal spaces of `S j`; they form the negative normal bundle `ν⁻ j`, of rank
`λ_j`. Crossing a critical level attaches the negative disc bundles of the pieces on that level, and
the relative homology of the band splits over them
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle`).
A Thom class of `ν⁻ j` with coefficients in a field `K` identifies the contribution of `S j` with
the homology of `S j` shifted by `λ_j`
(`nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass`, in the
namespace `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`). This file adds up these contributions:

* the negative disc-sphere pair `(D_ε, S_ε)` of a critical submanifold whose negative normal bundle
  of rank `r` has a Thom class over `K` has `dim Hₘ(D_ε, S_ε; K) = b_{m - r}(S; K)` for `r ≤ m`, and
  `0` for `m < r`;
* if `c` is the only critical value of `f` in `[a, b]`, with `a < c < b`, and every `ν⁻ j` has a
  Thom class over `K`, then `dim Hₘ({f ≤ b}, {f ≤ a}; K) = ∑ⱼ b_{m - λ_j}(S j; K)`, the sum over the
  pieces on the level `c` of index at most `m`;
* summing over a cut of `f` into such bands, the Morse–Bott counts
  `cₖ = ∑ⱼ b_{k - λ_j}(S j; K)` (`TauCeti.IsMorseBottFamily.morseBottCount`) and the Betti numbers
  `bₖ` of `M` over `K` satisfy Bott's polynomial identity
  `∑ cₖ tᵏ = ∑ bₖ tᵏ + (1 + t) Q(t)`, with `Q` of degree below `dim M` and natural number
  coefficients, and the strong Morse–Bott inequalities `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`.

An orientation of a real vector bundle provides a Thom class with coefficients in every field
(`TauCeti.VectorBundleOrientation.exists_isThomClass`), so the identity and the inequalities hold
over every field, for instance `ℚ`, when the negative normal bundles are oriented, as complex
negative normal bundles are. Without such a Thom class the homology of a piece must be twisted by
the orientation local system of its negative normal bundle, which this file does not treat.

The Thom isomorphism needs the model fibre `Fin r → ℝ` of `ν⁻` in the universe of its base, so the
manifolds, their models and the field `K` live in `Type`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`:

* `finrank_singularHomology_negativeDiscSpherePair_of_isThomClass` and
  `finite_singularHomology_negativeDiscSpherePair_of_isThomClass`: the dimension of the homology
  of the negative disc-sphere pair, and its finiteness over a compact base.

In the namespace `TauCeti.IsMorseBottFamily`:

* `finrank_singularHomology_sublevelPair_of_isThomClass`: the dimension of the relative homology
  of a band with one critical value is the sum of the shifted Betti numbers of the pieces on that
  level.
* `exists_morseBottCount_eq_bettiNumber_add_coeff_of_isThomClass` and
  `exists_morseBottCount_eq_bettiNumber_add_coeff_of_orientation`: Bott's polynomial identity.
* `sum_range_neg_one_pow_mul_bettiNumber_le_morseBottCount_of_isThomClass` and
  `sum_range_neg_one_pow_mul_bettiNumber_le_morseBottCount_of_orientation`: the strong Morse–Bott
  inequalities.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Function Limits Module Set Topology
open Polynomial (X)
open scoped ContDiff Manifold Polynomial

/-! ### The dimension of the homology of a negative disc-sphere pair -/

namespace TauCeti.SmoothEmbedding.IsCriticalSubmanifold

variable {E : Type} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} {S : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J 1 S] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) {ε : ℝ}
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') {r : ℕ}
  (hV : letI := i.normalSpaceFiberBundle hn hdim
    HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
  (hε : 0 < ε) {K : Type} [Field K]
  (u : letI := i.normalSpaceFiberBundle hn hdim
    haveI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := hV.fiberBundle
    (thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin r → ℝ)))
  (hu : letI := i.normalSpaceFiberBundle hn hdim
    haveI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
    letI := hV.fiberBundle
    IsThomClass (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) u)

include hε hu in
/-- **The dimension of the homology of the negative disc-sphere pair.** Let `i` be a critical
submanifold of `f`, let `g` be a fibre metric on its normal bundle, and suppose that the negative
normal spaces have continuous local frames of size `r`, so that they form a vector bundle `ν⁻` of
rank `r`, with a Thom class `u` with coefficients in a field `K`. Then for `ε > 0` the negative disc
bundle `D_ε`, relative to the negative sphere bundle `S_ε`, has
`dim Hₘ(D_ε, S_ε; K) = b_{m - r}(S; K)` for `r ≤ m`, and `dim Hₘ(D_ε, S_ε; K) = 0` for `m < r`. -/
theorem finrank_singularHomology_negativeDiscSpherePair_of_isThomClass (m : ℕ) :
    finrank K ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of K K) m :
        ModuleCat K) =
      if r ≤ m then bettiNumber K S (m - r) else 0 := by
  split_ifs with hrm
  · obtain ⟨e⟩ :=
      h.nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass hn g
        hdim hV hε u hu (Nat.add_sub_cancel' hrm)
    rw [bettiNumber_def, e.toLinearEquiv.finrank_eq]
  · have := ModuleCat.isZero_iff_subsingleton.1
      (h.isZero_singularHomology_negativeDiscSpherePair_of_lt hn g hdim hV hε (ModuleCat.of K K)
        (not_le.1 hrm))
    exact finrank_zero_of_subsingleton

include hε hu in
/-- **The homology of the negative disc-sphere pair over a compact base is finite-dimensional.**
Under the hypotheses of `finrank_singularHomology_negativeDiscSpherePair_of_isThomClass`, if `S` is
a compact Hausdorff boundaryless manifold then every `Hₘ(D_ε, S_ε; K)` is finite-dimensional. -/
theorem finite_singularHomology_negativeDiscSpherePair_of_isThomClass [J.Boundaryless]
    [IsManifold J ∞ S] [T2Space S] [CompactSpace S] (m : ℕ) :
    Module.Finite K ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of K K) m :
      ModuleCat K) := by
  rcases le_or_gt r m with hrm | hmr
  · obtain ⟨e⟩ :=
      h.nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass hn g
        hdim hV hε u hu (Nat.add_sub_cancel' hrm)
    have := finite_singularHomology_of_compactSpace S J (ModuleCat.of K K) (m - r)
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.1
      (h.isZero_singularHomology_negativeDiscSpherePair_of_lt hn g hdim hV hε (ModuleCat.of K K)
        hmr)
    infer_instance

end TauCeti.SmoothEmbedding.IsCriticalSubmanifold

/-! ### The Morse–Bott inequalities -/

namespace TauCeti.IsMorseBottFamily

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)]
  [∀ j, FiniteDimensional ℝ (P j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  (hn : (∞ : ℕ∞ω) ≠ 0) (h : IsMorseBottFamily i f)
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (h.index j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
  {K : Type} [Field K]
  (u : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j,
      letI := subbundleTopology (P j) (F' := Fin (h.index j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI := (hV j).fiberBundle
      (thomPair (Fin (h.index j) → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin (h.index j) → ℝ)))
  (hu : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j,
      letI := subbundleTopology (P j) (F' := Fin (h.index j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI := (hV j).fiberBundle
      IsThomClass (Fin (h.index j) → ℝ) (fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) (u j))

include hdim g hV u hu in
open scoped Classical in
/-- **The dimension of the relative homology across a Morse–Bott level.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact Hausdorff second-countable
boundaryless manifold, with pieces modelled on boundaryless models, and let `K` be a field. For
each piece `S j`, let `g j` be a smooth fibre metric on its normal bundle, whose negative normal
spaces form the negative normal bundle `ν⁻ j` of rank the index `λ_j` of the piece, and let `u j`
be a Thom class of `ν⁻ j` with coefficients in `K`. If `a < c < b` and `c` is the only critical
value of `f` in `[a, b]`, then `dim Hₘ({f ≤ b}, {f ≤ a}; K)` is the sum of the Betti numbers
`b_{m - λ_j}(S j; K)` over the pieces `S j` on the level `c` with `λ_j ≤ m`. -/
theorem finrank_singularHomology_sublevelPair_of_isThomClass [Fintype ι] {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (m : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) m :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ h.index j ≤ m, bettiNumber K (S j) (m - h.index j) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  have (j : ι) : CompactSpace (S j) :=
    (Topology.IsClosedEmbedding.mk (i j).isEmbedding (h.isClosed_range j)).compactSpace
  have (j : ι) : T2Space (S j) := (i j).isEmbedding.t2Space
  -- The band splits over the pieces on the level `c`, each contributing the relative homology of
  -- attaching its negative disc bundle `D j ε` to `{f ≤ c - ε}`.
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle hn hac hcb hcrit hdim g
  have hε : ε₀ / 2 ∈ Ioo 0 ε₀ := ⟨half_pos hε₀, half_lt_self hε₀⟩
  obtain ⟨hsrc, -, hiso⟩ := hmain (ε₀ / 2) hε
  obtain ⟨e⟩ := hiso (ModuleCat.of K K) m
  -- Each such attachment has the homology of the negative disc-sphere pair of its piece.
  have hpair (j : {j // ∀ s, f (i j s) = c}) :=
    let hj := (h.isNondegenerateCriticalSubmanifold j).toIsCriticalSubmanifold
    hj.nonempty_singularHomology_negativeDiscSpherePair_iso_union hn (g j).toRiemannianMetric
      h.contMDiff.continuous (hdim j) (hV j) hε.1
      ((h.isNondegenerateCriticalSubmanifold j).isCompact_negativeDiscBundle hn h.contMDiff
        (hdim j) (g j) _)
      ((Θ j).contMDiffOn.continuousOn.mono (hsrc j)) ((Θ j).toPartialEquiv.injOn.mono (hsrc j))
      (fun x hx ↦ hΘf j x (hsrc j hx)) (ModuleCat.of K K) m
  have (j : {j // ∀ s, f (i j s) = c}) :=
    have := (h.isNondegenerateCriticalSubmanifold j).toIsCriticalSubmanifold
      |>.finite_singularHomology_negativeDiscSpherePair_of_isThomClass hn
        (g j).toRiemannianMetric (hdim j) (hV j) hε.1 (u j) (hu j) m
    Module.Finite.equiv (hpair j).some.toLinearEquiv
  rw [e.toLinearEquiv.finrank_eq, ← (biproduct.isoCoproduct _).toLinearEquiv.finrank_eq,
    ModuleCat.finrank_biproduct, ← Finset.filter_filter, Finset.sum_filter,
    Finset.sum_subtype (p := fun j ↦ ∀ s, f (i j s) = c) _ (fun j ↦ by simp)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← (hpair j).some.toLinearEquiv.finrank_eq,
    (h.isNondegenerateCriticalSubmanifold j).toIsCriticalSubmanifold
      |>.finrank_singularHomology_negativeDiscSpherePair_of_isThomClass hn
        (g j).toRiemannianMetric (hdim j) (hV j) hε.1 (u j) (hu j) m]

include hdim g hV u hu in
/-- Cut at `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` into critical bands, the Morse–Bott count in degree `m` is
the sum of the dimensions of the relative homology of the bands: each piece lies on the critical
level of exactly one band. -/
private theorem morseBottCount_eq_sum_finrank_sublevelPair {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ}
    (hs₀ : ∀ x, s 0 < f x) (hsN : ∀ x, f x ≤ s (N + 1))
    (hband : ∀ j, IsCriticalBand I f (s j) (s (j + 1))) (m : ℕ) :
    h.morseBottCount K m = (∑ j ∈ Finset.range (N + 1),
      finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) m :
        ModuleCat K) : ℕ) := by
  classical
  have := h.finite
  let := Fintype.ofFinite ι
  choose c hc hcrit using fun j ↦ (hband j).exists_mem_Ioo_forall_eq
  -- The value `v a` of `f` on the piece `a`, and the band `β a` whose critical level carries it.
  let v (a : ι) : ℝ := f (i a (h.nonempty a).some)
  have hv (a : ι) (x : S a) : f (i a x) = v a := h.subsingleton_image_range hn a
    (mem_image_of_mem f (mem_range_self x)) (mem_image_of_mem f (mem_range_self _))
  have hex (a : ι) : ∃ j, v a ≤ s (j + 1) := ⟨N, hsN _⟩
  let β (a : ι) : ℕ := Nat.find (hex a)
  have hlev (a : ι) (j : ℕ) : (∀ x, f (i a x) = c j) ↔ β a = j := by
    have := h.nonempty a
    simp only [hv, forall_const]
    refine ⟨fun he ↦ le_antisymm (Nat.find_min' _ (he ▸ (hc j).2.le)) (not_lt.1 fun hlt ↦ ?_),
      fun hβ ↦ ?_⟩
    · have := hs (Nat.succ_le_of_lt hlt)
      linarith [Nat.find_spec (hex a), (hc j).1]
    · subst hβ
      -- The value of the piece lies in `(s (β a), s (β a + 1)]`, so it is the critical value there.
      have h0 : s (β a) < v a := by
        rcases Nat.eq_zero_or_pos (β a) with h0 | h0
        · exact h0 ▸ hs₀ _
        · have h0' : 0 < Nat.find (hex a) := h0
          have : ¬v a ≤ s (Nat.find (hex a) - 1 + 1) :=
            Nat.find_min (hex a) (Nat.sub_lt h0' one_pos)
          rwa [Nat.sub_add_cancel h0', not_le] at this
      exact hcrit _ _ (h.range_subset_criticalPoints a (mem_range_self _))
        ⟨h0.le, Nat.find_spec (hex a)⟩
  rw [h.morseBottCount_eq_sum]
  congr 1
  calc ∑ a with h.index a ≤ m, bettiNumber K (S a) (m - h.index a)
      = ∑ j ∈ Finset.range (N + 1), ∑ a with h.index a ≤ m ∧ β a = j,
          bettiNumber K (S a) (m - h.index a) := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := {a | h.index a ≤ m}) (g := β)
          fun a _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.find_min' _ (hsN _)))]
        simp only [Finset.filter_filter]
    _ = _ := Finset.sum_congr rfl fun j _ ↦ by
        rw [h.finrank_singularHomology_sublevelPair_of_isThomClass hn hdim g hV u hu (hc j).1
          (hc j).2 (hcrit j) m]
        exact Finset.sum_congr (Finset.filter_congr fun a _ ↦ by rw [hlev, and_comm])
          fun _ _ ↦ rfl

include hdim g hV u hu in
/-- A Morse–Bott function on a compact manifold can be cut at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`, starting below and ending above all its values, such that the
Morse–Bott count is the sum of the dimensions of the relative homology of the bands. -/
private theorem exists_cut_morseBottCount_eq_sum :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j, IsRegularValue I 𝓘(ℝ) f (s j)) ∧ ∀ m, h.morseBottCount K m =
        (∑ j ∈ Finset.range (N + 1), finrank K ((sublevelPair f (hs j.le_succ)).singularHomology
          (ModuleCat.of K K) m : ModuleCat K) : ℕ) := by
  obtain ⟨s, N, hs, hs₀, hsN, hband, hreg⟩ :=
    exists_monotone_isCriticalBand_of_finite_image_criticalPoints (I := I) h.contMDiff.continuous
      (h.finite_image_criticalPoints hn)
  exact ⟨s, hs, N, hs₀, hsN, hreg,
    h.morseBottCount_eq_sum_finrank_sublevelPair hn hdim g hV u hu hs hs₀ hsN hband⟩

include hdim g hV u hu in
/-- **Bott's polynomial identity from Thom classes of the negative normal bundles.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact Hausdorff second-countable
boundaryless manifold `M` of dimension `m`, with pieces modelled on boundaryless models, and let `K`
be a field. For each piece `S j`, let `g j` be a smooth fibre metric on its normal bundle, whose
negative normal spaces form the negative normal bundle `ν⁻ j` of rank the index `λ_j` of the piece,
and suppose that `ν⁻ j` has a Thom class with coefficients in `K`. Then the Morse–Bott counts
`cₖ = ∑ⱼ b_{k - λ_j}(S j; K)` and the Betti numbers `bₖ` of `M` over `K` satisfy
`∑ cₖ tᵏ = ∑ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q` with natural number coefficients and
degree below `m`. The identity is stated coefficientwise, with the counts in `ℕ∞`, so that it
includes their finiteness. -/
theorem exists_morseBottCount_eq_bettiNumber_add_coeff_of_isThomClass :
    ∃ Q : ℕ[X], Q.degree < finrank ℝ E ∧
      ∀ k, h.morseBottCount K k = (bettiNumber K M k + ((1 + X) * Q).coeff k : ℕ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hcount⟩ :=
    h.exists_cut_morseBottCount_eq_sum hn hdim g hV u hu
  obtain ⟨Q, hQ, -, hQ0⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN (fun j _ ↦ hreg (j + 1)) le_rfl
  refine ⟨Q, (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun k hk ↦ hQ0 k (by exact_mod_cast hk),
    fun k ↦ ?_⟩
  rw [hcount k]
  have hk := congrArg (fun p : ℕ[X] ↦ p.coeff k) hQ
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range, ← bettiNumber_def] at hk
  split_ifs at hk with hkn
  · exact_mod_cast hk
  · -- Above the dimension of `M` neither the bands nor `M` have homology.
    have hlt : finrank ℝ E < k := by lia
    rw [bettiNumber_eq_zero_of_finrank_lt M I K hlt, Finset.sum_eq_zero fun j _ ↦ ?_]
    · rw [← hk]
    · have := ModuleCat.isZero_iff_subsingleton.1
        (isZero_singularHomology_sublevelPair_of_contMDiff h.contMDiff
          h.contMDiff.continuous.isProperMap (hs j.le_succ) (hreg j) (hreg (j + 1))
          (ModuleCat.of K K) hlt)
      exact finrank_zero_of_subsingleton

include hdim g hV u hu in
/-- **The strong Morse–Bott inequalities from Thom classes of the negative normal bundles.** Under
the hypotheses of `exists_morseBottCount_eq_bettiNumber_add_coeff_of_isThomClass`, write `bₖ` for
the Betti numbers of `M` over `K` and `cₖ = ∑ⱼ b_{k - λ_j}(S j; K)` for the Morse–Bott counts. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀` for every `n`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_morseBottCount_of_isThomClass (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (h.morseBottCount K k).toNat := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hcount⟩ :=
    h.exists_cut_morseBottCount_eq_sum hn hdim g hV u hu
  simpa only [hcount, ENat.toNat_natCast, bettiNumber_def] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN (fun j _ ↦ hreg (j + 1)) n

/-! ### Oriented negative normal bundles -/

section Orientation

variable (o : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j,
      letI := subbundleTopology (P j) (F' := Fin (h.index j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI := (hV j).fiberBundle
      haveI := (hV j).vectorBundle
      VectorBundleOrientation (Fin (h.index j) → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) (Fin (h.index j)))

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless] in
include o in
/-- Oriented negative normal bundles have Thom classes with coefficients in every field. -/
private theorem exists_isThomClass_of_orientation (K : Type) [Field K] :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j,
      letI := subbundleTopology (P j) (F' := Fin (h.index j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI := (hV j).fiberBundle
      ∃ u : (thomPair (Fin (h.index j) → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s).singularCohomology
          (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin (h.index j) → ℝ)),
        IsThomClass (Fin (h.index j) → ℝ) (fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) u := fun j ↦ by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let := subbundleTopology (P j) (F' := Fin (h.index j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let := (hV j).fiberBundle
  have := (hV j).vectorBundle
  exact VectorBundleOrientation.exists_isThomClass (by simp) (o j) K

include o in
/-- **Bott's polynomial identity for oriented negative normal bundles.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact Hausdorff second-countable
boundaryless manifold `M` of dimension `m`, with pieces modelled on boundaryless models. For each
piece `S j`, let `g j` be a smooth fibre metric on its normal bundle, whose negative normal spaces
form the negative normal bundle `ν⁻ j` of rank the index `λ_j` of the piece, and suppose that `ν⁻ j`
is oriented. Then for every field `K` the Morse–Bott counts `cₖ = ∑ⱼ b_{k - λ_j}(S j; K)` and the
Betti numbers `bₖ` of `M` over `K` satisfy `∑ cₖ tᵏ = ∑ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q`
with natural number coefficients and degree below `m`. -/
theorem exists_morseBottCount_eq_bettiNumber_add_coeff_of_orientation (K : Type) [Field K] :
    ∃ Q : ℕ[X], Q.degree < finrank ℝ E ∧
      ∀ k, h.morseBottCount K k = (bettiNumber K M k + ((1 + X) * Q).coeff k : ℕ) := by
  choose u hu using h.exists_isThomClass_of_orientation hn hdim g hV o K
  exact h.exists_morseBottCount_eq_bettiNumber_add_coeff_of_isThomClass hn hdim g hV u hu

include o in
/-- **The strong Morse–Bott inequalities for oriented negative normal bundles.** Under the
hypotheses of `exists_morseBottCount_eq_bettiNumber_add_coeff_of_orientation`, for every field `K`
write `bₖ` for the Betti numbers of `M` over `K` and `cₖ = ∑ⱼ b_{k - λ_j}(S j; K)` for the
Morse–Bott counts. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀` for every `n`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_morseBottCount_of_orientation (K : Type)
    [Field K] (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (h.morseBottCount K k).toNat := by
  choose u hu using h.exists_isThomClass_of_orientation hn hdim g hV o K
  exact h.sum_range_neg_one_pow_mul_bettiNumber_le_morseBottCount_of_isThomClass hn hdim g hV u
    hu n

end Orientation

end TauCeti.IsMorseBottFamily
