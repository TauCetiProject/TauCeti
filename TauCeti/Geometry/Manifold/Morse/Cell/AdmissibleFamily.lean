/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# A common width for compact families of Morse charts

A compact family of charts with jointly open coordinate domains has a common coordinate
ball about its centres. For a Morse function with a compact band about a level, the ball
can be chosen together with a smaller band containing no other critical value.
`TauCeti.IsMorse.exists_admissible_morseChartFamily_width` makes this choice uniformly for
finitely many families; every smaller positive width remains admissible.

`TauCeti.IsMorse.exists_pos_homotopy_morseFamilyCharacteristicMap_polarFactor` applies this
choice to two families of normalized Morse charts. It supplies a width and the homotopies
of their characteristic maps as maps of pairs, up to the polar factors of the chart
transitions. Unlike the fixed-width comparison, it does not require a prescribed coordinate
disc to fit in every chart or a prescribed band to contain just one critical value.

No topology on the type of partial homeomorphisms is needed: joint openness of their targets
and joint continuity of their inverses are stated on their actual domains. The parameter
space need only be compact, not Hausdorff or a finite CW complex.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric Filter Topology
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {c δ : ℝ}
  {P : Type*} [TopologicalSpace P] [CompactSpace P] {ι : Type*} [Finite ι]

/-- Finitely many compact families of centred charts admit a common positive width in a compact
Morse band. At every smaller positive width the band is compact, has no critical point off the
central level, and every chart contains the closed coordinate ball of radius `√(2ε)`.
The coordinate domains must be jointly open; pointwise openness alone is not sufficient. -/
theorem IsMorse.exists_admissible_morseChartFamily_width [IsManifold I 1 M] (hf : IsMorse I f)
    {F : Type*} [NormedAddCommGroup F]
    (ψ : P → ι → OpenPartialHomeomorph M F)
    (hzero : ∀ p i, (0 : F) ∈ (ψ p i).target)
    (hopen : ∀ i, IsOpen {q : P × F | q.2 ∈ (ψ q.1 i).target})
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε₀ ∈ Ioc 0 δ, ∀ ε ∈ Ioc 0 ε₀,
      IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) ∧
      (∀ x, c - ε ≤ f x → f x ≤ c + ε → f x ≠ c → mfderiv I 𝓘(ℝ) f x ≠ 0) ∧
      ∀ p i, closedBall (0 : F) √(2 * ε) ⊆ (ψ p i).target := by
  -- Compactness turns the jointly open targets into one neighbourhood of zero.
  have htarget : ∀ᶠ z : F in 𝓝 0, ∀ i p, z ∈ (ψ p i).target := by
    apply eventually_all.2
    intro i
    have hi := isCompact_univ.eventually_forall_of_forall_eventually
      (X := F) (Y := P) (x₀ := 0) (P := fun z p ↦ z ∈ (ψ p i).target)
      (fun p _ ↦ ((hopen i).preimage continuous_swap).mem_nhds (hzero p i))
    simpa only [mem_univ, forall_const] using hi
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.eventually_iff.1 htarget
  obtain ⟨η, hη, hηδ, hcrit⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  refine ⟨min η (r ^ 2 / 2), ⟨lt_min hη (by positivity), (min_le_left _ _).trans hηδ⟩,
    fun ε hε ↦ ?_⟩
  have hεη : ε ≤ η := hε.2.trans (min_le_left _ _)
  have hεδ : ε ≤ δ := hεη.trans hηδ
  refine ⟨hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
    (preimage_mono (Icc_subset_Icc (by linarith [hεδ]) (by linarith [hεδ]))), ?_, ?_⟩
  · intro x hlow hupp hne hderiv
    exact hne (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.mpr hderiv,
      by constructor <;> linarith⟩)
  · intro p i z hz
    apply hball (closedBall_subset_closedBall (ε₁ := √(2 * ε)) (ε₂ := r) ?_ hz) i p
    rw [Real.sqrt_le_left hr.le]
    linarith [hε.2.trans (min_le_right η (r ^ 2 / 2))]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- Two compact families of normalized Morse charts can be compared at a common positive width
chosen inside any given compact Morse band. The comparison is continuous in the parameter and
keeps each attaching sphere in the lower sublevel. The isometries are the polar factors of the
negative blocks of the transition derivatives, and do not depend on the chosen width.

The transition derivatives are given on a common ball, but no common coordinate disc for the
characteristic maps and no isolation of the critical value in the initial band are assumed. -/
theorem IsMorse.exists_pos_homotopy_morseFamilyCharacteristicMap_polarFactor
    (hf : IsMorse I f) {n : ℕ}
    (ψ₀ ψ₁ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n)
    (hzero₀ : ∀ p i, 0 ∈ (ψ₀ p i).target) (hzero₁ : ∀ p i, 0 ∈ (ψ₁ p i).target)
    (hopen₀ : ∀ i, IsOpen {q : P × EuclideanSpace ℝ (Fin n) | q.2 ∈ (ψ₀ q.1 i).target})
    (hopen₁ : ∀ i, IsOpen {q : P × EuclideanSpace ℝ (Fin n) | q.2 ∈ (ψ₁ q.1 i).target})
    (hf₀ : ∀ p i, ∀ y ∈ (ψ₀ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ p i y j ^ 2)
    (hf₁ : ∀ p i, ∀ y ∈ (ψ₁ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ p i y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      {q | q.2 ∈ (ψ₀ q.1 i).target})
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      {q | q.2 ∈ (ψ₁ q.1 i).target})
    (hp : ∀ p i, (ψ₀ p i).symm 0 = (ψ₁ p i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₁ p i).symm ⁻¹' (ψ₀ p i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ₀ p i ((ψ₁ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ (ε : ℝ) (hε : ε ∈ Ioc 0 δ),
      IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) ∧
      (∀ x, c - ε ≤ f x → f x ≤ c + ε → f x ≠ c → mfderiv I 𝓘(ℝ) f x ≠ 0) ∧
      ∃ (hball₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target)
        (hball₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target),
      ∃ g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)),
        (∀ i p, ⇑(g i p) = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap ∘L D i p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap).polarFactor) ∧
        ∃ (hgc : ∀ i, Continuous fun p ↦ (g i p :
            EuclideanSpace ℝ (Fin (k i)) →L[ℝ] EuclideanSpace ℝ (Fin (k i))))
          (hc₀ : ∀ i, ContinuousOn
            (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
            (univ ×ˢ closedBall 0 √ε))
          (hc₁ : ∀ i, ContinuousOn
            (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
            (univ ×ˢ closedBall 0 √ε))
          (K : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.1.le hball₁ hf₁ hc₁ i).Homotopy
            ((morseFamilyCharacteristicMap ψ₀ k hk hε.1.le hball₀ hf₀ hc₀ i).comp
              (ContinuousMap.fst.prodMk (diskMapFamily.{u} (g i) (hgc i))))),
          ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
            K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
              {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
  let ψ : P → Bool × ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    fun p j ↦ if j.1 then ψ₁ p j.2 else ψ₀ p j.2
  have hz : ∀ p i, 0 ∈ (ψ p i).target := by
    rintro p ⟨b, i⟩
    cases b
    · exact hzero₀ p i
    · exact hzero₁ p i
  have ho : ∀ i, IsOpen {q : P × EuclideanSpace ℝ (Fin n) | q.2 ∈ (ψ q.1 i).target} := by
    rintro ⟨b, i⟩
    cases b
    · exact hopen₀ i
    · exact hopen₁ i
  obtain ⟨ε, hε, hwidth⟩ := hf.exists_admissible_morseChartFamily_width ψ hz ho hδ hcompact
  obtain ⟨hcomp, hreg, hball⟩ := hwidth ε ⟨hε.1, le_rfl⟩
  have hb₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target := fun p i ↦
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith [hε.1]))).trans
      (hball p (false, i))
  have hb₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target := fun p i ↦
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith [hε.1]))).trans
      (hball p (true, i))
  have hc₀ i : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε) := (hs₀ i).mono (fun q hq ↦ hb₀ q.1 i hq.2)
  have hc₁ i : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε) := (hs₁ i).mono (fun q hq ↦ hb₁ q.1 i hq.2)
  obtain ⟨g, hg, hgc, K, hK⟩ := exists_homotopy_morseFamilyCharacteristicMap_polarFactor
    hf.contMDiff ψ₀ ψ₁ k hk hε.1 hb₀ hb₁ hf₀ hf₁ hc₀ hc₁ hp hr htr hT hD
    (hcomp.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl (by linarith [hε.1]))))
    (fun x hx₁ hx₂ ↦ hreg x hx₁ (by linarith [hε.1]) (ne_of_lt hx₂))
  exact ⟨ε, hε, hcomp, hreg, hb₀, hb₁, g, hg, hgc, hc₀, hc₁, K, hK⟩

end TauCeti
