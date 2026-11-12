/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment

/-!
# Families of Morse cells over a parameter space

Let `f` be a function on `M`, and let `φ i p`, for `i` in an index set and `p` in a parameter
space `P`, be charts with values in `ℝⁿ` in which

`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`,

and whose targets contain the closed ball of radius `√ε`. Write `M_a = {f ≤ a}`. Each chart
carries the characteristic map `w ↦ (φ i p)⁻¹(√ε • (w, 0))` of its cell, a map of pairs
`(D^{k i}, ∂D^{k i}) → (M_{c+ε}, M_{c-ε})`
(`OpenPartialHomeomorph.morseCharacteristicMap`). When the inverses of the charts are jointly
continuous in `p` and in the point of the ball, these maps form continuous families
`P × D^{k i} → M_{c+ε}` (`TauCeti.morseCharacteristicFamily`), whose restrictions to the boundary
spheres are families of attaching maps `P × ∂D^{k i} → M_{c-ε}`
(`TauCeti.morseAttachingFamily`). These are the data of the fiberwise adjunction space
`(P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` (`TauCeti.fiberwiseCellAttachment`), whose fibre over `p` is
`M_{c-ε}` with the cells of the charts `φ i p` attached, together with its comparison map to
`P × M_{c+ε}` over `P` (`TauCeti.fiberwiseCellComparison`). Restricting the chart families along
a map `g : P' → P` of parameter spaces restricts these families along `g`
(`TauCeti.morseCharacteristicFamily_comp_apply`, `TauCeti.morseAttachingFamily_comp_apply`), which
is the hypothesis of the base change `TauCeti.fiberwiseCellAttachmentMap`.

Two such families `φ₀` and `φ₁` with common centres, over a compact parameter space, are compared
as in Milnor's Lemma 3.6, now over `P`
(`TauCeti.exists_homotopy_morseCharacteristicFamily_polarFactor`).
Let the transitions `φ₀ i p ∘ (φ₁ i p)⁻¹` have derivatives near the origin jointly continuous in
`p`, and let `g i p` be the polar factor of the negative block of the derivative at the origin, an
orthogonal map of `ℝ^{k i}`. If `f⁻¹[c - ε, c]` is compact and contains no critical point below
the level `c`, then each `g i` is a continuous family of orthogonal maps, and a homotopy `K i`
over `P` deforms the characteristic family of `φ₁` to that of `φ₀` composed with `g i`, keeping
the boundary spheres in `M_{c-ε}`. These are exactly the inputs of the fiberwise reattachment map

`E : (P × M_{c-ε}) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × M_{c-ε}) ∪_{α₀} ⨆ᵢ (P × D^{k i})`

(`TauCeti.fiberwiseCellReattachment`, with self-maps `TauCeti.TopCat.diskMapFamily (g i)` of the
discs), which lies over `P`, is the identity on `P × M_{c-ε}`, and satisfies `Φ₀ ∘ E ≃ Φ₁`
relative to `P × M_{c-ε}` through maps over `P`, for the comparison maps `Φ₀` and `Φ₁`
(`TauCeti.fiberwiseCellReattachmentHomotopy`). The homotopies `K i` are those of
`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor_family`, one family of charts at a
time.

## Main definitions

* `TauCeti.morseCharacteristicFamily`: the characteristic maps of a family of Morse charts, as one
  continuous map `P × D^{k i} → M_{c+ε}`.
* `TauCeti.morseAttachingFamily`: their restrictions to the boundary spheres, as maps
  `P × ∂D^{k i} → M_{c-ε}`, with `M_{c-ε}` viewed inside `M_{c+ε}`.

## Main results

* `TauCeti.morseCharacteristicFamily_diskBoundaryInclusion`: on the boundary spheres, the
  characteristic family is the attaching family.
* `TauCeti.exists_homotopy_morseCharacteristicFamily_polarFactor`: **Milnor's comparison of two
  chart families over a compact parameter space.** The characteristic families of `φ₁` and of `φ₀`
  composed with the polar factors of the transitions are homotopic over `P`, keeping the boundary
  spheres in `M_{c-ε}`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

universe u

open Set Metric unitInterval CategoryTheory
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

section Family

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type*} {f : M → ℝ} {c ε : ℝ}
  {P : Type*} [TopologicalSpace P]
  (φ : ι → P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ i p, closedBall 0 √ε ⊆ (φ i p).target)
  (hf : ∀ i p, ∀ y ∈ (φ i p).source,
    f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ i p y j ^ 2)
  (hs : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ i q.1).symm q.2)
    (univ ×ˢ closedBall 0 √ε))

include hs in
/-- The **characteristic family** of a family of Morse charts `φ i p` over a parameter space `P`:
the map `(p, w) ↦ (φ i p)⁻¹(√ε • (w, 0))` from `P × D^{k i}` to the sublevel `M_{c+ε}`, which over
each `p` is the characteristic map of the cell of `φ i p`. It is continuous when the inverses of
the charts are jointly continuous in `p` and in the point of the closed ball of radius `√ε`. -/
def morseCharacteristicFamily (i : ι) : C(P × TopCat.disk.{u} (k i), {x | f x ≤ c + ε}) where
  toFun q := (φ i q.1).morseCharacteristicMap (hk i) hε (hball i q.1) (hf i q.1) q.2
  continuous_toFun := continuous_induced_rng.2 <|
    ((continuousOn_morseCellMap_family (hk i) (hs i)).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp (continuous_uliftDown.comp
        continuous_snd))) fun q ↦ ⟨mem_univ _, q.2.down.2⟩).congr fun q ↦
      (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball i q.1) (hf i q.1) (hk i) hε
        q.2).symm

@[simp]
theorem morseCharacteristicFamily_apply (i : ι) (q : P × TopCat.disk.{u} (k i)) :
    morseCharacteristicFamily φ k hk hε hball hf hs i q =
      (φ i q.1).morseCharacteristicMap (hk i) hε (hball i q.1) (hf i q.1) q.2 :=
  (rfl)

/-- The point `(φ i p)⁻¹(√ε • (s, 0))` of a boundary sphere `‖s‖ = 1` lies in the lower sublevel
`M_{c-ε}`. -/
private theorem apply_morseCharacteristicFamily_diskBoundaryInclusion_le (i : ι)
    (q : P × TopCat.diskBoundary.{u} (k i)) :
    f (morseCharacteristicFamily φ k hk hε hball hf hs i
      (q.1, TopCat.diskBoundaryInclusion (k i) q.2)) ≤ c - ε := by
  rw [morseCharacteristicFamily_apply,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion (hball i q.1)
      (hf i q.1) (hk i) hε q.2]
  exact ((φ i q.1).morseAttachingMap (hk i) hε (hball i q.1) (hf i q.1) q.2).2

/-- The **attaching family** of a family of Morse charts `φ i p` over a parameter space `P`: the
restriction `(p, s) ↦ (φ i p)⁻¹(√ε • (s, 0))` of the characteristic family to `P × ∂D^{k i}`,
which lands in the lower sublevel `M_{c-ε}`, viewed inside `M_{c+ε}`. Over each `p` it is the
attaching map of the cell of `φ i p`. -/
def morseAttachingFamily (i : ι) :
    C(P × TopCat.diskBoundary.{u} (k i), {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) where
  toFun q := ⟨morseCharacteristicFamily φ k hk hε hball hf hs i
      (q.1, TopCat.diskBoundaryInclusion (k i) q.2),
    apply_morseCharacteristicFamily_diskBoundaryInclusion_le φ k hk hε hball hf hs i q⟩
  continuous_toFun := ((morseCharacteristicFamily φ k hk hε hball hf hs i).continuous.comp
    (continuous_fst.prodMk ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
      continuous_snd))).subtype_mk _

/-- Over each parameter, the attaching family is the attaching map of the cell of the chart. -/
@[simp]
theorem coe_coe_morseAttachingFamily_apply (i : ι) (q : P × TopCat.diskBoundary.{u} (k i)) :
    ((morseAttachingFamily φ k hk hε hball hf hs i q : {x | f x ≤ c + ε}) : M) =
      (φ i q.1).morseAttachingMap (hk i) hε (hball i q.1) (hf i q.1) q.2 :=
  OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion (hball i q.1) (hf i q.1)
    (hk i) hε q.2

/-- On the boundary spheres, the characteristic family is the attaching family. This is the
compatibility with which the characteristic families define the comparison map
`TauCeti.fiberwiseCellComparison` out of the fiberwise adjunction space of the attaching
families. -/
theorem morseCharacteristicFamily_diskBoundaryInclusion (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseCharacteristicFamily φ k hk hε hball hf hs i (p, TopCat.diskBoundaryInclusion (k i) s) =
      morseAttachingFamily φ k hk hε hball hf hs i (p, s) :=
  (rfl)

variable {P' : Type*} [TopologicalSpace P'] (g : P' → P)
  (hs' : ∀ i, ContinuousOn (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (φ i (g q.1)).symm q.2)
    (univ ×ˢ closedBall 0 √ε))

/-- The characteristic family of the charts `φ i (g p)` restricted along a map `g : P' → P` of
parameter spaces is the characteristic family of `φ` restricted along `g`. -/
theorem morseCharacteristicFamily_comp_apply (i : ι) (p : P') (w : TopCat.disk.{u} (k i)) :
    morseCharacteristicFamily (fun i p ↦ φ i (g p)) k hk hε (fun i p ↦ hball i (g p))
        (fun i p ↦ hf i (g p)) hs' i (p, w) =
      morseCharacteristicFamily φ k hk hε hball hf hs i (g p, w) :=
  (rfl)

/-- The attaching family of the charts `φ i (g p)` restricted along a map `g : P' → P` of
parameter spaces is the attaching family of `φ` restricted along `g`. -/
theorem morseAttachingFamily_comp_apply (i : ι) (p : P') (s : TopCat.diskBoundary.{u} (k i)) :
    morseAttachingFamily (fun i p ↦ φ i (g p)) k hk hε (fun i p ↦ hball i (g p))
        (fun i p ↦ hf i (g p)) hs' i (p, s) =
      morseAttachingFamily φ k hk hε hball hf hs i (g p, s) :=
  (rfl)

end Family

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ} {ι : Type*} {P : Type*} [TopologicalSpace P]

/-- **Milnor's comparison of two families of Morse charts over a compact parameter space.** Let
`φ₀ i p` and `φ₁ i p`, for `p` in a compact space `P`, be charts with common centres in which
`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²` and whose targets contain the closed ball of radius
`√ε`. Suppose that their inverses are jointly continuous in `p` and in the point of that ball, and
that on a ball of radius `r i` about the origin the transitions `φ₀ i p ∘ (φ₁ i p)⁻¹` are defined
and differentiable with derivatives `D i p y` jointly continuous in `p` and `y`. Suppose that
`f⁻¹[c - ε, c]` is compact and that `f` has no critical point with value in `[c - ε, c)`. Let
`g i p` be the polar factor of the negative block `ι† (D i p 0) ι` of `D i p 0`, where
`ι : ℝ^{k i} → ℝⁿ` extends by zero onto the first `k i` coordinates. Then each `g i p` is a linear
isometry, jointly continuous in `p` and the point of `ℝ^{k i}`, and a homotopy `K i` over `P`
deforms the characteristic family of `φ₁` to the characteristic family of `φ₀` composed with the
disk maps of `g i`, keeping the boundary spheres in the lower sublevel `M_{c-ε}`.

These are the self-maps of the discs and the homotopies from which
`TauCeti.fiberwiseCellReattachment` builds the reattachment map between the fiberwise adjunction
spaces of the attaching families of `φ₁` and `φ₀`. -/
theorem exists_homotopy_morseCharacteristicFamily_polarFactor [CompactSpace P]
    (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (φ₀ φ₁ : ι → P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
    (hk : ∀ i, k i ≤ n) (hε : 0 < ε) (hball₀ : ∀ i p, closedBall 0 √ε ⊆ (φ₀ i p).target)
    (hball₁ : ∀ i p, closedBall 0 √ε ⊆ (φ₁ i p).target)
    (hf₀ : ∀ i p, ∀ y ∈ (φ₀ i p).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₀ i p y j ^ 2)
    (hf₁ : ∀ i p, ∀ y ∈ (φ₁ i p).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * φ₁ i p y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ₀ i q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (φ₁ i q.1).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ i p, (φ₀ i p).symm 0 = (φ₁ i p).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ i p, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (φ₁ i p).symm ⁻¹' (φ₀ i p).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ∀ i p, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ φ₀ i p ((φ₁ i p).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ (g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
      (hg : ∀ i, Continuous fun q : P × EuclideanSpace ℝ (Fin (k i)) ↦ g i q.1 q.2),
      (∀ i p, ⇑(g i p) = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap ∘L D i p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap).polarFactor) ∧
      ∃ K : ∀ i, (morseCharacteristicFamily φ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
          ((morseCharacteristicFamily φ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
            (ContinuousMap.fst.prodMk (TopCat.diskMapFamily (g i) (hg i)))),
        ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
          {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
  choose g hg hcont K hK₀ hK₁ hKb using fun i ↦
    exists_homotopy_morseCharacteristicMap_polarFactor_family hfs (φ₀ i) (φ₁ i) (hk i) hε
      (hball₀ i) (hball₁ i) (hf₀ i) (hf₁ i) (hs₀ i) (hs₁ i) (hp i) (hr i) (htr i) (hT i) (hD i)
      hcompact hreg
  -- The polar factors are jointly continuous, since they depend continuously on `p` as operators.
  have hgc (i : ι) : Continuous fun q : P × EuclideanSpace ℝ (Fin (k i)) ↦ g i q.1 q.2 :=
    (((hcont i).comp continuous_fst).clm_apply continuous_snd).congr fun q ↦ by
      simp only [Function.comp_apply, hg]
  exact ⟨g, hgc, hg, fun i ↦
    { toContinuousMap := K i
      map_zero_left q := hK₀ i q.1 q.2
      map_one_left := by
        rintro ⟨p, w⟩
        simpa using hK₁ i p w }, hKb⟩

end Comparison

end TauCeti
