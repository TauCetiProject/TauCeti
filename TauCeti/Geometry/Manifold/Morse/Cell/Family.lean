/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.CharacteristicHomotopy
public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment

/-!
# The Morse cells of compact families of charts

Let `ψ p i`, for `p` in a parameter space `P` and `i` in an index type `ι`, be charts of a manifold
`M` with values in `ℝⁿ`, in which

`f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`,

whose targets contain the closed ball of radius `√ε` and whose inverses are jointly continuous in
`p` and the point of that ball. Over each `p` the charts `ψ p i` attach one cell `D^{k i}` to the
lower sublevel `M_{c-ε} = {f ≤ c - ε}` for each `i`, with characteristic map
`w ↦ (ψ p i)⁻¹(√ε • (w, 0))` (`OpenPartialHomeomorph.morseCharacteristicMap`). This file packages
these maps as families over `P`:

* `TauCeti.morseFamilyCharacteristicMap`: the characteristic maps
  `P × D^{k i} → M_{c+ε}`, `(p, w) ↦ (ψ p i)⁻¹(√ε • (w, 0))`;
* `TauCeti.morseFamilyAttachingMap`: their restrictions `P × ∂D^{k i} → M_{c-ε}` to the boundary
  spheres.

These are the data of the fiberwise adjunction space
`(P × M_{c-ε}) ∪_α ⨆ᵢ (P × D^{k i})` (`TauCeti.fiberwiseCellAttachment`) and of its comparison
map to `P × M_{c+ε}` (`TauCeti.fiberwiseCellComparison`), which over each `p` is the attachment
of the cells of the charts `ψ p i`. Restricting the charts along a map `P' → P` restricts these
families (`TauCeti.morseFamilyCharacteristicMap_comp_apply`,
`TauCeti.morseFamilyAttachingMap_comp_apply`), so the fiberwise constructions over `P` restrict
to the same constructions over `P'` (`TauCeti.fiberwiseCellAttachmentMap`).

Milnor compares the cells attached by two choices of charts through a homotopy of maps of pairs
`K : χ₁ ≃ χ₀ ∘ h` for a self-map `h` of the disc pair, from which he builds the reattachment map
`E : M_{c-ε} ∪_{α₁} D → M_{c-ε} ∪_{α₀} D`. For two compact families of charts `ψ₀` and `ψ₁` with
common centres, transitions with jointly continuous derivatives near the origin, and a compact
band `f⁻¹[c - ε, c]` free of critical points below `c`, this file constructs such data over `P`
(`TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`): for each `i`, `h i (p, ·)`
is the linear isometry of the disc given by the polar factor of the negative block of the
derivative of the transition `ψ₀ p i ∘ (ψ₁ p i)⁻¹` at the origin, and `K i` is a homotopy over
`P` from the characteristic maps of `ψ₁` to those of `ψ₀` composed with `h i`, keeping the
boundary spheres in `M_{c-ε}`. Fed into `TauCeti.fiberwiseCellReattachment`, these data give the
reattachment map

`E : (P × M_{c-ε}) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × M_{c-ε}) ∪_{α₀} ⨆ᵢ (P × D^{k i})`

over `P`, and `TauCeti.fiberwiseCellReattachmentHomotopy` is then a homotopy from `Φ₀ ∘ E` to
`Φ₁` relative to `P × M_{c-ε}` through maps over `P`, for the comparison maps `Φ₀` and `Φ₁`.

Any self-maps `h i` of the discs admitting such homotopies preserve the boundary spheres, as the
fiberwise reattachment map requires
(`TauCeti.mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap`).

## Main definitions

* `TauCeti.morseFamilyCharacteristicMap`, `TauCeti.morseFamilyAttachingMap`: the characteristic
  and attaching maps of the Morse cells of a family of charts, as families over `P`.

## Main results

* `TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`: the characteristic maps of
  two compact families of Morse charts are homotopic as families of maps of pairs over `P`, up to
  the polar factors of their transitions.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

section Family

variable {M : Type u} [TopologicalSpace M] {n : ℕ} {ι : Type*} {f : M → ℝ} {c ε : ℝ}
  {P : Type*} [TopologicalSpace P]
  (ψ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ι → ℕ)
  (hk : ∀ i, k i ≤ n) (hε : 0 ≤ ε) (hball : ∀ p i, closedBall 0 √ε ⊆ (ψ p i).target)
  (hf : ∀ p i, ∀ y ∈ (ψ p i).source,
    f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ p i y j ^ 2)
  (hs : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ q.1 i).symm q.2)
    (univ ×ˢ closedBall 0 √ε))

include hs in
/-- The characteristic maps `P × D^{k i} → M_{c+ε}`, `(p, w) ↦ (ψ p i)⁻¹(√ε • (w, 0))`, of the
cells of a family of charts `ψ p i` in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose
targets contain the closed ball of radius `√ε` and whose inverses are jointly continuous in `p`
and the point of that ball. Over each `p` it is
`OpenPartialHomeomorph.morseCharacteristicMap` of `ψ p i`. -/
def morseFamilyCharacteristicMap (i : ι) : C(P × TopCat.disk.{u} (k i), {x | f x ≤ c + ε}) where
  toFun q := (ψ q.1 i).morseCharacteristicMap (hk i) hε (hball q.1 i) (hf q.1 i) q.2
  continuous_toFun := continuous_induced_rng.2 <|
    ((continuousOn_morseCellMap_family (ψ := fun p ↦ ψ p i) (hk i) (hs i)).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp (continuous_uliftDown.comp
        continuous_snd))) fun q ↦ ⟨mem_univ _, q.2.down.2⟩).congr fun q ↦
      (OpenPartialHomeomorph.coe_morseCharacteristicMap_apply (hball q.1 i) (hf q.1 i) (hk i) hε
        q.2).symm

@[simp]
theorem morseFamilyCharacteristicMap_apply (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    morseFamilyCharacteristicMap ψ k hk hε hball hf hs i (p, w) =
      (ψ p i).morseCharacteristicMap (hk i) hε (hball p i) (hf p i) w :=
  (rfl)

include hs in
/-- The attaching maps `P × ∂D^{k i} → M_{c-ε}` of the cells of a family of charts: the
restrictions of `TauCeti.morseFamilyCharacteristicMap` to the boundary spheres, which they send
into the lower sublevel `M_{c-ε}`, viewed inside `M_{c+ε}`. Over each `p` it is
`OpenPartialHomeomorph.morseAttachingMap` of `ψ p i`. -/
def morseFamilyAttachingMap (i : ι) :
    C(P × TopCat.diskBoundary.{u} (k i), {y : {x | f x ≤ c + ε} | f y ≤ c - ε}) where
  toFun q := ⟨morseFamilyCharacteristicMap ψ k hk hε hball hf hs i
      (q.1, TopCat.diskBoundaryInclusion (k i) q.2),
    (congrArg f (OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion
      (hball q.1 i) (hf q.1 i) (hk i) hε q.2)).trans_le
        ((ψ q.1 i).morseAttachingMap (hk i) hε (hball q.1 i) (hf q.1 i) q.2).2⟩
  continuous_toFun := ((morseFamilyCharacteristicMap ψ k hk hε hball hf hs i).continuous.comp
    (continuous_fst.prodMk ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
      continuous_snd))).subtype_mk _

/-- On the boundary spheres, the characteristic maps are the attaching maps. This is the
compatibility `TauCeti.fiberwiseCellAttachment` and `TauCeti.fiberwiseCellComparison` require. -/
theorem morseFamilyCharacteristicMap_diskBoundaryInclusion (i : ι) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    morseFamilyCharacteristicMap ψ k hk hε hball hf hs i (p, TopCat.diskBoundaryInclusion (k i) s) =
      morseFamilyAttachingMap ψ k hk hε hball hf hs i (p, s) :=
  (rfl)

@[simp]
theorem coe_morseFamilyAttachingMap_apply (i : ι) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    ((morseFamilyAttachingMap ψ k hk hε hball hf hs i (p, s) : {x | f x ≤ c + ε}) : M) =
      (ψ p i).morseAttachingMap (hk i) hε (hball p i) (hf p i) s :=
  OpenPartialHomeomorph.coe_morseCharacteristicMap_diskBoundaryInclusion (hball p i) (hf p i)
    (hk i) hε s

variable {P' : Type*} [TopologicalSpace P'] (g : P' → P)
  (hs' : ∀ i, ContinuousOn (fun q : P' × EuclideanSpace ℝ (Fin n) ↦ (ψ (g q.1) i).symm q.2)
    (univ ×ˢ closedBall 0 √ε))

/-- The characteristic maps of the charts restricted along a map `g : P' → P` of parameter spaces
are the characteristic maps over `P` restricted along `g`. -/
theorem morseFamilyCharacteristicMap_comp_apply (i : ι) (p : P') (w : TopCat.disk.{u} (k i)) :
    morseFamilyCharacteristicMap (fun p ↦ ψ (g p)) k hk hε (fun p ↦ hball (g p))
        (fun p ↦ hf (g p)) hs' i (p, w) =
      morseFamilyCharacteristicMap ψ k hk hε hball hf hs i (g p, w) :=
  (rfl)

/-- The attaching maps of the charts restricted along a map `g : P' → P` of parameter spaces are
the attaching maps over `P` restricted along `g`. -/
theorem morseFamilyAttachingMap_comp_apply (i : ι) (p : P') (s : TopCat.diskBoundary.{u} (k i)) :
    morseFamilyAttachingMap (fun p ↦ ψ (g p)) k hk hε (fun p ↦ hball (g p))
        (fun p ↦ hf (g p)) hs' i (p, s) =
      morseFamilyAttachingMap ψ k hk hε hball hf hs i (g p, s) :=
  (rfl)

/-- **A homotopy of families of maps of pairs into `χ ∘ h` forces `h` to preserve the boundary
spheres.** Let `χ i` be the characteristic maps of the cells of a family of charts, with
`0 < ε`, and let `h` be a family over `P` of self-maps of the disc `D^{k i}`. If `K` is a homotopy
from some family `g'` to `(p, w) ↦ χ i (p, h (p, w))` keeping the boundary spheres in the lower
sublevel `M_{c-ε}`, then each `h (p, ·)` sends the boundary sphere into itself. This is the form
of the hypotheses of `TauCeti.fiberwiseCellReattachment`. -/
theorem mapsTo_range_diskBoundaryInclusion_of_homotopy_morseFamilyCharacteristicMap
    (hε : 0 < ε) {i : ι}
    {h : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i))}
    {g' : C(P × TopCat.disk.{u} (k i), {x | f x ≤ c + ε})}
    (K : g'.Homotopy ((morseFamilyCharacteristicMap ψ k hk hε.le hball hf hs i).comp
      (ContinuousMap.fst.prodMk h)))
    (hK : ∀ t p (s : TopCat.diskBoundary.{u} (k i)),
      K (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ {y : {x | f x ≤ c + ε} | f y ≤ c - ε})
    (p : P) :
    MapsTo (fun w ↦ h (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))) :=
  mapsTo_range_diskBoundaryInclusion_of_morseCharacteristicMap_le (hk i) hε
    (hball p i) (hf p i) (h := TopCat.ofHom (h.comp ((ContinuousMap.const _ p).prodMk
      (ContinuousMap.id _)))) fun s ↦ by
    have hKs := hK 1 p s
    rw [K.apply_one, ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.fst_apply,
      morseFamilyCharacteristicMap_apply] at hKs
    -- `hKs` is the goal up to evaluating the `TopCat.ofHom` of `w ↦ h (p, w)`.
    exact hKs

end Family

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n : ℕ} {ι : Type*} {P : Type*} [TopologicalSpace P]

/-- **The characteristic maps of two compact families of Morse charts are homotopic as families of
maps of pairs over the parameter space, up to the polar factors of their transitions.** Let
`ψ₀ p i` and `ψ₁ p i`, for `p` in a compact space `P` and `i : ι`, be charts with common centres
`(ψ₀ p i)⁻¹ 0 = (ψ₁ p i)⁻¹ 0` in which `f = c - Σ_{j < k i} yⱼ² + Σ_{j ≥ k i} yⱼ²`, whose targets
contain the closed ball of radius `√ε` and whose inverses are jointly continuous in `p` and the
point of that ball. Suppose that on a ball of radius `r i` about the origin the transitions
`ψ₀ p i ∘ (ψ₁ p i)⁻¹` are defined and differentiable, with derivatives `D i p y` jointly
continuous in `p` and `y`, that `f⁻¹[c - ε, c]` is compact and that `f` has no critical point with
value in `[c - ε, c)`. Let `g i p` be the polar factor of the negative block `ι† (D i p 0) ι` of
`D i p 0`, where `ι : ℝ^{k i} → ℝⁿ` extends by zero onto the first `k i` coordinates. Then each
`g i p` is a linear isometry, the disc maps `(p, w) ↦ g i p w` form a continuous family `h i` over
`P`, and there are homotopies `K i` over `P` from the characteristic maps `χ₁ i` of the charts
`ψ₁ p i` to `(p, w) ↦ χ₀ i (p, g i p w)` keeping the boundary spheres in the lower sublevel
`M_{c-ε}`. These are the data of the fiberwise reattachment map
`TauCeti.fiberwiseCellReattachment` between the families of cells of `ψ₁` and of `ψ₀`. -/
theorem exists_homotopy_morseFamilyCharacteristicMap_polarFactor (hfs : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    [CompactSpace P] (ψ₀ ψ₁ : P → ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n) (hε : 0 < ε)
    (hball₀ : ∀ p i, closedBall 0 √ε ⊆ (ψ₀ p i).target)
    (hball₁ : ∀ p i, closedBall 0 √ε ⊆ (ψ₁ p i).target)
    (hf₀ : ∀ p i, ∀ y ∈ (ψ₀ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₀ p i y j ^ 2)
    (hf₁ : ∀ p i, ∀ y ∈ (ψ₁ p i).source,
      f y = c + ∑ j, (if j.val < k i then -1 else 1) * ψ₁ p i y j ^ 2)
    (hs₀ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hs₁ : ∀ i, ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₁ q.1 i).symm q.2)
      (univ ×ˢ closedBall 0 √ε))
    (hp : ∀ p i, (ψ₀ p i).symm 0 = (ψ₁ p i).symm 0) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (htr : ∀ p i, ball (0 : EuclideanSpace ℝ (Fin n)) (r i) ⊆ (ψ₁ p i).symm ⁻¹' (ψ₀ p i).source)
    {D : ι → P → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p i, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (r i),
      HasFDerivAt (fun z ↦ ψ₀ p i ((ψ₁ p i).symm z)) (D i p y) y)
    (hD : ∀ i, ContinuousOn (Function.uncurry (D i)) (univ ×ˢ ball 0 (r i)))
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ g : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)),
      (∀ i p, ⇑(g i p) = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap ∘L D i p 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (hk i))).toContinuousLinearMap).polarFactor) ∧
      ∃ (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
        (_ : ∀ i p w, h i (p, w) = (g i p).diskMap w)
        (K : ∀ i, (morseFamilyCharacteristicMap ψ₁ k hk hε.le hball₁ hf₁ hs₁ i).Homotopy
          ((morseFamilyCharacteristicMap ψ₀ k hk hε.le hball₀ hf₀ hs₀ i).comp
            (ContinuousMap.fst.prodMk (h i)))),
        ∀ i t p (s : TopCat.diskBoundary.{u} (k i)),
          K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈
            {y : {x | f x ≤ c + ε} | f y ≤ c - ε} := by
  choose g hg hgc K hK₀ hK₁ hKb using fun i ↦
    exists_homotopy_morseCharacteristicMap_polarFactor_family hfs (fun p ↦ ψ₀ p i)
      (fun p ↦ ψ₁ p i) (hk i) hε (fun p ↦ hball₀ p i) (fun p ↦ hball₁ p i) (fun p ↦ hf₀ p i)
      (fun p ↦ hf₁ p i) (hs₀ i) (hs₁ i) (fun p ↦ hp p i) (hr i) (fun p ↦ htr p i)
      (fun p ↦ hT p i) (hD i) hcompact hreg
  -- The polar factors are jointly continuous in the parameter and the point.
  have hgc' (i : ι) : Continuous fun q : P × EuclideanSpace ℝ (Fin (k i)) ↦ g i q.1 q.2 :=
    (((hgc i).comp continuous_fst).clm_apply continuous_snd).congr fun q ↦ by
      simp only [Function.comp_apply, hg]
  let h (i : ι) : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)) :=
    ⟨fun q ↦ (g i q.1).diskMap q.2, continuous_induced_rng.2 <| continuous_induced_rng.2 <|
      ((hgc' i).comp (continuous_fst.prodMk (continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_snd)))).congr fun q ↦
          ((g i q.1).coe_diskMap_apply_down q.2).symm⟩
  exact ⟨g, hg, h, fun i p w ↦ rfl, fun i ↦ ⟨K i, fun q ↦ hK₀ i q.1 q.2, fun q ↦ hK₁ i q.1 q.2⟩,
    fun i t p s ↦ hKb i t p s⟩

end Smooth

end TauCeti
