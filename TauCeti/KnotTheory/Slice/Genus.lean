/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.ENat.Lattice
public import TauCeti.KnotTheory.Slice.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# The smooth slice genus of a knot

The **slice genus** `g_s(K)` (or four-ball genus) of a knot `K ⊆ S³` is the least genus of a
compact, connected, orientable surface smoothly and properly embedded in the four-ball `D⁴` with
boundary `K`. It is `0` for the smoothly slice knots, which bound a disc (classically exactly for
them, a converse not proved here), and it is the quantity bounded below by the concordance
invariants `|σ(K)| / 2` and `|τ(K)|`.

As for sliceness (`TauCeti.IsSmoothlySlice`), the knot is a smooth circle embedding
`K : S¹ → Sⁿ` into the unit sphere of an `(n + 1)`-dimensional real inner product space `E`, so that
`S³ ⊆ ℝ⁴` is the case `n = 3`. A **smooth slice surface** for `K`
(`TauCeti.SmoothSliceSurface K`) bundles

* a compact, connected, orientable smooth surface `S` with boundary, modelled on the half-plane
  `EuclideanHalfSpace 2` (orientability is `TauCeti.Orientable`, the existence of an atlas whose
  coordinate changes have derivatives of positive determinant);
* a smooth embedding `Φ : S → Dⁿ⁺¹` of manifolds with boundary, properly embedded (the preimage
  of the boundary sphere is the boundary of `S`), which carries the boundary of `S` onto the image
  of `K`.

The carrier of the surface is a type with instances, as everywhere in Tau Ceti; it is bundled here
only because the slice genus is a minimum over all such surfaces. Since `Φ` is an embedding, the
boundary of `S` is homeomorphic to the image of `K`, a circle, so `S` has exactly one boundary
component; and `S` is Hausdorff, being embedded in the ball. Only the image of `K` enters, so the
slice genus does not depend on the parametrization or orientation of the knot.

The **genus** of a slice surface (`TauCeti.SmoothSliceSurface.genus`) is read off its rational
singular homology: a compact, connected, orientable surface of genus `g` with one boundary circle
has `H₁(S; ℚ) ≅ ℚ²ᵍ`, so its genus is half the dimension of `H₁(S; ℚ)`. The slice genus
(`TauCeti.sliceGenus K`) is the infimum of the genera of the slice surfaces of `K`, valued in `ℕ∞`
so that it is `⊤` rather than `0` should `K` have no slice surface at all. (Every knot in `S³`
bounds a Seifert surface, whose interior can be pushed into `D⁴`, so `g_s(K)` is finite for
`n = 3`; that existence theorem is not proved here.)

A smooth slice disc is a slice surface whose carrier is the closed unit disc, which is compact,
connected and orientable (`TauCeti.orientable_closedBall`), and contractible, so its first homology
vanishes and its genus is `0`. Hence smoothly slice knots, in particular the unknot, have slice
genus `0`. The converse, that a slice surface of genus `0` is a disc, needs the classification of
compact surfaces and is not proved here.

## Main definitions

* `TauCeti.SmoothSliceSurface K`: a smooth slice surface for `K`.
* `TauCeti.SmoothSliceSurface.genus`: the genus `dim H₁(S; ℚ) / 2` of a slice surface.
* `TauCeti.sliceGenus K`: the smooth slice genus of `K`, in `ℕ∞`.
* `TauCeti.IsSmoothSliceDisc.toSmoothSliceSurface`: a smooth slice disc as a slice surface.

## Main results

* `TauCeti.sliceGenus_le_genus`, `TauCeti.le_sliceGenus_iff`: the slice genus is the infimum of
  the genera of the slice surfaces.
* `TauCeti.sliceGenus_lt_top_iff`, `TauCeti.exists_genus_eq_sliceGenus`: the slice genus is finite
  exactly when a slice surface exists, and is then attained.
* `TauCeti.sliceGenus_congr_range`, `TauCeti.sliceGenus_rotate`, `TauCeti.sliceGenus_reverse`: the
  slice genus only depends on the image of the knot.
* `TauCeti.IsSmoothSliceDisc.genus_toSmoothSliceSurface`: a slice disc has genus `0`.
* `TauCeti.IsSmoothlySlice.sliceGenus_eq_zero`, `TauCeti.sliceGenus_unknot`: smoothly slice knots,
  and in particular the unknot, have slice genus `0`.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for the four-ball genus.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots and surfaces in `D⁴`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory AlgebraicTopology Manifold Metric Module Set
open scoped EuclideanSpace Manifold ContDiff

attribute [local instance] Complex.finrank_real_complex_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A **smooth slice surface** for a smooth circle embedding `K : S¹ → Sⁿ` in the unit sphere of
`E`: a compact, connected, orientable smooth surface with boundary, together with a smooth
embedding into the closed unit ball of `E`, in the sense of manifolds with boundary, which is
properly embedded (the preimage of the boundary sphere is the boundary of the surface) and carries
the boundary of the surface onto the image of `K`. -/
structure SmoothSliceSurface (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) where
  /-- The underlying surface. -/
  carrier : Type
  /-- The topology of the surface. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The charts of the surface, modelled on the half-plane. -/
  [chartedSpace : ChartedSpace (EuclideanHalfSpace 2) carrier]
  /-- The surface is a smooth manifold with boundary. -/
  [isManifold : IsManifold (𝓡∂ 2) ∞ carrier]
  /-- The surface is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The surface is connected. -/
  [connectedSpace : ConnectedSpace carrier]
  /-- The surface is orientable. -/
  [orientable : Orientable (𝓡∂ 2) ∞ carrier]
  /-- The embedding of the surface into the closed unit ball. -/
  toFun : carrier → closedBall (0 : E) 1
  /-- The surface is smoothly embedded, as a manifold with boundary. -/
  isSmoothEmbedding : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ toFun
  /-- The surface is properly embedded: it meets the boundary sphere exactly along its boundary. -/
  preimage_boundary :
    toFun ⁻¹' (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) = (𝓡∂ 2).boundary carrier
  /-- The boundary of the surface is carried onto the image of `K`. -/
  image_boundary : (Subtype.val ∘ toFun) '' (𝓡∂ 2).boundary carrier = Subtype.val '' range K

namespace SmoothSliceSurface

attribute [instance] topologicalSpace chartedSpace isManifold compactSpace connectedSpace orientable

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The first singular homology `H₁(S; ℚ)` of a slice surface, with rational coefficients. -/
abbrev firstHomology (S : SmoothSliceSurface K) : Type :=
  ((singularHomologyFunctor (ModuleCat ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj (TopCat.of S.carrier)

/-- The **genus** of a slice surface: half the dimension of its first rational homology. A
compact, connected, orientable surface of genus `g` with one boundary circle has
`H₁(S; ℚ) ≅ ℚ²ᵍ`. -/
def genus (S : SmoothSliceSurface K) : ℕ :=
  finrank ℚ S.firstHomology / 2

/-- The genus of a slice surface is half the dimension of its first rational homology. -/
theorem genus_def (S : SmoothSliceSurface K) : S.genus = finrank ℚ S.firstHomology / 2 :=
  (rfl)

/-- A slice surface for `K` is one for every knot `K'` with the same image. -/
def congrRange (S : SmoothSliceSurface K) (h : range K = range K') : SmoothSliceSurface K' where
  carrier := S.carrier
  toFun := S.toFun
  isSmoothEmbedding := S.isSmoothEmbedding
  preimage_boundary := S.preimage_boundary
  image_boundary := h ▸ S.image_boundary

/-- Transporting a slice surface to a knot with the same image keeps its genus. -/
@[simp]
theorem genus_congrRange (S : SmoothSliceSurface K) (h : range K = range K') :
    (S.congrRange h).genus = S.genus :=
  (rfl)

end SmoothSliceSurface

open SmoothSliceSurface

/-- The **smooth slice genus** `g_s(K)` of a smooth circle embedding `K : S¹ → Sⁿ`: the least
genus of a smooth slice surface for `K`, or `⊤` if there is none. -/
def sliceGenus (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  ⨅ S : SmoothSliceSurface K, (S.genus : ℕ∞)

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The slice genus is the infimum of the genera of all slice surfaces. -/
theorem sliceGenus_def : sliceGenus K = ⨅ S : SmoothSliceSurface K, (S.genus : ℕ∞) :=
  (rfl)

/-- The slice genus is at most the genus of any slice surface. -/
theorem sliceGenus_le_genus (S : SmoothSliceSurface K) : sliceGenus K ≤ S.genus :=
  iInf_le _ S

/-- A lower bound for the slice genus is a lower bound for the genus of every slice surface. -/
@[simp]
theorem le_sliceGenus_iff {m : ℕ∞} :
    m ≤ sliceGenus K ↔ ∀ S : SmoothSliceSurface K, m ≤ S.genus :=
  le_iInf_iff

/-- The slice genus is attained when a slice surface exists. -/
theorem exists_genus_eq_sliceGenus [Nonempty (SmoothSliceSurface K)] :
    ∃ S : SmoothSliceSurface K, (S.genus : ℕ∞) = sliceGenus K :=
  ENat.exists_eq_iInf _

/-- The slice genus is finite exactly when a slice surface exists. -/
@[simp]
theorem sliceGenus_lt_top_iff : sliceGenus K < ⊤ ↔ Nonempty (SmoothSliceSurface K) :=
  ENat.iInf_natCast_lt_top

/-- Two knots with the same image have the same slice genus. -/
theorem sliceGenus_congr_range (h : range K = range K') : sliceGenus K = sliceGenus K' :=
  le_antisymm (le_sliceGenus_iff.2 fun S ↦ by simpa using sliceGenus_le_genus (S.congrRange h.symm))
    (le_sliceGenus_iff.2 fun S ↦ by simpa using sliceGenus_le_genus (S.congrRange h))

/-- The slice genus does not depend on the rotation of the parametrization. -/
@[simp]
theorem sliceGenus_rotate (a : Circle) : sliceGenus (K.rotate a) = sliceGenus K :=
  sliceGenus_congr_range (K.range_rotate a)

/-- The slice genus does not depend on the orientation of the knot. -/
@[simp]
theorem sliceGenus_reverse : sliceGenus K.reverse = sliceGenus K :=
  sliceGenus_congr_range K.range_reverse

/-! ### Slice discs -/

/-- A smooth slice disc for `K`, as a smooth slice surface whose carrier is the closed unit disc:
the disc is compact, connected and orientable. -/
def IsSmoothSliceDisc.toSmoothSliceSurface {Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1}
    (h : IsSmoothSliceDisc K Φ) : SmoothSliceSurface K where
  carrier := closedBall (0 : ℂ) 1
  compactSpace := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  connectedSpace := isConnected_iff_connectedSpace.1
    ((convex_closedBall 0 1).isConnected (nonempty_closedBall.2 zero_le_one))
  orientable := orientable_closedBall le_rfl
  toFun := Φ
  isSmoothEmbedding := h.isSmoothEmbedding
  preimage_boundary := h.preimage_boundary
  image_boundary := by
    rw [← h.image_range_inclusion, boundary_closedBall]
    congr 1
    exact (Set.range_inclusion _).symm

/-- A smooth slice disc has genus `0`: the disc is contractible, so its first homology
vanishes. -/
@[simp]
theorem IsSmoothSliceDisc.genus_toSmoothSliceSurface
    {Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1} (h : IsSmoothSliceDisc K Φ) :
    h.toSmoothSliceSurface.genus = 0 := by
  have : ContractibleSpace h.toSmoothSliceSurface.carrier :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace (nonempty_closedBall.2 zero_le_one)
  have := ModuleCat.isZero_iff_subsingleton.1 <|
    isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℚ ℚ)
      (TopCat.of h.toSmoothSliceSurface.carrier) one_ne_zero
  rw [genus_def, finrank_zero_of_subsingleton, Nat.zero_div]

/-- **Smoothly slice knots have slice genus `0`.** -/
theorem IsSmoothlySlice.sliceGenus_eq_zero (h : IsSmoothlySlice K) : sliceGenus K = 0 := by
  obtain ⟨Φ, hΦ⟩ := h.elim
  exact nonpos_iff_eq_zero.1 <| by
    simpa using sliceGenus_le_genus hΦ.toSmoothSliceSurface

/-- **The unknot has slice genus `0`.** -/
@[simp]
theorem sliceGenus_unknot : sliceGenus unknot = 0 :=
  isSmoothlySlice_unknot.sliceGenus_eq_zero

end TauCeti
