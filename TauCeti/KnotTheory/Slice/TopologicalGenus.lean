/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Slice.Genus
import Mathlib.Analysis.Convex.Contractible
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.Geometry.Manifold.Orientation.ClosedBall

/-!
# The topological slice genus of a knot

The **topological slice genus** `g_s^top(K)` of a knot `K ⊆ S³` is the least genus of a compact,
connected, orientable surface *locally flatly* and properly embedded in the four-ball `D⁴` with
boundary `K`. It is the topological counterpart of the smooth slice genus `TauCeti.sliceGenus`,
exactly as topological sliceness (`TauCeti.IsTopologicallySlice`) is the counterpart of smooth
sliceness: it is `0` on topologically slice knots and at most the smooth slice genus, and the gap
between the two genera is the subject of Freedman's work on topological four-manifolds.

As in `TauCeti.KnotTheory.Slice.Genus`, the knot is a smooth circle embedding `K : S¹ → Sⁿ` into
the unit sphere of an `(n + 1)`-dimensional real inner product space `E`, with `S³ ⊆ ℝ⁴` the case
`n = 3`. A **topological slice surface** for `K` (`TauCeti.TopologicalSliceSurface K`) bundles

* a compact, connected, orientable surface `S` with boundary, modelled on the half-plane
  `EuclideanHalfSpace 2`;
* a locally flat embedding `Φ : S → Dⁿ⁺¹` (`TauCeti.IsLocallyFlat`), with tangential model the
  half-plane and complementary model `ℝⁿ⁻¹`, which is properly embedded (the preimage of the
  boundary sphere is the boundary of `S`) and carries the boundary of `S` onto the image of `K`.

Only the embedding is weakened from the smooth case. The abstract surface `S` still carries a
smooth structure, which is used to state its orientability (`TauCeti.Orientable`). This is no
restriction: every compact topological surface is homeomorphic to a smooth one (by Radó's
triangulation theorem and the classification of surfaces), and the conditions on `Φ` and the
genus only see the topology of `S`. The same convention is used for locally flat slice discs
(`TauCeti.IsTopologicalSliceDisc`), whose carrier is the smooth closed unit disc.

The **genus** of a topological slice surface (`TauCeti.TopologicalSliceSurface.genus`) is half the
dimension of its first rational homology, as for smooth slice surfaces, and the topological slice
genus (`TauCeti.topologicalSliceGenus K`) is the infimum of these genera in `ℕ∞`.

A smooth slice surface is a neat smooth embedding of manifolds with boundary, hence locally flat
(`TauCeti.IsLocallyFlat.of_isSmoothEmbedding_of_preimage_boundary_of_sub_eq`), so it is a
topological slice surface of the same genus
(`TauCeti.SmoothSliceSurface.toTopologicalSliceSurface`). Hence the topological slice genus is at
most the smooth one (`TauCeti.topologicalSliceGenus_le_sliceGenus`). A locally flat slice disc is
a topological slice surface of genus `0`, so topologically slice knots have topological slice genus
`0`. The converse, that a slice surface of genus `0` is a disc, needs the classification of compact
surfaces and is not proved here.

## Main definitions

* `TauCeti.TopologicalSliceSurface K`: a locally flat slice surface for `K`.
* `TauCeti.TopologicalSliceSurface.genus`: the genus `dim H₁(S; ℚ) / 2` of such a surface.
* `TauCeti.topologicalSliceGenus K`: the topological slice genus of `K`, in `ℕ∞`.
* `TauCeti.SmoothSliceSurface.toTopologicalSliceSurface`: a smooth slice surface, read as a
  topological one.
* `TauCeti.IsTopologicalSliceDisc.toTopologicalSliceSurface`: a locally flat slice disc as a
  topological slice surface.

## Main results

* `TauCeti.topologicalSliceGenus_le_genus`, `TauCeti.le_topologicalSliceGenus_iff`: the
  topological slice genus is the infimum of the genera of the topological slice surfaces.
* `TauCeti.topologicalSliceGenus_lt_top_iff`, `TauCeti.exists_genus_eq_topologicalSliceGenus`: it
  is finite exactly when a topological slice surface exists, and is then attained.
* `TauCeti.topologicalSliceGenus_le_sliceGenus`: the topological slice genus is at most the smooth
  slice genus.
* `TauCeti.topologicalSliceGenus_congr_range`, `TauCeti.topologicalSliceGenus_rotate`,
  `TauCeti.topologicalSliceGenus_reverse`,
  `TauCeti.topologicalSliceGenus_congr_linearIsometryEquiv`: it only depends on the image of the
  knot, and is invariant under linear isometries of the ambient spaces.
* `TauCeti.IsTopologicallySlice.topologicalSliceGenus_eq_zero`,
  `TauCeti.topologicalSliceGenus_unknot`: topologically slice knots, and in particular the unknot,
  have topological slice genus `0`.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for the smooth and topological four-ball genera.
* M. Freedman and F. Quinn, *Topology of 4-Manifolds*, Princeton (1990), Section 11.7, for locally
  flat surfaces in the four-ball.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Manifold Metric Module Set
open scoped EuclideanSpace Manifold ContDiff

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fact (finrank ℝ F = n + 1)]

/-- A **topological slice surface** for a smooth circle embedding `K : S¹ → Sⁿ` in the unit sphere
of `E`: a compact, connected, orientable surface with boundary, together with a locally flat
embedding into the closed unit ball of `E`, with tangential model the half-plane and complementary
model `ℝⁿ⁻¹`, which is properly embedded (the preimage of the boundary sphere is the boundary of the
surface) and carries the boundary of the surface onto the image of `K`. The surface carries a smooth
structure only to state its orientability; the embedding is merely locally flat. -/
structure TopologicalSliceSurface (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) where
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
  [orientable : Orientable (𝓡∂ 2) carrier]
  /-- The embedding of the surface into the closed unit ball. -/
  toFun : carrier → closedBall (0 : E) 1
  /-- The surface is locally flatly embedded, flat up to the boundary sphere. -/
  isLocallyFlat : IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1))) toFun
  /-- The surface is properly embedded: it meets the boundary sphere exactly along its boundary. -/
  preimage_boundary :
    toFun ⁻¹' (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) = (𝓡∂ 2).boundary carrier
  /-- The boundary of the surface is carried onto the image of `K`. -/
  image_boundary : (Subtype.val ∘ toFun) '' (𝓡∂ 2).boundary carrier = Subtype.val '' range K

namespace TopologicalSliceSurface

attribute [instance] topologicalSpace chartedSpace isManifold compactSpace connectedSpace orientable

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The first singular homology `H₁(S; ℚ)` of a topological slice surface, with rational
coefficients. -/
abbrev firstHomology (S : TopologicalSliceSurface K) : Type :=
  ((singularHomologyFunctor (ModuleCat ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj (TopCat.of S.carrier)

/-- The **genus** of a topological slice surface: half the dimension of its first rational
homology. A compact, connected, orientable surface of genus `g` with one boundary circle has
`H₁(S; ℚ) ≅ ℚ²ᵍ`. -/
def genus (S : TopologicalSliceSurface K) : ℕ :=
  finrank ℚ S.firstHomology / 2

/-- The genus of a topological slice surface is half the dimension of its first rational
homology. -/
theorem genus_def (S : TopologicalSliceSurface K) : S.genus = finrank ℚ S.firstHomology / 2 :=
  (rfl)

/-- A topological slice surface for `K` is one for every knot `K'` with the same image. -/
def congrRange (S : TopologicalSliceSurface K) (h : range K = range K') :
    TopologicalSliceSurface K' where
  carrier := S.carrier
  toFun := S.toFun
  isLocallyFlat := S.isLocallyFlat
  preimage_boundary := S.preimage_boundary
  image_boundary := h ▸ S.image_boundary

/-- Transporting a topological slice surface to a knot with the same image keeps its genus. -/
@[simp]
theorem genus_congrRange (S : TopologicalSliceSurface K) (h : range K = range K') :
    (S.congrRange h).genus = S.genus :=
  (rfl)

/-- Transport of a topological slice surface for `K` along a linear isometry `e : E ≃ₗᵢ[ℝ] F` of
the ambient spaces: the same surface, embedded by `e ∘ S.toFun`, is a topological slice surface for
`K' = e ∘ K`. -/
def mapLinearIsometryEquiv (S : TopologicalSliceSurface K) (e : E ≃ₗᵢ[ℝ] F)
    {K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : F) 1)} (hK' : ∀ z, (K' z : F) = e (K z)) :
    TopologicalSliceSurface K' where
  carrier := S.carrier
  toFun := e.toLinearIsometry.unitClosedBallMap ∘ S.toFun
  isLocallyFlat := by
    have := S.isLocallyFlat.homeomorph_comp
      (e.unitClosedBallDiffeomorph (m := n + 1) (n := n + 1) (k := ∞)).toHomeomorph
    rwa [Diffeomorph.coe_toHomeomorph, LinearIsometryEquiv.coe_unitClosedBallDiffeomorph] at this
  preimage_boundary := by
    rw [← S.preimage_boundary]
    ext x
    simp [boundary_closedBall]
  image_boundary := by
    have hcomp : Subtype.val ∘ (e.toLinearIsometry.unitClosedBallMap ∘ S.toFun) =
        e ∘ (Subtype.val ∘ S.toFun) :=
      funext fun x ↦ by simp
    rw [hcomp, image_comp, S.image_boundary]
    simp only [← range_comp]
    exact congrArg range (funext fun z ↦ by simp [hK'])

/-- Transporting a topological slice surface along a linear isometry of the ambient spaces keeps
its genus. -/
@[simp]
theorem genus_mapLinearIsometryEquiv (S : TopologicalSliceSurface K) (e : E ≃ₗᵢ[ℝ] F)
    {K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : F) 1)} (hK' : ∀ z, (K' z : F) = e (K z)) :
    (S.mapLinearIsometryEquiv e hK').genus = S.genus :=
  (rfl)

end TopologicalSliceSurface

open TopologicalSliceSurface

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- A smooth slice surface for `K`, read as a topological slice surface: a neat smooth embedding of
manifolds with boundary is locally flat with tangential model the half-plane and complementary
model `ℝⁿ⁻¹`. -/
def SmoothSliceSurface.toTopologicalSliceSurface (S : SmoothSliceSurface K) :
    TopologicalSliceSurface K where
  carrier := S.carrier
  toFun := S.toFun
  isLocallyFlat := .of_isSmoothEmbedding_of_preimage_boundary_of_sub_eq (by simp)
    S.isSmoothEmbedding S.preimage_boundary (by omega)
  preimage_boundary := S.preimage_boundary
  image_boundary := S.image_boundary

/-- A smooth slice surface has the same genus as a topological slice surface. -/
@[simp]
theorem SmoothSliceSurface.genus_toTopologicalSliceSurface (S : SmoothSliceSurface K) :
    S.toTopologicalSliceSurface.genus = S.genus := by
  rw [TopologicalSliceSurface.genus_def, SmoothSliceSurface.genus_def]
  rfl

/-- A locally flat slice disc for `K`, as a topological slice surface whose carrier is the closed
unit disc: the disc is compact, connected and orientable. -/
def IsTopologicalSliceDisc.toTopologicalSliceSurface
    {Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1} (h : IsTopologicalSliceDisc K Φ) :
    TopologicalSliceSurface K where
  carrier := closedBall (0 : ℂ) 1
  compactSpace := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  connectedSpace := isConnected_iff_connectedSpace.1
    ((convex_closedBall 0 1).isConnected (nonempty_closedBall.2 zero_le_one))
  orientable := orientable_closedBall
  toFun := Φ
  isLocallyFlat := h.isLocallyFlat
  preimage_boundary := h.preimage_boundary
  image_boundary := by
    rw [← h.image_range_inclusion, boundary_closedBall]
    congr 1
    exact (Set.range_inclusion _).symm

/-- A locally flat slice disc has genus `0`: the disc is contractible, so its first homology
vanishes. -/
@[simp]
theorem IsTopologicalSliceDisc.genus_toTopologicalSliceSurface
    {Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1} (h : IsTopologicalSliceDisc K Φ) :
    h.toTopologicalSliceSurface.genus = 0 := by
  have : ContractibleSpace h.toTopologicalSliceSurface.carrier :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace (nonempty_closedBall.2 zero_le_one)
  simp [genus_def]

/-- The **topological slice genus** `g_s^top(K)` of a smooth circle embedding `K : S¹ → Sⁿ`: the
least genus of a topological slice surface for `K`, or `⊤` if there is none. -/
def topologicalSliceGenus (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  ⨅ S : TopologicalSliceSurface K, (S.genus : ℕ∞)

/-- The topological slice genus is the infimum of the genera of all topological slice surfaces. -/
theorem topologicalSliceGenus_def :
    topologicalSliceGenus K = ⨅ S : TopologicalSliceSurface K, (S.genus : ℕ∞) :=
  (rfl)

/-- The topological slice genus is at most the genus of any topological slice surface. -/
theorem topologicalSliceGenus_le_genus (S : TopologicalSliceSurface K) :
    topologicalSliceGenus K ≤ S.genus :=
  iInf_le _ S

/-- A lower bound for the topological slice genus is a lower bound for the genus of every
topological slice surface. -/
@[simp]
theorem le_topologicalSliceGenus_iff {m : ℕ∞} :
    m ≤ topologicalSliceGenus K ↔ ∀ S : TopologicalSliceSurface K, m ≤ S.genus :=
  le_iInf_iff

/-- The topological slice genus is attained when a topological slice surface exists. -/
theorem exists_genus_eq_topologicalSliceGenus [Nonempty (TopologicalSliceSurface K)] :
    ∃ S : TopologicalSliceSurface K, (S.genus : ℕ∞) = topologicalSliceGenus K :=
  ENat.exists_eq_iInf _

/-- The topological slice genus is finite exactly when a topological slice surface exists. -/
@[simp]
theorem topologicalSliceGenus_lt_top_iff :
    topologicalSliceGenus K < ⊤ ↔ Nonempty (TopologicalSliceSurface K) :=
  ENat.iInf_natCast_lt_top

/-- **The topological slice genus is at most the smooth slice genus**: every smooth slice surface
is a topological slice surface of the same genus. -/
theorem topologicalSliceGenus_le_sliceGenus : topologicalSliceGenus K ≤ sliceGenus K :=
  le_sliceGenus_iff.2 fun S ↦ by
    simpa using topologicalSliceGenus_le_genus S.toTopologicalSliceSurface

/-- Two knots with the same image have the same topological slice genus. -/
theorem topologicalSliceGenus_congr_range (h : range K = range K') :
    topologicalSliceGenus K = topologicalSliceGenus K' :=
  le_antisymm
    (le_topologicalSliceGenus_iff.2 fun S ↦ by
      simpa using topologicalSliceGenus_le_genus (S.congrRange h.symm))
    (le_topologicalSliceGenus_iff.2 fun S ↦ by
      simpa using topologicalSliceGenus_le_genus (S.congrRange h))

/-- The topological slice genus does not depend on the rotation of the parametrization. -/
@[simp]
theorem topologicalSliceGenus_rotate (a : Circle) :
    topologicalSliceGenus (K.rotate a) = topologicalSliceGenus K :=
  topologicalSliceGenus_congr_range (K.range_rotate a)

/-- The topological slice genus does not depend on the orientation of the knot. -/
@[simp]
theorem topologicalSliceGenus_reverse : topologicalSliceGenus K.reverse = topologicalSliceGenus K :=
  topologicalSliceGenus_congr_range K.range_reverse

/-- The topological slice genus is invariant under linear isometries of the ambient spaces: if
`K' = e ∘ K` for a linear isometry `e : E ≃ₗᵢ[ℝ] F`, then `K'` and `K` have the same topological
slice genus. -/
theorem topologicalSliceGenus_congr_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] F)
    {K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : F) 1)} (hK' : ∀ z, (K' z : F) = e (K z)) :
    topologicalSliceGenus K' = topologicalSliceGenus K := by
  have hK : ∀ z, (K z : E) = e.symm (K' z) := fun z ↦ by simp [hK']
  exact le_antisymm
    (le_topologicalSliceGenus_iff.2 fun S ↦ by
      simpa using topologicalSliceGenus_le_genus (S.mapLinearIsometryEquiv e hK'))
    (le_topologicalSliceGenus_iff.2 fun S ↦ by
      simpa using topologicalSliceGenus_le_genus (S.mapLinearIsometryEquiv e.symm hK))

/-- **Topologically slice knots have topological slice genus `0`.** -/
theorem IsTopologicallySlice.topologicalSliceGenus_eq_zero (h : IsTopologicallySlice K) :
    topologicalSliceGenus K = 0 := by
  obtain ⟨Φ, hΦ⟩ := h.elim
  exact nonpos_iff_eq_zero.1 <| by
    simpa using topologicalSliceGenus_le_genus hΦ.toTopologicalSliceSurface

/-- **The unknot has topological slice genus `0`.** -/
@[simp]
theorem topologicalSliceGenus_unknot : topologicalSliceGenus unknot = 0 :=
  isTopologicallySlice_unknot.topologicalSliceGenus_eq_zero

end TauCeti
