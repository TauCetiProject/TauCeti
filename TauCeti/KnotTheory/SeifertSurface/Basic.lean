/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Hemisphere
public import TauCeti.Geometry.Manifold.Orientation.ClosedBall
public import TauCeti.KnotTheory.SmoothCircle
import Mathlib.Analysis.Convex.Contractible

/-!
# Seifert surfaces and the Seifert genus of a knot

A **Seifert surface** for a knot `K ⊆ S³` is a compact, connected, orientable surface smoothly
embedded in `S³` whose boundary is `K`. Every knot has one (Seifert's algorithm), and the least
genus of a Seifert surface is the **genus** `g(K)` of the knot, its Seifert genus. It vanishes
exactly for the unknot, it bounds the slice genus from above, and it is the quantity in Giffen's
conjecture on the `0`-surgery `S³₀(K)` (Kirby's problem 1.41 (B)), answered by Gabai.

As for slice surfaces (`TauCeti.SmoothSliceSurface`), the knot is a smooth circle embedding
`K : S¹ → Sⁿ` into the unit sphere of an `(n + 1)`-dimensional real inner product space `E`, so
that `S³ ⊆ ℝ⁴` is the case `n = 3`. A **Seifert surface** for `K` (`TauCeti.SeifertSurface K`)
bundles

* a compact, connected, orientable smooth surface `S` with boundary, modelled on the half-plane
  `EuclideanHalfSpace 2` (orientability is `TauCeti.Orientable`);
* a smooth embedding `Φ : S → Sⁿ` of manifolds with boundary carrying the boundary of `S` onto the
  image of `K`.

The carrier of the surface is a type with instances; it is bundled only because the Seifert genus
is a minimum over all such surfaces. Since `Φ` is an embedding, the boundary of `S` is homeomorphic
to the image of `K`, a circle, so `S` has exactly one boundary component. Only the image of `K`
enters, so the Seifert genus does not depend on the parametrization or orientation of the knot.

The **genus** of a Seifert surface (`TauCeti.SeifertSurface.genus`) is read off its rational
singular homology, as for slice surfaces: a compact, connected, orientable surface of genus `g`
with one boundary circle has `H₁(S; ℚ) ≅ ℚ²ᵍ`, so its genus is half the dimension of `H₁(S; ℚ)`.
The Seifert genus (`TauCeti.seifertGenus K`) is the infimum of the genera of the Seifert surfaces of
`K`, valued in `ℕ∞` so that it is `⊤` rather than `0` should `K` have no Seifert surface at all.
(Seifert's algorithm shows that it is finite for `n = 3`; that existence theorem is not proved
here.) An ambient diffeomorphism of the sphere carries Seifert surfaces of `K` to Seifert surfaces
of its image, so the Seifert genus is invariant under ambient diffeomorphisms
(`TauCeti.seifertGenus_transDiffeomorph`), and in particular under ambient isotopy.

For a great circle `ι S¹` and a unit vector `v` orthogonal to `ι ℂ`, the hemisphere of the great
two-sphere through `ι S¹` and `-v` is a Seifert disc, the image of the closed unit disc of `ℂ`
under inverse stereographic projection from `v` of `w ↦ 2 ι w`
(`LinearIsometry.closedBallHemisphereMap`). The disc is contractible, so it has genus `0`, and
great circles in spheres of dimension at least two, in particular the unknot, have Seifert genus
`0` (`TauCeti.seifertGenus_greatCircle`, `TauCeti.seifertGenus_unknot`). The converse, that a knot
of Seifert genus `0` is the unknot, needs the classification of compact surfaces and the
Schoenflies theorem, and is not proved here.

## Main definitions

* `TauCeti.SeifertSurface K`: a smooth Seifert surface for `K`.
* `TauCeti.SeifertSurface.genus`: the genus `dim H₁(S; ℚ) / 2` of a Seifert surface
  (`TauCeti.surfaceGenus`).
* `TauCeti.seifertGenus K`: the Seifert genus of `K`, in `ℕ∞`.
* `TauCeti.SeifertSurface.congrRange`, `TauCeti.SeifertSurface.transDiffeomorph`: a Seifert surface
  for a knot with the same image, and for the image of the knot under an ambient diffeomorphism.
* `TauCeti.SeifertSurface.hemisphere`: the hemisphere Seifert disc of a great circle.

## Main results

* `TauCeti.seifertGenus_le_genus`, `TauCeti.le_seifertGenus_iff`: the Seifert genus is the infimum
  of the genera of the Seifert surfaces.
* `TauCeti.seifertGenus_lt_top_iff`, `TauCeti.exists_genus_eq_seifertGenus`: it is finite exactly
  when a Seifert surface exists, and is then attained.
* `TauCeti.seifertGenus_congr_range`, `TauCeti.seifertGenus_rotate`,
  `TauCeti.seifertGenus_reverse`: the Seifert genus only depends on the image of the knot.
* `TauCeti.seifertGenus_transDiffeomorph`: it is invariant under ambient diffeomorphisms.
* `TauCeti.SeifertSurface.genus_hemisphere`: the hemisphere disc has genus `0`.
* `TauCeti.seifertGenus_greatCircle`, `TauCeti.seifertGenus_unknot`: great circles in `Sⁿ`,
  `n ≥ 2`, and in particular the unknot, have Seifert genus `0`.

## References

* H. Seifert, *Über das Geschlecht von Knoten*, Math. Ann. 110 (1935), 571–592.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 2
  (Seifert surfaces and the genus of a knot).
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 5 (Seifert surfaces).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Manifold Metric Module Set
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A **Seifert surface** for a smooth circle embedding `K : S¹ → Sⁿ` in the unit sphere of `E`: a
compact, connected, orientable smooth surface with boundary, together with a smooth embedding into
the sphere, in the sense of manifolds with boundary, which carries the boundary of the surface onto
the image of `K`. -/
structure SeifertSurface (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) where
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
  /-- The embedding of the surface into the sphere. -/
  toFun : carrier → sphere (0 : E) 1
  /-- The map is a smooth embedding of manifolds with boundary. -/
  isSmoothEmbedding : IsSmoothEmbedding (𝓡∂ 2) (𝓡 n) ∞ toFun
  /-- The boundary of the surface is carried onto the image of `K`. -/
  image_boundary : toFun '' (𝓡∂ 2).boundary carrier = range K

namespace SeifertSurface

attribute [instance] topologicalSpace chartedSpace isManifold compactSpace connectedSpace orientable

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The **genus** of a Seifert surface: half the dimension of its first rational homology
(`TauCeti.surfaceGenus`). A compact, connected, orientable surface of genus `g` with one boundary
circle has `H₁(S; ℚ) ≅ ℚ²ᵍ`, so this is the genus of `S`: since `S.toFun` is an embedding, the
boundary of `S` is homeomorphic to the image of `K`, a single circle. -/
def genus (S : SeifertSurface K) : ℕ :=
  surfaceGenus S.carrier

/-- The genus of a Seifert surface is the genus `TauCeti.surfaceGenus` of its carrier. -/
theorem genus_def (S : SeifertSurface K) : S.genus = surfaceGenus S.carrier :=
  (rfl)

/-- A Seifert surface for `K` is a Seifert surface for every knot `K'` with the same image. -/
@[expose] def congrRange (S : SeifertSurface K) (h : range K = range K') : SeifertSurface K' where
  carrier := S.carrier
  toFun := S.toFun
  isSmoothEmbedding := S.isSmoothEmbedding
  image_boundary := h ▸ S.image_boundary

/-- Transporting a Seifert surface to a knot with the same image keeps its genus. -/
@[simp]
theorem genus_congrRange (S : SeifertSurface K) (h : range K = range K') :
    (S.congrRange h).genus = S.genus :=
  (rfl)

/-- Transport of a Seifert surface for `K` along a diffeomorphism `e` of the sphere: the same
surface, embedded by `e ∘ S.toFun`, is a Seifert surface for the transported knot `e ∘ K`. -/
@[expose] def transDiffeomorph (S : SeifertSurface K)
    (e : sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1) :
    SeifertSurface (K.transDiffeomorph e) where
  carrier := S.carrier
  toFun := e ∘ S.toFun
  isSmoothEmbedding := isSmoothEmbedding_diffeomorph_comp S.isSmoothEmbedding e
  image_boundary := by
    rw [image_comp, S.image_boundary, SmoothEmbedding.range_transDiffeomorph]

/-- Transporting a Seifert surface along an ambient diffeomorphism keeps its genus. -/
@[simp]
theorem genus_transDiffeomorph (S : SeifertSurface K)
    (e : sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1) :
    (S.transDiffeomorph e).genus = S.genus :=
  (rfl)

end SeifertSurface

/-- The **Seifert genus** `g(K)` of a smooth circle embedding `K : S¹ → Sⁿ`: the least genus of a
Seifert surface for `K`, or `⊤` if there is none. -/
def seifertGenus (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  ⨅ S : SeifertSurface K, (S.genus : ℕ∞)

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The Seifert genus is the infimum of the genera of all Seifert surfaces. -/
theorem seifertGenus_def : seifertGenus K = ⨅ S : SeifertSurface K, (S.genus : ℕ∞) :=
  (rfl)

/-- The Seifert genus is at most the genus of any Seifert surface. -/
theorem seifertGenus_le_genus (S : SeifertSurface K) : seifertGenus K ≤ S.genus :=
  iInf_le _ S

/-- A lower bound for the Seifert genus is a lower bound for the genus of every Seifert surface. -/
@[simp]
theorem le_seifertGenus_iff {m : ℕ∞} :
    m ≤ seifertGenus K ↔ ∀ S : SeifertSurface K, m ≤ S.genus :=
  le_iInf_iff

/-- The Seifert genus is attained when a Seifert surface exists. -/
theorem exists_genus_eq_seifertGenus [Nonempty (SeifertSurface K)] :
    ∃ S : SeifertSurface K, (S.genus : ℕ∞) = seifertGenus K :=
  ENat.exists_eq_iInf _

/-- The Seifert genus is finite exactly when a Seifert surface exists. -/
@[simp]
theorem seifertGenus_lt_top_iff : seifertGenus K < ⊤ ↔ Nonempty (SeifertSurface K) :=
  ENat.iInf_natCast_lt_top

/-- Two knots with the same image have the same Seifert genus. -/
theorem seifertGenus_congr_range (h : range K = range K') : seifertGenus K = seifertGenus K' :=
  le_antisymm
    (le_seifertGenus_iff.2 fun S ↦ by simpa using seifertGenus_le_genus (S.congrRange h.symm))
    (le_seifertGenus_iff.2 fun S ↦ by simpa using seifertGenus_le_genus (S.congrRange h))

/-- The Seifert genus does not depend on the rotation of the parametrization. -/
@[simp]
theorem seifertGenus_rotate (a : Circle) : seifertGenus (K.rotate a) = seifertGenus K :=
  seifertGenus_congr_range (K.range_rotate a)

/-- The Seifert genus does not depend on the orientation of the knot. -/
@[simp]
theorem seifertGenus_reverse : seifertGenus K.reverse = seifertGenus K :=
  seifertGenus_congr_range K.range_reverse

/-- **The Seifert genus is invariant under ambient diffeomorphisms** of the sphere. -/
@[simp]
theorem seifertGenus_transDiffeomorph (e : sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1) :
    seifertGenus (K.transDiffeomorph e) = seifertGenus K := by
  have hK : (K.transDiffeomorph e).transDiffeomorph e.symm = K := by
    apply SmoothEmbedding.ext
    intro z
    simp
  refine le_antisymm (le_seifertGenus_iff.2 fun S ↦ ?_) (le_seifertGenus_iff.2 fun S ↦ ?_)
  · simpa using seifertGenus_le_genus (S.transDiffeomorph e)
  · simpa [hK] using seifertGenus_le_genus (S.transDiffeomorph e.symm)

/-! ### The hemisphere disc of a great circle -/

namespace SeifertSurface

variable {ι : ℂ →ₗᵢ[ℝ] E} {v : sphere (0 : E) 1}

/-- The **hemisphere Seifert disc** of the great circle `ι S¹`, for a unit vector `v` orthogonal
to `ι ℂ`: the closed unit disc of `ℂ`, embedded in the sphere as the hemisphere centred at `-v` of
the great two-sphere through `ι S¹` and `v`, by inverse stereographic projection from `v` of
`w ↦ 2 ι w` (`LinearIsometry.closedBallHemisphereMap`). -/
@[expose] def hemisphere (hv : ∀ z, ⟪(v : E), ι z⟫_ℝ = 0) :
    SeifertSurface (SmoothCircleEmbedding.greatCircle (n := n) ι) where
  carrier := closedBall (0 : ℂ) 1
  compactSpace := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  connectedSpace := isConnected_iff_connectedSpace.1
    ((convex_closedBall 0 1).isConnected (nonempty_closedBall.2 zero_le_one))
  orientable := orientable_closedBall
  toFun := ι.closedBallHemisphereMap v hv
  isSmoothEmbedding := ι.isSmoothEmbedding_closedBallHemisphereMap hv
  image_boundary := by
    ext p
    simp only [boundary_closedBall, mem_image, mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : ‖(x : ℂ)‖ = 1 := by simpa using hx
      refine ⟨⟨x, mem_sphere_zero_iff_norm.2 hx1⟩, Subtype.ext ?_⟩
      exact (SmoothCircleEmbedding.coe_greatCircle_apply ι _).trans
        (ι.closedBallHemisphereMap_apply_of_norm_eq_one hv hx1).symm
    · rintro ⟨z, rfl⟩
      refine ⟨⟨z, by simp⟩, by simp, Subtype.ext ?_⟩
      rw [SmoothCircleEmbedding.coe_greatCircle_apply,
        ι.closedBallHemisphereMap_apply_of_norm_eq_one hv (by simp)]

/-- **The hemisphere disc has genus `0`**: the disc is contractible, so its first homology
vanishes. -/
@[simp]
theorem genus_hemisphere (hv : ∀ z, ⟪(v : E), ι z⟫_ℝ = 0) :
    (hemisphere (n := n) hv).genus = 0 := by
  have : ContractibleSpace (hemisphere (n := n) hv).carrier :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace (nonempty_closedBall.2 zero_le_one)
  rw [genus_def, surfaceGenus_eq_zero_of_contractibleSpace]

end SeifertSurface

/-- **Great circles have Seifert genus `0`** in spheres of dimension at least two: they bound a
hemisphere disc. -/
@[simp]
theorem seifertGenus_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) (hn : 2 ≤ n) :
    seifertGenus (SmoothCircleEmbedding.greatCircle (n := n) ι) = 0 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨v, hv⟩ := ι.exists_mem_sphere_inner_eq_zero <| by
    rw [Complex.finrank_real_complex, Fact.out (p := finrank ℝ E = n + 1)]
    omega
  exact nonpos_iff_eq_zero.1 <| by
    simpa using seifertGenus_le_genus (SeifertSurface.hemisphere (n := n) hv)

attribute [local instance] finrank_euclideanSpace_fin_succ_fact in
/-- **The unknot has Seifert genus `0`.** -/
@[simp]
theorem seifertGenus_unknot : seifertGenus unknot = 0 := by
  rw [unknot_eq_greatCircle]
  exact seifertGenus_greatCircle _ (by norm_num)

end TauCeti
