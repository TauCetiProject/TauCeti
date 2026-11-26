/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.DualHull
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Weyl
-- Proof-only: root-plane decompositions over a maximal torus, and density of the regular
-- elements of `t` by the Baire property of locally compact spaces.
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.Geometry.Lie.Subgroup.Torus.Root.Plane
import TauCeti.Topology.Algebra.Module.Baire

/-!
# Projected coadjoint orbits lie in the convex hull of a projected Weyl orbit

Let `T` be a maximal torus of a compact Lie group `G`, with Lie algebra `𝔱` and Weyl group
`W = N(T) / T` acting on `𝔱` by `Subgroup.weylAdjointRepresentation`. Let `B` be an `Ad`-invariant
inner product on `𝔤 = GroupLieAlgebra I G`, let `e : LeftInvariantDerivation I G ≃ 𝔤` be
evaluation at the identity, and let `t = e(𝔱) ⊆ 𝔤`. For `μ ∈ 𝔱` the covector `ν = B (e μ)` is
fixed by `T`, and restricting covectors to `t` is the projection `pr : 𝔤* → t*`. This file proves
one half of **Kostant's convexity theorem**,

`pr (G · ν) ⊆ conv (pr (W · ν))`,

that is, for every `g ∈ G` the restriction of `Ad*_g ν` to `t` is a convex combination of the
restrictions of the covectors `B (e (w μ))`, `w ∈ W`
(`TauCeti.Lie.domRestrict_coadjointRepresentation_mem_convexHull`). Since `W · ν ⊆ G · ν`, the
two sets have the same convex hull
(`TauCeti.Lie.convexHull_range_domRestrict_coadjointRepresentation`). Kostant's convexity theorem
says moreover that for connected `G` the projection `pr (G · ν)` is itself convex, hence equal to
`conv (pr (W · ν))`; that reverse inclusion is not proved here.

The argument is the one for torus moment maps
(`TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`), on the coadjoint
orbit `O = G ⧸ G_ν`. The Lie algebra `t` is a maximal abelian subspace of `𝔤`, so it carries a
root-plane decomposition `𝔤 = t + Σ F_i` with roots `α_i ∈ t*`, and an element of `t` at which no
root vanishes (`TauCeti.Lie.IsMaximalTorus.exists_isRootPlaneDecomposition`). For such a regular
`X`, the height `f_X = ⟨·, X⟩` attains its maximum on the compact orbit at a critical point, and
the critical points of `f_X` are the Weyl group points `[n_w]`, whose images are `B (e (w μ))`
(`TauCeti.IsRootPlaneDecomposition.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit`).
So the maximum of a regular height is attained at a Weyl group point
(`TauCeti.IsRootPlaneDecomposition.exists_forall_orbitMap_coadjointRepresentation_apply_le`). The
regular elements are dense in `t` (`Submodule.dense_setOf_forall_notMem_of_isClosed`), and the
support-function criterion `IsCompact.mem_convexHull_image_of_dense` turns domination in these
directions into membership in the convex hull. In turn, every height `f_X` with `X ∈ t`, regular
or not, attains its maximum at a Weyl group point
(`TauCeti.Lie.exists_forall_coadjointRepresentation_apply_le`).

No connectedness of `G` is used. For `G = O(2)` and its rotation torus, the orbit of a nonzero `ν`
is `{ν, -ν} = W · ν`, whose projection is not convex: the inclusion above holds, while the convexity
theorem needs connectedness.

## Main results

* `TauCeti.IsRootPlaneDecomposition.exists_forall_orbitMap_coadjointRepresentation_apply_le`: the
  height of a regular element of `t` attains its maximum on the coadjoint orbit at a Weyl group
  point.
* `TauCeti.Lie.domRestrict_coadjointRepresentation_mem_convexHull`: the projected coadjoint orbit
  lies in the convex hull of the projected Weyl orbit, `pr (Ad*_g ν) ∈ conv (pr (W · ν))`.
* `TauCeti.Lie.convexHull_range_domRestrict_coadjointRepresentation`: the projected orbit and the
  projected Weyl orbit have the same convex hull.
* `TauCeti.Lie.exists_forall_coadjointRepresentation_apply_le`: every height `f_X`, `X ∈ t`,
  attains its maximum over the orbit at a Weyl group point.

## References

* B. Kostant, *On convexity, the Weyl group and the Iwasawa decomposition*, Ann. Sci. École Norm.
  Sup. (4) 6 (1973), 413–455.
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27.
-/

public section

noncomputable section

open Function Module Set Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {T : Subgroup G} [IsMulCommutative T] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {t : Submodule ℝ (GroupLieAlgebra I G)}

/-! ### Regular heights attain their maxima at Weyl group points -/

namespace TauCeti.IsRootPlaneDecomposition

variable {ι : Type*} {α : ι → Dual ℝ t} {F : ι → Submodule ℝ (GroupLieAlgebra I G)}
  {J : (i : ι) → End ℝ (F i)}

/-- **A regular height attains its maximum at a Weyl group point.** Let `T` be a maximal torus of a
compact Lie group, `B` an invariant form with trivial left radical, and `𝔤 = t + Σ F_i` a
root-plane decomposition over the image `t` of the Lie algebra `𝔱` of `T`. For `μ ∈ 𝔱` and `X ∈ t`
at which no root vanishes, some Weyl group element `w` satisfies `f_X(y) ≤ ⟨B (e (w μ)), X⟩` for
every point `y` of the coadjoint orbit of `B (e μ)`. -/
theorem exists_forall_orbitMap_coadjointRepresentation_apply_le [CompactSpace G] [Finite ι]
    (hD : IsRootPlaneDecomposition B t α F J) (hT : IsMaximalTorus T)
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hsep : B.SeparatingLeft)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) {X : t} (hX : ∀ i, α i X ≠ 0) :
    ∃ w : T.normalizerQuotient, ∀ y,
      (coadjointRepresentation ℝ I G).orbitMap
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) y X ≤
        B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ)) X := by
  -- On the compact orbit the height attains its maximum, at a critical point, which is a Weyl
  -- group point.
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (Module.Dual.contMDiff_orbitMap_coadjointRepresentation_apply _ (X : GroupLieAlgebra I G)
      ).continuous.continuousOn
  have hcrit : y₀ ∈ range (normalizerQuotientToCoadjointOrbit B hB μ) := by
    rw [← hD.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit hT hB hsep ht μ hX]
    exact hy₀.mem_criticalPoints BoundarylessManifold.isInteriorPoint
  obtain ⟨w, rfl⟩ := hcrit
  refine ⟨w, fun y ↦ ?_⟩
  rw [← orbitMap_normalizerQuotientToCoadjointOrbit hB μ w]
  exact hy₀ (mem_univ y)

end TauCeti.IsRootPlaneDecomposition

/-! ### The projected orbit lies in the convex hull of the projected Weyl orbit -/

namespace TauCeti.Lie

/-- **The projected coadjoint orbit lies in the convex hull of the projected Weyl orbit.** This is
one half of Kostant's convexity theorem. Let `T` be a maximal torus of a compact Lie group `G`, `B`
an `Ad`-invariant inner product on `𝔤`, and `t` the image of the Lie algebra `𝔱` of `T` under the
evaluation `e` at the identity. For `μ ∈ 𝔱` and `g ∈ G`, the restriction to `t` of `Ad*_g ν`,
`ν = B (e μ)`, lies in the convex hull of the restrictions to `t` of the covectors `B (e (w μ))`
for `w` in the Weyl group: `pr (G · ν) ⊆ conv (pr (W · ν))`. -/
theorem domRestrict_coadjointRepresentation_mem_convexHull [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hBs : B.IsSymm) (hpos : ∀ a, a ≠ 0 → 0 < B a a)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (g : G) :
    (coadjointRepresentation ℝ I G g
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))).domRestrict t ∈
      convexHull ℝ (range fun w : T.normalizerQuotient ↦
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint
            (T.weylAdjointRepresentation (I := I) w μ))).domRestrict t) := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsep : B.SeparatingLeft := fun a ha ↦ by
    by_contra h
    exact (hpos a h).ne' (ha a)
  obtain ⟨r, α, F, J, hD, -, X₀, hX₀⟩ := hT.exists_isRootPlaneDecomposition hBs hpos
    (lieInvariant_of_isInvariantForm_adjointRepresentation hB) ht
  -- The regular elements of `t`, at which no root vanishes, are dense: `t` is a finite-dimensional
  -- space, hence locally compact and Baire.
  have : LocallyCompactSpace (GroupLieAlgebra I G) := inferInstanceAs (LocallyCompactSpace E)
  have : LocallyCompactSpace t :=
    t.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hdense : Dense {X : t | ∀ k, X ∉ LinearMap.ker (α k)} :=
    Submodule.dense_setOf_forall_notMem_of_isClosed _
      (fun k ↦ (LinearMap.ker (α k)).isClosed_of_finiteDimensional)
      fun k hk ↦ hX₀ k (by rw [← LinearMap.mem_ker, hk]; trivial)
  -- Apply the support-function criterion on the finite set of Weyl group points of the orbit.
  have hfin := hD.finite_criticalPoints_orbitMap_coadjointRepresentation hT hB hsep ht μ hX₀
  rw [hD.criticalPoints_eq_range_normalizerQuotientToCoadjointOrbit hT hB hsep ht μ hX₀] at hfin
  have hmem := hfin.isCompact.mem_convexHull_image_of_dense
    (ν := fun y ↦ ((coadjointRepresentation ℝ I G).orbitMap _ y).domRestrict t)
    (p := ((coadjointRepresentation ℝ I G).orbitMap _ (g : G ⧸ _)).domRestrict t)
    (fun X ↦ (Module.Dual.contMDiff_orbitMap_coadjointRepresentation_apply _
      (X : GroupLieAlgebra I G)).continuous.continuousOn) hdense fun X hX ↦ by
      obtain ⟨w, hw⟩ := hD.exists_forall_orbitMap_coadjointRepresentation_apply_le hT hB hsep ht μ
        fun k ↦ by simpa using hX k
      refine ⟨_, mem_range_self w, ?_⟩
      rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply,
        orbitMap_normalizerQuotientToCoadjointOrbit]
      exact hw _
  rw [← range_comp] at hmem
  simpa only [Representation.orbitMap_mk, comp_def,
    orbitMap_normalizerQuotientToCoadjointOrbit] using hmem

/-- A Weyl group point of the coadjoint orbit of `ν = B (e μ)` is a point of the orbit: for `w` the
class of `n ∈ N(T)`, `B (e (w μ)) = Ad*_n ν`. -/
private theorem exists_coadjointRepresentation_eq_bilinForm_weylAdjointRepresentation
    (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (w : T.normalizerQuotient) :
    ∃ g : G, coadjointRepresentation ℝ I G g
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ)) =
      B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ)) := by
  induction w using QuotientGroup.induction_on with | H n =>
  refine ⟨n, ?_⟩
  rw [← orbitMap_normalizerQuotientToCoadjointOrbit hB μ, normalizerQuotientToCoadjointOrbit_mk,
    Representation.orbitMap_mk]

/-- **The projected coadjoint orbit and the projected Weyl orbit have the same convex hull.** Let
`T` be a maximal torus of a compact Lie group `G`, `B` an `Ad`-invariant inner product on `𝔤`, and
`t` the image of the Lie algebra `𝔱` of `T`. For `μ ∈ 𝔱` and `ν = B (e μ)`, the restrictions to
`t` of the covectors `Ad*_g ν`, `g ∈ G`, and of the covectors `B (e (w μ))`, `w` in the Weyl
group, have the same convex hull: `conv (pr (G · ν)) = conv (pr (W · ν))`. -/
theorem convexHull_range_domRestrict_coadjointRepresentation [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hBs : B.IsSymm) (hpos : ∀ a, a ≠ 0 → 0 < B a a)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    convexHull ℝ (range fun g : G ↦ (coadjointRepresentation ℝ I G g
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint μ))).domRestrict t) =
      convexHull ℝ (range fun w : T.normalizerQuotient ↦
        (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint
            (T.weylAdjointRepresentation (I := I) w μ))).domRestrict t) := by
  refine (convexHull_min ?_ (convex_convexHull ℝ _)).antisymm (convexHull_mono ?_)
  · rintro _ ⟨g, rfl⟩
    exact domRestrict_coadjointRepresentation_mem_convexHull hT hB hBs hpos ht μ g
  · rintro _ ⟨w, rfl⟩
    obtain ⟨g, hg⟩ := exists_coadjointRepresentation_eq_bilinForm_weylAdjointRepresentation hB μ w
    exact ⟨g, congrArg (LinearMap.domRestrict · t) hg⟩

/-- **Heights attain their maxima at Weyl group points.** Let `T` be a maximal torus of a compact
Lie group `G`, `B` an `Ad`-invariant inner product on `𝔤`, and `t` the image of the Lie algebra `𝔱`
of `T`. For `μ ∈ 𝔱`, `ν = B (e μ)` and every `X ∈ t`, regular or not, some Weyl group element `w`
satisfies `(Ad*_g ν) X ≤ ⟨B (e (w μ)), X⟩` for every `g ∈ G`. -/
theorem exists_forall_coadjointRepresentation_apply_le [CompactSpace G]
    (hT : IsMaximalTorus T) (hB : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B)
    (hBs : B.IsSymm) (hpos : ∀ a, a ≠ 0 → 0 < B a a)
    (ht : t = (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.map
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
        BoundarylessManifold.isInteriorPoint).toLinearEquiv.toLinearMap)
    (μ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) (X : t) :
    ∃ w : T.normalizerQuotient, ∀ g : G,
      coadjointRepresentation ℝ I G g
          (B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
            BoundarylessManifold.isInteriorPoint μ)) X ≤
        B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ)) X := by
  have := hT.finite_normalizerQuotient (I := I)
  -- Take `w₀` maximizing `⟨B (e (w μ)), X⟩` over the finite Weyl group; evaluation at `X` is
  -- linear, so its value on the convex hull of the projected Weyl orbit is at most this maximum.
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : T.normalizerQuotient ↦
    B (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint (T.weylAdjointRepresentation (I := I) w μ)) X
  refine ⟨w₀, fun g ↦ ?_⟩
  obtain ⟨_, ⟨w, rfl⟩, hle⟩ :=
    ((Module.Dual.eval ℝ t X).convexOn convex_univ).exists_ge_of_mem_convexHull (subset_univ _)
      (domRestrict_coadjointRepresentation_mem_convexHull hT hB hBs hpos ht μ g)
  exact hle.trans (hw₀ w)

end TauCeti.Lie
