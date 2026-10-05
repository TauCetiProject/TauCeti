/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Geometry.Sphere.Circle
public import TauCeti.KnotTheory.SmoothCircle

/-!
# The knot group

The **knot group** of a knot `K : S¹ → M` is the fundamental group of its complement
`M \ K(S¹)` (`TauCeti.SmoothCircleEmbedding.KnotGroup`). It is the classical invariant through
which the Alexander module of a knot in `S³` is read: the commutator subgroup `π'` of the knot group
is the kernel of the abelianization `π → H₁(S³ \ K) ≅ ℤ`, so it is the fundamental group of the
infinite cyclic cover `X∞` of the complement, and the Alexander module `H₁(X∞)` is `π' / π''`.

A knot **has perfect commutator subgroup**
(`TauCeti.SmoothCircleEmbedding.HasPerfectCommutatorSubgroup`) when `π'' = π'` at every basepoint
of the complement, that is, when the Alexander module vanishes. For a knot in `S³`, or more
generally in a homology `3`-sphere, the Alexander module is presented by the square matrix
`tV - Vᵀ` of a Seifert matrix `V`, so it vanishes exactly when its order ideal is the unit ideal:
the condition is equivalent to the Alexander polynomial being `1` (Crowell; see Freedman–Quinn,
Theorem 11.7B). This is the hypothesis of Freedman's theorem that such knots are topologically
slice.

The knot group is invariant under ambient diffeomorphisms
(`TauCeti.SmoothCircleEmbedding.knotGroupTransDiffeomorphMulEquiv`), and the condition depends only
on the image of the knot, so it is unchanged by reparametrization. For a great circle of the
three-sphere the complement deformation retracts onto the complementary great circle
(`TauCeti.sphereDiffHomotopyEquiv`), so the knot group is infinite cyclic
(`TauCeti.SmoothCircleEmbedding.knotGroupGreatCircleMulEquiv`). In particular the unknot has abelian
knot group, hence trivial commutator subgroup, and it has perfect commutator subgroup.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.KnotGroup`: the fundamental group of the complement of a knot.
* `TauCeti.SmoothCircleEmbedding.HasPerfectCommutatorSubgroup`: the commutator subgroup of the
  knot group is perfect at every basepoint.

## Main results

* `TauCeti.SmoothCircleEmbedding.knotGroupTransDiffeomorphMulEquiv`: an ambient diffeomorphism
  induces an isomorphism of knot groups.
* `TauCeti.SmoothCircleEmbedding.hasPerfectCommutatorSubgroup_transDiffeomorph_iff`,
  `TauCeti.SmoothCircleEmbedding.hasPerfectCommutatorSubgroup_rotate_iff` and
  `TauCeti.SmoothCircleEmbedding.hasPerfectCommutatorSubgroup_reverse_iff`: the condition is
  invariant under ambient diffeomorphisms and reparametrizations.
* `TauCeti.SmoothCircleEmbedding.knotGroupGreatCircleMulEquiv`: the knot group of a great circle in
  the three-sphere is infinite cyclic.
* `TauCeti.SmoothCircleEmbedding.hasPerfectCommutatorSubgroup_greatCircle` and
  `TauCeti.hasPerfectCommutatorSubgroup_unknot`: great circles, and in particular the unknot, have
  perfect commutator subgroup.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 3 (knot groups) and Chapter 7
  (the infinite cyclic cover and the Alexander module).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (the Alexander module and its presentation by `tV - Vᵀ`).
* M. Freedman and F. Quinn, *Topology of 4-Manifolds*, Princeton (1990), Theorem 11.7B, for the
  equivalence of a perfect commutator subgroup with Alexander polynomial one, attributed there to
  Crowell.
-/

public section

noncomputable section

open scoped EuclideanSpace

namespace TauCeti

namespace SmoothCircleEmbedding

open Set Metric Module
open scoped Manifold ContDiff ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The **knot group** of a smooth circle embedding `K : S¹ → M` at a basepoint `x` of the
complement: the fundamental group of `M \ K(S¹)` at `x`. -/
abbrev KnotGroup (K : SmoothCircleEmbedding I M) (x : ((range K)ᶜ : Set M)) : Type _ :=
  FundamentalGroup ((range K)ᶜ : Set M) x

/-- A knot `K` **has perfect commutator subgroup** if at every basepoint of its complement the
commutator subgroup `π' = [π, π]` of the knot group `π` is perfect, `[π', π'] = π'`. Equivalently,
the abelian group `π' / [π', π']`, the Alexander module of a knot in `S³`, is trivial. For a knot in
a homology `3`-sphere, `π'` is the kernel of the abelianization `π → ℤ`, and this condition is
equivalent to the knot having Alexander polynomial `1` (Freedman–Quinn, Theorem 11.7B, after
Crowell). -/
def HasPerfectCommutatorSubgroup (K : SmoothCircleEmbedding I M) : Prop :=
  ∀ x : ((range K)ᶜ : Set M), Group.IsPerfect (commutator (K.KnotGroup x))

/-- A knot has perfect commutator subgroup exactly when, at every basepoint of its complement, the
commutator subgroup of its knot group is perfect. -/
theorem hasPerfectCommutatorSubgroup_iff (K : SmoothCircleEmbedding I M) :
    K.HasPerfectCommutatorSubgroup ↔
      ∀ x : ((range K)ᶜ : Set M), Group.IsPerfect (commutator (K.KnotGroup x)) :=
  Iff.rfl

/-- Whether a knot has perfect commutator subgroup depends only on its image. -/
theorem hasPerfectCommutatorSubgroup_congr_range {K K' : SmoothCircleEmbedding I M}
    (h : range K = range K') :
    K.HasPerfectCommutatorSubgroup ↔ K'.HasPerfectCommutatorSubgroup := by
  -- The condition only involves the complement of the image, so substitute the image.
  have key : ∀ s t : Set M, s = t →
      ((∀ x : (sᶜ : Set M), Group.IsPerfect (commutator (FundamentalGroup (sᶜ : Set M) x))) ↔
        ∀ x : (tᶜ : Set M), Group.IsPerfect (commutator (FundamentalGroup (tᶜ : Set M) x))) := by
    rintro s t rfl
    rfl
  exact key _ _ h

/-- Reparametrizing a knot by a rotation of the circle does not change whether it has perfect
commutator subgroup. -/
@[simp]
theorem hasPerfectCommutatorSubgroup_rotate_iff (K : SmoothCircleEmbedding I M) (a : Circle) :
    (K.rotate a).HasPerfectCommutatorSubgroup ↔ K.HasPerfectCommutatorSubgroup :=
  hasPerfectCommutatorSubgroup_congr_range (range_rotate K a)

/-- Reversing the orientation of a knot does not change whether it has perfect commutator
subgroup. -/
@[simp]
theorem hasPerfectCommutatorSubgroup_reverse_iff (K : SmoothCircleEmbedding I M) :
    K.reverse.HasPerfectCommutatorSubgroup ↔ K.HasPerfectCommutatorSubgroup :=
  hasPerfectCommutatorSubgroup_congr_range (range_reverse K)

section Ambient

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  (K : SmoothCircleEmbedding I M) (e : M ≃ₘ⟮I, I⟯ P)

/-- An ambient diffeomorphism `e` carries the complement of `K` homeomorphically onto the
complement of `e ∘ K`. -/
def complHomeomorphTransDiffeomorph :
    ((range K)ᶜ : Set M) ≃ₜ ((range (SmoothEmbedding.transDiffeomorph K e))ᶜ : Set P) :=
  e.toHomeomorph.subtype fun x => by
    rw [mem_compl_iff, mem_compl_iff, SmoothEmbedding.range_transDiffeomorph]
    exact (e.injective.mem_set_image).not.symm

/-- The homeomorphism of complements induced by an ambient diffeomorphism is that diffeomorphism. -/
@[simp]
theorem coe_complHomeomorphTransDiffeomorph_apply (x : ((range K)ᶜ : Set M)) :
    (complHomeomorphTransDiffeomorph K e x : P) = e x :=
  (rfl)

/-- **The knot group is invariant under ambient diffeomorphisms.** A diffeomorphism `e` of the
ambient manifold induces an isomorphism from the knot group of `K` at `x` to that of `e ∘ K` at
`e x`. -/
def knotGroupTransDiffeomorphMulEquiv (x : ((range K)ᶜ : Set M)) :
    K.KnotGroup x ≃*
      KnotGroup (SmoothEmbedding.transDiffeomorph K e) (complHomeomorphTransDiffeomorph K e x) :=
  FundamentalGroup.homeomorphMulEquiv (complHomeomorphTransDiffeomorph K e) x

/-- Transporting a knot by an ambient diffeomorphism does not change whether it has perfect
commutator subgroup. -/
@[simp]
theorem hasPerfectCommutatorSubgroup_transDiffeomorph_iff :
    HasPerfectCommutatorSubgroup (SmoothEmbedding.transDiffeomorph K e) ↔
      K.HasPerfectCommutatorSubgroup := by
  -- The isomorphism of knot groups carries the commutator subgroup onto the commutator subgroup.
  refine ⟨fun h x => ?_, fun h y => ?_⟩
  · have := h (complHomeomorphTransDiffeomorph K e x)
    have := Group.IsPerfect.map (H := commutator _)
      (knotGroupTransDiffeomorphMulEquiv K e x).symm.toMonoidHom
    rwa [← derivedSeries_one, map_derivedSeries_eq (MulEquiv.surjective _), derivedSeries_one]
      at this
  · obtain ⟨x, rfl⟩ := (complHomeomorphTransDiffeomorph K e).surjective y
    have := h x
    have := Group.IsPerfect.map (H := commutator _)
      (knotGroupTransDiffeomorphMulEquiv K e x).toMonoidHom
    rwa [← derivedSeries_one, map_derivedSeries_eq (MulEquiv.surjective _), derivedSeries_one]
      at this

end Ambient

/-! ### Great circles in the three-sphere -/

section GreatCircle

attribute [local instance] finrank_real_complex_fact'

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = 3 + 1)]
  (ι : ℂ →ₗᵢ[ℝ] F)

/-- The complement of a great circle `ι S¹` in the unit sphere consists of the unit vectors
outside the plane `ι ℂ`. -/
theorem compl_range_greatCircle :
    ((range (greatCircle (n := 3) ι))ᶜ : Set (sphere (0 : F) 1)) =
      ({x | (x : F) ∉ LinearMap.range ι.toLinearMap} : Set (sphere (0 : F) 1)) := by
  ext x
  rw [mem_compl_iff, mem_ofPred_eq, not_iff_not, LinearMap.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa using congrArg Subtype.val hz⟩
  · rintro ⟨w, hw⟩
    have hw' : ι w = x := hw
    have hn : ‖w‖ = 1 := by
      rw [← ι.norm_map, hw']
      exact norm_eq_of_mem_sphere x
    exact ⟨⟨w, by simp [Submonoid.unitSphere, hn]⟩,
      Subtype.ext ((coe_greatCircle_apply ι _).trans hw')⟩

/-- The complement of a great circle `ι S¹` in the three-sphere is homotopy equivalent to a circle:
it deformation retracts onto the complementary great circle, the unit sphere of `(ι ℂ)ᗮ`. -/
def complRangeGreatCircleHomotopyEquiv :
    ((range (greatCircle (n := 3) ι))ᶜ : Set (sphere (0 : F) 1)) ≃ₕ Circle :=
  have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ 3
  (Homeomorph.setCongr (compl_range_greatCircle ι)).toHomotopyEquiv.trans
    ((sphereDiffHomotopyEquiv (LinearMap.range ι.toLinearMap)).trans
      ((LinearIsometryEquiv.unitSphereIsometryEquiv
        ((stdOrthonormalBasis ℝ (LinearMap.range ι.toLinearMap)ᗮ).reindex
          (finCongr (Submodule.finrank_add_finrank_orthogonal' (by
            rw [LinearMap.finrank_range_of_inj ι.injective, Complex.finrank_real_complex,
              (Fact.out : finrank ℝ F = 3 + 1)])))).repr).toHomeomorph.trans
        EuclideanSpace.sphereHomeomorphCircle).toHomotopyEquiv)

/-- **The knot group of a great circle in the three-sphere is infinite cyclic.** For a linear
isometric copy `ι ℂ` of the plane in a four-dimensional real inner product space, the fundamental
group of the complement of the great circle `ι S¹` in the unit sphere is `ℤ` at every basepoint. -/
def knotGroupGreatCircleMulEquiv
    (x : ((range (greatCircle (n := 3) ι))ᶜ : Set (sphere (0 : F) 1))) :
    (greatCircle (n := 3) ι).KnotGroup x ≃* Multiplicative ℤ :=
  ((complRangeGreatCircleHomotopyEquiv ι).fundamentalGroupMulEquiv x).trans
    (Circle.fundamentalGroupMulEquiv _)

/-- The knot group of a great circle in the three-sphere is abelian. -/
instance isMulCommutative_knotGroup_greatCircle
    (x : ((range (greatCircle (n := 3) ι))ᶜ : Set (sphere (0 : F) 1))) :
    IsMulCommutative ((greatCircle (n := 3) ι).KnotGroup x) :=
  ⟨⟨fun a b => (knotGroupGreatCircleMulEquiv ι x).injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

/-- A great circle in the three-sphere has perfect commutator subgroup: its knot group is abelian,
so the commutator subgroup is trivial. -/
theorem hasPerfectCommutatorSubgroup_greatCircle :
    (greatCircle (n := 3) ι).HasPerfectCommutatorSubgroup := fun _ =>
  Subgroup.isPerfect_iff.2 (by rw [commutator_eq_bot, Subgroup.commutator_bot_left])

end GreatCircle

end SmoothCircleEmbedding

/-- **The unknot has perfect commutator subgroup**: its knot group is infinite cyclic. -/
theorem hasPerfectCommutatorSubgroup_unknot : unknot.HasPerfectCommutatorSubgroup := by
  have h : unknot = SmoothCircleEmbedding.greatCircle complexToEuclideanFour :=
    SmoothEmbedding.ext fun z => Subtype.ext (by simp)
  rw [h]
  exact SmoothCircleEmbedding.hasPerfectCommutatorSubgroup_greatCircle complexToEuclideanFour

end TauCeti
