/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Chart.Transition

/-!
# Triple overlaps of the standard charts of the Grassmannian

Let `M` be a module over a commutative ring `R` and let `x y z : Fin k → M`. Inside the chart of
`G(k, M; R)` at `x`, the overlap with the chart at `y` is the basic open set of the determinant
`transitionDet R x y`, with coordinate ring `OverlapAlgebra R x y`
(`TauCeti.RingTheory.Grassmannian.Chart.Transition`). The triple overlap with the charts at `y`
and at `z` is the basic open set of `transitionDet R x z` inside it: its coordinate ring
`Module.Grassmannian.TripleAlgebra R x y z` is the localization of `OverlapAlgebra R x y` away
from the image of `transitionDet R x z`. Its `R`-algebra maps to `A` are the points of
`G(k, A ⊗[R] M; A)` lying in the three charts (`Module.Grassmannian.tripleHomEquiv`).

Read in the chart at `x`, the triple overlap is the intersection of the overlaps with the charts at
`y` and at `z`. The universal point of the triple overlap lies in the charts at `x` and `z`, which
gives a map `Module.Grassmannian.TripleAlgebra.inr` from `OverlapAlgebra R x z`, and with the two
maps from `OverlapAlgebra R x y` and `OverlapAlgebra R x z`, `TripleAlgebra R x y z` is a pushout
of commutative rings over `ChartAlgebra R x` (`Module.Grassmannian.TripleAlgebra.isPushout`). Under
`Spec`, this identifies the triple overlap with the fibre product of the two overlaps over the chart
at `x`.

The three charts can be listed in any order, and the triple overlaps for the cyclic orders
`(x, y, z)` and `(y, z, x)` corepresent the same points. The **cyclic map**
`Module.Grassmannian.TripleAlgebra.cycle R x y z`, from `TripleAlgebra R y z x` to
`TripleAlgebra R x y z`, is the map compatible with the points
(`Module.Grassmannian.TripleAlgebra.tripleHomEquiv_comp_cycle`). Going round the three cyclic
orders gives the identity (`Module.Grassmannian.TripleAlgebra.cycle_cycle`), so the cyclic maps are
isomorphisms (`Module.Grassmannian.TripleAlgebra.cycleAlgEquiv`), and the cyclic map is compatible
with the transition isomorphism from the chart at `x` to the chart at `y`
(`Module.Grassmannian.TripleAlgebra.cycle_comp_inr`). These are the cocycle
conditions under which the charts glue to the Grassmannian scheme.

## Main definitions

* `Module.Grassmannian.TripleAlgebra R x y z`: the coordinate ring of the overlap of the charts at
  `x`, `y` and `z`, read in the chart at `x`.
* `Module.Grassmannian.tripleHomEquiv R x y z A`: `R`-algebra maps `TripleAlgebra R x y z → A` are
  the points over `A` lying in the three charts.
* `Module.Grassmannian.TripleAlgebra.inr R x y z`: the map
  `OverlapAlgebra R x z → TripleAlgebra R x y z`.
* `Module.Grassmannian.TripleAlgebra.cycle R x y z`: the cyclic map
  `TripleAlgebra R y z x → TripleAlgebra R x y z`.
* `Module.Grassmannian.TripleAlgebra.cycleAlgEquiv R x y z`: the cyclic map as an isomorphism.

## Main results

* `Module.Grassmannian.TripleAlgebra.isPushout`: the triple overlap is the pushout of the two
  overlaps over the chart.
* `Module.Grassmannian.TripleAlgebra.cycle_cycle`: the cocycle condition.
* `Module.Grassmannian.TripleAlgebra.cycle_comp_inr`: compatibility of the cyclic map with
  the transition isomorphism.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

open ChartAlgebra

section Triple

variable (R)

/-- The coordinate ring of the overlap of the charts at `x`, `y` and `z`, read in the chart at
`x`: the localization of `OverlapAlgebra R x y` away from the image of `transitionDet R x z`. Its
`R`-algebra maps to `A` are the points over `A` lying in the three charts
(`Module.Grassmannian.tripleHomEquiv`). -/
abbrev TripleAlgebra (x y z : Fin k → M) : Type (max u v) :=
  Localization.Away (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y) (transitionDet R x z))

variable {A : Type w} [CommRing A] [Algebra R A]

-- A point lying in the three charts is classified, in the overlap of the charts at `x` and `y`, by
-- a map sending the image of `transitionDet R x z` to a unit.
private lemma isUnit_overlapHomEquiv_symm_transitionDet (x y z : Fin k → M)
    (N : ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ∩
      chart A (fun i ↦ (1 : A) ⊗ₜ[R] z i))) :
    IsUnit ((overlapHomEquiv R x y A).symm ⟨N.1, N.2.1⟩
      (algebraMap _ _ (transitionDet R x z))) := by
  rw [overlapHomEquiv_symm_apply_algebraMap]
  exact (chartHomEquiv_mem_chart_iff x z _).1 <| by simpa using N.2.2

-- The map classifying a point lying in the three charts.
private noncomputable def tripleLift (x y z : Fin k → M)
    (N : ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ∩
      chart A (fun i ↦ (1 : A) ⊗ₜ[R] z i))) :
    TripleAlgebra R x y z →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom _ (isUnit_overlapHomEquiv_symm_transitionDet R x y z N)

-- Its restriction to `OverlapAlgebra R x y` is the map classifying the point there.
private lemma tripleLift_comp (x y z : Fin k → M)
    (N : ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ∩
      chart A (fun i ↦ (1 : A) ⊗ₜ[R] z i))) :
    (tripleLift R x y z N).comp (IsScalarTower.toAlgHom R _ (TripleAlgebra R x y z)) =
      (overlapHomEquiv R x y A).symm ⟨N.1, N.2.1⟩ :=
  AlgHom.ext fun a ↦ by simp [tripleLift]

/-- `R`-algebra maps `TripleAlgebra R x y z → A` are the points of `G(k, A ⊗[R] M; A)` lying in the
charts at `x`, `y` and `z`: the point attached to `g` is the point of the overlap of the charts at
`x` and `y` classified by the restriction of `g` to `OverlapAlgebra R x y`. -/
noncomputable def tripleHomEquiv (x y z : Fin k → M) (A : Type w) [CommRing A] [Algebra R A] :
    (TripleAlgebra R x y z →ₐ[R] A) ≃
      ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ∩
        chart A (fun i ↦ (1 : A) ⊗ₜ[R] z i)) where
  toFun g := ⟨(overlapHomEquiv R x y A (g.comp (IsScalarTower.toAlgHom R _ _))).1,
    (overlapHomEquiv R x y A _).2, by
      rw [coe_overlapHomEquiv_apply, chartHomEquiv_mem_chart_iff]
      exact (IsLocalization.Away.algebraMap_isUnit (S := TripleAlgebra R x y z)
        (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y) (transitionDet R x z))).map g⟩
  invFun N := tripleLift R x y z N
  left_inv g := IsLocalization.algHom_ext (Submonoid.powers
      (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y) (transitionDet R x z))) <|
    (tripleLift_comp R x y z _).trans <| (overlapHomEquiv R x y A).symm_apply_apply _
  right_inv N := Subtype.ext <| by
    simp only [tripleLift_comp, Equiv.apply_symm_apply]

variable {R}

@[simp]
theorem coe_tripleHomEquiv_apply (x y z : Fin k → M) (g : TripleAlgebra R x y z →ₐ[R] A) :
    (tripleHomEquiv R x y z A g : G(k, A ⊗[R] M; A)) =
      (overlapHomEquiv R x y A (g.comp (IsScalarTower.toAlgHom R _ _))).1 :=
  (rfl)

/-- `tripleHomEquiv` is natural: composing with `f : A → B` corresponds to base change of points
along `f`. -/
theorem tripleHomEquiv_comp (x y z : Fin k → M) {B : Type w} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : TripleAlgebra R x y z →ₐ[R] A) :
    (tripleHomEquiv R x y z B (f.comp g)).1 = map f (tripleHomEquiv R x y z A g).1 := by
  simpa [AlgHom.comp_assoc] using overlapHomEquiv_comp x y f (g.comp (IsScalarTower.toAlgHom R _ _))

/-- `R`-algebra maps out of `TripleAlgebra R x y z` are determined by the points they classify. -/
theorem TripleAlgebra.hom_ext {x y z : Fin k → M} {g g' : TripleAlgebra R x y z →ₐ[R] A}
    (h : (tripleHomEquiv R x y z A g).1 = (tripleHomEquiv R x y z A g').1) : g = g' :=
  (tripleHomEquiv R x y z A).injective (Subtype.ext h)

namespace TripleAlgebra

variable (R)

/-- The map from the coordinate ring of the overlap of the charts at `x` and `z` to the
coordinate ring of the triple overlap of the charts at `x`, `y` and `z`: the map classifying the
universal point of the triple overlap, which lies in the charts at `x` and `z`. -/
noncomputable def inr (x y z : Fin k → M) : OverlapAlgebra R x z →ₐ[R] TripleAlgebra R x y z :=
  (overlapHomEquiv R x z _).symm
    ⟨(tripleHomEquiv R x y z _ (AlgHom.id R _)).1, (tripleHomEquiv R x y z _ _).2.1.1,
      (tripleHomEquiv R x y z _ _).2.2⟩

variable {R}

/-- The two maps from the coordinate ring of the chart at `x` to `TripleAlgebra R x y z`, through
the overlaps with the charts at `y` and at `z`, agree. -/
theorem inr_comp_toAlgHom (x y z : Fin k → M) :
    (inr R x y z).comp (IsScalarTower.toAlgHom R (ChartAlgebra R x) (OverlapAlgebra R x z)) =
      (IsScalarTower.toAlgHom R (OverlapAlgebra R x y) (TripleAlgebra R x y z)).comp
        (IsScalarTower.toAlgHom R (ChartAlgebra R x) (OverlapAlgebra R x y)) := by
  -- both maps classify the universal point of the triple overlap in the chart at `x`
  have : (chartHomEquiv R x _).symm
      ⟨(tripleHomEquiv R x y z _ (AlgHom.id R _)).1, (tripleHomEquiv R x y z _ _).2.1.1⟩ =
        (IsScalarTower.toAlgHom R (OverlapAlgebra R x y) (TripleAlgebra R x y z)).comp
          (IsScalarTower.toAlgHom R (ChartAlgebra R x) (OverlapAlgebra R x y)) :=
    (chartHomEquiv R x _).symm_apply_eq.2 <| Subtype.ext <| by
      rw [coe_tripleHomEquiv_apply, coe_overlapHomEquiv_apply, AlgHom.id_comp]
  refine AlgHom.ext fun a ↦ ?_
  rw [← this]
  exact overlapHomEquiv_symm_apply_algebraMap x z _ a

/-- The point classified by the restriction of `g` along `inr` is the point classified by `g`. -/
theorem overlapHomEquiv_comp_inr (x y z : Fin k → M) (g : TripleAlgebra R x y z →ₐ[R] A) :
    (overlapHomEquiv R x z A (g.comp (inr R x y z))).1 = (tripleHomEquiv R x y z A g).1 := by
  rw [coe_overlapHomEquiv_apply, coe_tripleHomEquiv_apply, coe_overlapHomEquiv_apply,
    AlgHom.comp_assoc, inr_comp_toAlgHom, AlgHom.comp_assoc]

/-- **The triple overlap is the pushout of the two overlaps over the chart.** In the chart at `x`,
the coordinate ring of the triple overlap with the charts at `y` and `z` is the pushout of the
coordinate rings of the overlaps with the charts at `y` and at `z`. Under `Spec`, the triple overlap
is the fibre product of the two overlaps over the chart. -/
theorem isPushout (x y z : Fin k → M) :
    IsPushout (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)))
      (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x z)))
      (CommRingCat.ofHom (algebraMap (OverlapAlgebra R x y) (TripleAlgebra R x y z)))
      (CommRingCat.ofHom (inr R x y z : OverlapAlgebra R x z →+* TripleAlgebra R x y z)) := by
  have : IsLocalization ((Submonoid.powers (transitionDet R x z)).map
      (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))) (TripleAlgebra R x y z) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact CommRingCat.isPushout_of_isLocalization _ _
    (RingHom.ext fun a ↦ DFunLike.congr_fun (inr_comp_toAlgHom (R := R) x y z) a)
    (Submonoid.powers (transitionDet R x z))

variable (R)

/-- The **cyclic map** between the coordinate rings of the triple overlap of the charts at `x`, `y`
and `z`, read in the charts at `y` and at `x`: the map classifying the universal point of
`TripleAlgebra R x y z`, which lies in the charts at `y`, `z` and `x`. It is compatible with the
points (`Module.Grassmannian.TripleAlgebra.tripleHomEquiv_comp_cycle`), and it is an isomorphism,
with inverse the composite of the cyclic maps for the other two cyclic orders
(`Module.Grassmannian.TripleAlgebra.cycle_cycle`), bundled as
`Module.Grassmannian.TripleAlgebra.cycleAlgEquiv`. -/
noncomputable def cycle (x y z : Fin k → M) : TripleAlgebra R y z x →ₐ[R] TripleAlgebra R x y z :=
  (tripleHomEquiv R y z x _).symm
    ⟨(tripleHomEquiv R x y z _ (AlgHom.id R _)).1, ⟨(tripleHomEquiv R x y z _ _).2.1.2,
      (tripleHomEquiv R x y z _ _).2.2⟩, (tripleHomEquiv R x y z _ _).2.1.1⟩

variable {R}

/-- The cyclic map is compatible with the points: precomposing
`g : TripleAlgebra R x y z →ₐ[R] A` with it gives the map classifying the same point, now read in
the chart at `y`. -/
-- `A` lies in the universe of the coordinate rings, where base change of points along `g`
-- (`Module.Grassmannian.map`) is defined.
theorem tripleHomEquiv_comp_cycle {A : Type (max u v)} [CommRing A] [Algebra R A]
    (x y z : Fin k → M) (g : TripleAlgebra R x y z →ₐ[R] A) :
    (tripleHomEquiv R y z x A (g.comp (cycle R x y z))).1 = (tripleHomEquiv R x y z A g).1 := by
  rw [tripleHomEquiv_comp, cycle, Equiv.apply_symm_apply, ← tripleHomEquiv_comp, AlgHom.comp_id]

/-- **The cocycle condition.** Going round the three cyclic orders of the charts at `x`, `y` and
`z` gives the identity of `TripleAlgebra R x y z`. -/
theorem cycle_cycle (x y z : Fin k → M) :
    (cycle R x y z).comp ((cycle R y z x).comp (cycle R z x y)) = AlgHom.id R _ :=
  hom_ext <| by
    rw [← AlgHom.comp_assoc, tripleHomEquiv_comp_cycle, tripleHomEquiv_comp_cycle,
      ← AlgHom.id_comp (cycle R x y z), tripleHomEquiv_comp_cycle]

variable (R) in
/-- The cyclic map `TripleAlgebra R y z x → TripleAlgebra R x y z` as an isomorphism. Its inverse is
the composite of the cyclic maps for the other two cyclic orders. -/
noncomputable def cycleAlgEquiv (x y z : Fin k → M) :
    TripleAlgebra R y z x ≃ₐ[R] TripleAlgebra R x y z :=
  AlgEquiv.ofAlgHom (cycle R x y z) ((cycle R y z x).comp (cycle R z x y)) (cycle_cycle x y z)
    ((AlgHom.comp_assoc _ _ _).trans (cycle_cycle y z x))

@[simp]
theorem toAlgHom_cycleAlgEquiv (x y z : Fin k → M) :
    (cycleAlgEquiv R x y z : TripleAlgebra R y z x →ₐ[R] TripleAlgebra R x y z) = cycle R x y z :=
  (rfl)

@[simp]
theorem coe_cycleAlgEquiv (x y z : Fin k → M) : ⇑(cycleAlgEquiv R x y z) = cycle R x y z :=
  (rfl)

@[simp]
theorem toAlgHom_cycleAlgEquiv_symm (x y z : Fin k → M) :
    ((cycleAlgEquiv R x y z).symm : TripleAlgebra R x y z →ₐ[R] TripleAlgebra R y z x) =
      (cycle R y z x).comp (cycle R z x y) :=
  (rfl)

/-- The cyclic map is compatible with the transition isomorphism from the chart at `x` to
the chart at `y`: on the coordinate ring of the overlap of the charts at `y` and `x`, both send the
universal point to the universal point of the triple overlap. -/
theorem cycle_comp_inr (x y z : Fin k → M) :
    (cycle R x y z).comp (inr R y z x) =
      (IsScalarTower.toAlgHom R (OverlapAlgebra R x y) (TripleAlgebra R x y z)).comp
        (transitionAlgEquiv R x y : OverlapAlgebra R y x →ₐ[R] OverlapAlgebra R x y) := by
  refine (overlapHomEquiv R y x _).injective (Subtype.ext ?_)
  rw [overlapHomEquiv_comp_inr, overlapHomEquiv_comp_transitionAlgEquiv,
    ← AlgHom.id_comp (cycle R x y z), tripleHomEquiv_comp_cycle, coe_tripleHomEquiv_apply,
    AlgHom.id_comp]

end TripleAlgebra

end Triple

end Module.Grassmannian
