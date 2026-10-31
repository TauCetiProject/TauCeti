/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Homogeneous ideals of projective orbit images

Let `m` be a unimodular vector in a finite projective comodule `M` over a commutative Hopf
algebra `H`. The projective orbit morphism `Spec H ⟶ Proj(Sym(M∨))` sends a point `x` of `Spec H`,
including a nonclosed one, to the homogeneous prime ideal of those forms of positive degree whose
orbit coordinate lies in `x`. This file records that description and three consequences.

* A form of positive degree whose orbit coordinate is a unit vanishes nowhere on the orbit, so a
  point of projective space at which that form vanishes lies outside the orbit.
* If `m` is a weight vector, with coaction `m ↦ m ⊗ c` for a group-like `c`, the orbit coordinate
  of a form `s` of degree `n` is `s(m) cⁿ`. Over a field the orbit of the line through `m` is then
  a single point: lines spanned by weight vectors are fixed by the whole group scheme, not just by
  its rational points.
* If `H` is a domain and no nonzero form of positive degree has vanishing orbit coordinate, then
  the image of the generic point of `Spec H` specializes to every point of projective space. In
  particular the orbit is dense.

These are the inputs for computing the orbits of explicit actions on projective space, such as
the action of the multiplicative group on the projective line.

## Main results

* `GroupLike.matrixCoefficient_of_mem_weightSpace`: matrix coefficients of a weight vector.
* `TauCeti.Comodule.mem_projectiveOrbitMap_iff`: the homogeneous ideal of the image of a point.
* `TauCeti.Comodule.notMem_range_projectiveOrbitMap_of_isUnit`: points on the zero locus of a form
  with invertible orbit coordinate lie outside the orbit.
* `TauCeti.Comodule.orbitCoordinates_of_mem_weightSpace`: orbit coordinates of a weight vector.
* `TauCeti.Comodule.range_projectiveOrbitMap_of_mem_weightSpace`: the orbit of the line through a
  weight vector is a single point.
* `TauCeti.Comodule.dense_range_projectiveOrbitMap`: an orbit whose coordinates satisfy no
  homogeneous relation is dense.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

section Coalgebra

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A matrix coefficient of a weight vector `m` of weight `c` is the multiple `φ(m) c` of `c`. -/
theorem _root_.GroupLike.matrixCoefficient_of_mem_weightSpace {c : GroupLike R C} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (φ : Module.Dual R M) :
    matrixCoefficient (C := C) φ m = φ m • c.val := by
  rw [matrixCoefficient_def, GroupLike.mem_weightSpace.mp hc]
  simp

end Coalgebra

section Bialgebra

variable {R H M : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The orbit coordinates of a weight vector: a form `s` of degree `n` goes to `s(m) cⁿ`, where
`c` is the weight of `m`. -/
theorem orbitCoordinates_of_mem_weightSpace {c : GroupLike R H} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) {n : ℕ}
    {s : SymmetricAlgebra R (Module.Dual R M)}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    orbitCoordinates (H := H) m s =
      algebraMap R H (SymmetricAlgebra.lift (Module.Dual.eval R M m) s) * c.val ^ n := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap a => simp
  | add x y i _ _ ihx ihy => simp only [map_add, ihx, ihy, add_mul]
  | mem_mul x hx i y _ ih =>
      obtain ⟨φ, rfl⟩ := hx
      rw [map_mul, ih, orbitCoordinates_ι, GroupLike.matrixCoefficient_of_mem_weightSpace hc]
      simp [Algebra.smul_def, pow_succ]
      ring

end Bialgebra

section Ring

variable {R H M : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

/-- A form of positive degree vanishes at the image of a point `x` of `Spec H` exactly when its
orbit coordinate lies in `x`. This holds at every point, closed or not. -/
theorem mem_projectiveOrbitMap_iff (m : M) (hm : Module.IsUnimodular R m) (x : Spec (.of H))
    {s : SymmetricAlgebra R (Module.Dual R M)} {n : ℕ} (hn : 0 < n)
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n) :
    s ∈ (projectiveOrbitMap (H := H) m hm x).asHomogeneousIdeal ↔
      orbitCoordinates (H := H) m s ∈ x.asIdeal := by
  have h := congrArg (fun U : (Spec (.of H)).Opens ↦ x ∈ U)
    (projectiveOrbitMap_preimage_basicOpen m hm hn hs)
  rw [basicOpen_eq_of_affine] at h
  -- The scheme carriers use their own membership instances. Identify these with the
  -- spectrum ideals; the open lemmas cannot rewrite through those instances directly.
  change (s ∉ (projectiveOrbitMap (H := H) m hm x).asHomogeneousIdeal) =
    (orbitCoordinates (H := H) m s ∉ x.asIdeal) at h
  exact not_iff_not.mp (Iff.of_eq h)

/-- If a form of positive degree has an invertible orbit coordinate, then no point of its zero
locus lies on the orbit. -/
theorem notMem_range_projectiveOrbitMap_of_isUnit (m : M) (hm : Module.IsUnimodular R m)
    {s : SymmetricAlgebra R (Module.Dual R M)} {n : ℕ} (hn : 0 < n)
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n)
    (hu : IsUnit (orbitCoordinates (H := H) m s))
    {y : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))}
    (hy : s ∈ y.asHomogeneousIdeal) :
    y ∉ Set.range (projectiveOrbitMap (H := H) m hm) := by
  rintro ⟨x, rfl⟩
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    ((mem_projectiveOrbitMap_iff m hm x hn hs).mp hy) hu)

/-- If `H` is a domain and no nonzero form of positive degree has vanishing orbit coordinate,
then the image of the generic point of `Spec H` specializes to every point of projective
space. -/
theorem projectiveOrbitMap_bot_specializes [IsDomain H] (m : M) (hm : Module.IsUnimodular R m)
    (hrel : ∀ n > 0, ∀ s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n,
      orbitCoordinates (H := H) m s = 0 → s = 0)
    (y : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M))) :
    projectiveOrbitMap (H := H) m hm ⟨⊥, Ideal.isPrime_bot⟩ ⤳ y := by
  set 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)
  set η := projectiveOrbitMap (H := H) m hm ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨d, hd, t, ht, hty⟩ := ProjectiveSpectrum.exists_le_mem_notMem y 1
  -- Every homogeneous component `a` of an element of `η`, multiplied by a form `t` of positive
  -- degree outside `y`, has vanishing orbit coordinate, so `a * t = 0` and `a ∈ y`.
  have hcomp (i : ℕ) (a : SymmetricAlgebra R (Module.Dual R M)) (ha : a ∈ 𝒜 i)
      (haη : a ∈ η.asHomogeneousIdeal) : a ∈ y.asHomogeneousIdeal := by
    have hat : a * t ∈ 𝒜 (i + d) := SetLike.mul_mem_graded ha ht
    have hatη : a * t ∈ η.asHomogeneousIdeal :=
      Ideal.mul_mem_right t η.asHomogeneousIdeal.toIdeal haη
    have hzero := hrel (i + d) (by omega) (a * t) hat
      ((mem_projectiveOrbitMap_iff m hm _ (by omega) hat).mp hatη)
    have hmem : a * t ∈ y.asHomogeneousIdeal := by
      rw [hzero]
      exact zero_mem _
    exact (y.isPrime.mem_or_mem hmem).resolve_right hty
  classical
  rw [specializes_iff_mem_closure]
  refine (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := 𝒜) η y).mp fun a ha ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  exact sum_mem fun i _ ↦ hcomp i _ (SetLike.coe_mem _)
    (η.asHomogeneousIdeal.isHomogeneous i ha)

/-- If `H` is a domain and no nonzero form of positive degree has vanishing orbit coordinate,
then the orbit is dense in projective space. -/
theorem dense_range_projectiveOrbitMap [IsDomain H] (m : M) (hm : Module.IsUnimodular R m)
    (hrel : ∀ n > 0, ∀ s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n,
      orbitCoordinates (H := H) m s = 0 → s = 0) :
    Dense (Set.range (projectiveOrbitMap (H := H) m hm)) := fun y ↦
  closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
    (specializes_iff_mem_closure.mp (projectiveOrbitMap_bot_specializes m hm hrel y))

end Ring

section Field

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The orbit of the line through a weight vector is a single point: all points of `Spec H`,
closed or not, have the same image. -/
theorem projectiveOrbitMap_eq_of_mem_weightSpace {c : GroupLike k H} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (hm : Module.IsUnimodular k m)
    (x y : Spec (.of H)) :
    projectiveOrbitMap (H := H) m hm x = projectiveOrbitMap (H := H) m hm y := by
  -- Both images contain a form of positive degree exactly when the form vanishes at `m`.
  have key (z : Spec (.of H)) {n : ℕ} (hn : 0 < n) {s : SymmetricAlgebra k (Module.Dual k M)}
      (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M) n) :
      s ∈ (projectiveOrbitMap (H := H) m hm z).asHomogeneousIdeal ↔
        SymmetricAlgebra.lift (Module.Dual.eval k M m) s = 0 := by
    rw [mem_projectiveOrbitMap_iff m hm z hn hs, orbitCoordinates_of_mem_weightSpace hc hs]
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra hne
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (((isUnit_iff_ne_zero.mpr hne).map (algebraMap k H)).mul (c.2.isUnit.pow n)))
  exact ProjectiveSpectrum.ext_of_mem_pos fun n hn s hs ↦ (key x hn hs).trans (key y hn hs).symm

/-- The orbit of the line through a weight vector is the single point given by that line. -/
theorem range_projectiveOrbitMap_of_mem_weightSpace {c : GroupLike k H} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (hm : Module.IsUnimodular k m) :
    Set.range (projectiveOrbitMap (H := H) m hm) =
      {projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Set.mem_range_self _, by
    rintro _ ⟨x, rfl⟩
    exact projectiveOrbitMap_eq_of_mem_weightSpace hc hm x _⟩

end Field

end TauCeti.Comodule
