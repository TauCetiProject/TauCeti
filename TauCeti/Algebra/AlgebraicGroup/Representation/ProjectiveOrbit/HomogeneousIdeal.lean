/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Weight
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
  the image of the generic point of `Spec H` specializes to every point of projective space. More
  generally, without assuming that `H` is a domain, the orbit is then dense.

These are the inputs for computing the orbits of explicit actions on projective space, such as
the action of the multiplicative group on the projective line.

## Main results

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
  rw [mul_comm]
  exact AlgHom.apply_eq_pow_mul_of_forall_ι_eq
    ((Algebra.ofId R H).comp (SymmetricAlgebra.lift (Module.Dual.eval R M m)))
    (orbitCoordinates m) c.val (fun φ ↦ by
      simp [orbitCoordinates_ι, GroupLike.matrixCoefficient_of_mem_weightSpace hc,
        Algebra.smul_def, mul_comm]) hs

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

/-- If no nonzero form of positive degree has vanishing orbit coordinate, then the orbit is dense
in projective space. -/
theorem dense_range_projectiveOrbitMap (m : M) (hm : Module.IsUnimodular R m)
    (hrel : ∀ n > 0, ∀ s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M) n,
      orbitCoordinates (H := H) m s = 0 → s = 0) :
    Dense (Set.range (projectiveOrbitMap (H := H) m hm)) := fun y ↦ by
  set 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R M)
  obtain ⟨d, hd, t, ht, hty⟩ := ProjectiveSpectrum.exists_le_mem_notMem y 1
  -- A homogeneous form lying in the ideal of every orbit image, multiplied by `t`, has a nilpotent
  -- orbit coordinate, hence a power with vanishing orbit coordinate, hence a nilpotent power.
  have hcomp (i : ℕ) (a : SymmetricAlgebra R (Module.Dual R M)) (ha : a ∈ 𝒜 i)
      (hax : ∀ x : Spec (.of H), a ∈ (projectiveOrbitMap (H := H) m hm x).asHomogeneousIdeal) :
      a ∈ y.asHomogeneousIdeal := by
    have hat : a * t ∈ 𝒜 (i + d) := SetLike.mul_mem_graded ha ht
    have hnil : orbitCoordinates (H := H) m (a * t) ∈ nilradical H := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      exact (mem_projectiveOrbitMap_iff m hm ⟨J, hJ⟩ (by omega) hat).mp
        (Ideal.mul_mem_right t _ (hax ⟨J, hJ⟩))
    obtain ⟨N, hN⟩ := hnil
    have hpow : (a * t) ^ (N + 1) = 0 := by
      refine hrel _ (by simp; omega) _ (SetLike.pow_mem_graded _ hat) ?_
      rw [map_pow, pow_succ, hN, zero_mul]
    have hmem : (a * t) ^ (N + 1) ∈ y.asHomogeneousIdeal := by
      rw [hpow]
      exact zero_mem _
    exact (y.isPrime.mem_or_mem (y.isPrime.mem_of_pow_mem _ hmem)).resolve_right hty
  change y ∈ closure (Set.range (projectiveOrbitMap (H := H) m hm) : Set (ProjectiveSpectrum 𝒜))
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  intro a ha
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  refine sum_mem fun i _ ↦ hcomp i _ (SetLike.coe_mem _) fun x ↦ ?_
  have hi := (ProjectiveSpectrum.vanishingIdeal
    (Set.range (projectiveOrbitMap (H := H) m hm) : Set (ProjectiveSpectrum 𝒜))).isHomogeneous i ha
  have hi' : (DirectSum.decompose 𝒜 a i : SymmetricAlgebra R (Module.Dual R M)) ∈
      (ProjectiveSpectrum.vanishingIdeal
        (Set.range (projectiveOrbitMap (H := H) m hm) : Set (ProjectiveSpectrum 𝒜)) :
        Set (SymmetricAlgebra R (Module.Dual R M))) := hi
  rw [ProjectiveSpectrum.coe_vanishingIdeal] at hi'
  exact hi' _ ⟨x, rfl⟩

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
