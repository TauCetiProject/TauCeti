/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
public import TauCeti.LinearAlgebra.Unimodular
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints

/-!
# Projective orbits of finite constant groups

Let `G` be a finite group, `k` a field and `ρ` a representation of `G` on a finite-dimensional
`k`-vector space `V`, regarded as a representation of the constant group scheme attached to `G`.
Every point of the spectrum of the coordinate ring `G → k` is the rational point given by an
element of `G`, by `TauCeti.ConstantGroup.exists_eq_kernelPoint_eval`. Hence the orbit of a line
`[m]` in the projective space of lines of `V`, defined as the full image of the projective orbit
morphism, is the finite set of closed points `[ρ g m]`. In particular it is closed.

For a permutation representation, attached to an action of `G` on a finite set `ι`, the orbit of
the line through the basis vector `e_i` is the set of lines `[e_j]` for `j` in the orbit of `i`,
and these lines are distinct. So the orbit is connected only when `i` is a fixed point.

The basic example is the group `C₂ = Perm (Fin 2)` swapping the two coordinates of `k²`: the
orbit of `[1 : 0]` is the closed, disconnected two-point set `{[1 : 0], [0 : 1]}`, that is,
`{0, ∞}` in the projective line. Closed orbits of disconnected groups therefore need not be
connected.

## Main declarations

* `TauCeti.ConstantGroup.range_projectiveOrbitMap`: the orbit of a line consists of the images of
  the rational points.
* `TauCeti.ConstantGroup.projectiveOrbitMap_kernelPoint_eval_eq_iff`: two such images agree
  exactly when the translated vectors span the same line.
* `TauCeti.ConstantGroup.isClosed_range_projectiveOrbitMap`: orbits of finite constant groups are
  closed.
* `TauCeti.ConstantGroup.range_projectiveOrbitMap_single`: the orbit of a basis line under a
  permutation representation.
* `TauCeti.ConstantGroup.isPreconnected_range_projectiveOrbitMap_single_iff`: that orbit is
  preconnected exactly when the basis index is fixed.
* `TauCeti.ConstantGroup.range_projectiveOrbitMap_swap` and
  `TauCeti.ConstantGroup.not_isPreconnected_range_projectiveOrbitMap_swap`: the coordinate swap
  of `k²` has the disconnected closed orbit `{[1 : 0], [0 : 1]}`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, Springer (1991), §1.8.
-/

public section

open AlgebraicGeometry

namespace TauCeti.ConstantGroup

universe u

section Orbit

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable (ρ : Representation k G V)

/-- The orbit of a line under a finite constant group consists of the images of the rational
points given by the group elements. -/
theorem range_projectiveOrbitMap (m : V) (hm : Module.IsUnimodular k m) :
    letI := representationComodule k ρ
    Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm) =
      Set.range fun g : G ↦
        Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm
          (AlgHom.kernelPoint (eval k G g)) := by
  let := representationComodule k ρ
  refine subset_antisymm ?_ (Set.range_comp_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := exists_eq_kernelPoint_eval G x
  exact ⟨g, rfl⟩

/-- The images of the rational points `g` and `h` under the orbit morphisms of `[m]` and `[p]`
agree exactly when `ρ g m` and `ρ h p` span the same line. -/
theorem projectiveOrbitMap_kernelPoint_eval_eq_iff (m : V) (hm : Module.IsUnimodular k m)
    (p : V) (hp : Module.IsUnimodular k p) (g h : G) :
    letI := representationComodule k ρ
    Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm
        (AlgHom.kernelPoint (eval k G g)) =
      Comodule.projectiveOrbitMap (H := coordinateRing k G) p hp
        (AlgHom.kernelPoint (eval k G h)) ↔
      k ∙ ρ g m = k ∙ ρ h p := by
  let := representationComodule k ρ
  rw [← toPoints_apply, ← toPoints_apply, Comodule.projectiveOrbitMap_kernelPoint_eq_iff_span_eq,
    basePointsRepresentation_toPoints, basePointsRepresentation_toPoints]

/-- The orbit of a line under a finite constant group is finite. -/
theorem finite_range_projectiveOrbitMap (m : V) (hm : Module.IsUnimodular k m) :
    letI := representationComodule k ρ
    (Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm)).Finite := by
  rw [range_projectiveOrbitMap]
  exact Set.finite_range _

/-- Orbits of lines under finite constant groups are closed. -/
theorem isClosed_range_projectiveOrbitMap (m : V) (hm : Module.IsUnimodular k m) :
    letI := representationComodule k ρ
    IsClosed (Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm)) := by
  let := representationComodule k ρ
  rw [range_projectiveOrbitMap, ← Set.iUnion_singleton_eq_range]
  exact isClosed_iUnion_of_finite fun g ↦ mem_closedPoints_iff.mp
    (Comodule.projectiveOrbitMap_kernelPoint_mem_closedPoints m hm _)

end Orbit

section Permutation

variable (k : Type u) [Field k] {G : Type u} [Group G] [Fintype G]
variable {ι : Type u} [Finite ι] [MulAction G ι]

/-- Under the permutation representation of `G` on `k[ι]`, the image of the rational point `g`
under the orbit morphism of the basis line `[e_i]` is the basis line `[e_{g • i}]`. -/
theorem projectiveOrbitMap_single_kernelPoint_eval (g : G) (i : ι) :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    Comodule.projectiveOrbitMap (H := coordinateRing k G) (MonoidAlgebra.single i (1 : k))
        (MonoidAlgebra.isUnimodular_single i) (AlgHom.kernelPoint (eval k G g)) =
      Comodule.projectiveOrbitMap (H := coordinateRing k G) (MonoidAlgebra.single (g • i) (1 : k))
        (MonoidAlgebra.isUnimodular_single (g • i)) (AlgHom.kernelPoint (eval k G 1)) := by
  refine (projectiveOrbitMap_kernelPoint_eval_eq_iff (Representation.ofMulAction k G ι) _ _ _ _
    g 1).mpr ?_
  simp

/-- Distinct basis lines `[e_i]` are distinct points of projective space. -/
theorem projectiveOrbitMap_single_kernelPoint_eval_one_injective :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    Function.Injective fun i : ι ↦
      Comodule.projectiveOrbitMap (H := coordinateRing k G) (MonoidAlgebra.single i (1 : k))
        (MonoidAlgebra.isUnimodular_single i) (AlgHom.kernelPoint (eval k G 1)) := by
  intro i j hij
  replace hij := (projectiveOrbitMap_kernelPoint_eval_eq_iff (Representation.ofMulAction k G ι)
    _ _ _ _ 1 1).mp hij
  simp only [map_one, Module.End.one_apply] at hij
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hij.le (Submodule.mem_span_singleton_self (MonoidAlgebra.single i (1 : k))))
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one, MonoidAlgebra.single_inj] at hc
  exact (hc.resolve_right fun h ↦ one_ne_zero h.2).1.symm

/-- Under a permutation representation, the orbit of the basis line `[e_i]` is the set of basis
lines `[e_j]` for `j` in the orbit of `i`. -/
theorem range_projectiveOrbitMap_single (i : ι) :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G)
        (MonoidAlgebra.single i (1 : k)) (MonoidAlgebra.isUnimodular_single i)) =
      (fun j : ι ↦ Comodule.projectiveOrbitMap (H := coordinateRing k G)
          (MonoidAlgebra.single j (1 : k)) (MonoidAlgebra.isUnimodular_single j)
          (AlgHom.kernelPoint (eval k G 1))) '' MulAction.orbit G i := by
  rw [range_projectiveOrbitMap]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g • i, MulAction.mem_orbit i g, (projectiveOrbitMap_single_kernelPoint_eval k g i).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, projectiveOrbitMap_single_kernelPoint_eval k g i⟩

/-- Under a permutation representation, the orbit of the basis line `[e_i]` is preconnected
exactly when `i` is fixed by `G`. Otherwise it consists of at least two closed points. -/
theorem isPreconnected_range_projectiveOrbitMap_single_iff (i : ι) :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    IsPreconnected (Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G)
        (MonoidAlgebra.single i (1 : k)) (MonoidAlgebra.isUnimodular_single i))) ↔
      ∀ g : G, g • i = i := by
  let := representationComodule k (Representation.ofMulAction k G ι)
  set P : ι → _ := fun j : ι ↦ Comodule.projectiveOrbitMap (H := coordinateRing k G)
    (MonoidAlgebra.single j (1 : k)) (MonoidAlgebra.isUnimodular_single j)
    (AlgHom.kernelPoint (eval k G 1))
  have hP : Function.Injective P := projectiveOrbitMap_single_kernelPoint_eval_one_injective k
  have hclosed (s : Set ι) : IsClosed (P '' s) := by
    rw [Set.image_eq_iUnion]
    exact (Set.toFinite s).isClosed_biUnion fun j _ ↦ mem_closedPoints_iff.mp
      (Comodule.projectiveOrbitMap_kernelPoint_mem_closedPoints _ _ _)
  rw [range_projectiveOrbitMap_single]
  constructor
  · intro h g
    by_contra hg
    -- Split the orbit into the closed point `[e_i]` and the closed image of the rest.
    obtain ⟨x, -, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp h (P '' {i})
      (P '' (MulAction.orbit G i \ {i})) (hclosed _) (hclosed _)
      (by
        rw [← Set.image_union, Set.union_sdiff_self]
        exact Set.image_mono Set.subset_union_right)
      ⟨P i, Set.mem_image_of_mem _ (MulAction.mem_orbit_self i), Set.mem_image_of_mem _ rfl⟩
      ⟨P (g • i), Set.mem_image_of_mem _ (MulAction.mem_orbit i g),
        Set.mem_image_of_mem _ ⟨MulAction.mem_orbit i g, hg⟩⟩
    obtain ⟨j, rfl, rfl⟩ := hx₁
    obtain ⟨j', ⟨_, hj'⟩, hjj'⟩ := hx₂
    exact hj' (hP hjj')
  · intro h
    have : MulAction.orbit G i = {i} := by
      ext j
      simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ h g, fun hj ↦ ⟨1, by rw [one_smul, hj]⟩⟩
    rw [this, Set.image_singleton]
    exact isPreconnected_singleton

end Permutation

section Swap

variable (k : Type) [Field k]

/-- The orbit of `[1 : 0]` under the constant group `C₂ = Perm (Fin 2)` swapping the two
coordinates of `k²` is the two-point set `{[1 : 0], [0 : 1]}`. -/
theorem range_projectiveOrbitMap_swap :
    letI := representationComodule k (Representation.ofMulAction k (Equiv.Perm (Fin 2)) (Fin 2))
    Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k (Equiv.Perm (Fin 2)))
        (MonoidAlgebra.single (0 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 0)) =
      {Comodule.projectiveOrbitMap (H := coordinateRing k (Equiv.Perm (Fin 2)))
          (MonoidAlgebra.single (0 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 0)
          (AlgHom.kernelPoint (eval k _ 1)),
        Comodule.projectiveOrbitMap (H := coordinateRing k (Equiv.Perm (Fin 2)))
          (MonoidAlgebra.single (1 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 1)
          (AlgHom.kernelPoint (eval k _ 1))} := by
  rw [range_projectiveOrbitMap_single]
  have horbit : MulAction.orbit (Equiv.Perm (Fin 2)) (0 : Fin 2) = {0, 1} := by
    ext j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun _ ↦ by fin_cases j <;> simp, fun _ ↦ ?_⟩
    exact ⟨Equiv.swap 0 j, by simp [Equiv.Perm.smul_def]⟩
  rw [horbit, Set.image_pair]

/-- The orbit of `[1 : 0]` under the coordinate swap of `k²` is closed. -/
theorem isClosed_range_projectiveOrbitMap_swap :
    letI := representationComodule k (Representation.ofMulAction k (Equiv.Perm (Fin 2)) (Fin 2))
    IsClosed (Set.range (Comodule.projectiveOrbitMap
      (H := coordinateRing k (Equiv.Perm (Fin 2)))
      (MonoidAlgebra.single (0 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 0))) :=
  isClosed_range_projectiveOrbitMap _ _ _

/-- The closed orbit of `[1 : 0]` under the coordinate swap of `k²` is disconnected. -/
theorem not_isPreconnected_range_projectiveOrbitMap_swap :
    letI := representationComodule k (Representation.ofMulAction k (Equiv.Perm (Fin 2)) (Fin 2))
    ¬ IsPreconnected (Set.range (Comodule.projectiveOrbitMap
      (H := coordinateRing k (Equiv.Perm (Fin 2)))
      (MonoidAlgebra.single (0 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 0))) := by
  rw [isPreconnected_range_projectiveOrbitMap_single_iff]
  exact fun h ↦ by simpa [Equiv.Perm.smul_def] using h (Equiv.swap 0 1)

end Swap

end TauCeti.ConstantGroup
