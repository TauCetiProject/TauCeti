/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
public import TauCeti.Algebra.MonoidAlgebra.Basis
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
* `TauCeti.ConstantGroup.projectiveOrbitMap_kernelPoint_eval_eq_iff_span_eq`: two such images agree
  exactly when the translated vectors span the same line.
* `TauCeti.ConstantGroup.isClosed_range_projectiveOrbitMap`: orbits of finite constant groups are
  closed.
* `TauCeti.ConstantGroup.isPreconnected_range_projectiveOrbitMap_iff`: the orbit of `[m]` is
  preconnected exactly when every `ρ g m` spans the line of `m`.
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
theorem projectiveOrbitMap_kernelPoint_eval_eq_iff_span_eq (m : V) (hm : Module.IsUnimodular k m)
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

/-- The images of a set of rational points under the orbit morphism of a line form a closed set:
they are finitely many closed points. -/
theorem isClosed_image_projectiveOrbitMap_kernelPoint_eval (m : V) (hm : Module.IsUnimodular k m)
    (s : Set G) :
    letI := representationComodule k ρ
    IsClosed ((fun g : G ↦ Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm
      (AlgHom.kernelPoint (eval k G g))) '' s) := by
  let := representationComodule k ρ
  rw [Set.image_eq_iUnion]
  exact (Set.toFinite s).isClosed_biUnion fun g _ ↦ mem_closedPoints_iff.mp
    (Comodule.projectiveOrbitMap_kernelPoint_mem_closedPoints m hm _)

/-- Orbits of lines under finite constant groups are closed. -/
theorem isClosed_range_projectiveOrbitMap (m : V) (hm : Module.IsUnimodular k m) :
    letI := representationComodule k ρ
    IsClosed (Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm)) := by
  rw [range_projectiveOrbitMap, ← Set.image_univ]
  exact isClosed_image_projectiveOrbitMap_kernelPoint_eval ρ m hm _

/-- The orbit of a line `[m]` under a finite constant group is preconnected exactly when every
`ρ g m` spans the same line as `m`. Otherwise it splits into the closed point `[m]` and the closed
set of the other points. -/
theorem isPreconnected_range_projectiveOrbitMap_iff (m : V) (hm : Module.IsUnimodular k m) :
    letI := representationComodule k ρ
    IsPreconnected (Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm)) ↔
      ∀ g : G, k ∙ ρ g m = k ∙ m := by
  let := representationComodule k ρ
  rw [range_projectiveOrbitMap]
  set P : G → _ := fun g : G ↦ Comodule.projectiveOrbitMap (H := coordinateRing k G) m hm
    (AlgHom.kernelPoint (eval k G g))
  have hP (g : G) : P g = P 1 ↔ k ∙ ρ g m = k ∙ m := by
    have := projectiveOrbitMap_kernelPoint_eval_eq_iff_span_eq ρ m hm m hm g 1
    rwa [map_one, one_apply_eq_self] at this
  have hclosed (s : Set G) : IsClosed (P '' s) :=
    isClosed_image_projectiveOrbitMap_kernelPoint_eval ρ m hm s
  constructor
  · intro h g
    by_contra hg
    -- Split the orbit into the closed point `[m]` and the closed image of the other points.
    obtain ⟨x, -, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp h (P '' {1})
      (P '' {g | P g ≠ P 1}) (hclosed _) (hclosed _)
      (by
        rintro _ ⟨g', rfl⟩
        by_cases hg' : P g' = P 1
        · exact Or.inl ⟨1, rfl, hg'.symm⟩
        · exact Or.inr ⟨g', hg', rfl⟩)
      ⟨P 1, ⟨1, rfl⟩, 1, rfl, rfl⟩ ⟨P g, ⟨g, rfl⟩, g, (hP g).not.mpr hg, rfl⟩
    obtain ⟨_, rfl, rfl⟩ := hx₁
    obtain ⟨g', hg', hg'1⟩ := hx₂
    exact hg' hg'1
  · intro h
    have hrange : Set.range P = {P 1} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨⟨1, rfl⟩, by
        rintro _ ⟨g, rfl⟩
        exact (hP g).mpr (h g)⟩
    rw [hrange]
    exact isPreconnected_singleton

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
        (MonoidAlgebra.isUnimodular_single (g • i))
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (coordinateRing k G))) := by
  rw [← eval_one_eq_counitAlgHom k G]
  refine (projectiveOrbitMap_kernelPoint_eval_eq_iff_span_eq (Representation.ofMulAction k G ι)
    _ _ _ _ g 1).mpr ?_
  simp

/-- Distinct basis lines `[e_i]` are distinct points of projective space. -/
theorem projectiveOrbitMap_single_kernelPoint_one_injective :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    Function.Injective fun i : ι ↦
      Comodule.projectiveOrbitMap (H := coordinateRing k G) (MonoidAlgebra.single i (1 : k))
        (MonoidAlgebra.isUnimodular_single i)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (coordinateRing k G))) := by
  intro i j hij
  simp only [← eval_one_eq_counitAlgHom k G] at hij
  simpa using
    (projectiveOrbitMap_kernelPoint_eval_eq_iff_span_eq (Representation.ofMulAction k G ι)
      _ _ _ _ 1 1).mp hij

/-- Under a permutation representation, the orbit of the basis line `[e_i]` is the set of basis
lines `[e_j]` for `j` in the orbit of `i`. -/
theorem range_projectiveOrbitMap_single (i : ι) :
    letI := representationComodule k (Representation.ofMulAction k G ι)
    Set.range (Comodule.projectiveOrbitMap (H := coordinateRing k G)
        (MonoidAlgebra.single i (1 : k)) (MonoidAlgebra.isUnimodular_single i)) =
      (fun j : ι ↦ Comodule.projectiveOrbitMap (H := coordinateRing k G)
          (MonoidAlgebra.single j (1 : k)) (MonoidAlgebra.isUnimodular_single j)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (coordinateRing k G)))) ''
        MulAction.orbit G i := by
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
  rw [isPreconnected_range_projectiveOrbitMap_iff]
  simp

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
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k _)),
        Comodule.projectiveOrbitMap (H := coordinateRing k (Equiv.Perm (Fin 2)))
          (MonoidAlgebra.single (1 : Fin 2) (1 : k)) (MonoidAlgebra.isUnimodular_single 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k _))} := by
  rw [range_projectiveOrbitMap_single]
  have horbit : MulAction.orbit (Equiv.Perm (Fin 2)) (0 : Fin 2) = {0, 1} := by
    rw [MulAction.orbit_eq_univ]
    ext j
    fin_cases j <;> simp
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
