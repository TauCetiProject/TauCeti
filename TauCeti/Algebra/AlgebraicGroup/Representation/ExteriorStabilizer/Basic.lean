/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SubspaceStabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.LinearAlgebra.ExteriorAlgebra.TopSubspace
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior-line detection of closed subgroups

A finite-dimensional regular subcomodule containing generators of a closed subgroup's
ideal realizes that subgroup as a subspace stabilizer. Over every commutative value algebra `A`,
the top-exterior-line criterion in the exterior algebra over `A` of `A ⊗ V`, together with
compatibility of the exterior point action with scalar extension, turns this into the stabilizer
of a line in the finite-dimensional exterior-power comodule `⋀ᵈ V`, where `d` is the dimension of
the defining subspace. This works for nonreduced value algebras and subgroup schemes. The subgroup
character on that line is constructed in
`TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character`.

## Main statements

* `TauCeti.Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff`: a point
  stabilizes the top exterior line of a subspace exactly when it stabilizes the subspace.
* `TauCeti.HopfIdeal.mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq`:
  a finite regular subcomodule containing ideal generators realizes the subgroup as a line
  stabilizer over every value algebra.
* `TauCeti.HopfIdeal.exists_line_stabilizerHopfIdeal_eq`: every closed subgroup with finitely
  generated defining ideal is the stabilizer Hopf ideal of a line in a finite-dimensional comodule.
* `Submodule.stabilizerHopfIdeal_range_exteriorPowerMap`: the stabilizer Hopf ideal of the top
  exterior line `range (exteriorPower.map n W.subtype)` of a subspace `W` (where `n = finrank k W`)
  equals `W.stabilizerHopfIdeal H`.
* `Submodule.stabilizerHopfIdeal_span_ιMulti`: the stabilizer Hopf ideal of the line spanned by the
  exterior product of a linearly independent tuple `v` equals
  `(span k (range v)).stabilizerHopfIdeal H`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct
open CategoryTheory

universe u v w

namespace TauCeti.Comodule

variable {k : Type u} [Field k] {H : Type v} [CommSemiring H] [HopfAlgebra k H]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Comodule k H V]

attribute [local instance] exteriorPower

/-- Over a field, a point stabilizes the scalar extension of the top exterior line of a subspace
`W` of a finite-dimensional representation `V` exactly when it stabilizes the scalar extension of
`W`. The line is the image of `⋀ᵈ W` in the representation `⋀ᵈ V`, where `d = dim W`. This holds
over every commutative value algebra, including nonreduced ones. -/
theorem map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff (W : Submodule k V)
    (A : Type*) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    ((LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype)).baseChange A).map
        (endOfPoint (⋀[k]^(Module.finrank k W) V) g.ofConv) =
      (LinearMap.range (_root_.exteriorPower.map (Module.finrank k W) W.subtype)).baseChange A ↔
    (W.baseChange A).map (endOfPoint V g.ofConv) = W.baseChange A := by
  rw [map_endOfPoint_baseChange_range_exteriorPowerMap_eq_iff, ← pointsAction_toLinearMap,
    Submodule.map_topExteriorLine_baseChange_eq_iff]

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

attribute [local instance] Comodule.exteriorPower

/-- A finite regular subcomodule containing ideal generators realizes the closed subgroup as
the stabilizer of a line: the image of the top exterior power of the defining subspace in the
corresponding exterior power of the subcomodule. This holds over every value algebra. -/
theorem mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq
    (I : HopfIdeal k H) (V : Subcomodule k H H) [Module.Finite k V]
    (hgen : I.toIdeal ≤ Ideal.span ((V : Set H) ∩ (I : Set H)))
    (A : CommAlgCat.{w} k) (g : HopfAlgebra.points (R := k) (H := H) A) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H I A ↔
      ((LinearMap.range (_root_.exteriorPower.map (Module.finrank k (I.definingSubspace V))
          (I.definingSubspace V).subtype)).baseChange A).map
        (Comodule.endOfPoint (⋀[k]^(Module.finrank k (I.definingSubspace V)) V) g.ofConv) =
      (LinearMap.range (_root_.exteriorPower.map (Module.finrank k (I.definingSubspace V))
          (I.definingSubspace V).subtype)).baseChange A := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  rw [Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff]
  exact I.mem_quotientPointsSubgroup_iff_map_definingSubspace_eq V hgen A g

/-- Every closed subgroup with finitely generated defining ideal is the stabilizer Hopf ideal of a
one-dimensional subspace of a finite-dimensional comodule. -/
theorem exists_line_stabilizerHopfIdeal_eq (I : HopfIdeal k H) (hI : I.toIdeal.FG) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (L : Submodule k M),
      Module.finrank k L = 1 ∧ L.stabilizerHopfIdeal H = I := by
  obtain ⟨V, hV, hgen⟩ := I.exists_finite_subcomodule_generating hI
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let W := I.definingSubspace V
  let n := Module.finrank k W
  let L := LinearMap.range (_root_.exteriorPower.map n W.subtype)
  let instComodM : Comodule k H (⋀[k]^n V) := Comodule.exteriorPower k H V n
  refine ⟨⋀[k]^n V, inferInstance, inferInstance, instComodM, inferInstance, L, ?_, ?_⟩
  · rw [TauCeti.exteriorPower.finrank_range_map W.injective_subtype, Nat.choose_self]
  · exact L.stabilizerHopfIdeal_eq_of_forall_mem_quotientPointsSubgroup_iff I fun A _ _ g ↦
      I.mem_quotientPointsSubgroup_iff_map_baseChange_range_exteriorPowerMap_eq V hgen
        (CommAlgCat.of k A) g

end TauCeti.HopfIdeal

namespace Submodule

section ExteriorStabilizer

variable {k : Type u} {H : Type v} {M : Type w} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M] [Module.Finite k M]

/-- Over a field, the stabilizer Hopf ideal of the top exterior line
`LinearMap.range (exteriorPower.map n W.subtype)` of a subspace `W` of a finite-dimensional
comodule (where `n = Module.finrank k W`) equals the stabilizer Hopf ideal of `W`. -/
theorem stabilizerHopfIdeal_range_exteriorPowerMap (W : Submodule k M) {n : ℕ}
    (hn : Module.finrank k W = n) :
    (letI : TauCeti.Comodule k H (⋀[k]^n M) := TauCeti.Comodule.exteriorPower k H M n
     (LinearMap.range (_root_.exteriorPower.map n W.subtype)).stabilizerHopfIdeal H) =
      W.stabilizerHopfIdeal H := by
  subst hn
  let _ : TauCeti.Comodule k H (⋀[k]^(Module.finrank k W) M) :=
    TauCeti.Comodule.exteriorPower k H M (Module.finrank k W)
  exact stabilizerHopfIdeal_eq_of_forall_map_endOfPoint_eq_iff _ W fun A _ _ g ↦
    TauCeti.Comodule.map_endOfPoint_baseChange_range_exteriorPowerMap_finrank_eq_iff W A g

/-- Over a field, the line spanned by the exterior product of a linearly independent tuple `v` in a
finite-dimensional comodule has the same stabilizer Hopf ideal as `span k (range v)`. -/
theorem stabilizerHopfIdeal_span_ιMulti {d : ℕ} {v : Fin d → M} (hv : LinearIndependent k v) :
    (letI : TauCeti.Comodule k H (⋀[k]^d M) := TauCeti.Comodule.exteriorPower k H M d
     (k ∙ _root_.exteriorPower.ιMulti k d v).stabilizerHopfIdeal H) =
      (Submodule.span k (Set.range v)).stabilizerHopfIdeal H := by
  let W := Submodule.span k (Set.range v)
  have hdimW : Module.finrank k W = d := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  let E := LinearMap.range (_root_.exteriorPower.map d W.subtype)
  have hdimE : Module.finrank k E = 1 := by
    rw [TauCeti.exteriorPower.finrank_range_map W.injective_subtype, hdimW, Nat.choose_self]
  have hmem : _root_.exteriorPower.ιMulti k d v ∈ E :=
    ⟨_root_.exteriorPower.ιMulti k d (fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩),
      _root_.exteriorPower.map_apply_ιMulti W.subtype _⟩
  have hE : k ∙ _root_.exteriorPower.ιMulti k d v = E :=
    (eq_span_singleton_of_mem_of_finrank_eq_one hdimE hmem
      ((_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv)).symm
  let _ : TauCeti.Comodule k H (⋀[k]^d M) := TauCeti.Comodule.exteriorPower k H M d
  rw [hE]
  exact W.stabilizerHopfIdeal_range_exteriorPowerMap hdimW

end ExteriorStabilizer

end Submodule
