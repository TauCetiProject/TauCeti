/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.SolvableSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.AlgebraicGroup.Representation.TriangularEmbedding
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation

/-!
# Solvability detected by closed projective orbits

Let `G` be an affine group of finite type over an algebraically closed field `k`. A closed orbit
of a line `[m]` in the projective space of a finite-dimensional representation is *trivial* when
the line is a subrepresentation, that is, when the stabilizer of `k ∙ m` is all of `G`. This file
shows that `G` is solvable exactly when every closed projective orbit is trivial, provided `G` is
reduced and connected.

If every closed orbit is trivial, then every nonzero finite-dimensional representation has a
weight vector: the whole projective space is a nonempty closed invariant set, so it contains a
closed orbit, whose line is then a subrepresentation. By the triangular embedding criterion, `G`
is then a closed subgroup of an upper-triangular group, hence solvable. This direction needs no
connectedness or reducedness assumption. Conversely, for a reduced connected solvable group the
Borel fixed-point theorem makes every closed orbit a single point, so its line is stable under all
rational points, and reducedness promotes this to a subrepresentation.

The first direction is the input for an induction on dimension in the conjugacy of Borel
subgroups. A group that is not solvable has a closed projective orbit whose stabilizer is a
proper closed subgroup, and every reduced connected solvable closed subgroup is contained in a
conjugate of that proper subgroup.

## Main declarations

* `TauCeti.Comodule.isSolvable_points_of_forall_stabilizerHopfIdeal_eq_bot_of_isClosed`: if every
  closed projective orbit of an affine group is trivial, its points with values in every
  commutative algebra form a solvable group.
* `TauCeti.Comodule.isSolvable_iff_forall_stabilizerHopfIdeal_eq_bot_of_isClosed`: **a reduced
  connected group is solvable exactly when all of its closed projective orbits are trivial.**
* `TauCeti.Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_span_iff`: the rational points
  of the stabilizer of `k ∙ m` are the rational points fixing the orbit base point `[m]`.
* `TauCeti.HopfIdeal.exists_ne_bot_forall_exists_conjugate_le_of_not_isSolvable`: **an
  affine group that is not solvable has a proper closed subgroup containing a conjugate of
  every reduced connected solvable closed subgroup.**

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§10.4 and 11.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 16 and Theorem 17.5.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u w

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The rational points of the stabilizer of the line `k ∙ m` are exactly the rational points
fixing the base point `[m]` of its projective orbit. -/
theorem mem_quotientPointsSubgroup_stabilizerHopfIdeal_span_iff
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
    (m : M) (hm : Module.IsUnimodular k m) (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        ((k ∙ m).stabilizerHopfIdeal H) (CommAlgCat.of k k) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  rw [Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff,
    projectiveOrbitMap_kernelPoint_eq_one_iff]

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- **Solvability from trivial closed orbits.** If the line of every closed projective orbit of
an affine group of finite type over an algebraically closed field is a
subrepresentation, then the points of the group with values in every commutative algebra form a
solvable group. -/
theorem isSolvable_points_of_forall_stabilizerHopfIdeal_eq_bot_of_isClosed
    (horbit : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
      (m : M) (hm : Module.IsUnimodular k m),
      IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) →
        (k ∙ m).stabilizerHopfIdeal H = ⊥)
    (A : Type w) [CommRing A] [Algebra k A] :
    Group.IsSolvable (WithConv (H →ₐ[k] A)) := by
  obtain ⟨n, f, hf⟩ := exists_upperTriangular_surjective_of_weight_vectors (k := k) (H := H)
    fun V _ _ _ _ _ ↦ by
      -- The whole projective space of `V` is nonempty, so it contains a closed orbit.
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hv' : Module.IsUnimodular k v :=
        Module.isUnimodular_iff.mpr (Module.Projective.exists_dual_eq_one k hv)
      obtain ⟨m, hm, hclosed, -⟩ :=
        exists_isClosed_range_projectiveOrbitMap_subset_of_isClosed (H := H) isClosed_univ
          ⟨projectiveOrbitMap (H := H) v hv'
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)), Set.mem_univ _⟩
          fun _ ↦ Set.mapsTo_univ _ _
      have hm0 : m ≠ 0 := by
        rintro rfl
        obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hm
        simp at hφ
      exact hasNonzeroWeightVector_of_toSubmodule_eq_span
        ⟨k ∙ m, (Submodule.stabilizerHopfIdeal_eq_bot_iff _).mp (horbit V m hm hclosed)⟩ hm0
        rfl
  let _ := GeneralLinear.UpperTriangular.isSolvable_points k A n
  exact Group.isSolvable_of_isSolvable_injective
    (f := BialgHom.mapDomain (A := A) f.hom)
    (CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective f hf (CommAlgCat.of k A))

/-- **Closed-orbit criterion for solvability.** A reduced connected affine group of finite type
over an algebraically closed field is solvable exactly when the line of each of its closed
projective orbits is a subrepresentation. -/
theorem isSolvable_iff_forall_stabilizerHopfIdeal_eq_bot_of_isClosed
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
        (m : M) (hm : Module.IsUnimodular k m),
        IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)) →
          (k ∙ m).stabilizerHopfIdeal H = ⊥ := by
  refine ⟨fun _ M _ _ _ _ m hm hclosed ↦ ?_, fun horbit ↦
    isSolvable_points_of_forall_stabilizerHopfIdeal_eq_bot_of_isClosed horbit k⟩
  -- Every rational point preserves the line, and rational points detect subcomodules.
  rw [Submodule.stabilizerHopfIdeal_eq_bot_iff]
  refine fun _ hx ↦ Submodule.coact_mem_range_of_forall_endOfPoint_tmul_mem_baseChange
    (K := k) _ (fun g x hx ↦ ?_) hx
  rw [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  refine Submodule.tmul_mem_baseChange_of_mem _ ?_
  rw [← map_span_eq_span_of_isClosed_range_projectiveOrbitMap_of_isSolvable m hm hclosed
    (toConv g)]
  exact Submodule.mem_map_of_mem hx

end TauCeti.Comodule

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **A proper subgroup containing all connected solvable subgroups up to conjugacy.** An
affine group of finite type over an algebraically closed field whose rational points
do not form a solvable group has a proper closed subgroup containing a conjugate of every reduced
connected closed subgroup with solvable rational points. -/
theorem exists_ne_bot_forall_exists_conjugate_le_of_not_isSolvable
    (hH : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k))) :
    ∃ D : HopfIdeal k H, D ≠ ⊥ ∧ ∀ (I : HopfIdeal k H)
      [IsReduced (FiniteTypeCommHopfAlgCat.quotient H I)]
      [ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I))]
      [Group.IsSolvable (WithConv ((FiniteTypeCommHopfAlgCat.quotient H I) →ₐ[k] k))],
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I := by
  have h := mt
    (fun horbit ↦ Comodule.isSolvable_points_of_forall_stabilizerHopfIdeal_eq_bot_of_isClosed
      (H := H) horbit k) hH
  simp only [not_forall] at h
  obtain ⟨M, _, _, _, _, m, hm, hclosed, hD⟩ := h
  exact ⟨_, hD, fun I _ _ _ ↦ exists_conjugate_le_of_isClosed_projectiveOrbit _ I m hm hclosed
    (Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_span_iff m hm)⟩

end TauCeti.HopfIdeal
