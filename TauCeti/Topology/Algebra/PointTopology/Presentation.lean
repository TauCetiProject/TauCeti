/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Extension.Presentation.Basic
public import TauCeti.Topology.Algebra.PointTopology.Functoriality

/-!
# Polynomial presentations of point spaces

For a presentation of an `R`-algebra `S` and a topological `k`-algebra `E`, an `E`-point of
`S` over `k` amounts to an `E`-point of `R` and values for the generators satisfying the
relations. This identification is a homeomorphism for the evaluation topologies. In particular,
restriction of points from `S` to `R` becomes projection onto the coefficient point.

For a submersive presentation, the evaluated Jacobian minor is a unit at every solution
(`TauCeti.RingTheory.Extension.Presentation.Submersive`). Thus these point spaces have
precisely the polynomial description needed to apply the implicit function theorem, with the
base point allowed to vary.

We use Mathlib's `Algebra.Presentation`, developed by Jung Tao Cheng, Christian Merten and
Andrew Yang. The topological identification is the presentation argument of B. Conrad,
*Weil and Grothendieck approaches to adelic points*, Proposition 2.1.
-/

public section

open Topology MvPolynomial
open scoped TauCeti.PointTopology

namespace Algebra.Presentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E] [TopologicalSpace E] [IsTopologicalSemiring E]
  (P : Presentation R S ι σ)

open TauCeti.PointTopology

/-- A presentation identifies its point space with the polynomial solution space, in the
evaluation topology, compatibly with projection to the coefficient point. -/
noncomputable def pointsHomeomorph :
    (S →ₐ[k] E) ≃ₜ
      {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} :=
  (IsEmbedding.toHomeomorph
    (f := fun x : S →ₐ[k] E ↦
      (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i))) (by
        let f := (aeval (R := R) P.val).restrictScalars k
        have h := (mvPolynomialTowerHomeomorph k R E ι).isEmbedding.comp
          (isEmbedding_comap_of_surjective f P.aeval_val_surjective)
        have hcoord : (mvPolynomialTowerHomeomorph k R E ι ∘
            (fun x : S →ₐ[k] E ↦ x.comp f)) =
            fun x ↦ (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i)) := by
          ext x <;> simp [f, AlgHom.comp_assoc]
        exact hcoord ▸ h)).trans (Homeomorph.setCongr P.range_points_coordinates)

/-- The solution attached to a point records its restriction and its generator values. -/
@[simp]
theorem pointsHomeomorph_apply_coe (x : S →ₐ[k] E) :
    (P.pointsHomeomorph x).val =
      (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i)) := (rfl)

/-- Recovering a point from a solution gives the prescribed coefficient point. -/
@[simp]
theorem pointsHomeomorph_symm_comp
    (z : {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0}) :
    (P.pointsHomeomorph.symm z).comp (IsScalarTower.toAlgHom k R S) = z.val.1 := by
  have h := P.pointsHomeomorph_apply_coe (P.pointsHomeomorph.symm z)
  simpa using (congrArg Prod.fst h).symm

/-- Recovering a point from a solution gives the prescribed generator values. -/
@[simp]
theorem pointsHomeomorph_symm_apply_val
    (z : {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0})
    (i : ι) :
    P.pointsHomeomorph.symm z (P.val i) = z.val.2 i := by
  have h := P.pointsHomeomorph_apply_coe (P.pointsHomeomorph.symm z)
  simpa using (congrArg (fun w ↦ w.2 i) h).symm

section BaseRing

variable {K S ι σ : Type*} [CommRing K] [CommRing S] [Algebra K S] [TopologicalSpace K]
  [IsTopologicalRing K] (P : Presentation K S ι σ)

/-- Over the base ring `K`, a presentation identifies the points `S →ₐ[K] K`, in the evaluation
topology, with the zero set of its relations in `ι → K`. This is
`Algebra.Presentation.pointsHomeomorph` with the unique coefficient point `K →ₐ[K] K` dropped. -/
noncomputable def pointsHomeomorphZeroSet :
    (S →ₐ[K] K) ≃ₜ {y : ι → K | (fun j ↦ eval y (P.relation j)) = 0} :=
  letI : Unique (K →ₐ[K] K) :=
    { default := Algebra.ofId K K, uniq := fun _ ↦ Subsingleton.elim _ _ }
  P.pointsHomeomorph.trans <| (Homeomorph.uniqueProd (K →ₐ[K] K) (ι → K)).subtype fun z ↦ by
    simp only [Subsingleton.elim z.1 (Algebra.ofId K K), MvPolynomial.aevalTower_ofId,
      MvPolynomial.aeval_eq_eval, Homeomorph.coe_uniqueProd, Set.mem_ofPred_eq, funext_iff,
      Pi.zero_apply]

/-- The zero of the relations attached to a point is its vector of generator values. -/
@[simp]
theorem coe_pointsHomeomorphZeroSet_apply (x : S →ₐ[K] K) :
    (P.pointsHomeomorphZeroSet x : ι → K) = fun i ↦ x (P.val i) := (rfl)

/-- Recovering a point from a zero of the relations gives the prescribed generator values. -/
@[simp]
theorem pointsHomeomorphZeroSet_symm_apply_val
    (y : {y : ι → K | (fun j ↦ eval y (P.relation j)) = 0}) (i : ι) :
    P.pointsHomeomorphZeroSet.symm y (P.val i) = y.val i := by
  have h := P.coe_pointsHomeomorphZeroSet_apply (P.pointsHomeomorphZeroSet.symm y)
  simpa using (congrArg (fun w ↦ w i) h).symm

end BaseRing

end Algebra.Presentation
