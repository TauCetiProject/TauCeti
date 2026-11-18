/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import TauCeti.Topology.Algebra.PointTopology.Functoriality

/-!
# Polynomial presentations of point spaces

For a presentation of an `R`-algebra `S` and a topological `k`-algebra `E`, an `E`-point of
`S` over `k` amounts to an `E`-point of `R` and values for the generators satisfying the
relations. This identification is a homeomorphism for the evaluation topologies. In particular,
restriction of points from `S` to `R` becomes projection onto the coefficient point.

For a submersive presentation, the evaluated Jacobian minor is a unit at every solution.
Thus these point spaces have precisely the polynomial description needed to apply the
implicit function theorem, with the base point allowed to vary.

We use Mathlib's `Algebra.Presentation` and `Algebra.SubmersivePresentation`, developed by
Jung Tao Cheng, Christian Merten and Andrew Yang. The topological identification is the
presentation argument of B. Conrad, *Weil and Grothendieck approaches to adelic points*,
Proposition 2.1; the submersive case supplies the local equations used in §4.
-/

public section

open Topology MvPolynomial
open scoped TauCeti.PointTopology

namespace TauCeti.PointTopology

variable {k R E ι : Type*} [CommSemiring k] [CommSemiring R] [Algebra k R]
  [CommSemiring E] [Algebra k E] [TopologicalSpace E] [IsTopologicalSemiring E]

/-- Polynomial evaluation is jointly continuous in the coefficient point and variable values. -/
@[fun_prop]
theorem _root_.MvPolynomial.continuous_aevalTower (p : MvPolynomial ι R) :
    Continuous fun z : (R →ₐ[k] E) × (ι → E) ↦ aevalTower z.1 z.2 p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simpa only [aevalTower_C, Function.comp_def] using (continuous_eval r).comp continuous_fst
  | add p q hp hq => simpa only [map_add, Pi.add_apply] using hp.fun_add hq
  | mul_X p i hp =>
    simpa only [map_mul, aevalTower_X, Pi.mul_apply, Function.comp_def] using
      hp.fun_mul ((continuous_apply i).comp continuous_snd)

/-- A polynomial-algebra point consists of a coefficient point and freely chosen coordinates. -/
noncomputable def mvPolynomialTowerHomeomorph :
    (MvPolynomial ι R →ₐ[k] E) ≃ₜ (R →ₐ[k] E) × (ι → E) where
  toFun x := (x.comp (IsScalarTower.toAlgHom k R (MvPolynomial ι R)), fun i ↦ x (X i))
  invFun z := aevalTower z.1 z.2
  left_inv x := by
    apply AlgHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext <;> intro a <;> simp
  right_inv z := by simp [aevalTower_comp_toAlgHom]
  continuous_toFun := (continuous_comap _).prodMk (continuous_pi fun i ↦ continuous_eval (X i))
  continuous_invFun := continuous_iff.2 continuous_aevalTower

/-- The coefficient component of a polynomial point is restriction to the coefficient algebra. -/
@[simp]
theorem mvPolynomialTowerHomeomorph_apply_fst (x : MvPolynomial ι R →ₐ[k] E) :
    (mvPolynomialTowerHomeomorph x).1 =
      x.comp (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) := (rfl)

/-- The coordinate components of a polynomial point are its values on the variables. -/
@[simp]
theorem mvPolynomialTowerHomeomorph_apply_snd (x : MvPolynomial ι R →ₐ[k] E) (i : ι) :
    (mvPolynomialTowerHomeomorph x).2 i = x (X i) := (rfl)

/-- The polynomial point with given coefficients and coordinates is algebra evaluation. -/
@[simp]
theorem mvPolynomialTowerHomeomorph_symm_apply (z : (R →ₐ[k] E) × (ι → E)) :
    mvPolynomialTowerHomeomorph.symm z = aevalTower z.1 z.2 := (rfl)

end TauCeti.PointTopology

namespace Algebra.Presentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E] [TopologicalSpace E] [IsTopologicalSemiring E]
  (P : Presentation R S ι σ)

open TauCeti.PointTopology

omit [TopologicalSpace E] [IsTopologicalSemiring E] in
/-- The coordinate image of a presented algebra is the solution set of its defining relations,
with the coefficient point varying over points of the base algebra. -/
theorem range_points_coordinates :
    Set.range (fun x : S →ₐ[k] E ↦
      (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i))) =
      {z : (R →ₐ[k] E) × (ι → E) | ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ j
    exact (MvPolynomial.map_aeval P.val x.toRingHom (P.relation j)).symm.trans (by simp)
  · intro hz
    let f := (aeval (R := R) P.val).restrictScalars k
    have hker : RingHom.ker f ≤ RingHom.ker (aevalTower z.1 z.2) := by
      have hfker : RingHom.ker f = P.ker := by
        rw [P.ker_eq_ker_aeval_val]
        rfl
      rw [hfker, ← P.span_range_relation_eq_ker]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hz j)
    have hmem : aevalTower z.1 z.2 ∈
        Set.range (fun x : S →ₐ[k] E ↦ x.comp f) := by
      rw [AlgHom.range_comp_right_of_surjective f P.aeval_val_surjective]
      exact hker
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, Prod.ext ?_ (funext fun i ↦ ?_)⟩
    · ext r
      simpa [f] using congrArg (fun g : MvPolynomial ι R →ₐ[k] E ↦ g (C r)) hx
    · simpa [f] using congrArg (fun g : MvPolynomial ι R →ₐ[k] E ↦ g (X i)) hx

/-- A presentation identifies its point space with the polynomial solution space, in the
evaluation topology, compatibly with projection to the coefficient point. -/
noncomputable def pointsHomeomorph :
    (S →ₐ[k] E) ≃ₜ
      {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0} := by
  let f := (aeval (R := R) P.val).restrictScalars k
  have h := (mvPolynomialTowerHomeomorph (k := k) (R := R) (E := E) (ι := ι)).isEmbedding.comp
    (isEmbedding_comap_of_surjective f P.aeval_val_surjective)
  have hcoord : (mvPolynomialTowerHomeomorph ∘ (fun x : S →ₐ[k] E ↦ x.comp f)) =
      fun x ↦ (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i)) := by
    ext x <;> simp [f, AlgHom.comp_assoc]
  rw [hcoord] at h
  exact h.toHomeomorph.trans (Homeomorph.setCongr P.range_points_coordinates)

/-- The solution attached to a point records its restriction and its generator values. -/
@[simp]
theorem pointsHomeomorph_apply_coe (x : S →ₐ[k] E) :
    (P.pointsHomeomorph x).val =
      (x.comp (IsScalarTower.toAlgHom k R S), fun i ↦ x (P.val i)) := by
  simp [pointsHomeomorph, Homeomorph.setCongr]

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

end Algebra.Presentation

namespace Algebra.PreSubmersivePresentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E]
  [Fintype σ] [DecidableEq σ] (P : PreSubmersivePresentation R S ι σ)

/-- At every point of a presubmersive presentation, the evaluated Jacobian minor is the
value of the algebraic Jacobian. Mathlib indexes this minor by variable first, relation second. -/
theorem det_jacobiMatrix_points_coordinates (x : S →ₐ[k] E) :
    ((aevalTower (x.comp (IsScalarTower.toAlgHom k R S))
      (fun i ↦ x (P.val i))).mapMatrix P.jacobiMatrix).det =
        x P.jacobian := by
  rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply]
  exact ((aevalTower (x.comp (IsScalarTower.toAlgHom k R S))
    (fun i ↦ x (P.val i))).toRingHom.map_det _).symm.trans
      (MvPolynomial.map_aeval P.val x.toRingHom _).symm

end Algebra.PreSubmersivePresentation

namespace Algebra.SubmersivePresentation

variable {k R S E ι σ : Type*} [CommSemiring k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [CommRing E] [Algebra k E] [Fintype σ] [DecidableEq σ]
  (P : SubmersivePresentation R S ι σ)

/-- The Jacobian minor is invertible at every solution of a submersive presentation. -/
theorem isUnit_det_jacobiMatrix_solution
    (z : {z : (R →ₐ[k] E) × (ι → E) // ∀ j, aevalTower z.1 z.2 (P.relation j) = 0}) :
    IsUnit (((aevalTower z.val.1 z.val.2).mapMatrix P.jacobiMatrix).det) := by
  obtain ⟨x, hx⟩ := (Set.ext_iff.mp (P.toPresentation.range_points_coordinates
    (k := k) (E := E)) z.val).mpr z.property
  rw [← hx, P.det_jacobiMatrix_points_coordinates]
  exact P.jacobian_isUnit.map x

end Algebra.SubmersivePresentation
