/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Conductor
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The two branches above the origin of a split node

The inverse image of the origin under the branch inclusion is the spectrum of `R × R`.
Algebraically, `branchValues` is the pushout of `branchMap` along `origin`. The proof uses
the existing conductor calculation, so it retains the full scheme structure over arbitrary
commutative rings, including nonreduced bases.

The branch algebra is the normalization when the base is an integrally closed domain, as
proved in `TauCeti.RingTheory.Node.Normalization`; no such assertion is made for arbitrary bases.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

open Polynomial CategoryTheory Limits

namespace TauCeti.NodeAlgebra

variable (R : Type*) [CommRing R]

/-- The origin of the split node, viewed as an `R`-valued point. -/
def origin : NodeAlgebra R 0 →ₐ[R] R := lift 0 0 0 (by simp)

/-- Both branch coordinates vanish at the split origin. -/
@[simp]
theorem origin_coord (i : Fin 2) : origin R (coord (0 : R) i) = 0 := by
  fin_cases i <;> simp [origin]

/-- Restriction to both branch origins repeats the value at the node origin. -/
theorem branchValues_comp_branchMap :
    (branchValues R).comp (branchMap R) =
      (Algebra.ofId R (R × R)).comp (origin R) := by
  ext <;> simp

/-- The split origin has precisely the Jacobian ideal as its defining ideal. -/
theorem ker_origin : RingHom.ker (origin R).toRingHom = jacobianIdeal (0 : R) := by
  rw [← comap_branchConductor_eq_jacobianIdeal, branchConductor_eq_ker_branchValues]
  ext z
  have hz := AlgHom.congr_fun (branchValues_comp_branchMap R) z
  simp only [AlgHom.comp_apply, Algebra.ofId_apply] at hz
  simp [Ideal.mem_comap, RingHom.mem_ker, hz]

/-- Pulling the branch algebra back to the origin gives the two independent branch values. -/
theorem isPushout_branchValues :
    IsPushout (CommRingCat.ofHom (branchMap R).toRingHom)
      (CommRingCat.ofHom (origin R).toRingHom)
      (CommRingCat.ofHom (branchValues R).toRingHom)
      (CommRingCat.ofHom (algebraMap R (R × R))) := by
  have comm : CommRingCat.ofHom (branchMap R).toRingHom ≫
        CommRingCat.ofHom (branchValues R).toRingHom =
      CommRingCat.ofHom (origin R).toRingHom ≫
        CommRingCat.ofHom (algebraMap R (R × R)) := by
    exact congrArg (fun f : NodeAlgebra R 0 →ₐ[R] R × R ↦
      CommRingCat.ofHom f.toRingHom) (branchValues_comp_branchMap R)
  let desc (s : PushoutCocone (CommRingCat.ofHom (branchMap R).toRingHom)
      (CommRingCat.ofHom (origin R).toRingHom)) : CommRingCat.of (R × R) ⟶ s.pt :=
    CommRingCat.ofHom ((branchValues R).toRingHom.liftOfSurjective
      (branchValues_surjective R) ⟨s.inl.hom, by
        -- Specify the projection here: rewriting the AlgHom coercion would also change
        -- the dependent carrier of the pushout cocone.
        rw [show RingHom.ker (branchValues R).toRingHom = branchConductor R from
          (branchConductor_eq_ker_branchValues R).symm, ← map_jacobianIdeal_eq_branchConductor,
          Ideal.map_le_iff_le_comap]
        intro z hz
        have hzero : origin R z = 0 := RingHom.mem_ker.mp ((ker_origin R).symm ▸ hz)
        exact RingHom.mem_ker.mpr
          ((ConcreteCategory.congr_hom s.condition z).trans (by simp [hzero]))⟩)
  have fac (s) : CommRingCat.ofHom (branchValues R).toRingHom ≫ desc s = s.inl := by
    ext p
    exact RingHom.liftOfSurjective_comp_apply _ _ _ p
  refine ⟨⟨comm⟩, ⟨PushoutCocone.IsColimit.mk comm desc fac ?_ ?_⟩⟩
  · intro s
    ext r
    have h := ConcreteCategory.congr_hom (fac s) (branchMap R (algebraMap R _ r))
    have hs := ConcreteCategory.congr_hom s.condition (algebraMap R _ r)
    simpa using h.trans hs
  · intro s m hm _
    ext r
    obtain ⟨p, rfl⟩ := branchValues_surjective R r
    exact (ConcreteCategory.congr_hom hm p).trans
      (ConcreteCategory.congr_hom (fac s) p).symm

end TauCeti.NodeAlgebra
