/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import Mathlib.RingTheory.Henselian

/-!
# Henselianity of the pointed étale colimit

The colimit of pointed étale neighbourhoods with values in a field is a henselian local ring.
No local-ring hypothesis on the base or separable-closure hypothesis on the field is needed. In
particular this applies to the strict henselization formed with a separable closure of the
residue field, before taking its completion.

A monic polynomial and an approximate root descend to a common neighbourhood. The kernel of
the pointing is the maximal ideal of the colimit, so the image of the approximate root is an
actual simple root in the target field. A standard étale refinement adjoins a root with that
same image, giving the required lift in the colimit.

## References

* Stacks Project, Tag 04GP, henselianity of the strict henselization.
* `TauCeti.RingTheory.Henselization.Henselian`, for descent of a monic polynomial to one
  neighbourhood and adjoining a root by a standard étale refinement.
-/

public section

open CategoryTheory Polynomial

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The colimit of pointed étale neighbourhoods with values in a field is henselian local.
In particular the strict henselization of a local ring is henselian. -/
@[stacks 04GP "(2), henselian"]
instance henselianLocalRing : HenselianLocalRing (algebra R Ω) where
  is_henselian f hf a₀ hfa₀ hu := by
    classical
    -- A monic polynomial is determined by its degree and the finitely many lower coefficients.
    obtain ⟨B, b, hb⟩ := exists_stage_family R Ω
      (fun i : Option (Fin f.natDegree) ↦ i.elim a₀ fun j ↦ f.coeff j)
    have hb₀ : stage R Ω B (b none) = a₀ := hb none
    have hbj (j : Fin f.natDegree) : stage R Ω B (b (some j)) = f.coeff j := hb (some j)
    let g : Polynomial B.obj.left :=
      X ^ f.natDegree + ∑ j : Fin f.natDegree, C (b (some j)) * X ^ (j : ℕ)
    have hg : g.Monic := monic_X_pow_add (degree_sum_fin_lt _)
    have hgf : g.map (stage R Ω B).toRingHom = f := by
      conv_rhs => rw [hf.as_sum, ← Fin.sum_univ_eq_sum_range (fun j ↦ C (f.coeff j) * X ^ j)]
      simp [g, Polynomial.map_sum, hbj]
    have heval (p : Polynomial B.obj.left) :
        toTarget R Ω (stage R Ω B (p.eval (b none))) =
          toTarget R Ω ((p.map (stage R Ω B).toRingHom).eval a₀) := by
      rw [← hb₀]
      exact congrArg (toTarget R Ω) (eval_map_apply (stage R Ω B).toRingHom (p := p) (b none)).symm
    have hread (p : Polynomial B.obj.left) :
        (p.eval₂ B.obj.hom.hom.toRingHom (B.obj.hom.hom (b none))).down =
          toTarget R Ω ((p.map (stage R Ω B).toRingHom).eval a₀) := by
      calc
        _ = (B.obj.hom.hom (p.eval (b none))).down := by
          exact congrArg ULift.down (eval₂_at_apply B.obj.hom.hom.toRingHom (b none))
        _ = _ := by rw [← toTarget_stage_apply, heval]
    -- The maximal ideal is the kernel of the pointing, and units remain units at the point.
    have hroot : g.eval₂ B.obj.hom.hom.toRingHom (B.obj.hom.hom (b none)) = 0 := by
      apply ULift.ext
      rw [hread, hgf]
      exact RingHom.mem_ker.mp ((ker_toTarget_eq_maximalIdeal R Ω).symm ▸ hfa₀)
    have hunit : IsUnit
        (g.derivative.eval₂ B.obj.hom.hom.toRingHom (B.obj.hom.hom (b none))) := by
      have hdown : IsUnit
          (g.derivative.eval₂ B.obj.hom.hom.toRingHom (B.obj.hom.hom (b none))).down := by
        rw [hread, ← derivative_map, hgf]
        exact hu.map (toTarget R Ω).toRingHom
      exact (MulEquiv.isUnit_map (ULift.ringEquiv (R := Ω))).mp hdown
    obtain ⟨D, φ, c, hc, hpoint⟩ := B.exists_refinement_isRoot R Ω g hg
      (B.obj.hom.hom (b none)) hroot hunit
    have hφ : (stage R Ω D).toRingHom.comp φ.hom.left.hom.toRingHom =
        (stage R Ω B).toRingHom := by
      ext y
      exact stage_hom_apply R Ω φ y
    refine ⟨stage R Ω D c, ?_, ?_⟩
    · have h := hc.map (stage R Ω D).toRingHom
      rw [Polynomial.map_map, hφ, hgf] at h
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
    · rw [← ker_toTarget_eq_maximalIdeal, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, map_sub,
        toTarget_stage_apply, ← hb₀, toTarget_stage_apply, hpoint, sub_self]

end TauCeti.StrictHenselization
