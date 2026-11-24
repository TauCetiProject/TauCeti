/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Primitive submodules

A submodule is primitive when its quotient has no torsion, that is, when it contains every
element of which it contains a multiple by a regular scalar (see
`Submodule.isTorsionFree_quotient_iff`). For a submodule of a torsion-free module over a
Dedekind domain whose quotient is finitely generated, this is exactly being a direct summand.
In particular, an injective homomorphism of finite free abelian groups is primitive precisely
when its image has a complement.

## Main results

* `Submodule.exists_isCompl_iff_isTorsionFree_quotient`: the direct-summand criterion.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.5.
-/

public section

namespace Submodule

variable {R M : Type*} [CommRing R] [IsDedekindDomain R]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

/-- A submodule of a torsion-free module over a Dedekind domain with finitely generated quotient
has torsion-free quotient if and only if it admits a complementary submodule. -/
theorem exists_isCompl_iff_isTorsionFree_quotient
    (S : Submodule R M) [Module.Finite R (M ⧸ S)] :
    (∃ T : Submodule R M, IsCompl S T) ↔ Module.IsTorsionFree R (M ⧸ S) := by
  refine ⟨fun ⟨T, hT⟩ ↦ ?_, fun _ ↦ ?_⟩
  · -- The quotient is isomorphic to the complement, a submodule of a torsion-free module.
    exact (S.quotientEquivOfIsCompl T hT).injective.moduleIsTorsionFree _ (map_smul _)
  · -- Over a Dedekind domain the torsion-free quotient is flat, and being finitely generated
    -- over a Noetherian ring it is finitely presented, so it is projective by
    -- `Module.Flat.projective_of_finitePresentation`. Hence the quotient map splits; the
    -- quotient map followed by the splitting is an idempotent with kernel `S`, and its range
    -- is a complement.
    have := Module.finitePresentation_of_finite R (M ⧸ S)
    have := Module.Flat.projective_of_finitePresentation (R := R) (M := M ⧸ S)
    obtain ⟨g, hg⟩ := S.mkQ.exists_rightInverse_of_surjective S.range_mkQ
    have hgx (x : M ⧸ S) : S.mkQ (g x) = x := LinearMap.congr_fun hg x
    have hidem : IsIdempotentElem (g ∘ₗ S.mkQ) := by
      ext x
      simp [hgx]
    have h := (LinearMap.IsIdempotentElem.isCompl hidem).symm
    rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_inverse hg), ker_mkQ] at h
    exact ⟨_, h⟩

end Submodule
