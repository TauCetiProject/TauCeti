/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Projection

/-!
# Primitive submodules

A submodule is primitive when its quotient has no torsion, that is, when it contains every
element of which it contains a multiple by a regular scalar. For a submodule of a torsion-free
module over a principal ideal domain whose quotient is finitely generated, this is exactly
being a direct summand. In particular, an injective homomorphism of finite free abelian groups
is primitive precisely when its image has a complement.

## Main results

* `Submodule.isTorsionFree_quotient_iff`: a submodule has torsion-free quotient if and only if
  it is saturated.
* `Submodule.exists_isCompl_iff_isTorsionFree_quotient`: the direct-summand criterion.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.5.
-/

public section

namespace Submodule

/-- The quotient by a submodule is torsion-free if and only if the submodule contains every
element of which it contains a multiple by a regular scalar. Over a domain the regular scalars
are exactly the nonzero ones, see `isRegular_iff_ne_zero`. -/
theorem isTorsionFree_quotient_iff {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {S : Submodule R M} :
    Module.IsTorsionFree R (M ⧸ S) ↔ ∀ (c : R) (z : M), IsRegular c → c • z ∈ S → z ∈ S := by
  refine ⟨fun _ c z hc hz ↦ ?_, fun hS ↦ ⟨fun c hc x y hxy ↦ ?_⟩⟩
  · rw [← Quotient.mk_eq_zero, Quotient.mk_smul] at hz
    exact (Quotient.mk_eq_zero S).mp (hc.smul_eq_zero_iff_right.mp hz)
  · obtain ⟨x, rfl⟩ := Quotient.mk_surjective S x
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective S y
    -- Beta-reduce the scalar multiplications in the `IsSMulRegular` hypothesis.
    dsimp only at hxy
    rw [← Quotient.mk_smul, ← Quotient.mk_smul, Quotient.eq, ← smul_sub] at hxy
    exact (Quotient.eq S).mpr (hS c _ hc hxy)

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

/-- A submodule of a torsion-free module over a PID with finitely generated quotient has
torsion-free quotient if and only if it admits a complementary submodule. -/
theorem exists_isCompl_iff_isTorsionFree_quotient
    (S : Submodule R M) [Module.Finite R (M ⧸ S)] :
    (∃ T : Submodule R M, IsCompl S T) ↔ Module.IsTorsionFree R (M ⧸ S) := by
  refine ⟨fun ⟨T, hT⟩ ↦ ?_, fun _ ↦ ?_⟩
  · -- The quotient is isomorphic to the complement, a submodule of a torsion-free module.
    exact (S.quotientEquivOfIsCompl T hT).injective.moduleIsTorsionFree _ (map_smul _)
  · -- The quotient is free, so the quotient map splits; the quotient map followed by the
    -- splitting is an idempotent with kernel `S`, and its range is a complement.
    obtain ⟨g, hg⟩ := S.mkQ.exists_rightInverse_of_surjective S.range_mkQ
    have hidem : IsIdempotentElem (g ∘ₗ S.mkQ) := by
      rw [isIdempotentElem_iff, Module.End.mul_eq_comp, LinearMap.comp_assoc,
        ← LinearMap.comp_assoc S.mkQ, hg, LinearMap.id_comp]
    have h := (LinearMap.IsIdempotentElem.isCompl hidem).symm
    rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_inverse hg), ker_mkQ] at h
    exact ⟨_, h⟩

end Submodule
