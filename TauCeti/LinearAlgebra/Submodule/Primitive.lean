/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Projection

/-!
# Primitive submodules over principal ideal domains

A submodule of a torsion-free module over a principal ideal domain is primitive when its
quotient has no torsion. When the quotient is finitely generated, such a submodule is exactly
a direct summand. In particular, an injective homomorphism of finite free abelian groups is
primitive precisely when its image has a complement.

## Main results

* `Submodule.exists_isCompl_iff_isTorsionFree_quotient`: the direct-summand criterion.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.5.
-/

public section

namespace TauCeti

universe u

namespace Submodule

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

/-- A submodule of a torsion-free module over a PID with finitely generated quotient has
torsion-free quotient if and only if it admits a complementary submodule. -/
theorem _root_.Submodule.exists_isCompl_iff_isTorsionFree_quotient
    (S : Submodule R M) [Module.Finite R (M ⧸ S)] :
    (∃ T : Submodule R M, IsCompl S T) ↔ Module.IsTorsionFree R (M ⧸ S) := by
  constructor
  · rintro ⟨T, hT⟩
    have : Module.IsTorsionFree R T :=
      T.subtype_injective.moduleIsTorsionFree T.subtype (fun _ _ => map_smul T.subtype _ _)
    exact ((S.quotientEquivOfIsCompl T hT).injective).moduleIsTorsionFree
      (S.quotientEquivOfIsCompl T hT).toLinearMap (fun _ _ => map_smul _ _ _)
  · intro h
    have : Module.IsTorsionFree R (M ⧸ S) := h
    have : Module.Free R (M ⧸ S) := Module.free_of_finite_type_torsion_free'
    obtain ⟨g, hg⟩ := S.mkQ.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr S.mkQ_surjective)
    let e : M →ₗ[R] M := LinearMap.id - g.comp S.mkQ
    have he : ∀ x, e x ∈ S := by
      intro x
      rw [← S.ker_mkQ, LinearMap.mem_ker]
      have hx : S.mkQ (g (S.mkQ x)) = S.mkQ x := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hg (S.mkQ x)
      simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        map_sub, hx, sub_self]
    let p : M →ₗ[R] S := e.codRestrict S he
    have hp : ∀ x : S, p x = x := by
      intro x
      apply Subtype.ext
      have hx : S.mkQ (x : M) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [S.ker_mkQ]
        exact x.2
      simp [p, e, hx]
    exact ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp⟩

end Submodule

end TauCeti
