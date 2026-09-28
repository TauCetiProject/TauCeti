/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Primitive submodules of finite free abelian groups

A submodule of a finitely generated torsion-free abelian group is primitive when its quotient
has no torsion.
Such a submodule is exactly a direct summand. Consequently an injective homomorphism of
finite free abelian groups is primitive precisely when its image has a complement. This
criterion lets primitive lattice embeddings be handled through an actual direct-sum
decomposition of their underlying integral modules.

The forward implication uses that a finitely generated torsion-free module over `ℤ` is free,
and that free modules are projective. The latter splits the quotient map.

## Main results

* `Submodule.exists_isCompl_iff_quotient_torsionFree`: the direct-summand criterion.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.5.
-/

public section

namespace TauCeti

universe u

namespace Submodule

variable {M : Type u} [AddCommGroup M] [Module.Finite ℤ M]
  [Module.IsTorsionFree ℤ M]

/-- A submodule of a finitely generated torsion-free abelian group has torsion-free quotient
if and only if it admits a complementary submodule. -/
theorem _root_.Submodule.exists_isCompl_iff_quotient_torsionFree (S : Submodule ℤ M) :
    (∃ T : Submodule ℤ M, IsCompl S T) ↔ Module.IsTorsionFree ℤ (M ⧸ S) := by
  constructor
  · rintro ⟨T, hT⟩
    have : Module.IsTorsionFree ℤ T :=
      T.subtype_injective.moduleIsTorsionFree T.subtype (fun _ _ => map_smul T.subtype _ _)
    exact ((S.quotientEquivOfIsCompl T hT).injective).moduleIsTorsionFree
      (S.quotientEquivOfIsCompl T hT).toLinearMap (fun _ _ => map_smul _ _ _)
  · intro h
    have : Module.IsTorsionFree ℤ (M ⧸ S) := h
    have : Module.Free ℤ (M ⧸ S) := Module.free_of_finite_type_torsion_free'
    obtain ⟨g, hg⟩ := S.mkQ.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr S.mkQ_surjective)
    let e : M →ₗ[ℤ] M := LinearMap.id - g.comp S.mkQ
    have he : ∀ x, e x ∈ S := by
      intro x
      rw [← S.ker_mkQ, LinearMap.mem_ker]
      have hx : S.mkQ (g (S.mkQ x)) = S.mkQ x := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hg (S.mkQ x)
      simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        map_sub, hx, sub_self]
    let p : M →ₗ[ℤ] S := e.codRestrict S he
    have hp : ∀ x : S, p x = x := by
      intro x
      apply Subtype.ext
      have hx : S.mkQ (x : M) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [S.ker_mkQ]
        exact x.2
      simp [p, e, hx]
    have hker : LinearMap.ker p = LinearMap.range g := by
      ext x
      constructor
      · intro hx
        have hex : e x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        refine ⟨S.mkQ x, ?_⟩
        have : x - g (S.mkQ x) = 0 := hex
        exact (sub_eq_zero.mp this).symm
      · rintro ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        have hy : S.mkQ (g y) = y := by
          simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun hg y
        simp [p, e, hy]
    refine ⟨LinearMap.range g, ?_⟩
    rw [← hker]
    exact LinearMap.isCompl_of_proj hp

end Submodule

end TauCeti
