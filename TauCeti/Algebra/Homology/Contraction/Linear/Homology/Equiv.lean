/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Homology.SquareZero

/-!
# The homology of a contraction

A contraction of a module `M` with a square-zero endomorphism `dM` onto `(N, dN)` is a chain
homotopy equivalence: its projection retracts its inclusion, and its homotopy shows that the
inclusion followed by the projection is homotopic to the identity. So the inclusion induces an
isomorphism from the homology of `dN` to the homology of `dM`, with inverse induced by the
projection (`TauCeti.LinearContraction.homologyEquiv`). This is how a contraction computes the
homology of `dM` from the smaller module `N`, for instance after cancelling generators by Gaussian
elimination.

## Main definitions

* `TauCeti.LinearContraction.homologyEquiv`: the isomorphism of homologies induced by the
  inclusion of a contraction.

## Main results

* `TauCeti.LinearContraction.mem_range_of_incl_mem_range` and
  `TauCeti.LinearContraction.exists_mem_ker_sub_incl_mem_range`: the inclusion detects boundaries,
  and every cycle of `dM` is the inclusion of a cycle of `dN` up to a boundary, without any
  square-zero hypothesis.
-/

public section

namespace TauCeti.LinearContraction

section Semiring

variable {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

/-- An element of the retract whose inclusion is a boundary of `dM` is a boundary of `dN`. -/
theorem mem_range_of_incl_mem_range (c : LinearContraction dM dN) {y : N}
    (hy : c.incl y ∈ LinearMap.range dM) : y ∈ LinearMap.range dN := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨c.proj x, by rw [← c.proj_dM_apply, hx, c.proj_incl_apply]⟩

/-- Every cycle of `dM` differs from the inclusion of a cycle of `dN` by a boundary of `dM`. -/
theorem exists_mem_ker_sub_incl_mem_range (c : LinearContraction dM dN) {x : M}
    (hx : x ∈ LinearMap.ker dM) : ∃ y ∈ LinearMap.ker dN, x - c.incl y ∈ LinearMap.range dM := by
  refine ⟨c.proj x, ?_, ?_⟩
  · rw [LinearMap.mem_ker, ← c.proj_dM_apply, LinearMap.mem_ker.1 hx, map_zero]
  · rw [c.incl_proj_apply, LinearMap.mem_ker.1 hx, map_zero, sub_zero, sub_sub_cancel]
    exact ⟨c.homotopy x, rfl⟩

end Semiring

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {dM : Module.End R M} {dN : Module.End R N}

/-- The inclusion of a contraction of `(M, dM)` onto `(N, dN)`, for square-zero `dM`, induces an
isomorphism from the homology of `dN` to the homology of `dM`, inverse to the map induced by the
projection. -/
noncomputable def homologyEquiv (c : LinearContraction dM dN) (hdM : dM ∘ₗ dM = 0) :
    dN.homology (c.dN_comp_dN_eq_zero hdM) ≃ₗ[R] dM.homology hdM :=
  LinearEquiv.ofLinearMap (LinearMap.homologyMap c.incl _ hdM c.dM_comp_incl.symm)
    (LinearMap.homologyMap c.proj hdM _ c.proj_comp_dM)
    (by
      have hfg :
          c.incl ∘ₗ c.proj - LinearMap.id = dM ∘ₗ (-c.homotopy) + (-c.homotopy) ∘ₗ dM := by
        rw [c.incl_comp_proj, LinearMap.comp_neg, LinearMap.neg_comp]
        abel
      rw [LinearMap.homologyMap_comp_homologyMap,
        LinearMap.homologyMap_eq_of_sub_eq _ LinearMap.id _ _ _ _ (by simp) hfg,
        LinearMap.homologyMap_id])
    (by
      rw [LinearMap.homologyMap_comp_homologyMap]
      simp only [proj_comp_incl, LinearMap.homologyMap_id])

/-- The isomorphism of homologies sends the class of a cycle `z` of `dN` to the class of its
inclusion. -/
@[simp]
theorem homologyEquiv_mk (c : LinearContraction dM dN) (hdM : dM ∘ₗ dM = 0)
    (z : LinearMap.ker dN) :
    c.homologyEquiv hdM (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨c.incl z, LinearMap.map_mem_ker_of_comp_eq (d := dN) (e := dM)
        c.incl c.dM_comp_incl.symm z.property⟩ :=
  LinearMap.homologyMap_mk c.incl _ hdM c.dM_comp_incl.symm z

/-- The inverse isomorphism of homologies sends the class of a cycle `z` of `dM` to the class of
its projection. -/
@[simp]
theorem homologyEquiv_symm_mk (c : LinearContraction dM dN) (hdM : dM ∘ₗ dM = 0)
    (z : LinearMap.ker dM) :
    (c.homologyEquiv hdM).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨c.proj z, LinearMap.map_mem_ker_of_comp_eq (d := dM) (e := dN)
        c.proj c.proj_comp_dM z.property⟩ :=
  LinearMap.homologyMap_mk c.proj hdM _ c.proj_comp_dM z

end TauCeti.LinearContraction
