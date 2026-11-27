/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import TauCeti.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis
import TauCeti.LinearAlgebra.SesquilinearForm.DualSubmodule

/-!
# Indices of dual lattices

Let `R` be a principal ideal domain with fraction field `K`, let `V` be a `K`-vector space and `B`
a nondegenerate bilinear form on `V`. The dual of an `R`-submodule `N` of `V` is
`N^∨ = {x | B x y ∈ R for all y ∈ N}`, Mathlib's `LinearMap.BilinForm.dualSubmodule`. Duality
reverses inclusions, and for full lattices it preserves indices: `[N^∨ : N^∨ ∩ N'^∨]` is
`[N' : N ∩ N']`, so `[N^∨ : N'^∨] = [N' : N]` when `N ≤ N'`
(`LinearMap.BilinForm.relIndex_dualSubmodule`). As in Mathlib's `AddSubgroup.relIndex`, an infinite
index is read as `0`; over the ring of integers of a nonarchimedean local field all these indices
are finite, and the identity is what makes the product `vol(N) vol(N^∨)` of the Haar volumes of a
lattice and of its dual independent of the lattice.

For `N ≤ N'` the proof uses a Smith normal form: there is a basis `e` of `V` with `N' = span R e`
and `N = span R (a • e)` for nonzero `aᵢ ∈ R`. If `f` is the basis dual to `e` for `B`, the duals
are `N'^∨ = span R f` and `N^∨ = span R (a⁻¹ • f)`, so the linear automorphism of `V` with
`eᵢ ↦ aᵢ⁻¹ • fᵢ` maps `N'` onto `N^∨` and `N` onto `N'^∨`. In general `N^∨ ∩ N'^∨` is the dual of
`N ⊔ N'`, which reduces the identity to the inclusion `N ≤ N ⊔ N'`.

## Main results

* `LinearMap.BilinForm.relIndex_dualSubmodule`: `[N^∨ : N^∨ ∩ N'^∨] = [N' : N ∩ N']` for full
  lattices `N`, `N'` and a nondegenerate form.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter II, §5.
-/

public section

open Module

namespace LinearMap.BilinForm

variable {R K V : Type*} [CommRing R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The case `N ≤ N'` of `LinearMap.BilinForm.relIndex_dualSubmodule`: a Smith normal form of `N`
in `N'` gives an automorphism of `V` mapping `N'` onto `N^∨` and `N` onto `N'^∨`. -/
private theorem relIndex_dualSubmodule_of_le (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) {N N' : Submodule R V} [N.IsFullLattice K] [N'.IsFullLattice K]
    (h : N ≤ N') :
    (B.dualSubmodule N').toAddSubgroup.relIndex (B.dualSubmodule N).toAddSubgroup =
      N.toAddSubgroup.relIndex N'.toAddSubgroup := by
  classical
  have := IsDomain.of_faithfulSMul R K
  have := Submodule.IsLattice.free K N'
  have := Submodule.IsLattice.finite K N'
  -- A Smith normal form of `N` inside `N'`: bases `b` of `N'` and `a • b` of `N`.
  have hrank : finrank R (N.comap N'.subtype) = finrank R N' := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq,
      Submodule.finrank_eq_finrank K N Submodule.IsFullLattice.span_eq_top,
      Submodule.finrank_eq_finrank K N' Submodule.IsFullLattice.span_eq_top]
  obtain ⟨b, a, ab, hab⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Module.Free.chooseBasis R N') hrank
  have hw (i : _) : IsUnit (algebraMap R K (a i)) := by
    refine Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 fun ha ↦
      ab.ne_zero i (Subtype.ext ?_))
    rw [hab, ha, zero_smul, Submodule.coe_zero]
  -- `e` is a `K`-basis of `V` spanning `N'`, and `e' = a • e` spans `N`.
  set e := b.extendOfIsFullLattice K
  set e' := e.isUnitSMul hw
  have hN' : Submodule.span R (Set.range e) = N' := b.span_range_extendOfIsFullLattice
  have hN : Submodule.span R (Set.range e') = N := by
    have he' : ⇑e' = (ab.map (Submodule.comapSubtypeEquivOfLe h)).extendOfIsFullLattice K := by
      funext i
      simp only [e', e, Basis.isUnitSMul_apply, Basis.extendOfIsFullLattice_apply,
        Basis.map_apply, Submodule.comapSubtypeEquivOfLe_apply_coe, hab, Submodule.coe_smul,
        algebraMap_smul]
    rw [he', Basis.span_range_extendOfIsFullLattice]
  -- The automorphism `T` of `V` with `T eᵢ = f'ᵢ`, for `f'` the basis dual to `e'`, maps `N'`
  -- onto `N^∨` and, since `f' = a⁻¹ • f` for the basis `f` dual to `e`, maps `N` onto `N'^∨`.
  set T := (e.equiv (B.dualBasis hB e') (Equiv.refl _)).restrictScalars R
  have hTN' : N'.map (T : V →ₗ[R] V) = B.dualSubmodule N := by
    rw [← hN', ← hN, Submodule.map_span, ← Set.range_comp, B.dualSubmodule_span_of_basis hB e']
    congr 2
    funext i
    simp [T, Basis.equiv_apply]
  have hTN : N.map (T : V →ₗ[R] V) = B.dualSubmodule N' := by
    rw [← hN', ← hN, Submodule.map_span, ← Set.range_comp, B.dualSubmodule_span_of_basis hB e]
    congr 2
    funext i
    simp only [Function.comp_apply, T, e', LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
      Basis.isUnitSMul_apply, map_smul, Basis.equiv_apply, Equiv.refl_apply,
      e.dualBasis_isUnitSMul_apply B hB hw, smul_smul]
    rw [mul_inv_cancel₀ (hw i).ne_zero, one_smul]
  rw [← hTN, ← hTN', Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ T.injective]

/-- **Duality preserves the index of full lattices.** For full lattices `N`, `N'` and a
nondegenerate bilinear form `B` over the fraction field of a principal ideal domain,
`[N^∨ : N^∨ ∩ N'^∨] = [N' : N ∩ N']`, where `N^∨ = B.dualSubmodule N`. In particular
`[N^∨ : N'^∨] = [N' : N]` when `N ≤ N'`. Infinite indices are read as `0`. -/
theorem relIndex_dualSubmodule (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N N' : Submodule R V) [N.IsFullLattice K] [N'.IsFullLattice K] :
    (B.dualSubmodule N').toAddSubgroup.relIndex (B.dualSubmodule N).toAddSubgroup =
      N.toAddSubgroup.relIndex N'.toAddSubgroup := by
  have := Submodule.IsFullLattice.sup K N N'
  -- `N'^∨ ∩ N^∨` is the dual of `N ⊔ N'`, which contains `N` with index `[N' : N ∩ N']`.
  have hσ (r : R) : RingHom.id K (algebraMap R K r) ∈ (1 : Submodule R K) :=
    Submodule.mem_one.2 ⟨r, rfl⟩
  have hsup : B.dualSubmodule (N ⊔ N') = B.dualSubmodule N' ⊓ B.dualSubmodule N := by
    simp only [← LinearMap.dualSubmodule_eq_bilinFormDualSubmodule B hσ,
      LinearMap.dualSubmodule_sup, inf_comm]
  have hinf : (B.dualSubmodule N').toAddSubgroup ⊓ (B.dualSubmodule N).toAddSubgroup =
      (B.dualSubmodule (N ⊔ N')).toAddSubgroup := by
    rw [hsup]
    rfl
  rw [← AddSubgroup.inf_relIndex_right, hinf, relIndex_dualSubmodule_of_le B hB le_sup_left,
    Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left]

end LinearMap.BilinForm
