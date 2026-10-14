/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.Algebra.Coalgebra.Basic

/-!
# Recognizing coalgebras spanned by group-like elements

If every finite-dimensional comodule is spanned by its group-like weight spaces, then the
coalgebra is spanned by its group-like elements. Indeed, finite-dimensional subcomodules
exhaust the regular comodule, and a weight vector there is a counit multiple of its weight.

This extracts the regular-comodule argument of
`TauCeti.HopfAlgebra.groupLikeSetSpan_eq_top_of_isLinearlyReductive_of_isSolvable`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

namespace TauCeti.Subcoalgebra

universe u v

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A coalgebra is spanned by group-like elements if every finite-dimensional comodule is
spanned by its group-like weight spaces. No finite-dimensionality of the coalgebra is needed. -/
theorem groupLikeSetSpan_eq_top_of_finite_weightSpaces_span
    (hspan : ∀ M : FGComoduleCat.{u, v, v} k C,
      ⨆ c : GroupLike k C, c.weightSpace (M := M) = ⊤) :
    groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤ := by
  rw [groupLikeSetSpan_eq_top_iff_span_eq_top]
  refine eq_top_iff.mpr fun c _ ↦ ?_
  obtain ⟨N, hNfin, hN⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := C) c
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  -- A subcomodule and its underlying submodule have the same subtype carrier.
  have _ : Module.Finite k N := hNfin
  have hle : (⨆ g : GroupLike k C, g.weightSpace (M := N)) ≤
      (Submodule.span k (Set.range (GroupLike.val (R := k) (A := C)))).comap
        N.subtype.toLinearMap := by
    refine iSup_le fun g n hn ↦ ?_
    have hw := N.subtype.map_mem_groupLikeWeightSpace hn
    rw [GroupLike.mem_weightSpace, Comodule.instSelf_coact] at hw
    rw [Submodule.mem_comap, Comodule.Hom.coe_toLinearMap,
      Coalgebra.eq_counit_smul_of_comul_eq_tmul hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self g))
  have hmem := hle ((hspan (FGComoduleCat.of (R := k) (C := C) N)) ▸
    (Submodule.mem_top : (⟨c, hN⟩ : N) ∈ ⊤))
  simpa only [Submodule.mem_comap, Subcomodule.subtype_toLinearMap,
    SMulMemClass.subtype_apply] using hmem

end TauCeti.Subcoalgebra
