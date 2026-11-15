/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Order.SupIndep
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Independent families of submodules and traces

The traces `(I i).comap S.subtype` of an independent family of submodules `I` on a submodule `S`
are independent (`iSupIndep.comap_subtype`). When `⨆ i, U i = W` over a ring, those traces form an
internal direct-sum decomposition of `W`
(`DirectSum.isInternal_comap_subtype_of_iSupIndep_of_iSup_eq`).
-/

public section

/-- The traces of an independent family of submodules on a submodule `S` are independent. -/
theorem iSupIndep.comap_subtype {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S : Submodule R M} {I : ι → Submodule R M} (hI : iSupIndep I) :
    iSupIndep fun i ↦ (I i).comap S.subtype := by
  let e : Submodule R S ≃o Set.Iic S := S.mapIic
  rw [← iSupIndep_map_orderIso_iff e]
  have he : (e ∘ fun i ↦ (I i).comap S.subtype) = fun i ↦
      ⟨I i ⊓ S, Set.mem_Iic.mpr inf_le_right⟩ := by
    funext i
    apply Subtype.ext
    simp only [Function.comp_apply, e, Submodule.coe_mapIic_apply, Submodule.map_comap_subtype]
    rw [inf_comm]
  rw [he]
  exact iSupIndep.of_coe_Iic_comp (hI.mono fun _ ↦ inf_le_left)

/-- If an independent family of submodules `U` has supremum `W`, then its traces
`(U i).comap W.subtype` form an internal direct-sum decomposition of `W`. -/
theorem DirectSum.isInternal_comap_subtype_of_iSupIndep_of_iSup_eq {R M ι : Type*}
    [DecidableEq ι] [Ring R] [AddCommGroup M] [Module R M] {W : Submodule R M}
    {U : ι → Submodule R M} (hU : iSupIndep U) (hsup : ⨆ i, U i = W) :
    DirectSum.IsInternal (fun i ↦ (U i).comap W.subtype) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hU.comap_subtype ?_
  have hsup' : ⨆ i ∈ (Set.univ : Set ι), U i = W := by simpa using hsup
  have htop : ⨆ i ∈ (Set.univ : Set ι), (U i).comap W.subtype = ⊤ :=
    hsup' ▸ Submodule.biSup_comap_subtype_eq_top (Set.univ : Set ι) U
  simpa using htop
