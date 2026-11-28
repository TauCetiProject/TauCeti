/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.Doubling.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Isotropic graphs in an anisotropic double

For the difference of two copies of an anisotropic form, both coordinate projections of an
isotropic subspace are injective. At half the ambient dimension, they exhibit the subspace as
the graph of an isometry.
-/

public section

open Module

namespace Submodule

/-- An isotropic subspace of the double of an anisotropic form, of dimension at least that of
one factor, is the graph of a unique isometry of the form. -/
theorem existsUnique_isometry_graph_eq_of_le_orthogonalBilin_doubled {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {σ : K →+* K}
    {B : V →ₛₗ[σ] V →ₗ[K] K} (L : Submodule K (V × V))
    (hB : ∀ x : V, B x x = 0 → x = 0) (hL : L ≤ L.orthogonalBilin B.doubled)
    (hdim : finrank K V ≤ finrank K L) :
    ∃! g : B.isometryGroup, (g.val : V →ₗ[K] V).graph = L := by
  let p := (LinearMap.fst K V V).comp L.subtype
  let q := (LinearMap.snd K V V).comp L.subtype
  have hdiag (z : L) : B (p z) (p z) = B (q z) (q z) :=
    sub_eq_zero.mp (by
      simpa only [p, q, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        coe_subtype, LinearMap.doubled_apply] using hL z.property _ z.property)
  have hproj (f : L →ₗ[K] V) (hf : Function.Injective f) : Function.Bijective f := by
    refine ⟨hf, LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
      ((Submodule.finrank_le _).antisymm ?_))⟩
    rwa [LinearMap.finrank_range_of_inj hf]
  have hp : Function.Bijective p := hproj p <| (injective_iff_map_eq_zero p).2 fun z hz ↦ by
    have hqz : q z = 0 := hB _ (by simpa [hz] using (hdiag z).symm)
    exact Subtype.ext (Prod.ext hz hqz)
  have hq : Function.Bijective q := hproj q <| (injective_iff_map_eq_zero q).2 fun z hz ↦ by
    have hpz : p z = 0 := hB _ (by simpa [hz] using hdiag z)
    exact Subtype.ext (Prod.ext hpz hz)
  obtain ⟨g, hg⟩ := L.exists_equiv_eq_graph hp hq
  have hgi : g ∈ B.isometryGroup := B.mem_isometryGroup_iff.mpr
    ((B.graph_le_orthogonalBilin_doubled_iff g.toLinearMap).1 (by simpa only [← hg] using hL))
  refine ⟨⟨g, hgi⟩, hg.symm, fun v hv ↦ ?_⟩
  apply Subtype.ext
  ext x
  have hx : (x, v.val x) ∈ v.val.toLinearMap.graph := by simp
  exact (LinearMap.mem_graph_iff _ _).mp (hg ▸ hv ▸ hx)

end Submodule
