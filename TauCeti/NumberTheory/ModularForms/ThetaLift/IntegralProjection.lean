/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RepresentationTheory.GroupAlgebra.IntegralAction
import TauCeti.RepresentationTheory.Intertwining

/-!
# Prime-adic integrality after a scaled projection

In a theta lift equivariant for a finite group, one can project a translate before lifting
without losing prime-adic integrality, provided the group order clears the denominators of the
projector's coefficients. The scalar used to normalize the lift need not itself be integral:
it is the *scaled lift* that must be integral.

This is the integrality argument in `New.Data.goodProjTranslate_mem_integralForms` in
`grh/src/New/UpperBound/Size/ArchimedeanSize.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open TauCeti

namespace Representation.IntertwiningMap

/-- Suppose the coefficients of `|G| • e` are algebraic integers and the local integral
submodule is stable under the target action. If `c • T v` is integral at `ι`, then so is the
lift of `c` times `|G| • e` applied to any translate of `v`. Neither integrality of `v` nor
integrality of `c` is required. The result also applies to operators `e` that are not projectors. -/
theorem apply_scaled_projection_mem_of_isIntegral_coeff {G V W : Type*} [Monoid G] [Fintype G]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (T : IntertwiningMap ρ σ)
    (ι : PrimePadicIso) (L : Submodule ι.integers W) {e : MonoidAlgebra ℂ G}
    (he : ∀ g : G, IsIntegral ℤ (((Fintype.card G : ℂ) • e).coeff g))
    (hL : ∀ g : G, Set.MapsTo (σ g) L L) {c : ℂ} {v : V} (hv : c • T v ∈ L) (s : G) :
    T (c • ρ.asAlgebraHom ((Fintype.card G : ℂ) • e) (ρ s v)) ∈ L := by
  rw [map_smul, T.apply_asAlgebraHom, T.isIntertwining]
  rw [← map_smul, ← map_smul]
  refine σ.asAlgebraHom_mem_of_coeff_mem (S := ι.integers.toSubsemiring) L ?_ ?_
  · intro g _
    exact PrimePadicIso.mem_integers.mpr <|
      IsUltrametricDist.norm_le_one_of_isIntegral (fun _ _ _ ↦ norm_pow _ _)
        (he g |>.map ι.iso.toRingHom.toIntAlgHom)
  · intro g _
    exact hL g (hL s hv)

end Representation.IntertwiningMap
