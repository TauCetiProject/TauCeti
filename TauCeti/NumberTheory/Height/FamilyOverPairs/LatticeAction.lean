/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
public import TauCeti.RepresentationTheory.Intertwining
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RepresentationTheory.IntegralAction

/-!
# Integral combinations of translates under equivariant lifts

For a prime-adic embedding of `ℂ`, algebraic integers act on any submodule over the local
integer ring. An equivariant lift therefore carries a combination of translates with algebraic
integer coefficients into a stable integral submodule whenever the original lifted vector was
integral. One can scale the lifted vector before testing integrality.

This is the integral-action argument in `New.Data.goodProjTranslate_mem_integralForms`,
`grh/src/New/UpperBound/Size/ArchimedeanSize.lean` of lsernau/grh-lean at revision `72fead1`.
-/

public section

namespace Representation.IntertwiningMap

/-- If `c • f x` belongs to a stable local integral submodule `L`, then so does
`c • f (ρ.asAlgebraHom a (ρ s x))` for an algebraic-integer combination `a` of translates.
In particular `a` may be a projection multiplied by a scalar that clears its denominators. -/
theorem smul_apply_asAlgebraHom_mem_of_isIntegral_coeff
    {G V W : Type*} [Monoid G] [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : IntertwiningMap ρ σ)
    {ι : TauCeti.PrimePadicIso} (L : Submodule ι.integers W)
    (hL : ∀ g, Set.MapsTo (σ g) L L) {a : MonoidAlgebra ℂ G}
    (ha : ∀ g ∈ a.coeff.support, IsIntegral ℤ (a.coeff g)) (s : G) {c : ℂ} {x : V}
    (hx : c • f x ∈ L) : c • f (ρ.asAlgebraHom a (ρ s x)) ∈ L := by
  rw [f.apply_asAlgebraHom, f.isIntertwining, ← map_smul, ← map_smul]
  refine σ.asAlgebraHom_apply_mem_of_coeff_mem (S := ι.integers.toSubsemiring) L ?_ ?_
  · intro g hg
    exact TauCeti.PrimePadicIso.mem_integers.mpr
      (IsUltrametricDist.norm_le_one_of_isIntegral (fun _ _ _ ↦ norm_pow _ _)
        ((ha g hg).map ι.iso.toRingHom.toIntAlgHom))
  · exact fun g _ ↦ hL g (hL s hx)

end Representation.IntertwiningMap
