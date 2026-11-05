/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic

/-!
# Centralizers under closed immersions

A closed immersion of affine groups detects commutation after every extension of the value
algebra. Consequently it identifies the schematic centralizer of a diagonalizable subgroup
with the inverse image of its centralizer in the ambient group. The point criterion below
allows centralizers in matrix groups to be computed without reducedness assumptions.
-/

public section

namespace BialgHom

open TauCeti WithConv

universe u v w x y

variable {R : Type u} {H : Type v} {K : Type w} {X : Type x}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [CommRing K] [HopfAlgebra R K] [CommGroup X]

/-- A closed immersion detects membership in the schematic centralizer of a diagonalizable
subgroup, over every value algebra. Here `ρ` is the surjective coordinate map of the immersion. -/
theorem centralizerHopfIdeal_comp_le_ker_iff
    (ρ : H →ₐc[R] K) (hρ : Function.Surjective ρ)
    (π : K →ₐc[R] MonoidAlgebra R X)
    {A : Type y} [CommRing A] [Algebra R A] (g : WithConv (K →ₐ[R] A)) :
    (centralizerHopfIdeal (π.comp ρ)).toIdeal ≤
        RingHom.ker (mapDomain ρ g).ofConv ↔
      (centralizerHopfIdeal π).toIdeal ≤ RingHom.ker g.ofConv := by
  rw [centralizerHopfIdeal_le_ker_iff_commute_of_injective _ _ (AlgHom.id R _)
      Function.injective_id,
    centralizerHopfIdeal_le_ker_iff_commute_of_injective _ _ (AlgHom.id R _)
      Function.injective_id]
  simp only [AlgHom.id_comp, mapDomain_comp, MonoidHom.comp_apply]
  rw [← MonoidHom.comp_apply, ← mapValue_mapDomain, MonoidHom.comp_apply]
  exact commute_map_iff (mapDomain_injective_of_surjective ρ hρ)

end BialgHom
