/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType

/-!
# Hecke characters on principal finite ideles

A Hecke character is trivial on the full diagonal idele. Thus its value on the finite part of
that idele is the inverse of the product of its archimedean components. This compares the
principal values of a finite idele character with its infinity type. The proof is extracted
from `HeckeCharacter.idealCharacter_apply_toPrincipalIdeal_eq_prod_inv_mul_prod_inv`.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields.HeckeCharacter

/-- The value of a Hecke character on the finite part of the diagonal idele of `x` is the inverse
of the product of its infinite components at `x`. This does not require `x` to be a global unit
or to satisfy a congruence condition. -/
theorem apply_ofFiniteIdele_unitEmbedding {K : Type*} [Field K] [NumberField K]
    (χ : HeckeCharacter K) (x : Kˣ) :
    χ (IdeleGroup.ofFiniteIdele (𝓞 K) K (FiniteAdeleRing.unitEmbedding (𝓞 K) K x)) =
      (∏ w : InfinitePlace K,
        χ.infiniteComponent w (Units.map (algebraMap K w.Completion).toMonoidHom x))⁻¹ := by
  have hprincipal :
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x) : IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  have hsplit := congrArg (fun z : IdeleGroup (𝓞 K) K ↦ χ (QuotientGroup.mk z))
    (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (IdeleGroup.unitEmbedding (𝓞 K) K x))
  rw [QuotientGroup.mk_mul, map_mul, hprincipal, map_one,
    QuotientGroup.mk_prod, map_prod] at hsplit
  simp only [IdeleGroup.toFiniteIdele_unitEmbedding,
    ← IdeleClassGroup.ofCompletion_apply, ← infiniteComponent_apply,
    InfinitePlace.ideleInfiniteCoord_unitEmbedding] at hsplit
  exact eq_inv_of_mul_eq_one_right hsplit

end TauCeti.GlobalNumberFields.HeckeCharacter
