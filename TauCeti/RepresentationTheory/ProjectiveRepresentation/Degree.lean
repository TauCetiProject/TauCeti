/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Degree.Center
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.CommonExtension

/-!
# The degree of an irreducible projective representation divides the order of the group

Let `Q` be a finite group and `k` an algebraically closed field of characteristic zero. If a
projective representation `ρ : Q → V ≃ₗ[k] V`, with any factor set, acts on a nonzero space `V`
whose only subspaces stable under every `ρ g` are `0` and `V`, then `dim V` divides `|Q|`
(**Schur's theorem**; Isaacs, Chapter 11). Finite-dimensionality is not assumed: it follows from
irreducibility.

The proof lifts `ρ` to an ordinary representation of the finite central extension `E` of `Q`
through which every projective representation of `Q` linearizes
(`TauCeti.IsProjectiveRep.exists_commonExtension_linearization`). The lift agrees with `ρ` up to
scalars, so it has the same stable subspaces and is irreducible. The kernel of `E → Q` is central
(`TauCeti.projectiveLiftingFactorSet_ker_le_center`) with index `|Q|`, so the degree divides `|Q|`
by `Representation.finrank_dvd_index_of_le_center`.

## Main results

* `TauCeti.isIrreducible_of_apply_eq_smul`: a representation agreeing up to scalars with an
  irreducible projective representation is irreducible.
* `TauCeti.IsProjectiveRep.finrank_dvd_card`: Schur's theorem.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 11.
-/

public section

open Module

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **A representation agreeing up to scalars with an irreducible projective representation is
irreducible.** If `σ x` acts as a nonzero scalar multiple of `ρ (f x)` for a surjective `f`, then a
subspace stable under every `σ x` is stable under every `ρ g`, so it is `0` or the whole space. -/
theorem isIrreducible_of_apply_eq_smul [Nontrivial V] {E : Type*} [Monoid E] {f : E →* G}
    (hf : Function.Surjective f) {σ : Representation k E V} {ρ : G → V ≃ₗ[k] V} {c : E → kˣ}
    (hσ : ∀ x v, σ x v = (c x : k) • ρ (f x) v)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    σ.IsIrreducible := by
  refine ⟨fun T => ?_⟩
  have hT : ∀ g, ∀ w ∈ T.toSubmodule, ρ g w ∈ T.toSubmodule := fun g w hw => by
    obtain ⟨x, rfl⟩ := hf g
    have h := T.apply_mem_toSubmodule x hw
    rw [hσ] at h
    simpa using T.toSubmodule.smul_mem ((c x)⁻¹ : kˣ) h
  refine (hirr _ hT).imp (fun h => ?_) fun h => ?_
  · exact Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_top.symm)

variable [IsAlgClosed k] [CharZero k] [Finite G]

/-- **Schur's theorem on projective representations.** Over an algebraically closed field of
characteristic zero, the dimension of a nonzero projective representation of a finite group `G`,
with any factor set, whose only stable subspaces are `0` and the whole space, divides `|G|`. -/
theorem IsProjectiveRep.finrank_dvd_card [Nontrivial V]
    {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ} (hρ : IsProjectiveRep ρ α)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    finrank k V ∣ Nat.card G := by
  obtain ⟨π, c, -, hπ⟩ := hρ.exists_commonExtension_linearization
  let σ : Representation k (projectiveLiftingFactorSet k G).Extension V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π
  have : σ.IsIrreducible :=
    isIrreducible_of_apply_eq_smul (FactorSet.rightHom_surjective _) (c := c)
      (fun x v => by simp [σ, hπ]) hirr
  have h := Representation.finrank_dvd_index_of_le_center σ _
    (projectiveLiftingFactorSet_ker_le_center k G)
  rwa [Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (FactorSet.rightHom_surjective (projectiveLiftingFactorSet k G)),
    Subgroup.card_top] at h

end TauCeti
