/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.ResiduallyP
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP

/-!
# The discrete free group embeds in the free pro-`p` group

For a prime `p`, the canonical homomorphism `FreeGroup X →* freeProP p X` is injective. This is
the residual `p`-finiteness of free groups, `FreeGroup.exists_normal_isPGroup_quotient_notMem`,
read through the universal property of `freeProP p X`: a finite `p`-group quotient of
`FreeGroup X` is a discrete pro-`p` group, so the quotient map factors through `freeProP p X`.
In particular the generators of the free pro-`p` group satisfy no relation of the discrete free
group.

## Main results

* `TauCeti.freeProP.fromFreeGroup_injective`: the discrete free group injects into the free
  pro-`p` group.
-/

public section

namespace TauCeti

namespace freeProP

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-- **Free groups are residually `p`.** The canonical homomorphism from the discrete free group
on `X` to the free pro-`p` group on `X` is injective. -/
theorem fromFreeGroup_injective : Function.Injective (fromFreeGroup p X) := by
  refine (injective_iff_map_eq_one _).2 fun w hw ↦ ?_
  by_contra hne
  obtain ⟨N, _, _, hpN, hwN⟩ := FreeGroup.exists_normal_isPGroup_quotient_notMem (p := p) hne
  let : TopologicalSpace (FreeGroup X ⧸ N) := ⊥
  have : DiscreteTopology (FreeGroup X ⧸ N) := ⟨rfl⟩
  let φ := lift hpN.isProP fun x : X ↦ (FreeGroup.of x : FreeGroup X ⧸ N)
  have hφ : (φ : freeProP p X →* FreeGroup X ⧸ N).comp (fromFreeGroup p X) =
      QuotientGroup.mk' N :=
    FreeGroup.ext_hom _ _ fun x ↦ by simp [φ]
  apply hwN
  rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, ← hφ, MonoidHom.comp_apply,
    hw, map_one]

end freeProP

end TauCeti
