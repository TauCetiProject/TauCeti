/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.ResiduallyP
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Closed
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
import TauCeti.GroupTheory.FreeGroup.LowerCentralSeries

/-!
# The discrete free group embeds in the free pro-`p` group

For a prime `p`, the canonical homomorphism `FreeGroup X →* freeProP p X` is injective. This is
the residual `p`-finiteness of free groups, `FreeGroup.exists_normal_isPGroup_quotient_notMem`,
read through the universal property of `freeProP p X`: a finite `p`-group quotient of
`FreeGroup X` is a discrete pro-`p` group, so the quotient map factors through `freeProP p X`.
In particular the generators of the free pro-`p` group satisfy no relation of the discrete free
group.

Through this embedding, the free pro-`p` group inherits the non-nilpotency of free groups of rank
at least two (`FreeGroup.lowerCentralSeries_ne_bot`): in rank at least two no term `γ_n` of the
lower central series of `freeProP p X` is trivial, and neither is any term of its closed lower
central series, which contains it. So although the closed lower central series of a pro-`p` group
has trivial intersection (`TauCeti.IsProP.iInf_closedLowerCentralSeries_eq_bot`), for a free
pro-`p` group of rank at least two it never reaches `⊥` at a finite stage.

## Main results

* `TauCeti.freeProP.fromFreeGroup_injective`: the discrete free group injects into the free
  pro-`p` group.
* `TauCeti.freeProP.lowerCentralSeries_ne_bot`, `TauCeti.freeProP.closedLowerCentralSeries_ne_bot`:
  in rank at least two, no term of the lower central series or of the closed lower central series
  of the free pro-`p` group is trivial.
* `TauCeti.freeProP.not_isNilpotent`: a free pro-`p` group of rank at least two is not nilpotent.
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

/-- **The lower central series of a free pro-`p` group of rank at least two never vanishes.** The
discrete free group embeds in `freeProP p X`, and the image of each term of its lower central
series, which is never trivial, lies in the corresponding term for `freeProP p X`. -/
theorem lowerCentralSeries_ne_bot [Nontrivial X] (n : ℕ) :
    (⊤ : Subgroup (freeProP p X)).lowerCentralSeries n ≠ ⊥ := by
  intro h
  refine FreeGroup.lowerCentralSeries_ne_bot (X := X) n ?_
  rw [← Subgroup.map_eq_bot_iff_of_injective _ (fromFreeGroup_injective (p := p)), eq_bot_iff,
    ← h, Subgroup.map_lowerCentralSeries]
  exact Subgroup.lowerCentralSeries_mono n le_top

/-- **Free pro-`p` groups of rank at least two are not nilpotent.** -/
theorem not_isNilpotent [Nontrivial X] : ¬ Group.IsNilpotent (freeProP p X) := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  rintro ⟨n, hn⟩
  exact lowerCentralSeries_ne_bot (p := p) n hn

/-- **The closed lower central series of a free pro-`p` group of rank at least two never
vanishes.** Each term `γ_n` contains the corresponding term of the lower central series of the
underlying abstract group, which is nontrivial by `TauCeti.freeProP.lowerCentralSeries_ne_bot`. -/
theorem closedLowerCentralSeries_ne_bot [Nontrivial X] (n : ℕ) :
    closedLowerCentralSeries (freeProP p X) n ≠ ⊥ := by
  intro h
  refine lowerCentralSeries_ne_bot (p := p) (X := X) n ?_
  rw [eq_bot_iff, ← h, closedLowerCentralSeries_eq_topologicalClosure]
  exact Subgroup.le_topologicalClosure _

end freeProP

end TauCeti
