/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology

/-!
# The inclusion of continuous framed fields of different Sobolev orders

For `s ≤ s'`, a continuous field of the affine Sobolev space `A_m^(s') = x_m + H^(s')` is a
continuous field of `A_m^s` (`TauCeti.Vortex.SobolevFieldSpace.inclusion`), since
`A_m^(s') ⊆ A_m^s` (`TauCeti.Vortex.framedFieldSpace_mono`). In the coordinates of `x - x_m` it is
the inclusion `H^(s') ⊆ H^s` of Bessel-potential spaces
(`TauCeti.Vortex.SobolevFieldSpace.subRef_inclusion`), so for `s ≥ 0` it is continuous
(`TauCeti.Vortex.SobolevFieldSpace.continuous_inclusion`): the topology of `A_m^(s')` is finer.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.inclusion`: the inclusion `A_m^(s') ⊆ A_m^s` of continuous
  fields, for `s ≤ s'`.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.subRef_inclusion`: in the coordinates of `x - x_m`, the
  inclusion is the inclusion `H^(s') ⊆ H^s`.
* `TauCeti.Vortex.SobolevFieldSpace.continuous_inclusion`: the inclusion is continuous for
  `0 ≤ s ≤ s'`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s s' s'' : ℝ}

/-- **The inclusion `A_m^(s') ⊆ A_m^s`** of continuous framed fields, for `s ≤ s'`: a field of the
smaller affine space `A_m^(s')` is a field of `A_m^s` (`TauCeti.Vortex.framedFieldSpace_mono`). -/
def inclusion (h : s ≤ s') (x : SobolevFieldSpace f m s') : SobolevFieldSpace f m s :=
  ⟨x, framedFieldSpace_mono f m h x.mem_framedFieldSpace, x.continuous⟩

/-- The inclusion does not change the field. -/
@[simp]
theorem coe_inclusion (h : s ≤ s') (x : SobolevFieldSpace f m s') : ⇑(inclusion h x) = ⇑x :=
  (rfl)

/-- As an element of `A_m^s`, the included field is `Set.inclusion` of the original one. -/
@[simp]
theorem toFramedFieldSpace_inclusion (h : s ≤ s') (x : SobolevFieldSpace f m s') :
    (inclusion h x).toFramedFieldSpace =
      Set.inclusion (framedFieldSpace_mono f m h) x.toFramedFieldSpace :=
  (rfl)

/-- The inclusion of fields is injective. -/
theorem inclusion_injective (h : s ≤ s') :
    Function.Injective (inclusion (f := f) (m := m) h) :=
  fun _ _ hxy ↦ ext (congrArg (⇑) hxy)

/-- The inclusion of `A_m^s` into itself is the identity. -/
@[simp]
theorem inclusion_self (x : SobolevFieldSpace f m s) : inclusion le_rfl x = x :=
  (rfl)

/-- Inclusions of fields compose. -/
@[simp]
theorem inclusion_inclusion (h : s ≤ s') (h' : s' ≤ s'') (x : SobolevFieldSpace f m s'') :
    inclusion h (inclusion h' x) = inclusion (h.trans h') x :=
  (rfl)

/-- **The inclusion in the coordinates of `x - x_m`** is the inclusion `H^(s') ⊆ H^s` of
Bessel-potential spaces, for `0 ≤ s ≤ s'`. -/
theorem subRef_inclusion (h₀ : 0 ≤ s) (h : s ≤ s') (x : SobolevFieldSpace f m s') (j : Fin 4) :
    subRef (inclusion h x) j = BesselPotentialSpace.inclusion h (subRef x j) := by
  rw [subRef_eq_iff h₀, BesselPotentialSpace.inclusion_inclusion]
  exact coeFn_toLp_inclusion_subRef (h₀.trans h) x j

/-- **The inclusion `A_m^(s') ⊆ A_m^s` is continuous** for `0 ≤ s ≤ s'`: the topology of `A_m^(s')`
on its continuous fields is finer than that of `A_m^s`. -/
@[fun_prop]
theorem continuous_inclusion (h₀ : 0 ≤ s) (h : s ≤ s') :
    Continuous (inclusion (f := f) (m := m) h) := by
  refine (isEmbedding_subRef h₀).continuous_iff.2 (continuous_pi fun j ↦ ?_)
  simp only [Function.comp_def, subRef_inclusion h₀ h]
  exact (BesselPotentialSpace.inclusion h).continuous.comp
    ((continuous_apply j).comp continuous_subRef)

end SobolevFieldSpace

end TauCeti.Vortex
