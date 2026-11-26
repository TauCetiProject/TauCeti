/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Prod
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# The action-field specialization of Novikov series

Let `E : G →+ ℝ` be the energy of a group `G` of classes. The *action-weighted extension* is the
exponent group `G × ℝ` with the period `E_R (g, r) = E g + r`, which is
`E.coprod (AddMonoidHom.id ℝ)`: an exponent `(g, r)` records a class together with an action
shift, and the monomials `T^r = e^(0, r)` are the real action weights. The Novikov series over it
form the coefficient ring of Floer complexes whose generators carry action values.

For a ring homomorphism `ρ : R →+* k`, the *action-field map*
`TauCeti.NovikovSeries.actionFieldMap E ρ` forgets the classes and keeps only their total energy:
it is the pushforward `P_(ρ, E_R)` of `TauCeti.NovikovSeries.mapRingHom` along the period itself,
with values in the Novikov series `Nov(k, ℝ, id)` of real exponents. In coordinates,

`(φ_* a)(t) = ∑ᶠ g, ρ (a (g, t - E g))`   (`TauCeti.NovikovSeries.coeff_actionFieldMap`),

a finite sum, since only finitely many coefficients of `a` lie at period `t`. The monomial
`c e^(g, r)` goes to `ρ c T^(E g + r)` (`TauCeti.NovikovSeries.actionFieldMap_single`), so the
action weights `T^r` are kept. The map rescales periods by `1`: it sends the period neighbourhood
`U_C` into `U_C` (`TauCeti.NovikovSeries.actionFieldMap_mem_periodFiltration`), hence is
continuous, and it preserves nonnegative supports. When `k` is a field, the target
`Nov(k, ℝ, id)` is a field by `TauCeti.NovikovSeries.isField_iff`, since the identity period is
injective; every nonzero series there is a monomial times `1 - b` with `b` of positive support
(`TauCeti.NovikovSeries.exists_single_mul_one_sub_of_injective`), and it is the field of fractions
of its nonnegative subring (`TauCeti.NovikovSeries.isFractionRing_nonnegSubring`).

So the action-field map turns a complex over the action-weighted Novikov ring into a complex over
a field, without assuming that `E` is injective or discrete. It is neither injective nor flat in
general: classes of equal energy are identified. Since classes of different degrees may have equal
energy, it forgets any grading of the classes: it is the ungraded specialization, and a grading
survives only in a quotient of the degrees that identifies the degrees of classes of equal
energy. Since the action-weighted Novikov ring is the localization of its nonnegative subring
`Λ₀` at the action weights `T^r`, `r ≥ 0`
(`TauCeti.NovikovSeries.isLocalization_monomialSubmonoid_map_inr`), and these weights go to units
of `Nov(k, ℝ, id)`, the action-field map is the unique extension of its restriction to `Λ₀`.

## Main definitions

* `TauCeti.NovikovSeries.actionFieldMap E ρ`: the action-field map
  `Nov(R, G × ℝ, E_R) →+* Nov(k, ℝ, id)`.

## Main results

* `TauCeti.NovikovSeries.coeff_actionFieldMap`: the coefficient formula above.
* `TauCeti.NovikovSeries.actionFieldMap_single`: the image of a monomial.
* `TauCeti.NovikovSeries.actionFieldMap_mem_periodFiltration` and
  `TauCeti.NovikovSeries.continuous_actionFieldMap`: the map keeps every period cutoff and is
  continuous.
* `TauCeti.NovikovSeries.actionFieldMap_mem_nonnegSubring`: the map preserves nonnegative
  supports.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 5.1, on the
  universal Novikov ring and the energy filtration.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {R k G : Type*} [AddCommGroup G] (E : G →+ ℝ)

/-- The action period `E_R (g, r) = E g + r` rescales to the identity period by the factor `1`. -/
theorem exists_period_rescale_coprod_id :
    ∃ c > 0, ∀ h : G × ℝ,
      AddMonoidHom.id ℝ (E.coprod (AddMonoidHom.id ℝ) h) = c * E.coprod (AddMonoidHom.id ℝ) h :=
  ⟨1, one_pos, fun _ => (one_mul _).symm⟩

section Semiring

variable [Semiring R] [Semiring k] (ρ : R →+* k)

/-- The **action-field map** `φ_* : Nov(R, G × ℝ, E_R) →+* Nov(k, ℝ, id)`: the pushforward along
the coefficient map `ρ` and the action period `E_R (g, r) = E g + r`. It keeps only the total
energy of each exponent and sums the coefficients of equal energy. -/
def actionFieldMap :
    NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ)) →+*
      NovikovSeries k ℝ (AddMonoidHom.id ℝ) :=
  mapRingHom ρ (E.coprod (AddMonoidHom.id ℝ)) (exists_period_rescale_coprod_id E)

/-- The action-field map is the pushforward `P_(ρ, E_R)` of Novikov rings. -/
theorem actionFieldMap_eq_mapRingHom :
    actionFieldMap E ρ =
      mapRingHom ρ (E.coprod (AddMonoidHom.id ℝ)) (exists_period_rescale_coprod_id E) :=
  (rfl)

/-- **The coefficient formula.** The coefficient of the action-field image at the energy `t` is
the sum, over the classes `g`, of the images of the coefficients at `(g, t - E g)`. Only finitely
many terms are nonzero. -/
theorem coeff_actionFieldMap (a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ)))
    (t : ℝ) :
    (actionFieldMap E ρ a).coeff t = ∑ᶠ g, ρ (a.coeff (g, t - E g)) := by
  rw [actionFieldMap_eq_mapRingHom, mapRingHom_apply, coeff_map,
    AddMonoidHom.preimage_coprod_id_singleton,
    finsum_mem_range fun g g' h => (Prod.mk.inj h).1, AddMonoidHom.coe_ofClass]

/-- The action-field map sends the monomial `c e^(g, r)` to `ρ c T^(E g + r)`. -/
@[simp]
theorem actionFieldMap_single (h : G × ℝ) (c : R) :
    actionFieldMap E ρ (single h c) = single (E h.1 + h.2) (ρ c) := by
  rw [actionFieldMap_eq_mapRingHom, mapRingHom_apply, map_single, AddMonoidHom.coprod_apply,
    AddMonoidHom.id_apply, AddMonoidHom.coe_ofClass]

end Semiring

section Ring

variable [Ring R] [Ring k] (ρ : R →+* k)

/-- The action-field map keeps every period cutoff: it sends the period neighbourhood `U_C` of the
action-weighted Novikov ring into the period neighbourhood `U_C` of `Nov(k, ℝ, id)`. -/
theorem actionFieldMap_mem_periodFiltration {C : ℝ}
    {a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))}
    (ha : a ∈ periodFiltration R (E.coprod (AddMonoidHom.id ℝ)) C) :
    actionFieldMap E ρ a ∈ periodFiltration k (AddMonoidHom.id ℝ) C := by
  simpa [actionFieldMap_eq_mapRingHom] using
    map_mem_periodFiltration (ρ : R →+ k) _ (exists_period_rescale_coprod_id E)
      zero_le_one (fun h => (one_mul _).symm) ha

/-- The action-field map is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_actionFieldMap : Continuous (actionFieldMap E ρ) :=
  continuous_mapRingHom ρ _ _

/-- The action-field map sends series of nonnegative energy to series of nonnegative energy. -/
theorem actionFieldMap_mem_nonnegSubring
    {a : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))}
    (ha : a ∈ nonnegSubring R (E.coprod (AddMonoidHom.id ℝ))) :
    actionFieldMap E ρ a ∈ nonnegSubring k (AddMonoidHom.id ℝ) := by
  rw [actionFieldMap_eq_mapRingHom, mapRingHom_apply]
  exact map_mem_nonnegSubring (ρ : R →+ k) _ _ ha

end Ring

end NovikovSeries

end TauCeti
