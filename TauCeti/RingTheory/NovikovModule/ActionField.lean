/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Pushforward
public import TauCeti.RingTheory.NovikovSeries.ActionField

/-!
# The action-field specialization of completed combinations

For torsors under the action-weighted exponent group `G × ℝ`, with period
`E_R (g, r) = E g + r`, chosen lifts `r i` map each orbit onto a copy of `ℝ` through
`p ↦ E_R (p -ᵥ r i)`. The pushforward `TauCeti.NovikovModule.pushforward` along these maps
(`TauCeti.NovikovModule.actionFieldMap`), which sums the coefficients of points of equal
energy, is a completed combination over the Novikov series `Nov(k, ℝ, id)`, with one generator
for each energy in each orbit. Its coordinates are the images of the coordinates under the
action-field map of Novikov series (`TauCeti.NovikovModule.coordinates_actionFieldMap`), and
matrices go to their entrywise images (`TauCeti.NovikovModule.actionFieldMap_novikovMapOfMatrix`).
This specializes a finite Floer complex over the action-weighted Novikov ring to a finite
complex over `Nov(k, ℝ, id)`, which is the Novikov field when `k` is a field.

## Main definitions

* `TauCeti.NovikovModule.actionFieldPotential F r`: the potential of the action-field generators
  `Σ _ : ι, ℝ`.
* `TauCeti.NovikovModule.actionFieldMap`: the action-field specialization of completed
  combinations on torsors under the action-weighted exponent group.

## Main results

* `TauCeti.NovikovModule.actionFieldMap_single`: the specialization of point masses.
* `TauCeti.NovikovModule.continuous_actionFieldMap`: the specialization is continuous.
* `TauCeti.NovikovModule.coordinates_actionFieldMap`: the specialization in lift coordinates.
* `TauCeti.NovikovModule.actionFieldMap_smul`: semilinearity over the action-field map of
  Novikov rings.
* `TauCeti.NovikovModule.actionFieldMap_novikovMapOfMatrix`: the specialization of the map of a
  matrix.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 5.1.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovModule

variable {R : Type*}

section ActionField

variable {k G ι ι₀ : Type*} [AddCommGroup G] {E : G →+ ℝ} {P : ι → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (G × ℝ) (P i)] [∀ k, AddTorsor (G × ℝ) (P₀ k)] {F : (Σ i, P i) → ℝ}
  {F₀ : (Σ k, P₀ k) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - E.coprod (AddMonoidHom.id ℝ) h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - E.coprod (AddMonoidHom.id ℝ) h)

variable (F) in
/-- The potential of the action-field generators `Σ _ : ι, ℝ` for the lifts `r`: the energy `t` in
the orbit `i` has the potential `F (r i) - t`. -/
def actionFieldPotential (r : ∀ i, P i) (s : Σ _ : ι, ℝ) : ℝ :=
  F ⟨s.1, r s.1⟩ - s.2

@[simp]
theorem actionFieldPotential_apply (r : ∀ i, P i) (s : Σ _ : ι, ℝ) :
    actionFieldPotential F r s = F ⟨s.1, r s.1⟩ - s.2 :=
  (rfl)

variable (F) in
/-- On the action-field generators, translating the energy by `t` lowers the potential by `t`:
each orbit is a torsor under `ℝ` with the identity period. -/
theorem actionFieldPotential_vadd (r : ∀ i, P i) (i : ι) (t x : ℝ) :
    actionFieldPotential F r ⟨i, t +ᵥ x⟩ =
      actionFieldPotential F r ⟨i, x⟩ - AddMonoidHom.id ℝ t := by
  simp only [actionFieldPotential_apply, vadd_eq_add, AddMonoidHom.id_apply]
  ring

/-- The energy `E_R (p -ᵥ r i)` of a generator relative to the lift of its orbit. -/
private theorem vadd_vsub_energy (r : ∀ i, P i) (i : ι) (h : G × ℝ) (p : P i) :
    E.coprod (AddMonoidHom.id ℝ) ((h +ᵥ p) -ᵥ r i) =
      E.coprod (AddMonoidHom.id ℝ) h +ᵥ E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i) := by
  rw [vadd_vsub_assoc, map_add, vadd_eq_add]

include hF in
/-- The energy map `p ↦ E_R (p -ᵥ r i)` of each orbit preserves potentials. -/
theorem actionFieldPotential_energy (r : ∀ i, P i) (s : Σ i, P i) :
    actionFieldPotential F r
        (Sigma.map id (fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i)) s) = F s := by
  obtain ⟨i, p⟩ := s
  rw [Sigma.map_mk, actionFieldPotential_apply, potential_eq_sub_vsub hF r i p, id_eq]

section Semiring

variable [Semiring R] [Semiring k] (ρ : R →+* k)

/-- The **action-field specialization** of completed combinations on torsors under the
action-weighted exponent group `G × ℝ`: the pushforward along the coefficient map `ρ` and the
energy maps `p ↦ E_R (p -ᵥ r i)` from each orbit to `ℝ`, relative to lifts `r`. Its values are
completed combinations of the generators `Σ _ : ι, ℝ` with the potential
`TauCeti.NovikovModule.actionFieldPotential F r`. -/
def actionFieldMap (r : ∀ i, P i) :
    NovikovModule R F →ₛₗ[ρ] NovikovModule k (actionFieldPotential F r) :=
  pushforward ρ (Sigma.map id fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i))
    (actionFieldPotential_energy hF r)

/-- The action-field specialization is the pushforward along the energy maps of the orbits. -/
theorem actionFieldMap_apply (r : ∀ i, P i) (a : NovikovModule R F) :
    actionFieldMap hF ρ r a =
      pushforward ρ (Sigma.map id fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i))
        (actionFieldPotential_energy hF r) a :=
  (rfl)

/-- The action-field specialization sends the point mass `c` at `p` in the orbit `i` to the point
mass `ρ c` at the energy `E_R (p -ᵥ r i)` in the orbit `i`. -/
@[simp]
theorem actionFieldMap_single [DecidableEq (Σ i, P i)] [DecidableEq (Σ _ : ι, ℝ)] (r : ∀ i, P i)
    (i : ι) (p : P i) (c : R) :
    actionFieldMap hF ρ r (single ⟨i, p⟩ c) =
      single ⟨i, E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i)⟩ (ρ c) :=
  pushforward_single _ ρ _ c

variable [Finite ι]

/-- **The action-field specialization in coordinates.** In the lift coordinates of `r` and of the
energy `0` in each orbit, the action-field specialization of completed combinations is the
action-field map `TauCeti.NovikovSeries.actionFieldMap E ρ` of Novikov series in each orbit. -/
@[simp]
theorem coordinates_actionFieldMap (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates (actionFieldPotential_vadd F r) (fun _ => 0) (actionFieldMap hF ρ r a) i =
      NovikovSeries.actionFieldMap E ρ (coordinates hF r a i) := by
  have h := coordinates_pushforward hF (actionFieldPotential_vadd F r) ρ
    (NovikovSeries.exists_period_rescale_coprod_id E) (vadd_vsub_energy r)
    (actionFieldPotential_energy hF r) r a i
  simp only [vsub_self, map_zero] at h
  rw [actionFieldMap_apply, h, NovikovSeries.actionFieldMap_eq_mapRingHom]

/-- The action-field specialization is semilinear for the Novikov module structures of
`TauCeti.NovikovModule.module`, over the action-field map of Novikov rings. -/
theorem actionFieldMap_smul (r : ∀ i, P i)
    (β : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) (a : NovikovModule R F) :
    letI := module (R := R) hF
    letI := module (R := k) (actionFieldPotential_vadd F r)
    actionFieldMap hF ρ r (β • a) =
      NovikovSeries.actionFieldMap E ρ β • actionFieldMap hF ρ r a := by
  rw [actionFieldMap_apply, actionFieldMap_apply, NovikovSeries.actionFieldMap_eq_mapRingHom]
  exact pushforward_smul hF (actionFieldPotential_vadd F r) ρ
    (NovikovSeries.exists_period_rescale_coprod_id E) (vadd_vsub_energy r) _ β a

end Semiring

section Ring

variable [Ring R] [Ring k] (ρ : R →+* k)

/-- The action-field specialization is continuous for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_actionFieldMap (r : ∀ i, P i) : Continuous (actionFieldMap hF ρ r) :=
  continuous_pushforward _ ρ

end Ring

section CommSemiring

variable [CommSemiring R] [CommSemiring k] (ρ : R →+* k) [Finite ι] [Finite ι₀]

/-- **Specializing the map of a matrix.** The action-field specialization carries the
Novikov-linear map of a matrix `M` of action-weighted Novikov series to the map of the matrix of
the action-field images `TauCeti.NovikovSeries.actionFieldMap E ρ` of its entries, relative to the
energy `0` in each orbit. -/
theorem actionFieldMap_novikovMapOfMatrix (r : ∀ i, P i) (r₀ : ∀ k, P₀ k)
    (M : Matrix ι ι₀ (NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))))
    (a : NovikovModule R F) :
    actionFieldMap hF₀ ρ r₀ (novikovMapOfMatrix hF hF₀ r r₀ M a) =
      novikovMapOfMatrix (actionFieldPotential_vadd F r) (actionFieldPotential_vadd F₀ r₀)
        (fun _ => 0) (fun _ => 0) (M.map (NovikovSeries.actionFieldMap E ρ))
        (actionFieldMap hF ρ r a) := by
  have := Fintype.ofFinite ι
  refine (coordinates (actionFieldPotential_vadd F₀ r₀) fun _ => 0).injective
    (funext fun k => ?_)
  rw [coordinates_actionFieldMap, coordinates_novikovMapOfMatrix,
    coordinates_novikovMapOfMatrix, map_sum]
  simp only [map_mul, Matrix.map_apply, coordinates_actionFieldMap]

end CommSemiring

end ActionField

end NovikovModule

end TauCeti
