/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.GroupTheory.BruhatTits.Valuation

/-!
# The apartment of a valued root datum

Let `φ` be a valuation of a root datum `D` of type `Φ` in a group `G`, with coroot space `V`. The
*apartment* `A(φ)` is the affine space under `V` of the pairs `(ψ, v)` with `ψ = φ + v`, that is
`ψ a = φ a + a v` for every root `a`. Such a pair is determined by its *displacement* `v = x - φ`,
so we record a point `x` of the apartment by its displacement alone, and recover its valuation
`x.val = φ + (x - φ)`. The vector `v ∈ V` translates `x` to `v + x`, with valuation `x.val + v`.

The displacement is retained even when it is invisible to the roots: two points whose
displacements differ by a vector on which every root vanishes have the same valuation
(`Apartment.val_eq_val_iff`), but are different points. This central direction is what makes `A(φ)`
the *enlarged* apartment; the valuations of its points form the equipollence class of `φ`
(`Apartment.range_val`), the reduced apartment.

At a point `x`, the filtration subgroup `U (a, x, r) = {u ∈ U a : φ a u + a (x - φ) ≥ r}` is the
filtration `x.val.filtration a r` of the valuation of `x`, which is `U (a, r - a (x - φ))`
(`Apartment.filtration_val`); by `Apartment.val_vadd` and `Valuation.filtration_shift`, translating
`x` by `v` moves it to `U (a, v + x, r) = U (a, x, r - a v)`. If `φ` is compatible with a map
`ν : T → V`, then conjugation by `z ∈ T` carries `U (a, x, r)` onto `U (a, ν z + x, r)`
(`Valuation.isCompatible_iff_conjAct_smul_filtration_val`): `z` acts on the apartment by the
translation `ν z`.

The base point `φ` is not canonical: any point `b` of `A(φ)` is the base point of the apartment
`A(b.val)`, and the two apartments are identified by an affine equivalence with linear part the
identity which keeps the valuation of every point (`Apartment.transport`). In the new coordinates
the displacement of `x` becomes `x - b`.

## Main definitions

* `TauCeti.BruhatTits.Apartment`: the apartment of a valuation, an `AddTorsor` under the coroot
  space.
* `TauCeti.BruhatTits.Apartment.base`: the base point `φ`.
* `TauCeti.BruhatTits.Apartment.val`: the valuation `φ + (x - φ)` of a point `x`.
* `TauCeti.BruhatTits.Apartment.transport`: the change of base point.

## Main results

* `TauCeti.BruhatTits.Apartment.val_vadd`: `(v + x).val = x.val + v`.
* `TauCeti.BruhatTits.Apartment.range_val`: the valuations of the points of `A(φ)` are the
  valuations equipollent to `φ`.
* `TauCeti.BruhatTits.Apartment.val_eq_val_iff`: two points have the same valuation if and only if
  every root vanishes on their difference.
* `TauCeti.BruhatTits.Apartment.filtration_val`: `U (a, x, r) = U (a, r - a (x - φ))`.
* `TauCeti.BruhatTits.Valuation.isCompatible_iff_conjAct_smul_filtration_val`: `φ` is compatible
  with `ν` if and only if each `z ∈ T` conjugates `U (a, x, r)` onto `U (a, ν z + x, r)`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.2.5–6.2.6, p. 120, and 6.2.10, pp. 122–123.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  4.2.16, p. 94.
-/

public section

open scoped Pointwise

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} {G : Type*} [Group G] {D : RootDatum P G}

/-- The apartment of a valuation `φ` of a root datum: the affine space under the coroot space `N`
of the pairs `(φ + v, v)` with `v ∈ N`. A point `x` is recorded by its displacement `x - φ`; its
valuation is `Apartment.val x = φ + (x - φ)`. -/
@[ext]
structure Apartment (φ : Valuation D) where
  /-- The displacement `x - φ ∈ N` of the point `x` from the base point `φ`. -/
  displacement : N

namespace Apartment

variable {φ : Valuation D}

/-- The coroot space acts simply transitively on the apartment by translating displacements. -/
instance : AddTorsor N (Apartment φ) where
  vadd v x := ⟨v + x.displacement⟩
  zero_vadd x := Apartment.ext (zero_add x.displacement)
  add_vadd v w x := Apartment.ext (add_assoc v w x.displacement)
  vsub x y := x.displacement - y.displacement
  nonempty := ⟨⟨0⟩⟩
  vsub_vadd' x y := Apartment.ext (sub_add_cancel x.displacement y.displacement)
  vadd_vsub' v x := add_sub_cancel_right v x.displacement

@[simp]
theorem displacement_vadd (v : N) (x : Apartment φ) : (v +ᵥ x).displacement = v + x.displacement :=
  (rfl)

theorem vsub_def (x y : Apartment φ) : x -ᵥ y = x.displacement - y.displacement :=
  (rfl)

variable (φ) in
/-- The base point `φ` of its apartment, with displacement `0`. -/
def base : Apartment φ :=
  ⟨0⟩

@[simp]
theorem displacement_base : (base φ).displacement = 0 :=
  (rfl)

/-- The displacement of `x` is its difference `x - φ` with the base point. -/
@[simp]
theorem vsub_base (x : Apartment φ) : x -ᵥ base φ = x.displacement := by
  simp [vsub_def]

/-! ### The valuation of a point -/

/-- The valuation `φ + (x - φ)` of a point `x` of the apartment of `φ`. -/
def val (x : Apartment φ) : Valuation D :=
  φ.shift x.displacement

theorem val_def (x : Apartment φ) : x.val = φ.shift x.displacement :=
  (rfl)

/-- The valuation of `x` at `u ∈ U a` is `φ a u + a (x - φ)`. -/
@[simp]
theorem val_apply (x : Apartment φ) {i : ι} (u : D.U i) :
    x.val i u = φ i u + (P.root' i x.displacement : WithTop ℝ) := by
  rw [val_def, Valuation.shift_apply]

@[simp]
theorem val_base : (base φ).val = φ := by
  simp [val_def]

/-- Translating a point by `v` shifts its valuation by `v`: `(v + x).val = x.val + v`. -/
@[simp]
theorem val_vadd (v : N) (x : Apartment φ) : (v +ᵥ x).val = x.val.shift v := by
  simp [val_def, add_comm]

/-- The valuation of every point of the apartment of `φ` is equipollent to `φ`. -/
theorem equipollent_val (x : Apartment φ) : φ.Equipollent x.val := by
  rw [val_def]
  exact φ.equipollent_shift x.displacement

/-- The valuation of a point of the apartment of `φ` is discrete exactly when `φ` is. -/
@[simp]
theorem isDiscrete_val (x : Apartment φ) : x.val.IsDiscrete ↔ φ.IsDiscrete := by
  rw [val_def, Valuation.isDiscrete_shift_iff]

/-- The valuations of the points of the apartment of `φ` are exactly the valuations equipollent
to `φ`: the reduced apartment is the image of the apartment. -/
theorem range_val : Set.range (val (φ := φ)) = {ψ | φ.Equipollent ψ} := by
  ext ψ
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ equipollent_val x, fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := φ.equipollent_iff.mp h
  exact ⟨⟨v⟩, Valuation.ext fun i u ↦ by rw [val_apply, hv]⟩

/-- Translation by `v` keeps the valuation of a point if and only if every root vanishes
on `v`. -/
theorem val_vadd_eq_val_iff {v : N} {x : Apartment φ} :
    (v +ᵥ x).val = x.val ↔ ∀ i, P.root' i v = 0 := by
  rw [val_vadd, Valuation.shift_eq_self_iff]

/-- Two points of the apartment have the same valuation if and only if every root vanishes on
their difference. -/
theorem val_eq_val_iff {x y : Apartment φ} : x.val = y.val ↔ ∀ i, P.root' i (x -ᵥ y) = 0 := by
  have h := val_vadd_eq_val_iff (v := x -ᵥ y) (x := y)
  rwa [vsub_vadd] at h

/-! ### Filtrations at a point -/

/-- The filtration subgroup `U (a, x, r)` at a point `x` of the apartment is
`U (a, r - a (x - φ))`. -/
theorem filtration_val (x : Apartment φ) (i : ι) (r : ℝ) :
    x.val.filtration i r = φ.filtration i (r - P.root' i x.displacement) := by
  rw [val_def, Valuation.filtration_shift]

/-- The strict filtration at an apartment point uses the base valuation with the threshold
decreased by the root evaluated on the point's displacement. -/
theorem filtrationGT_val (x : Apartment φ) (i : ι) (r : ℝ) :
    x.val.filtrationGT i r = φ.filtrationGT i (r - P.root' i x.displacement) := by
  rw [val_def, Valuation.filtrationGT_shift]

/-! ### Change of base point -/

/-- The change of base point: a point `b` of the apartment of `φ` is the base point of the
apartment of `b.val`, and `x ↦ (x - b) + b.val` identifies the two apartments. It is an affine
equivalence with linear part the identity, and it keeps the valuation of every point
(`Apartment.val_transport`). -/
def transport (b : Apartment φ) : Apartment φ ≃ᵃ[ℝ] Apartment b.val :=
  (AffineEquiv.vaddConst ℝ b).symm.trans (AffineEquiv.vaddConst ℝ (base b.val))

/-- After the change of base point to `b`, the displacement of `x` is `x - b`. -/
@[simp]
theorem displacement_transport (b x : Apartment φ) :
    (transport b x).displacement = x.displacement - b.displacement := by
  simp [transport, vsub_def]

/-- The change of base point carries `b` to the new base point. -/
@[simp]
theorem transport_self (b : Apartment φ) : transport b b = base b.val := by
  ext
  simp

@[simp]
theorem linear_transport (b : Apartment φ) : (transport b).linear = LinearEquiv.refl ℝ N := by
  ext v
  rfl

/-- The change of base point keeps the valuation of every point. -/
@[simp]
theorem val_transport (b x : Apartment φ) : (transport b x).val = x.val := by
  simp only [val_def, displacement_transport, Valuation.shift_shift]
  rw [add_sub_cancel]

end Apartment

/-! ### Compatibility and the action of `T` -/

namespace Valuation

variable {φ : Valuation D} {ν : D.T → N}

/-- If `φ` is compatible with `ν`, then conjugation by `z ∈ T` carries the filtration subgroup
`U (a, x, r)` at a point `x` of the apartment onto `U (a, ν z + x, r)`: `z` acts on the apartment
by the translation `ν z`. -/
theorem IsCompatible.conjAct_smul_filtration_val (h : φ.IsCompatible ν) (x : Apartment φ)
    (i : ι) (z : D.T) (r : ℝ) :
    ConjAct.toConjAct (z : G) • x.val.filtration i r = (ν z +ᵥ x).val.filtration i r := by
  have hx : x.val.IsCompatible ν := by
    rw [Apartment.val_def, isCompatible_shift_iff]
    exact h
  rw [x.val.isCompatible_iff_filtration.mp hx i z r, Apartment.val_vadd, filtration_shift]

/-- A valuation `φ` is compatible with `ν : T → N` if and only if, at every point `x` of its
apartment, conjugation by each `z ∈ T` carries `U (a, x, r)` onto `U (a, ν z + x, r)`. -/
theorem isCompatible_iff_conjAct_smul_filtration_val :
    φ.IsCompatible ν ↔ ∀ (x : Apartment φ) (i : ι) (z : D.T) (r : ℝ),
      ConjAct.toConjAct (z : G) • x.val.filtration i r = (ν z +ᵥ x).val.filtration i r := by
  refine ⟨fun h x i z r ↦ h.conjAct_smul_filtration_val x i z r, fun h ↦ ?_⟩
  refine φ.isCompatible_iff_filtration.mpr fun i z r ↦ ?_
  simpa using h (Apartment.base φ) i z r

end Valuation

end TauCeti.BruhatTits
