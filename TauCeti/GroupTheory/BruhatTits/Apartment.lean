/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.GroupTheory.BruhatTits.Valuation

/-!
# The apartment of a valuation of a root datum

Let `φ` be a valuation of a root datum of type `Φ` in a group `G`, where `Φ` is a root pairing
over `ℝ` with coroot space `V`. The *apartment* `A(φ)` of `φ` consists of the pairs `(ψ, v)` of a
valuation `ψ` and a *displacement* `v ∈ V` with `ψ = φ + v`, that is `ψ a = φ a + a v` for every
root `a`. The coroot space acts by translation, `w +ᵥ (ψ, v) = (ψ + w, w + v)`, and this makes the
apartment an affine space under `V`, with base point `(φ, 0)`.

The valuation of a point is determined by its displacement, but not conversely: two points have
the same valuation exactly when every root vanishes on the difference of their displacements
(`TauCeti.BruhatTits.Apartment.val_eq_val_iff`). Keeping the displacement makes the apartment an
affine space under all of `V`, including the vectors annihilated by every root, which act as
central translations; the valuations themselves only form the reduced apartment, the
equipollence class of `φ` (`TauCeti.BruhatTits.Apartment.range_val`).

At a point `x = (ψ, v)` the root-group filtration is `U (a, x, r) := ψ.filtration a r`, the
elements `u` of `U a` with `φ a u + a v ≥ r`; translating `x` by `w` lowers the level by `a w`
(`TauCeti.BruhatTits.Apartment.vadd_val_filtration`). These are the filtrations from which the
parahoric subgroups of a reductive group over a local field are generated.

Choosing a point `o` of the apartment as a new base point identifies `A(φ)` with the apartment of
the valuation of `o`, keeping the valuation of every point and subtracting the displacement of `o`
(`TauCeti.BruhatTits.Apartment.transport`). The displacement of `o` is part of the data: when some
nonzero vector is annihilated by every root, the valuation of `o` alone does not determine the
identification.

## Main definitions

* `TauCeti.BruhatTits.Apartment`: the apartment of a valuation.
* `TauCeti.BruhatTits.Apartment.base`: its base point `(φ, 0)`.
* `TauCeti.BruhatTits.Apartment.instAddTorsor`: the apartment is an affine space under the coroot
  space.
* `TauCeti.BruhatTits.Apartment.transport`: the change of base point, an affine equivalence.

## Main results

* `TauCeti.BruhatTits.Apartment.val_eq_val_iff`: two points have the same valuation if and only if
  every root vanishes on their difference.
* `TauCeti.BruhatTits.Apartment.range_val`: the valuations of the points of `A(φ)` are the
  valuations equipollent to `φ`.
* `TauCeti.BruhatTits.Apartment.val_filtration`: `U (a, x, r) = U (a, r - a v)` for a point `x`
  of displacement `v`.
* `TauCeti.BruhatTits.Apartment.vadd_val_filtration`: `U (a, w +ᵥ x, r) = U (a, x, r - a w)`.
* `TauCeti.BruhatTits.Apartment.transport_self`: after the change of base point to `o`, the point
  `o` is the new base point.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.2.5–6.2.6, p. 120.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  4.2.16, p. 94.
-/

public section

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℝ M] [Module ℝ N]
  {G : Type*} [Group G] {P : RootPairing ι ℝ M N} {D : RootDatum P G}

/-- **The apartment of a valuation** `φ` of a root datum: the pairs `(ψ, v)` of a valuation `ψ`
and a displacement `v` in the coroot space with `ψ = φ + v`. It is an affine space under the
coroot space (`TauCeti.BruhatTits.Apartment.instAddTorsor`). -/
structure Apartment (φ : Valuation D) where
  /-- The valuation `ψ = φ + v` of the point. -/
  val : Valuation D
  /-- The displacement `v` of the point from the base valuation. -/
  displacement : N
  /-- The valuation of the point is the base valuation shifted by the displacement. -/
  val_eq : val = φ.shift displacement

namespace Apartment

open Valuation

attribute [simp] val_eq

variable {φ : Valuation D}

/-- A point of the apartment is determined by its displacement. -/
@[ext]
theorem ext {x y : Apartment φ} (h : x.displacement = y.displacement) : x = y := by
  obtain ⟨_, _, rfl⟩ := x
  obtain ⟨_, _, rfl⟩ := y
  simp_all

/-- The value of the valuation of a point `x` of displacement `v` is `φ a u + a v`. -/
theorem val_apply (x : Apartment φ) (i : ι) (u : D.U i) :
    x.val i u = φ i u + (P.root' i x.displacement : WithTop ℝ) := by
  simp

variable (φ) in
/-- The base point `(φ, 0)` of the apartment of `φ`. -/
def base : Apartment φ :=
  ⟨φ, 0, φ.shift_zero.symm⟩

@[simp]
theorem base_displacement : (base φ).displacement = 0 :=
  (rfl)

theorem base_val : (base φ).val = φ :=
  (rfl)

/-! ### The apartment as an affine space -/

/-- The coroot space acts on the apartment by translation, `w +ᵥ (ψ, v) = (ψ + w, w + v)`, and the
difference of two points is the difference of their displacements. -/
instance instAddTorsor : AddTorsor N (Apartment φ) where
  vadd w x := ⟨x.val.shift w, w + x.displacement, by rw [x.val_eq, shift_shift, add_comm]⟩
  zero_vadd x := ext (zero_add _)
  add_vadd w w' x := ext (add_assoc _ _ _)
  vsub x y := x.displacement - y.displacement
  nonempty := ⟨base φ⟩
  vsub_vadd' x y := ext (sub_add_cancel _ _)
  vadd_vsub' w x := add_sub_cancel_right _ _

/-- Translating a point by `w` adds `w` to its displacement. -/
@[simp]
theorem vadd_displacement (w : N) (x : Apartment φ) :
    (w +ᵥ x).displacement = w + x.displacement :=
  (rfl)

/-- Translating a point by `w` shifts its valuation by `w`. -/
theorem vadd_val (w : N) (x : Apartment φ) : (w +ᵥ x).val = x.val.shift w :=
  (rfl)

/-- The difference of two points is the difference of their displacements. -/
@[simp]
theorem vsub_eq_displacement_sub_displacement (x y : Apartment φ) :
    x -ᵥ y = x.displacement - y.displacement :=
  (rfl)

/-- The displacement of a point is its difference from the base point. -/
theorem vsub_base (x : Apartment φ) : x -ᵥ base φ = x.displacement := by
  simp

/-! ### Valuations of the points -/

/-- **Points with the same valuation.** Two points of the apartment have the same valuation if
and only if every root vanishes on their difference. -/
theorem val_eq_val_iff {x y : Apartment φ} : x.val = y.val ↔ ∀ i, P.root' i (x -ᵥ y) = 0 := by
  simp [shift_eq_shift_iff, sub_eq_zero]

/-- **The valuations of the points of the apartment of `φ` are the valuations equipollent to `φ`**,
which form the reduced apartment. -/
theorem range_val : Set.range (val : Apartment φ → Valuation D) = {ψ | φ.Equipollent ψ} := by
  ext ψ
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    rw [x.val_eq]
    exact φ.equipollent_shift _
  · obtain ⟨v, hv⟩ := φ.equipollent_iff.mp h
    exact ⟨⟨ψ, v, Valuation.ext fun i u ↦ by simp [hv]⟩, rfl⟩

/-- The filtration subgroup `U (a, x, r)` at a point `x` of displacement `v` is the filtration
subgroup `U (a, r - a v)` of the base valuation: it consists of the `u ∈ U a` with
`φ a u + a v ≥ r`. -/
theorem val_filtration (x : Apartment φ) (i : ι) (r : ℝ) :
    x.val.filtration i r = φ.filtration i (r - P.root' i x.displacement) := by
  simp

/-- **Translation and filtrations.** Translating a point `x` by `w` lowers the level of its
filtration subgroups by `a w`: `U (a, w +ᵥ x, r) = U (a, x, r - a w)`. -/
theorem vadd_val_filtration (w : N) (x : Apartment φ) (i : ι) (r : ℝ) :
    (w +ᵥ x).val.filtration i r = x.val.filtration i (r - P.root' i w) := by
  rw [vadd_val, filtration_shift]

/-! ### Change of base point -/

/-- **Change of base point.** A point `o` of the apartment of `φ` identifies it with the apartment
of the valuation of `o`: a point keeps its valuation, and its displacement decreases by that of
`o`. This is an affine equivalence with identity linear part. -/
def transport (o : Apartment φ) : Apartment φ ≃ᵃ[ℝ] Apartment o.val where
  toFun x := ⟨x.val, x.displacement - o.displacement, by
    rw [x.val_eq, o.val_eq, shift_shift, add_sub_cancel]⟩
  invFun y := ⟨y.val, y.displacement + o.displacement, y.val_eq.trans <|
    (congrArg (·.shift y.displacement) o.val_eq).trans (by rw [shift_shift, add_comm])⟩
  left_inv x := ext (sub_add_cancel _ _)
  right_inv y := Apartment.ext (add_sub_cancel_right _ _)
  linear := LinearEquiv.refl ℝ N
  map_vadd' x w := Apartment.ext (add_sub_assoc _ _ _)

/-- The change of base point to `o` subtracts the displacement of `o`. -/
@[simp]
theorem transport_apply_displacement (o x : Apartment φ) :
    (transport o x).displacement = x.displacement - o.displacement :=
  (rfl)

/-- The change of base point keeps the valuation of every point. -/
theorem transport_apply_val (o x : Apartment φ) : (transport o x).val = x.val :=
  (rfl)

@[simp]
theorem transport_symm_apply_displacement (o : Apartment φ) (y : Apartment o.val) :
    ((transport o).symm y).displacement = y.displacement + o.displacement :=
  (rfl)

@[simp]
theorem linear_transport (o : Apartment φ) : (transport o).linear = LinearEquiv.refl ℝ N :=
  (rfl)

/-- After the change of base point to `o`, the point `o` is the new base point. -/
@[simp]
theorem transport_self (o : Apartment φ) : transport o o = base o.val :=
  Apartment.ext (sub_self _)

end Apartment

end TauCeti.BruhatTits
