/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.PadicCharacter
public import TauCeti.RepresentationTheory.Transvection

/-!
# Tame monodromy in dimension two

Choose an additive topological identification `e : ℤ_ℓ(1) ≃ₜ+ ℤ_ℓ`, where `ℓ` differs from the
residue characteristic of a nonarchimedean local field `K`. For `c : ℚ_ℓ`, the tame character
defines the continuous inertia representation

`σ (x, y) = (x + y * c * e(t_ℓ(σ)), y)`.

For nonzero `c`, its invariant space is exactly the first coordinate line, and hence has
codimension one. Wild inertia acts trivially. These are the linear-algebraic inputs to the tame
conductor calculation for multiplicative reduction: once an inertia action is identified with
this representation, its tame contribution is one and its wild contribution vanishes. No
identification with the Tate module of a curve is asserted here.

The choice `e` is kept explicit; it exists by
`TauCeti.PadicTateTwist.nonempty_continuousAddEquiv`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], IV §2.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V §6.
-/

public section

noncomputable section

namespace TauCeti

open _root_.ValuativeRel MonoidHom

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : ℓ.Coprime (ringChar 𝓀[K]))
  (e : PadicTateTwist ℓ (AlgebraicClosure K) ≃ₜ+ ℤ_[ℓ]) (c : ℚ_[ℓ])

private def tameMonodromyCharacter : inertiaSubgroup K →* Multiplicative ℚ_[ℓ] where
  toFun σ := Multiplicative.ofAdd (c * (e (inertiaPadicTameCharacter K hℓ σ).toAdd : ℚ_[ℓ]))
  map_one' := by simp
  map_mul' σ τ := by simp [mul_add]

private theorem tameMonodromyCharacter_eq_one_iff :
    tameMonodromyCharacter K hℓ e c = 1 ↔ c = 0 := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := inertiaPadicTameCharacter_surjective K hℓ
      (Multiplicative.ofAdd (e.symm 1))
    have hval := congrArg (fun χ : inertiaSubgroup K →* Multiplicative ℚ_[ℓ] ↦
      (χ σ).toAdd) h
    simpa [tameMonodromyCharacter, hσ] using hval
  · rintro rfl
    ext σ
    simp [tameMonodromyCharacter]

private theorem tameMonodromyCharacter_ne_one (hc : c ≠ 0) :
    tameMonodromyCharacter K hℓ e c ≠ 1 :=
  fun h ↦ hc ((tameMonodromyCharacter_eq_one_iff K hℓ e c).mp h)

/-- The two-dimensional transvection representation of inertia with parameter `c`, after the
choice `e` of a coordinate on the Tate twist. -/
def tameMonodromyRepresentation :
    Representation ℚ_[ℓ] (inertiaSubgroup K) (ℚ_[ℓ] × ℚ_[ℓ]) :=
  transvectionRepresentation (tameMonodromyCharacter K hℓ e c)

/-- The coordinate formula for tame monodromy. -/
@[simp]
theorem tameMonodromyRepresentation_apply (σ : inertiaSubgroup K) (v : ℚ_[ℓ] × ℚ_[ℓ]) :
    tameMonodromyRepresentation K hℓ e c σ v =
      (v.1 + v.2 * (c * (e (inertiaPadicTameCharacter K hℓ σ).toAdd : ℚ_[ℓ])), v.2) := by
  simp [tameMonodromyRepresentation, tameMonodromyCharacter]

/-- The inertia action is jointly continuous in the group element and the vector. -/
theorem continuous_tameMonodromyRepresentation :
    Continuous (fun p : inertiaSubgroup K × (ℚ_[ℓ] × ℚ_[ℓ]) ↦
      tameMonodromyRepresentation K hℓ e c p.1 p.2) := by
  simp only [tameMonodromyRepresentation_apply]
  have ht := continuous_toAdd (X := PadicTateTwist ℓ (AlgebraicClosure K))
  fun_prop

/-- Wild inertia acts trivially in the tame monodromy representation. -/
theorem tameMonodromyRepresentation_eq_one_of_mem_wildInertiaSubgroup
    (σ : inertiaSubgroup K) (hσ : σ.1 ∈ wildInertiaSubgroup K) :
    tameMonodromyRepresentation K hℓ e c σ = 1 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [inertiaPadicTameCharacter_eq_one_of_mem_wildInertiaSubgroup σ.2 hσ]

/-- For nonzero monodromy parameter the fixed vectors are exactly those with second coordinate
zero. -/
theorem mem_invariants_tameMonodromyRepresentation_iff (hc : c ≠ 0) (v : ℚ_[ℓ] × ℚ_[ℓ]) :
    v ∈ (tameMonodromyRepresentation K hℓ e c).invariants ↔ v.2 = 0 := by
  exact mem_invariants_transvectionRepresentation_iff _
    (tameMonodromyCharacter_ne_one K hℓ e c hc) v

/-- The invariant space is the first coordinate line, expressed without choosing its basis. -/
@[simp]
theorem invariants_tameMonodromyRepresentation (hc : c ≠ 0) :
    (tameMonodromyRepresentation K hℓ e c).invariants =
      LinearMap.ker (LinearMap.snd ℚ_[ℓ] ℚ_[ℓ] ℚ_[ℓ]) := by
  exact invariants_transvectionRepresentation _ (tameMonodromyCharacter_ne_one K hℓ e c hc)

/-- A nonzero tame-monodromy representation has a one-dimensional invariant space. -/
theorem finrank_invariants_tameMonodromyRepresentation (hc : c ≠ 0) :
    Module.finrank ℚ_[ℓ] (tameMonodromyRepresentation K hℓ e c).invariants = 1 := by
  exact finrank_invariants_transvectionRepresentation _ (tameMonodromyCharacter_ne_one K hℓ e c hc)

/-- The tame contribution, the codimension of inertia invariants, is one for nonzero parameter.
This does not define or assume an Artin conductor. -/
theorem finrank_sub_finrank_invariants_tameMonodromyRepresentation (hc : c ≠ 0) :
    Module.finrank ℚ_[ℓ] (ℚ_[ℓ] × ℚ_[ℓ]) -
      Module.finrank ℚ_[ℓ] (tameMonodromyRepresentation K hℓ e c).invariants = 1 := by
  simp [finrank_invariants_tameMonodromyRepresentation K hℓ e c hc, Module.finrank_prod]

/-- The tame monodromy representation is trivial exactly when its parameter vanishes. -/
@[simp]
theorem tameMonodromyRepresentation_eq_one_iff :
    tameMonodromyRepresentation K hℓ e c = 1 ↔ c = 0 := by
  rw [tameMonodromyRepresentation, transvectionRepresentation_eq_one_iff,
    tameMonodromyCharacter_eq_one_iff]

/-- Vanishing monodromy gives the trivial representation. -/
@[simp]
theorem tameMonodromyRepresentation_zero : tameMonodromyRepresentation K hℓ e 0 = 1 :=
  (tameMonodromyRepresentation_eq_one_iff K hℓ e 0).mpr rfl

end TauCeti
