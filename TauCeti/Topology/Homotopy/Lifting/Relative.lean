/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ApplyProdMk
public import TauCeti.Topology.Homotopy.Lifting.Basic

/-!
# Lifting from zero-set strong deformation retracts

Let `A ⊆ Y` be the zero set of a continuous `u : Y → I` and a strong deformation retract of `Y`.
A map with homotopy lifting for `Y` has the right lifting property against the inclusion `A → Y`:
a compatible lift on `A` extends to `Y`, with its prescribed values retained exactly.

Writing `h` for the deformation, the homotopy `(t, y) ↦ h (1 - min 1 (t / u y), y)` runs from
the retraction to `y` by time `u y`. Its continuity at `A` follows from the compactness argument
`ContinuousMap.continuous_apply_prodMk_of_fixed`. Evaluating an ordinary homotopy lift at time
`u y` gives the extension. No regular lifting function or separation hypothesis is needed.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapters 6 and 7.
-/

public section

open Set unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- **Fixed-data relative lifting.** Let `A ⊆ Y` be the zero set of a continuous `u : Y → I` and
a strong deformation retract of `Y`, with retraction `r`. Then a map `p` with homotopy lifting
for `Y` lifts every commutative square from the inclusion `A → Y` to `p`: given `f : A → E` and
`g : Y → B` with
`p ∘ f = g` on `A`, there is a lift `ℓ : Y → E` of `g` restricting to `f` on `A`. -/
theorem HasHomotopyLiftingProperty.zeroSetSDR_liftingInclusion {Y : Type w}
    [TopologicalSpace Y] (hp : HasHomotopyLiftingProperty p Y) {A : Set Y}
    (u : C(Y, I)) (hu : ∀ y, u y = 0 ↔ y ∈ A) (r : C(Y, A))
    (hr : (ContinuousMap.id Y).HomotopicRel ((ContinuousMap.subtypeVal A).comp r) A)
    (f : C(A, E)) (g : C(Y, B)) (hfg : ∀ a, p (f a) = g a) :
    ∃ ℓ : C(Y, E), p ∘ ℓ = g ∧ ∀ a : A, ℓ a = f a := by
  have hr' (a : A) : r a = a := Subtype.ext (hr.fst_eq_snd a.2).symm
  obtain ⟨F⟩ := hr
  -- the homotopy `Φ (t, y) = F (1 - min 1 (t / u y), y)` from `r` to the point `y` at time `u y`
  let φ : I × Y → I := fun z ↦ σ (projIcc 0 1 zero_le_one ((z.1 : ℝ) / u z.2))
  have hφ (z : I × Y) (hz : z.2 ∉ A) : ContinuousAt φ z :=
    continuous_symm.continuousAt.comp
      (u.continuousAt_projIcc_div_of_notMem hu continuous_fst continuous_snd hz)
  let Φ : C(I × Y, Y) :=
    ⟨fun z ↦ F.toContinuousMap (φ z, z.2),
      F.toContinuousMap.continuous_apply_prodMk_of_fixed (fun t _ hy ↦ F.eq_fst t hy)
        continuous_snd hφ⟩
  have hΦ₀ (y : Y) : Φ (0, y) = r y := by
    simp only [Φ, φ, ContinuousMap.coe_mk]
    simp
  have hΦu (y : Y) : Φ (u y, y) = y := by
    by_cases hy : y ∈ A
    · exact F.eq_fst _ hy
    · simp only [Φ, φ, ContinuousMap.coe_mk]
      simp [div_self ((coe_ne_zero_iff_notMem hu y).2 hy)]
  obtain ⟨L, hL, hL₀⟩ := hp (f.comp r) (g.comp Φ) fun y ↦ by
    simp [hΦ₀, hfg]
  refine ⟨⟨fun y ↦ L (u y, y), by fun_prop⟩, funext fun y ↦ ?_, fun a ↦ ?_⟩
  · simpa [hΦu] using congrFun hL (u y, y)
  · have hua : u a = 0 := (hu a).2 a.2
    simp [hua, hL₀, hr']

end TauCeti
