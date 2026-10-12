/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.TwistedBoundary
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Frame
import TauCeti.FieldTheory.KrullTopology
import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.CartanDieudonne

/-!
# The twisted boundary of the Kummer lift in a diagonal frame

Let `L/K` be a separable quadratic extension, `σ : L → Kˢ` a `K`-embedding, `a ∈ Lˣ`, and let
`ρ_a : G_K → C₂ ≀ C₂ ⊂ O₂(Kˢ)` be the signed-permutation representation of `TauCeti.kummerInd`.
For a square root `√2 ∈ Kˢ` of `2`, its lift `\tilde{ρ}_a = pinLift ∘ ρ_a` into `Pin⁺`
(`TauCeti.kummerIndLift`) has a twisted boundary `δ(\tilde{ρ}_a)` with values `±1`
(`TauCeti.twistedBoundary`).

Let `(y₀, y₁)` be an orthogonal basis of the transferred form `Tr_*⟨a⟩`, with values
`w_j = Tr_{L/K}(a y_j²)`, and let `c_j ∈ Kˢ` be square roots of the `w_j`. The frame `P` of `y`
(`TauCeti.kummerFrame`) conjugates `ρ_a` into the diagonal cocycle of the Kummer characters of
`w₀` and `w₁` (`TauCeti.kummerFrame_conj`). This file transports that diagonalization to the
twisted boundary:

```text
δ(\tilde{ρ}_a)(g, h) = rootSign c₁ g · rootSign c₀ h + ∂ψ(g, h)
```

in `𝔽₂`, for a continuous `ψ : G_K → 𝔽₂` (`TauCeti.twistedBoundaryF2_kummerIndLift_cohomologous`),
that is, `δ(\tilde{ρ}_a)` is cohomologous to the cup product `(w₁) ∪ (w₀)` at cochain level.

The argument is Serre's. `P` has a `Pin⁺` lift `\tilde{P}` (`TauCeti.exists_isPinLift`), and
changing frame by `\tilde{P}` conjugates the twisted boundary by `\tilde{P}`
(`TauCeti.twistedBoundary_conj`), which leaves the scalar `δ(\tilde{ρ}_a)` unchanged. The
conjugated cochain `g ↦ \tilde{P}⁻¹ \tilde{ρ}_a(g) g(\tilde{P})` and the diagonal lift
`g ↦ e₁^{rootSign c₀ g} e₂^{rootSign c₁ g}` both lift the diagonal cocycle, so they differ by a
sign `(−1)^{ψ(g)}` (`TauCeti.IsPinLift.eq_or_eq_neg`), which is locally constant in `g`. The twisted
boundary of the diagonal lift is the cup product
(`TauCeti.twistedBoundary_pinDiagonalLift_rootSign`) and the sign changes it by `∂ψ`
(`TauCeti.twistedBoundary_neg_one_pow_mul`).

Together with `TauCeti.twistedBoundaryF2_kummerIndLift`, this shows that the pullback
`ρ_a^* c_{D₁₆}`, whose class is the Evens norm `N^{Ev}((a))`, is cohomologous to
`(w₁) ∪ (w₀) + (2) ∪ (d)`.

## Main results

* `TauCeti.twistedBoundaryF2_kummerIndLift_cohomologous`: the twisted boundary of
  `\tilde{ρ}_a`, read in `𝔽₂`, is the cup product of the Kummer characters of `w₁` and `w₀` up to
  the coboundary of a continuous `𝔽₂`-valued cochain.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

open Matrix ContCohomology

universe u

variable {K : Type u} [Field K] [NeZero (2 : K)] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **The twisted boundary of the Kummer lift is cohomologous to a cup product.** Let `y` be an
orthogonal basis of `Tr_*⟨a⟩`, with values `w_j = Tr_{L/K}(a y_j²)`, and let `c_j ∈ Kˢ` be
nonzero square roots of the `w_j`. Then there is a continuous `ψ : G_K → 𝔽₂` with
`δ(\tilde{ρ}_a)(g, h) = rootSign c₁ g · rootSign c₀ h + (ψ h − ψ (g h) + ψ g)` in `𝔽₂`: the
twisted boundary of `\tilde{ρ}_a = kummerIndLift σ hdeg a r hr s hs hr2` is cohomologous to the
cup product `(w₁) ∪ (w₀)` at cochain level. -/
theorem twistedBoundaryF2_kummerIndLift_cohomologous (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K}
    (hr2 : r2 ^ 2 = 2) (y : Fin 2 → L) (hy : Algebra.trace K L ((a : L) * y 0 * y 1) = 0)
    (c : Fin 2 → SeparableClosure K)
    (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K) (Algebra.trace K L ((a : L) * y i ^ 2)))
    (hc0 : ∀ i, c i ≠ 0) :
    ∃ ψ : AbsoluteGaloisGroup K → ZMod 2, Continuous ψ ∧ ∀ g h : AbsoluteGaloisGroup K,
      twistedBoundaryF2 (kummerIndLift σ hdeg a r hr s hs hr2) (g, h) =
        rootSign (c 1) g * rootSign (c 0) h + (ψ h - ψ (g * h) + ψ g) := by
  classical
  have hP g := kummerFrame_conj σ hdeg a r hr s hs y hy c hc hc0 g
  -- A `Pin⁺` lift `Q` of the frame, and the cochain `z` it conjugates `\tilde{ρ}_a` into.
  obtain ⟨Q, hQ⟩ := exists_isPinLift (hP 1).1
  have hQdet : IsUnit Q.det :=
    isUnit_det_of_right_inverse ((mem_orthogonalGroup_iff _ _).1 hQ.mem_orthogonalGroup)
  set z := fun g : AbsoluteGaloisGroup K => Q⁻¹ * kummerIndLift σ hdeg a r hr s hs hr2 g * Q.map g
    with hz_def
  -- `z g` and the diagonal lift both lift the diagonal cocycle, so they differ by a sign.
  have hz g : z g = pinDiagonalLift (fun i => rootSign (c i) g) ∨
      z g = -pinDiagonalLift (fun i => rootSign (c i) g) := by
    have h := (hQ.inv.mul (isPinLift_pinLift hr2 (kummerInd σ hdeg a r hr s hs g))).mul
      (hQ.map (g : SeparableClosure K →+* SeparableClosure K))
    rw [RingHom.coe_coe, (hP g).2, ← kummerIndLift_def] at h
    exact (isPinLift_pinDiagonalLift _).eq_or_eq_neg h
  let ψ g : ZMod 2 := if z g = pinDiagonalLift (fun i => rootSign (c i) g) then 0 else 1
  have hzψ : z = fun g => (-1) ^ (ψ g).val * pinDiagonalLift (fun i => rootSign (c i) g) := by
    funext g
    by_cases h : z g = pinDiagonalLift (fun i => rootSign (c i) g)
    · simp [ψ, h]
    · have hψ : ψ g = 1 := ite_eq_right h
      rw [hψ, (hz g).resolve_left h, ZMod.val_one, pow_one, neg_one_mul]
  refine ⟨ψ, ?_, fun g h => ?_⟩
  · -- `ψ g` only depends on `ρ_a(g)`, on `g(Q)` and on the signs of the `c_i`, all locally
    -- constant in `g`.
    have hρ : IsLocallyConstant (kummerInd σ hdeg a r hr s hs) := by
      rw [kummerInd_def]
      exact isLocallyConstant_indexTwoInd _ _ s hs _ (galoisSubgroup K L σ).isOpen'
        (continuous_galoisKummerCharacter σ a r hr)
    have hQm : IsLocallyConstant fun g : AbsoluteGaloisGroup K => Q.map g :=
      Matrix.isLocallyConstant_map fun _ _ => Algebra.IsIntegral.isIntegral _
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_)
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 hρ g₀,
      (IsLocallyConstant.iff_eventually_eq _).1 hQm g₀,
      Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1
        ((IsLocallyConstant.iff_continuous _).2 (continuous_rootSign (c i))) g₀]
      with g h₁ h₂ h₃
    simp only [ψ, z, kummerIndLift_def, h₁, h₂, h₃]
  · -- The twisted boundary of `z` is the sign of the cup product twisted by `∂ψ`, and, `z` being
    -- `\tilde{ρ}_a` in the frame `Q`, it is the twisted boundary of `\tilde{ρ}_a`.
    apply twistedBoundaryF2_eq_of_eq_sign
    suffices hδ : twistedBoundary (kummerIndLift σ hdeg a r hr s hs hr2) (g, h) =
        (-1) ^ (rootSign (c 1) g * rootSign (c 0) h + (ψ h - ψ (g * h) + ψ g)).val by
      simpa only [Algebra.smul_def, map_pow, map_neg, map_one, mul_one] using hδ
    refine (twistedBoundary_conj_eq_iff _ hQdet ((Commute.neg_one_left Q).pow_left _) _).1 ?_
    rw [← hz_def, hzψ, twistedBoundary_neg_one_pow_mul, twistedBoundary_pinDiagonalLift_rootSign hc,
      ← pow_val_add (by simp), add_comm (rootSign (c 1) g * _)]

end TauCeti
