/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.GaloisAction
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.EvensNorm
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.TwistedBoundary

/-!
# The twisted boundary of the `Pin⁺` lift of a Kummer representation

Let `K` be a field in which `2 ≠ 0`, let `L/K` be a quadratic extension with an embedding
`σ : L → Kˢ`, let `a ∈ Lˣ`, and let `ρ_a = Ind α_a : G_K → C₂ ≀ C₂` be the representation induced
from the Kummer character of `a` on `G_L` (`TauCeti.kummerInd`). Through the signed-permutation
representation `C₂ ≀ C₂ ⊂ O₂`, it is the action of `G_K` on the roots of `X² − σ a` and of its
conjugate. For a square root `r2` of `2` in `Kˢ`, composing `ρ_a` with the lift
`TauCeti.pinLift : C₂ ≀ C₂ → D₁₆ ⊂ M₂(Kˢ)` gives a lift `\tilde{ρ}_a` of `ρ_a` to `Pin⁺`
(`TauCeti.kummerIndLift`).

The matrix `\tilde{ρ}_a(g)` has entries in `Kˢ`, on which `G_K` acts, so `\tilde{ρ}_a` has
a **twisted boundary**
`δ(\tilde{ρ}_a)(g, h) = \tilde{ρ}_a(g) · g(\tilde{ρ}_a(h)) · \tilde{ρ}_a(g h)⁻¹`
(`TauCeti.twistedBoundary`). Two signs enter it. The factor set of `pinLift` is the `D₁₆`
extension cocycle `c_{D₁₆}`; and `g` fixes `e₁` and `e₂` but sends `t = (e₁ − e₂)/√2` to `±t`
according to the sign `rootSign r2 g` of `√2`, so it multiplies `pinLift w` by
`(−1)^{rootSign r2 g · c(w)}`, where `c(w)` is the swap coordinate of `w`
(`TauCeti.map_pinLift_galois`). The swap coordinate of `ρ_a(h)` is the character of `G_K` with
kernel `G_L`, which is `rootSign (σ x) h` for any `x ∈ L ∖ K`
(`TauCeti.coordC_kummerInd`, in `TauCeti.FieldTheory.GaloisCohomology.MuTwo.EvensNorm`).
Hence, as an identity of matrices,

```text
δ(\tilde{ρ}_a)(g, h) = (−1)^{c_{D₁₆}(ρ_a g, ρ_a h) + rootSign √2 g · rootSign x h}
```

(`TauCeti.twistedBoundary_kummerIndLift`): for `x` a square root of the discriminant `d` of
`L/K`, this is `δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (d)` at cochain level. The `𝔽₂`-reading of
the twisted boundary (`TauCeti.twistedBoundaryF2`) records its exponent
(`TauCeti.twistedBoundaryF2_kummerIndLift`).

This is the cochain identity by which Serre's second proof of his Théorème 1′ compares the
Evens norm `N^{Ev}((a))`, the class of `ρ_a^* c_{D₁₆}`, with the second Stiefel–Whitney class of
the trace form `Tr_*⟨a⟩`: the correction `(2) ∪ (d)` involves the discriminant of `L/K`, and not
that of `Tr_*⟨a⟩`.

## Main definitions

* `TauCeti.twistedBoundary`: the twisted boundary of a `GL₂(Kˢ)`-valued `1`-cochain of `G_K`.
* `TauCeti.twistedBoundaryF2`: the twisted boundary read in `𝔽₂`.
* `TauCeti.kummerIndLift`: the lift `\tilde{ρ}_a = pinLift ∘ ρ_a`.

## Main results

* `TauCeti.twistedBoundary_conj`: changing frame by `Q` conjugates the twisted boundary by `Q`.
* `TauCeti.map_pinLift_galois`: `g(pinLift w) = (−1)^{rootSign √2 g · c(w)} pinLift w`.
* `TauCeti.twistedBoundary_kummerIndLift`, `TauCeti.twistedBoundaryF2_kummerIndLift`:
  `δ(\tilde{ρ}_a)(g, h) = (−1)^{c_{D₁₆}(ρ_a g, ρ_a h) + rootSign √2 g · rootSign (σ x) h}` for
  any `x ∈ L ∖ K`; for `x` a square root of the discriminant `d ∈ K` of `L/K`, this is
  `δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (d)` at cochain level.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256.
-/

public section

noncomputable section

namespace TauCeti

open Matrix WreathC2 ContCohomology

universe u

variable {K : Type u} [Field K]

/-! ### The Galois action on the lift -/

section NeZero

variable [NeZero (2 : K)]

/-- `g ∈ G_K` sends a square root `r2` of `2` to `(−1)^{rootSign r2 g} r2`. -/
private theorem apply_sqrt_two {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g : AbsoluteGaloisGroup K) :
    (g : SeparableClosure K →+* SeparableClosure K) r2 = (-1) ^ (rootSign r2 g).val * r2 := by
  have hr0 : r2 ≠ 0 := by
    rintro rfl
    exact two_ne_zero (α := SeparableClosure K) (by simpa using hr2.symm)
  rcases g.apply_eq_or_eq_neg_of_sq_eq (c := (2 : K)) (by rw [hr2, map_ofNat]) with h | h
  · simp [h]
  · have hne : g r2 ≠ r2 := by
      rwa [h, ne_eq, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero, not_or,
        and_iff_right two_ne_zero]
    simp [rootSign_of_apply_ne hne, h, ZMod.val_one]

/-- **The Galois action on the lift `pinLift`:** `g ∈ G_K` fixes `e₁` and `e₂` and sends
`t = (e₁ − e₂)/√2` to `(−1)^{rootSign r2 g} t`, since `g r2 = ±r2`; so it multiplies `pinLift w` by
`(−1)^{rootSign r2 g · c(w)}`, where `c(w)` is the top coordinate of `w`, which counts the
factors `t`. -/
theorem map_pinLift_galois {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g : AbsoluteGaloisGroup K) (w : WreathC2) :
    (pinLift hr2 w).map g = (-1) ^ (rootSign r2 g * coordC w).val * pinLift hr2 w := by
  refine (map_pinLift_of_map_root hr2 (g : SeparableClosure K →+* SeparableClosure K) _
    (apply_sqrt_two hr2 g) w).trans ?_
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

end NeZero

/-! ### Frame changes and sign twists -/

/-- **A change of frame does not change a twisted boundary commuting with it:** for an invertible
matrix `Q` and a matrix `S` commuting with `Q` (for instance a scalar such as a sign `(−1)^n`), the
twisted boundary of `g ↦ Q⁻¹ · x(g) · g(Q)` is `S` exactly where that of `x` is. -/
theorem twistedBoundary_conj_eq_iff
    (x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K))
    {Q S : Matrix (Fin 2) (Fin 2) (SeparableClosure K)} (hQ : IsUnit Q.det) (hS : Commute S Q)
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) :
    twistedBoundary (fun g => Q⁻¹ * x g * Q.map g) q = S ↔ twistedBoundary x q = S := by
  have hc := hS.eq
  rw [twistedBoundary_conj x Q hQ q.1 q.2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · calc twistedBoundary x q
        _ = Q * (Q⁻¹ * twistedBoundary x q * Q) * Q⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one,
            Matrix.mul_nonsing_inv_cancel_left _ _ hQ]
        _ = S := by
          rw [h, ← hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
  · rw [h, Matrix.mul_assoc, hc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mul]

/-- **A sign twist changes the twisted boundary by a coboundary:** multiplying a cochain `x` by
the signs `(−1)^{ψ(g)}` multiplies its twisted boundary by `(−1)^{∂ψ}`, where
`∂ψ(g, h) = ψ(h) − ψ(g h) + ψ(g)` is the coboundary of `ψ : G_K → 𝔽₂`. -/
theorem twistedBoundary_neg_one_pow_mul
    (x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K))
    (ψ : AbsoluteGaloisGroup K → ZMod 2) (g h : AbsoluteGaloisGroup K) :
    twistedBoundary (fun g => (-1) ^ (ψ g).val * x g) (g, h) =
      (-1) ^ (ψ h - ψ (g * h) + ψ g).val * twistedBoundary x (g, h) := by
  have hsq : (-1 : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) ^ 2 = 1 := by simp
  -- The signs are central, are their own inverses, and are scalars.
  have hc (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) : Commute ((-1) ^ n) M :=
    (Commute.neg_one_left M).pow_left n
  have hinv (n : ℕ) : ((-1 : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) ^ n)⁻¹ = (-1) ^ n :=
    inv_eq_left_inv (by rw [← pow_add, ← two_mul, pow_mul, hsq, one_pow])
  have hs (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) :
      (-1) ^ n * M = ((-1 : SeparableClosure K) ^ n) • M := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  have hsq' : (-1 : SeparableClosure K) ^ 2 = 1 := by simp
  rw [twistedBoundary_apply, twistedBoundary_apply, ← AlgEquiv.mapMatrix_apply, map_mul, map_pow,
    map_neg, map_one, AlgEquiv.mapMatrix_apply, Matrix.mul_inv_rev, hinv,
    ← (hc _ (x (g * h))⁻¹).eq, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  simp only [hs, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, pow_val_add hsq']
  congr 1
  ring

/-- **The twisted boundary of a diagonal lift of Kummer characters is a cup product:** if
`c₀², c₁² ∈ K`, the twisted boundary of `g ↦ e₁^{rootSign c₀ g} e₂^{rootSign c₁ g}` is
`(g, h) ↦ (−1)^{rootSign c₁ g · rootSign c₀ h}`, the sign of the cup product of the Kummer
characters of `c₁²` and `c₀²`. -/
theorem twistedBoundary_pinDiagonalLift_rootSign {c : Fin 2 → SeparableClosure K}
    {w : Fin 2 → K} (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K) (w i))
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundary (fun g => pinDiagonalLift fun i => rootSign (c i) g) (g, h) =
      (-1) ^ (rootSign (c 1) g * rootSign (c 0) h).val := by
  have hmul : (fun i => rootSign (c i) (g * h)) =
      (fun i => rootSign (c i) g) + fun i => rootSign (c i) h := funext fun i =>
    rootSign_mul (g.apply_eq_or_eq_neg_of_sq_eq (hc i)) (h.apply_eq_or_eq_neg_of_sq_eq (hc i))
  have hD := (isPinLift_pinDiagonalLift (R := SeparableClosure K)
    fun i => rootSign (c i) (g * h)).mem_orthogonalGroup
  have hmap : (pinDiagonalLift fun i => rootSign (c i) h).map g =
      (pinDiagonalLift fun i => rootSign (c i) h : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) :=
    map_pinDiagonalLift (g : SeparableClosure K →+* SeparableClosure K) _
  rw [twistedBoundary_apply, hmap, pinDiagonalLift_mul, ← hmul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_right_inverse ((mem_orthogonalGroup_iff _ _).1 hD)),
    Matrix.mul_one]

/-! ### The lift of the Kummer representation -/

section KummerInd

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]

variable [NeZero (2 : K)]

/-- **The lift `\tilde{ρ}_a = pinLift ∘ ρ_a`** of the representation
`ρ_a = kummerInd σ hdeg a r hr s hs` into `D₁₆ ⊂ M₂(Kˢ)`, for a square root `r2` of `2` in `Kˢ`. -/
def kummerIndLift (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g : AbsoluteGaloisGroup K) : Matrix (Fin 2) (Fin 2) (SeparableClosure K) :=
  pinLift hr2 (kummerInd σ hdeg a r hr s hs g)

/-- `\tilde{ρ}_a(g)` is the `pinLift` of `ρ_a(g)`. -/
theorem kummerIndLift_def (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2)
    (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g : AbsoluteGaloisGroup K) :
    kummerIndLift σ hdeg a r hr s hs hr2 g = pinLift hr2 (kummerInd σ hdeg a r hr s hs g) :=
  (rfl)

/-- **`δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (d)` at cochain level,** as an identity of matrices:
`δ(\tilde{ρ}_a)(g, h) = (−1)^{c_{D₁₆}(ρ_a g, ρ_a h) + rootSign √2 g · rootSign x h}` for a generator
`x` of `L = K(x)`, such as a square root of the discriminant `d`. The factor set of `pinLift` is
`c_{D₁₆}` (`TauCeti.pinLift_mul_mul_inv`), `g` twists `pinLift w` by the sign
`(−1)^{rootSign √2 g · c(w)}` (`TauCeti.map_pinLift_galois`), and the top coordinate of `ρ_a h` is
`rootSign (σ x) h` (`TauCeti.coordC_kummerInd`). This `(2) ∪ (d)` is Serre's `(2)(d_E)`: it is
the discriminant of `L/K` that enters, and not that of `Tr_*⟨a⟩`. -/
theorem twistedBoundary_kummerIndLift (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) {x : L} (hx : x ∉ Set.range (algebraMap K L)) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundary (kummerIndLift σ hdeg a r hr s hs hr2) (g, h) =
      (-1) ^ (wreathD16Cocycle (kummerInd σ hdeg a r hr s hs g, kummerInd σ hdeg a r hr s hs h) +
        rootSign r2 g * rootSign (σ x) h).val := by
  rw [twistedBoundary_apply, kummerIndLift_def, kummerIndLift_def, kummerIndLift_def, map_mul]
  refine (pinLift_mul_map_mul_inv hr2 (g : SeparableClosure K →+* SeparableClosure K) _
    (apply_sqrt_two hr2 g) _ _).trans ?_
  rw [coordC_kummerInd σ hdeg a r hr s hs hx, Algebra.smul_def, mul_one, map_pow, map_neg,
    map_one]

/-- **`δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (d)` at cochain level, in `𝔽₂`:** the twisted boundary
of `\tilde{ρ}_a`, read in `𝔽₂`, is `c_{D₁₆}(ρ_a g, ρ_a h) + rootSign √2 g · rootSign x h`. -/
theorem twistedBoundaryF2_kummerIndLift (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) {x : L} (hx : x ∉ Set.range (algebraMap K L)) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundaryF2 (kummerIndLift σ hdeg a r hr s hs hr2) (g, h) =
      wreathD16Cocycle (kummerInd σ hdeg a r hr s hs g, kummerInd σ hdeg a r hr s hs h) +
        rootSign r2 g * rootSign (σ x) h := by
  apply twistedBoundaryF2_eq_of_eq_sign
  simpa only [Algebra.smul_def, map_pow, map_neg, map_one, mul_one] using
    (twistedBoundary_kummerIndLift σ hdeg hx a r hr s hs hr2 g h)

end KummerInd

end TauCeti
