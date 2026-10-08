/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.GaloisAction
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.EvensNorm

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
(`TauCeti.pinLift_map_galois`). The swap coordinate of `ρ_a(h)` is the character of `G_K` with
kernel `G_L`, which is `rootSign (σ x) h` for any `x ∈ L ∖ K` (`TauCeti.coordC_kummerInd`).
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

* `TauCeti.pinLift_map_galois`: `g(pinLift w) = (−1)^{rootSign √2 g · c(w)} pinLift w`.
* `TauCeti.coordC_kummerInd`: the swap coordinate of `ρ_a(h)` is `rootSign x h`.
* `TauCeti.twistedBoundary_kummerIndLift`, `TauCeti.twistedBoundaryF2_kummerIndLift`:
  `δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (x²)` at cochain level.

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

/-- **The Galois action on the lift `pinLift`:** `g ∈ G_K` fixes `e₁` and `e₂` and sends
`t = (e₁ − e₂)/√2` to `(−1)^{rootSign r2 g} t`, since `g r2 = ±r2`; so it multiplies `pinLift w` by
`(−1)^{rootSign r2 g · c(w)}`, where `c(w)` is the top coordinate of `w`, which counts the
factors `t`. -/
theorem pinLift_map_galois {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g : AbsoluteGaloisGroup K) (w : WreathC2) :
    (pinLift hr2 w).map g = (-1) ^ (rootSign r2 g * coordC w).val * pinLift hr2 w := by
  have hr0 : r2 ≠ 0 := by
    rintro rfl
    exact two_ne_zero (α := SeparableClosure K) (by simpa using hr2.symm)
  have hφ : (g : SeparableClosure K →+* SeparableClosure K) r2 =
      (-1) ^ (rootSign r2 g).val * r2 := by
    rcases g.apply_eq_or_eq_neg_of_sq_eq (c := (2 : K)) (by rw [hr2, map_ofNat]) with h | h
    · simp [h]
    · have hne : g r2 ≠ r2 := by
        rwa [h, ne_eq, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero, not_or,
          and_iff_right two_ne_zero]
      simp [rootSign_of_apply_ne hne, h, ZMod.val_one]
  refine (map_pinLift_of_map_root hr2 (g : SeparableClosure K →+* SeparableClosure K) _ hφ
    w).trans ?_
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

end NeZero

/-! ### The twisted boundary -/

/-- **The twisted boundary** of a matrix-valued `1`-cochain `x` of `G_K`,
`δ(x)(g, h) = x(g) · g(x(h)) · x(g h)⁻¹`, with `g` acting on the entries. For a cochain with
invertible values, it is identically `1` exactly when `x` is a `1`-cocycle for the action of
`G_K` on `GL₂(Kˢ)` through the entries. -/
def twistedBoundary (x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) :
    Matrix (Fin 2) (Fin 2) (SeparableClosure K) :=
  x q.1 * (x q.2).map q.1 * (x (q.1 * q.2))⁻¹

/-- The twisted boundary at `(g, h)` is `x(g) · g(x(h)) · x(g h)⁻¹`. -/
theorem twistedBoundary_apply
    (x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K))
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundary x (g, h) = x g * (x h).map g * (x (g * h))⁻¹ :=
  (rfl)

open Classical in
/-- **The twisted boundary read in `𝔽₂`:** `0` where the twisted boundary is `1` and `1`
elsewhere. Where the twisted boundary is a sign `±1`, this is its exponent
(`TauCeti.twistedBoundaryF2_eq_of_twistedBoundary_eq`). -/
def twistedBoundaryF2 (x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K))
    (q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K) : ZMod 2 :=
  if twistedBoundary x q = 1 then 0 else 1

/-- Where the twisted boundary is the sign `(−1)^e`, its reading in `𝔽₂` is the exponent `e`. -/
theorem twistedBoundaryF2_eq_of_twistedBoundary_eq [NeZero (2 : SeparableClosure K)]
    {x : AbsoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) (SeparableClosure K)}
    {q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K} {e : ZMod 2}
    (h : twistedBoundary x q = (-1) ^ e.val) : twistedBoundaryF2 x q = e := by
  have hbit : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  rcases hbit e with rfl | rfl
  · simp [twistedBoundaryF2, h]
  · have hne : (-1 : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) ≠ 1 := fun h' =>
      two_ne_zero (α := SeparableClosure K)
        (by simpa [neg_eq_iff_add_eq_zero, one_add_one_eq_two] using congrFun (congrFun h' 0) 0)
    simp [twistedBoundaryF2, h, ZMod.val_one, hne]

/-! ### The lift of the Kummer representation -/

section KummerInd

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The top coordinate of `ρ_a(h)` is `rootSign (σ x) h`** for a generator `x` of the
quadratic extension `L = K(x)`: both are the character of `G_K` with kernel `G_L`. -/
theorem coordC_kummerInd (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2)
    (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {x : L} (hx : x ∉ Set.range (algebraMap K L))
    (h : AbsoluteGaloisGroup K) : coordC (kummerInd σ hdeg a r hr s hs h) = rootSign (σ x) h := by
  have hG := mem_galoisSubgroup_iff_apply_eq_of_finrank_eq_two K L σ hdeg hx (g := h)
  rw [kummerInd_def, coordC_indexTwoInd]
  by_cases hh : h ∈ galoisSubgroup K L σ
  · rw [Subgroup.toAdd_indexTwoCharacter_of_mem _ hh, rootSign_of_apply_eq (hG.1 hh)]
  · rw [Subgroup.toAdd_indexTwoCharacter_of_notMem _ hh, rootSign_of_apply_ne (mt hG.2 hh)]

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
`(−1)^{rootSign √2 g · c(w)}` (`TauCeti.pinLift_map_galois`), and the top coordinate of `ρ_a h` is
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
  have h1 : (-1 : Matrix (Fin 2) (Fin 2) (SeparableClosure K)) ^ 2 = 1 := by simp
  -- Pull the Galois twist `(−1)^{rootSign √2 g · rootSign x h}` of the middle factor out to the
  -- left; what remains is the factor set of `pinLift`.
  rw [twistedBoundary_apply, kummerIndLift_def, kummerIndLift_def, kummerIndLift_def, map_mul,
    pinLift_map_galois hr2, coordC_kummerInd σ hdeg a r hr s hs hx, ← mul_assoc,
    ((Commute.neg_one_right _).pow_right _).eq, mul_assoc _ _ (pinLift hr2 _), mul_assoc,
    pinLift_mul_mul_inv, pow_val_add h1, ← pow_add, ← pow_add, add_comm]

/-- **`δ(\tilde{ρ}_a) = ρ_a^* c_{D₁₆} + (2) ∪ (d)` at cochain level, in `𝔽₂`:** the twisted boundary
of `\tilde{ρ}_a`, read in `𝔽₂`, is `c_{D₁₆}(ρ_a g, ρ_a h) + rootSign √2 g · rootSign x h`. -/
theorem twistedBoundaryF2_kummerIndLift (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) {x : L} (hx : x ∉ Set.range (algebraMap K L)) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) {r2 : SeparableClosure K} (hr2 : r2 ^ 2 = 2)
    (g h : AbsoluteGaloisGroup K) :
    twistedBoundaryF2 (kummerIndLift σ hdeg a r hr s hs hr2) (g, h) =
      wreathD16Cocycle (kummerInd σ hdeg a r hr s hs g, kummerInd σ hdeg a r hr s hs h) +
        rootSign r2 g * rootSign (σ x) h :=
  twistedBoundaryF2_eq_of_twistedBoundary_eq
    (twistedBoundary_kummerIndLift σ hdeg hx a r hr s hs hr2 g h)

end KummerInd

end TauCeti
