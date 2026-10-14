/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.Order.Northcott
public import TauCeti.LinearAlgebra.Projectivization.Basic
public import TauCeti.NumberTheory.Height.Basic

/-!
# The Northcott property on projective space

If a field has finitely many elements of bounded scalar height, its finite-dimensional
projective spaces have finitely many points of bounded multiplicative or logarithmic height.
The instances allow callers to use `Northcott.finite_le` and `Northcott.exists_min_image`.
Over a number field the scalar hypothesis follows from Mathlib's number-field instance.

Normalizing a nonzero coordinate to `1` bounds the scalar height of every coordinate of the
representative by the projective height. Such representatives form a finite product of finite
scalar sublevel sets. The statement concerns projective points: tuple heights are invariant
under nonzero scaling, so bounded-height tuples need not form a finite set.

## References

The proof is adapted from Ralf Stephan's `ArithmeticHeights/Northcott.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/e443c2479e19f7665b31d8e94e2317c8ced1ca06/ArithmeticHeights/Northcott.lean),
commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).
The mathematical argument is Hindry–Silverman, *Diophantine Geometry: An Introduction*,
Theorem B.2.3, for points over a fixed number field; see also Bombieri–Gubler,
*Heights in Diophantine Geometry*, Theorem 2.4.9, specialized to projective space and degree `1`.
-/

public section

namespace Projectivization

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- Projective multiplicative height has the Northcott property whenever scalar multiplicative
height does. In particular, this applies to every number field. -/
instance instNorthcottMulHeight [Northcott (mulHeight₁ (K := K))] :
    Northcott (mulHeight (K := K) (ι := ι)) where
  finite_le B := by
    have hpi : {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B}.Finite :=
      Set.Finite.pi' fun _ : ι ↦ Northcott.finite_le (h := mulHeight₁ (K := K)) B
    have hsub : (Subtype.val ⁻¹' {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B} :
        Set {w : ι → K // w ≠ 0}).Finite :=
      hpi.preimage Subtype.val_injective.injOn
    refine (hsub.image (mk' K)).subset ?_
    rintro x hx
    obtain ⟨v, hv, i₀, hi₀, -, rfl⟩ := exists_rep_apply_eq_one x
    refine ⟨⟨v, hv⟩, fun i ↦ ?_, rfl⟩
    have h := mulHeight₁_div_le_mulHeight v i i₀
    rw [hi₀, div_one] at h
    exact h.trans (by rwa [← mulHeight_mk hv])

/-- Projective logarithmic height has the Northcott property whenever projective multiplicative
height does, and hence whenever scalar multiplicative height does. -/
instance instNorthcottLogHeight [Northcott (mulHeight (K := K) (ι := ι))] :
    Northcott (logHeight (K := K) (ι := ι)) := by
  have heq : logHeight (K := K) (ι := ι) = Real.log ∘ mulHeight :=
    funext logHeight_eq_log_mulHeight
  rw [heq]
  exact Northcott.comp_of_bddAbove _ _ fun B ↦
    bddAbove_def.mpr ⟨Real.exp B, fun _ ↦ Real.le_exp_of_log_le⟩

end Projectivization
