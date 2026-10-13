/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge
import TauCeti.GroupTheory.Perm.Inversion

/-!
# Bracket wedges of continuous alternating maps

This file specializes the paired wedge to a continuous bilinear bracket. It provides the
bracket-valued product, its graded skew-symmetry when the bracket is skew-symmetric, and its
graded Jacobi identity, the algebraic laws of Lie-algebra-valued differential forms.

The bracket wedge is neither associative nor graded commutative. Its graded Jacobi identity
`(-1)^{km} [[φ ∧ ψ] ∧ χ] + (-1)^{kl} [[ψ ∧ χ] ∧ φ] + (-1)^{lm} [[χ ∧ φ] ∧ ψ] = 0`
holds whenever the bracket satisfies the cyclic Jacobi identity
`[[a, b], c] + [[b, c], a] + [[c, a], b] = 0`, which is its degree-zero case; no skew-symmetry is
needed.

## References

* Loring W. Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Graduate Texts in Mathematics 275, Springer, 2017, §21.
-/

public section

namespace TauCeti

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]
  {k l : ℕ}

/-- The bracket wedge of forms with values in `F`, obtained by applying the continuous bilinear
bracket `β` through the paired wedge. -/
noncomputable def bracketWedge (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    E [⋀^Fin (k + l)]→L[ℝ] F :=
  wedgeWith β φ ψ

-- Certify the definitional equality locally: the exported theorem cannot unfold the definition.
private theorem bracketWedge_def_aux (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β φ ψ = wedgeWith β φ ψ := rfl

/-- The bracket wedge is the paired wedge along the bracket. -/
theorem bracketWedge_def (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β φ ψ = wedgeWith β φ ψ := bracketWedge_def_aux β φ ψ

/-- The bracket wedge is given by the signed permutation formula for `wedgeWith`. -/
theorem bracketWedge_apply (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F)
    (v : Fin (k + l) → E) :
    bracketWedge β φ ψ v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
          β (φ (fun i => v (sigma (Fin.castAdd l i))))
            (ψ (fun j => v (sigma (Fin.natAdd k j)))) := by
  rw [bracketWedge_def, wedgeWith_apply]

/-- The bracket wedge is additive in its first form. -/
@[simp]
theorem bracketWedge_add_left (β : F →L[ℝ] F →L[ℝ] F)
    (φ φ' : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β (φ + φ') ψ = bracketWedge β φ ψ + bracketWedge β φ' ψ := by
  simpa only [bracketWedge_def] using wedgeWith_add_left β φ φ' ψ

/-- The bracket wedge is additive in its second form. -/
@[simp]
theorem bracketWedge_add_right (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ ψ' : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β φ (ψ + ψ') = bracketWedge β φ ψ + bracketWedge β φ ψ' := by
  simpa only [bracketWedge_def] using wedgeWith_add_right β φ ψ ψ'

/-- The bracket wedge respects scalar multiplication in its first form. -/
@[simp]
theorem bracketWedge_smul_left (β : F →L[ℝ] F →L[ℝ] F) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β (c • φ) ψ = c • bracketWedge β φ ψ := by
  simpa only [bracketWedge_def] using wedgeWith_smul_left β c φ ψ

/-- The bracket wedge respects scalar multiplication in its second form. -/
@[simp]
theorem bracketWedge_smul_right (β : F →L[ℝ] F →L[ℝ] F) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β φ (c • ψ) = c • bracketWedge β φ ψ := by
  simpa only [bracketWedge_def] using wedgeWith_smul_right β c φ ψ

/-- The bracket wedge vanishes when its first form is zero. -/
@[simp]
theorem bracketWedge_zero_left (β : F →L[ℝ] F →L[ℝ] F)
    (ψ : E [⋀^Fin l]→L[ℝ] F) :
    bracketWedge β (0 : E [⋀^Fin k]→L[ℝ] F) ψ = 0 := by
  simpa only [bracketWedge_def] using (wedgeWith_zero_left β ψ : _)

/-- The bracket wedge vanishes when its second form is zero. -/
@[simp]
theorem bracketWedge_zero_right (β : F →L[ℝ] F →L[ℝ] F)
    (φ : E [⋀^Fin k]→L[ℝ] F) :
    bracketWedge β φ (0 : E [⋀^Fin l]→L[ℝ] F) = 0 := by
  simpa only [bracketWedge_def] using (wedgeWith_zero_right β φ : _)

/-- A skew-symmetric bracket induces graded skew-symmetry on the bracket wedge. -/
theorem bracketWedge_skew {β : F →L[ℝ] F →L[ℝ] F} (hβ : ∀ a b, β a b = -β b a)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F)
    (v : Fin (k + l) → E) :
    bracketWedge β φ ψ v =
      -((-1 : ℝ) ^ (k * l) • bracketWedge β ψ φ (v ∘ Fin.cast (Nat.add_comm l k))) := by
  simpa only [bracketWedge_def] using wedgeWith_anticomm hβ φ ψ v

/-- The graded Jacobi identity of the bracket wedge of a `k`-form `φ`, an `l`-form `ψ` and an
`m`-form `χ`: `(-1)^{km} [[φ ∧ ψ] ∧ χ] + (-1)^{kl} [[ψ ∧ χ] ∧ φ] + (-1)^{lm} [[χ ∧ φ] ∧ ψ] = 0`,
the three terms being identified in degree `k + l + m` by `Fin.cast`. The only hypothesis is the
cyclic Jacobi identity of the bracket, which is the case of three `0`-forms; for a skew-symmetric
bracket it is the usual Jacobi identity. -/
theorem bracketWedge_jacobi {m : ℕ} {β : F →L[ℝ] F →L[ℝ] F}
    (hβ : ∀ a b c, β (β a b) c + β (β b c) a + β (β c a) b = 0)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F) (χ : E [⋀^Fin m]→L[ℝ] F)
    (v : Fin (k + l + m) → E) :
    (-1 : ℝ) ^ (k * m) • bracketWedge β (bracketWedge β φ ψ) χ v +
      (-1 : ℝ) ^ (k * l) • bracketWedge β (bracketWedge β ψ χ) φ
        (v ∘ Fin.cast (show l + m + k = k + l + m by omega)) +
      (-1 : ℝ) ^ (l * m) • bracketWedge β (bracketWedge β χ φ) ψ
        (v ∘ Fin.cast (show m + k + l = k + l + m by omega)) = 0 := by
  -- Expand the three iterated wedges as signed sums over permutations of their own index sets.
  simp only [bracketWedge_def, wedgeWith_wedgeWith_left_apply, Function.comp_apply]
  -- Rotate the index blocks of the second sum once, and of the third twice, into the order
  -- `k, l, m` of the first.
  have h₂ := sum_sign_smul_rotate_blocks (fun x y z => β (β (ψ y) (χ z)) (φ x)) v
  have h₃ := sum_sign_smul_rotate_blocks (k := l) (l := m) (m := k)
    (fun y z x => β (β (χ z) (φ x)) (ψ y))
    (fun i => v (Fin.cast (show l + m + k = k + l + m by omega) i))
  simp only [Fin.cast_cast] at h₃
  rw [h₂, h₃, sum_sign_smul_rotate_blocks (fun x y z => β (β (χ z) (φ x)) (ψ y)) v]
  -- Every term now carries the scalar `(-1) ^ (k * m) / (k! l! m!)`, and the three summands add
  -- up to the cyclic Jacobi sum.
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul]
  have hsq (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  set C := (-1 : ℝ) ^ (k * m) * ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹
  have hsign₂ : (-1 : ℝ) ^ (k * l) *
      (((l.factorial : ℝ) * m.factorial * k.factorial)⁻¹ * (-1) ^ (k * (l + m))) = C := by
    rw [show k * (l + m) = k * m + k * l by ring, pow_add]
    linear_combination C * hsq (k * l)
  have hsign₃ : (-1 : ℝ) ^ (l * m) * (((m.factorial : ℝ) * k.factorial * l.factorial)⁻¹ *
      ((-1) ^ (l * (m + k)) * (-1) ^ (k * (l + m)))) = C := by
    rw [show l * (m + k) = l * m + k * l by ring, show k * (l + m) = k * l + k * m by ring,
      pow_add, pow_add]
    linear_combination C * (((-1 : ℝ) ^ (k * l)) ^ 2 * hsq (l * m) + hsq (k * l))
  rw [hsign₂, hsign₃, ← smul_add, ← smul_add, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine (congrArg _ (Finset.sum_eq_zero fun σ _ => ?_)).trans (smul_zero _)
  rw [← smul_add, ← smul_add, hβ, smul_zero]

end TauCeti
