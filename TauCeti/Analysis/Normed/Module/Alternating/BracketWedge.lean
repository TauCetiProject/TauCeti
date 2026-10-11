/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge

/-!
# Bracket wedges of continuous alternating maps

This file specializes the paired wedge to a continuous skew-symmetric bracket. It provides the
bracket-valued product and its graded skew-symmetry, the first algebraic laws needed for
Lie-algebra-valued differential forms.

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

end TauCeti
