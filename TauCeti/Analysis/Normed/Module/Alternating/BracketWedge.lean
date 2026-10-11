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

/-- A skew-symmetric bracket induces graded skew-symmetry on the bracket wedge. -/
theorem bracketWedge_skew {β : F →L[ℝ] F →L[ℝ] F} (hβ : ∀ a b, β a b = -β b a)
    (φ : E [⋀^Fin k]→L[ℝ] F) (ψ : E [⋀^Fin l]→L[ℝ] F)
    (v : Fin (k + l) → E) :
    bracketWedge β φ ψ v =
      -((-1 : ℝ) ^ (k * l) • bracketWedge β ψ φ (v ∘ Fin.cast (Nat.add_comm l k))) := by
  have hflip : β.flip = -β := by
    ext a b
    simp only [ContinuousLinearMap.flip_apply, neg_apply]
    exact hβ b a
  rw [bracketWedge, wedgeWith_flip, hflip,
    show -β = (-1 : ℝ) • β by symm; exact neg_one_smul ℝ β,
    wedgeWith_smul_pairing]
  simp [bracketWedge]

end TauCeti
