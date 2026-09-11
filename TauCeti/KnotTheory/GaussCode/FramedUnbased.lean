/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Unbased

/-!
# Framed unbased Gauss codes

A framed unbased Gauss code forgets the traversal basepoint while retaining the integer framing.
The underlying oriented code is already quotiented by cyclic rotation, while its Seifert-relative
framing is an integer independent of the traversal basepoint. This is the framed refinement of
`OrientedGaussCode`, following the framing convention of Gompf and Stipsicz,
*4-Manifolds and Kirby Calculus*, Section 4.5.
-/

public section

namespace TauCeti

/-- An unbased oriented Gauss code equipped with a Seifert-relative framing coefficient. -/
structure FramedOrientedGaussCode (n : ℕ) where
  /-- Forget the framing, retaining the unbased oriented code. -/
  forgetFraming : OrientedGaussCode n
  /-- The integer framing coefficient relative to the Seifert framing. -/
  framing : ℤ

namespace FramedOrientedGaussCode

variable {n : ℕ}

/-- A framed code is determined by its underlying oriented code and framing coefficient. -/
@[ext] theorem ext {D E : FramedOrientedGaussCode n}
    (hcode : D.forgetFraming = E.forgetFraming) (hframing : D.framing = E.framing) : D = E := by
  cases D
  cases E
  simp_all

/-- Reflection reverses the framing coefficient. -/
def mirror (D : FramedOrientedGaussCode n) : FramedOrientedGaussCode n :=
  ⟨D.forgetFraming.mirror, -D.framing⟩

/-- Forgetting framing commutes with reflection. -/
@[simp] theorem forgetFraming_mirror (D : FramedOrientedGaussCode n) :
    D.mirror.forgetFraming = D.forgetFraming.mirror := (rfl)

/-- Reflection negates the framing coefficient. -/
@[simp] theorem framing_mirror (D : FramedOrientedGaussCode n) :
    D.mirror.framing = -D.framing := (rfl)

/-- Reflection is involutive. -/
@[simp] theorem mirror_mirror (D : FramedOrientedGaussCode n) : D.mirror.mirror = D := by
  ext <;> simp

/-- Reverse the orientation while preserving the framing coefficient. -/
def reverse (D : FramedOrientedGaussCode n) : FramedOrientedGaussCode n :=
  ⟨D.forgetFraming.reverse, D.framing⟩

/-- Forgetting framing commutes with orientation reversal. -/
@[simp] theorem forgetFraming_reverse (D : FramedOrientedGaussCode n) :
    D.reverse.forgetFraming = D.forgetFraming.reverse := (rfl)

/-- Orientation reversal preserves the framing coefficient. -/
@[simp] theorem framing_reverse (D : FramedOrientedGaussCode n) :
    D.reverse.framing = D.framing := (rfl)

/-- Orientation reversal is involutive. -/
@[simp] theorem reverse_reverse (D : FramedOrientedGaussCode n) : D.reverse.reverse = D := by
  ext <;> simp

/-- Reflection and orientation reversal commute. -/
@[simp] theorem mirror_reverse (D : FramedOrientedGaussCode n) :
    D.reverse.mirror = D.mirror.reverse := by
  ext <;> simp

/-- Relabel the crossings of a framed unbased code. -/
def relabel (D : FramedOrientedGaussCode n) (e : Fin n ≃ Fin n) : FramedOrientedGaussCode n :=
  ⟨D.forgetFraming.relabel e, D.framing⟩

/-- Forgetting framing commutes with crossing relabelling. -/
@[simp] theorem forgetFraming_relabel (D : FramedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).forgetFraming = D.forgetFraming.relabel e := (rfl)

/-- Crossing relabelling preserves the framing coefficient. -/
@[simp] theorem framing_relabel (D : FramedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).framing = D.framing := (rfl)

/-- Relabelling by the identity has no effect. -/
@[simp] theorem relabel_refl (D : FramedOrientedGaussCode n) :
    D.relabel (Equiv.refl _) = D := by
  ext <;> simp

/-- Successive crossing relabellings compose. -/
@[simp] theorem relabel_relabel (D : FramedOrientedGaussCode n) (e f : Fin n ≃ Fin n) :
    (D.relabel e).relabel f = D.relabel (e.trans f) := by
  ext <;> simp

/-- Reflection commutes with crossing relabelling. -/
@[simp] theorem mirror_relabel (D : FramedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).mirror = D.mirror.relabel e := by
  ext <;> simp

/-- Orientation reversal commutes with crossing relabelling. -/
@[simp] theorem reverse_relabel (D : FramedOrientedGaussCode n) (e : Fin n ≃ Fin n) :
    (D.relabel e).reverse = D.reverse.relabel e := by
  ext <;> simp

end FramedOrientedGaussCode

namespace FramedBasedOrientedGaussCode

variable {n : ℕ}

/-- Forget the traversal basepoint while retaining the framing coefficient. -/
def forgetBasepoint (D : FramedBasedOrientedGaussCode n) : FramedOrientedGaussCode n :=
  ⟨D.forgetFraming.forgetBasepoint, D.framing⟩

/-- Forgetting framing and forgetting the basepoint commute. -/
@[simp] theorem forgetFraming_forgetBasepoint (D : FramedBasedOrientedGaussCode n) :
    D.forgetBasepoint.forgetFraming = D.forgetFraming.forgetBasepoint := (rfl)

/-- Forgetting the basepoint retains the framing coefficient. -/
@[simp] theorem framing_forgetBasepoint (D : FramedBasedOrientedGaussCode n) :
    D.forgetBasepoint.framing = D.framing := (rfl)

/-- Two framed based codes have the same unbased presentation exactly when their underlying
codes differ by cyclic rotation and their framing coefficients agree. -/
@[simp] theorem forgetBasepoint_eq_iff {D E : FramedBasedOrientedGaussCode n} :
    D.forgetBasepoint = E.forgetBasepoint ↔
      (∃ k : ℤ,
        (BasedOrientedGaussCode.rotateBasepoint n ^ k) D.forgetFraming = E.forgetFraming) ∧
      D.framing = E.framing := by
  constructor
  · intro h
    exact ⟨BasedOrientedGaussCode.forgetBasepoint_eq_iff.mp
      (congrArg FramedOrientedGaussCode.forgetFraming h),
      congrArg FramedOrientedGaussCode.framing h⟩
  · rintro ⟨hcode, hframing⟩
    exact FramedOrientedGaussCode.ext
      (BasedOrientedGaussCode.forgetBasepoint_eq_iff.mpr hcode) hframing

end FramedBasedOrientedGaussCode

end TauCeti
