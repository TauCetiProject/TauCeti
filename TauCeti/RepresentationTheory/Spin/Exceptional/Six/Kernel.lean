/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.ExteriorSquare
public import TauCeti.LinearAlgebra.ExteriorPower.Kernel
import Mathlib.Data.Set.Card

/-!
# The kernel of the six-dimensional exterior-square representation

The exterior-square action of `SL₄` on `⋀²(K⁴)` has kernel the scalar matrices `±1`. Over a
domain of characteristic different from two this kernel has order two. Thus the exterior-square
orthogonal representation has the same central kernel as the vector representation of `Spin₆`;
the kernel computation is needed to compare these two realizations of the double cover.

The kernel characterization also holds in characteristic two, where the two scalar matrices
coincide. We use the basis criterion for the kernel of an exterior-square action, rather than
computing all the two-by-two minors of a four-by-four matrix.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
-/

public section

namespace TauCeti

variable (K : Type*) [CommRing K] [IsDomain K]

/-- The kernel of the exterior-square orthogonal action of `SL₄` consists of the scalar
matrices `±1`. In characteristic two these are the same matrix. -/
@[simp]
theorem spinSixSpecialLinearToIsometryGroup_eq_one_iff
    (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    spinSixSpecialLinearToIsometryGroup K g = 1 ↔
      (g : Matrix (Fin 4) (Fin 4) K) = 1 ∨ (g : Matrix (Fin 4) (Fin 4) K) = -1 := by
  let f := LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 4 → K)
    ((stdSLRep K 4).asGroupHom g)
  have hf : f.toLinearMap = stdSLRep K 4 g :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap _).trans
      (Representation.asGroupHom_apply _ _)
  have hext : spinSixSpecialLinearToIsometryGroup K g = 1 ↔
      exteriorPower.map 2 f.toLinearMap = LinearMap.id := by
    constructor
    · intro h
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun e : BilinForm.isometryGroup (spinSixWedgeForm K) ↦ e.1 x) h
      simpa [spinSixSpecialLinearToIsometryGroup_apply, Representation.exteriorPower_apply,
        hf] using hx
    · intro h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      simpa [spinSixSpecialLinearToIsometryGroup_apply, Representation.exteriorPower_apply,
        hf] using LinearMap.congr_fun h x
  rw [hext, (Pi.basisFun K (Fin 4)).exteriorPower_map_eq_id_iff_eq_or_eq_neg_id (by decide), hf,
    stdSLRep_apply]
  simp only [← Matrix.toLin'_apply', ← Matrix.toLin'_one, ← map_neg,
    Matrix.toLin'.injective.eq_iff]

/-- Away from characteristic two, the kernel of the exterior-square orthogonal action of
`SL₄` has exactly two elements. -/
theorem card_ker_spinSixSpecialLinearToIsometryGroup [NeZero (2 : K)] :
    Nat.card (spinSixSpecialLinearToIsometryGroup K).ker = 2 := by
  classical
  let gNeg : Matrix.SpecialLinearGroup (Fin 4) K := ⟨-1, by simp [Matrix.det_neg]; norm_num⟩
  have hgNeg : (gNeg : Matrix (Fin 4) (Fin 4) K) = -1 := rfl
  have hker : ((spinSixSpecialLinearToIsometryGroup K).ker : Set _) = {1, gNeg} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, spinSixSpecialLinearToIsometryGroup_eq_one_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← hgNeg, ← Matrix.SpecialLinearGroup.coe_one]
    exact or_congr Subtype.coe_injective.eq_iff Subtype.coe_injective.eq_iff
  have hne : (1 : Matrix.SpecialLinearGroup (Fin 4) K) ≠ gNeg := by
    intro h
    have hentry := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) K ↦
      (g : Matrix (Fin 4) (Fin 4) K) 0 0) h
    have : (1 : K) = -1 := by simpa [hgNeg] using hentry
    exact NeZero.ne (2 : K)
      (by simpa only [one_add_one_eq_two] using eq_neg_iff_add_eq_zero.mp this)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hker, Set.ncard_pair hne]

end TauCeti
