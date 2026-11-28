/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import TauCeti.NumberTheory.FrobeniusRiesz.ThickLetterOrbit
import Mathlib.Algebra.Group.Subgroup.Map
import TauCeti.Algebra.Group.Subgroup.SplitKernel
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.Data.ZMod.Two

/-!
# Involution coordinates for cyclic CM hosts

Let `χq` and `χd` be the quadratic characters cutting out the two auxiliary quadratic
fields, written with values in the multiplicative copy of `ZMod 2`. Complex conjugation
`c` is nontrivial on both fields; the ramified involution `σ` at the second auxiliary
prime is trivial on the first field and nontrivial on the second. The joint kernel `A`
and the two involutions then give product coordinates for the host Galois group.

The coordinates are ordered as in Levent Alpöge's `Formalism.HC.Frame.iod` and
`Formalism.HC.Frame.placeOf` (https://github.com/leanprover-community/riemann-hypothesis,
revision `40e56ba`). The subgroup fixing the second quadratic field consists exactly of
points with equal involution coordinates. Thus passage to its representatives by
complex conjugation changes only the first coordinate; the second coordinate tests
whether the Frobenius orbit can meet thick places.
-/

public section

open Multiplicative

namespace TauCeti.FrobeniusRiesz

private def involutionCoordinates {G : Type*} [Monoid G]
    (χq χd : G →* Multiplicative (ZMod 2)) :
    G →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := ofAdd ((χq g).toAdd, (χd g).toAdd - (χq g).toAdd)
  map_one' := by simp
  map_mul' x y := by simp [← ofAdd_add, sub_add_sub_comm]

private theorem ker_involutionCoordinates {G : Type*} [Group G]
    (χq χd : G →* Multiplicative (ZMod 2)) :
    (involutionCoordinates χq χd).ker = χq.ker ⊓ χd.ker := by
  ext g
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, involutionCoordinates,
    MonoidHom.coe_mk, OneHom.coe_mk, ← toAdd.injective.eq_iff, toAdd_ofAdd, toAdd_one,
    Prod.mk_eq_zero, sub_eq_zero]
  grind

variable {G : Type*} [CommGroup G]

private theorem involutionCoordinates_rightInverse
    (χq χd : G →* Multiplicative (ZMod 2)) (c σ : G) (hc : c ^ 2 = 1) (hσ : σ ^ 2 = 1)
    (hqc : χq c = ofAdd 1) (hdc : χd c = ofAdd 1)
    (hqσ : χq σ = 1) (hdσ : χd σ = ofAdd 1) :
    Function.RightInverse ((zmodProdMonoidHomEquiv 2 G).symm (⟨c, hc⟩, ⟨σ, hσ⟩))
      (involutionCoordinates χq χd) := by
  intro a
  rw [← ofAdd_toAdd a, zmodProdMonoidHomEquiv_symm_apply]
  obtain ⟨u, v⟩ := a.toAdd
  rcases ZMod.eq_zero_or_eq_one u with rfl | rfl <;>
    rcases ZMod.eq_zero_or_eq_one v with rfl | rfl <;>
    simp [involutionCoordinates, hqc, hdc, hqσ, hdσ]

/-- Split the host group into the joint kernel of the two quadratic characters, the
complex-conjugation coordinate and the ramified-involution coordinate, in that order. -/
noncomputable def cyclicHostInvolutionEquiv
    (χq χd : G →* Multiplicative (ZMod 2)) (c σ : G) (hc : c ^ 2 = 1) (hσ : σ ^ 2 = 1)
    (hqc : χq c = ofAdd 1) (hdc : χd c = ofAdd 1)
    (hqσ : χq σ = 1) (hdσ : χd σ = ofAdd 1) :
    G ≃* ↥(χq.ker ⊓ χd.ker) × Multiplicative (ZMod 2 × ZMod 2) :=
  ((involutionCoordinates χq χd).mulEquivKerProdOfRightInverse _
    (involutionCoordinates_rightInverse χq χd c σ hc hσ hqc hdc hqσ hdσ)
    (fun _ _ ↦ Commute.all _ _)).trans
    ((MulEquiv.subgroupCongr (ker_involutionCoordinates χq χd)).prodCongr (MulEquiv.refl _))

variable {χq χd : G →* Multiplicative (ZMod 2)} {c σ : G} {hc : c ^ 2 = 1} {hσ : σ ^ 2 = 1}
  {hqc : χq c = ofAdd 1} {hdc : χd c = ofAdd 1} {hqσ : χq σ = 1} {hdσ : χd σ = ofAdd 1}

/-- The two involution coordinates are the first character and the difference of the
second character and the first, in additive notation. -/
@[simp] theorem cyclicHostInvolutionEquiv_snd (g : G) :
    (cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ g).2 =
      ofAdd ((χq g).toAdd, (χd g).toAdd - (χq g).toAdd) := by
  rw [cyclicHostInvolutionEquiv, MulEquiv.trans_apply]
  -- The final kernel identification changes only the first coordinate.
  change ((involutionCoordinates χq χd).mulEquivKerProdOfRightInverse _ _ _ g).2 = _
  rw [MonoidHom.mulEquivKerProdOfRightInverse_snd]
  rfl

/-- Reassemble an element by multiplying the kernel coordinate by the indicated powers
of complex conjugation and the ramified involution. -/
@[simp] theorem cyclicHostInvolutionEquiv_symm_apply (a : ↥(χq.ker ⊓ χd.ker)) (u v : ZMod 2) :
    (cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ).symm (a, ofAdd (u, v)) =
      (a : G) * (c ^ u.val * σ ^ v.val) := by
  rw [cyclicHostInvolutionEquiv, MulEquiv.symm_trans_apply]
  -- The inverse kernel identification preserves the underlying element of `G`.
  simp [MulEquiv.prodCongr, Equiv.prodCongr]

/-- A representative fixes the second quadratic field exactly when its two involution
coordinates are equal. -/
theorem mem_ker_iff_cyclicHostInvolutionEquiv_snd (g : G) :
    g ∈ χd.ker ↔
      (cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ g).2.toAdd.1 =
      (cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ g).2.toAdd.2 := by
  simp only [cyclicHostInvolutionEquiv_snd, toAdd_ofAdd, MonoidHom.mem_ker]
  rw [eq_sub_iff_add_eq, CharTwo.add_self_eq_zero, ← toAdd_one, toAdd.injective.eq_iff, eq_comm]

section ThickLetters

open Set

/-- The two translates of a subset of the joint kernel giving the thick letters are precisely
those whose kernel coordinate lies in the subset and whose ramified coordinate is `1`. -/
theorem mem_involution_translates_iff {S : Set ↥(χq.ker ⊓ χd.ker)} {g : G} :
    g ∈ (fun a : ↥(χq.ker ⊓ χd.ker) ↦ (a : G) * σ) '' S ∪
        (fun a : ↥(χq.ker ⊓ χd.ker) ↦ (a : G) * (c * σ)) '' S ↔
      let e := cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ
      (e g).1 ∈ S ∧ (e g).2.toAdd.2 = 1 := by
  let e := cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ
  have h₀ (a : ↥(χq.ker ⊓ χd.ker)) : e ((a : G) * σ) = (a, ofAdd (0, 1)) := by
    apply e.eq_symm_apply.mp
    simp [e, ZMod.val_one_eq_one_mod]
  have h₁ (a : ↥(χq.ker ⊓ χd.ker)) : e ((a : G) * (c * σ)) = (a, ofAdd (1, 1)) := by
    apply e.eq_symm_apply.mp
    simp [e, ZMod.val_one_eq_one_mod]
  constructor
  · simp only [e] at h₀ h₁
    rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · simpa only [h₀, toAdd_ofAdd, and_true] using ha
    · simpa only [h₁, toAdd_ofAdd, and_true] using ha
  · rintro ⟨ha, hv⟩
    rcases ZMod.eq_zero_or_eq_one (e g).2.toAdd.1 with hu | hu
    · refine Or.inl ⟨(e g).1, ha, (e).injective ?_⟩
      rw [h₀]
      exact Prod.ext rfl (toAdd.injective (Prod.ext hu.symm hv.symm))
    · refine Or.inr ⟨(e g).1, ha, (e).injective ?_⟩
      rw [h₁]
      exact Prod.ext rfl (toAdd.injective (Prod.ext hu.symm hv.symm))

/-- Transport the marks of the thick-letter orbit to split coordinates. A subset of the joint
kernel contributes via its translate by the ramified involution and the conjugate translate. -/
theorem orbitMarks_involution_translates (N : ℕ) (y φ : G) (S : Set ↥(χq.ker ⊓ χd.ker)) :
    orbitMarks N y φ ((fun a : ↥(χq.ker ⊓ χd.ker) ↦ (a : G) * σ) '' S ∪
        (fun a : ↥(χq.ker ⊓ χd.ker) ↦ (a : G) * (c * σ)) '' S) =
      let e := cyclicHostInvolutionEquiv χq χd c σ hc hσ hqc hdc hqσ hdσ
      thickLetterOrbitMarks N (e y) (e φ) S := by
  ext i
  simp only [thickLetterOrbitMarks_def, mem_orbitMarks_iff,
    mem_involution_translates_iff (hc := hc) (hσ := hσ) (hqc := hqc) (hdc := hdc)
      (hqσ := hqσ) (hdσ := hdσ), map_mul, map_zpow, Set.mem_prod, Set.mem_ofPred_eq]

end ThickLetters

end TauCeti.FrobeniusRiesz
