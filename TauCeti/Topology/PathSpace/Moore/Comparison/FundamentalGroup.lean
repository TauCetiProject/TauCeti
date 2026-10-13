/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Moore loop components and the fundamental group

The path components of the Moore loop space identify with the fundamental group. The map on
loops is multiplicative when a loop is sent to the inverse of its fixed-interval homotopy class:
Mathlib multiplies endomorphisms by reversed categorical composition
(`FundamentalGroup.mul_def`), while Moore loops concatenate in traversal order.

The component identification uses the Moore/fixed-interval homotopy equivalence and
`HomotopyGroup.zerothHomotopyLoopSpaceEquivFundamentalGroup`. This convention gives the
multiplicative comparison needed for the degree-zero Pontryagin algebra.

See W. S. Massey, *Singular Homology Theory*, Chapter VII, and
Barraud--Damian--Humilière--Oancea, *Floer homology with DG coefficients*, §2.2,
https://arxiv.org/html/2404.07953v3#S2.SS2.
-/

public section

noncomputable section

namespace TauCeti.MooreLoopSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The multiplicative class of a Moore loop. The inverse compensates for Mathlib's convention
that the product of fundamental-group elements traverses the right factor first. -/
def fundamentalGroupHom (x : X) : MooreLoopSpace X x →* FundamentalGroup X x where
  toFun γ := Inv.inv (α := FundamentalGroup X x) (Path.Homotopic.Quotient.mk γ.toPath)
  map_one' := by
    have h : (1 : MooreLoopSpace X x).toPath = Path.refl x := by
      ext t
      simp [toPath_apply]
    rw [h]
    exact inv_one
  map_mul' γ δ := by
    let a : FundamentalGroup X x := Path.Homotopic.Quotient.mk γ.toPath
    let b : FundamentalGroup X x := Path.Homotopic.Quotient.mk δ.toPath
    have h : Path.Homotopic.Quotient.mk (γ * δ).toPath = b * a := by
      rw [FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans]
      apply Quotient.sound
      apply Path.joined_iff_homotopic.mp
      exact ⟨((mulToPathHomotopy x).evalAt (γ, δ)).symm.cast
        (mulToPath_apply (γ, δ)).symm (transToPath_apply (γ, δ)).symm⟩
    exact (congrArg (Inv.inv (α := FundamentalGroup X x)) h).trans (mul_inv_rev b a)

/-- The generator equation for the multiplicative Moore-loop class. -/
@[simp]
theorem fundamentalGroupHom_apply (γ : MooreLoopSpace X x) :
    fundamentalGroupHom x γ =
      Inv.inv (α := FundamentalGroup X x) (Path.Homotopic.Quotient.mk γ.toPath) :=
  (rfl)

/-- Path components of Moore loops identify with the fundamental group, in the multiplicative
convention of `fundamentalGroupHom`. -/
def zerothHomotopyEquivFundamentalGroup (x : X) :
    ZerothHomotopy (MooreLoopSpace X x) ≃ FundamentalGroup X x :=
  ({ toFun := Quotient.map toPath (fun _ _ h ↦ h.map continuous_toPath)
     invFun := Quotient.map Path.toMooreLoop (fun _ _ h ↦ h.map Path.continuous_toMooreLoop)
     left_inv := fun q ↦ Quotient.inductionOn q fun γ ↦
       by
         exact Quotient.sound ⟨((unitHomotopy (X := X) (x := x)).evalAt γ).cast
           (toLengthOne_apply γ).symm rfl⟩
     right_inv := fun q ↦ Quotient.inductionOn q fun p ↦
       congrArg ZerothHomotopy.mk (Path.toPath_toMooreLoop p) } :
      ZerothHomotopy (MooreLoopSpace X x) ≃ ZerothHomotopy (Path x x)).trans
    (HomotopyGroup.zerothHomotopyLoopSpaceEquivFundamentalGroup.trans (Equiv.inv _))

/-- The component equivalence agrees with the multiplicative class on loops. -/
@[simp]
theorem zerothHomotopyEquivFundamentalGroup_mk (γ : MooreLoopSpace X x) :
    zerothHomotopyEquivFundamentalGroup x (.mk γ) = fundamentalGroupHom x γ := by
  exact congrArg (Inv.inv (α := FundamentalGroup X x))
    (HomotopyGroup.zerothHomotopyLoopSpaceEquivFundamentalGroup_mk γ.toPath)

/-- The multiplicative loop class is natural under based continuous maps. -/
@[simp↓]
theorem fundamentalGroupHom_map (f : C(X, Y)) (hf : f x = y) (γ : MooreLoopSpace X x) :
    fundamentalGroupHom y (map f hf γ) =
      FundamentalGroup.mapOfEq f hf (fundamentalGroupHom x γ) := by
  rw [fundamentalGroupHom_apply, fundamentalGroupHom_apply, map_inv,
    FundamentalGroup.mapOfEq_apply]
  congr 1
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp [toPath_apply, Path.cast_coe, toMoorePath_map, MoorePath.map_apply]

end TauCeti.MooreLoopSpace
