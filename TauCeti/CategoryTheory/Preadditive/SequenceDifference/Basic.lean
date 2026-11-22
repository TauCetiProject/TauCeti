/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.TowerDifference

import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The sequence–difference map of a sequence

Let `X : ℕ ⥤ T` be a sequence `X₀ → X₁ → X₂ → ⋯` in a preadditive category whose terms admit a
countable coproduct `∐ X.obj`. The *sequence–difference map* is the endomorphism
`1 - s : ∐ X.obj ⟶ ∐ X.obj` (`CategoryTheory.Functor.sequenceDifference`), defined by duality
from `CategoryTheory.Functor.towerDifference` on `X.op` across `opCoproductIsoProduct X.obj`,
sending the `n`-th summand `Xₙ` to `ιₙ - φₙ ≫ ιₙ₊₁`. A morphism out of `∐ X.obj` annihilates
`sequenceDifference` if and only if its components form a cocone over `X`
(`CategoryTheory.Functor.sequenceDifference_comp_eq_zero_iff`,
`CategoryTheory.Functor.coconeOfSequenceDifference`), and colimits of `X` are the same as
cokernels of `X.sequenceDifference` (`CategoryTheory.Functor.isColimitCoconeOfSequenceDifference`,
`CategoryTheory.Functor.isColimitCokernelCoforkOfIsColimit`).

This is the sequential dual of `TauCeti.CategoryTheory.Preadditive.TowerDifference`.

## Main declarations

* `CategoryTheory.Functor.sequenceDifference`: the difference map `1 - s : ∐ X.obj ⟶ ∐ X.obj`.
* `CategoryTheory.Functor.ι_sequenceDifference`: its restriction to the `n`-th summand.
* `CategoryTheory.Functor.sequenceDifference_comp_eq_zero_iff`: compatibility criterion for
  morphisms out of `∐ X.obj`.
* `CategoryTheory.Functor.coconeOfSequenceDifference`: the cocone over `X` attached to a morphism
  annihilating `sequenceDifference`.
* `CategoryTheory.Functor.isColimitCoconeOfSequenceDifference`,
  `CategoryTheory.Functor.isColimitCokernelCoforkOfIsColimit`: a cokernel of the
  sequence–difference map is a colimit of the sequence, and a colimit of the sequence is a
  cokernel of the sequence–difference map.
* `CategoryTheory.Functor.sequenceDifference_naturality`: naturality in morphisms of sequences.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Functor

section SequenceDifference

variable {T : Type u} [Category.{v} T] [Preadditive T]
variable (X : ℕ ⥤ T) [HasCoproduct X.obj]

private instance hasProduct_op_obj : HasProduct (fun n : ℕ ↦ X.op.obj (op n)) :=
  inferInstanceAs (HasProduct fun n : ℕ ↦ op (X.obj n))

omit [Preadditive T] in
@[reassoc]
private lemma opCoproductIsoProduct_hom_comp_π_opObj (k : ℕ) :
    (opCoproductIsoProduct X.obj).hom ≫ Pi.π (fun n : ℕ ↦ X.op.obj (op n)) k =
      (Sigma.ι X.obj k).op :=
  opCoproductIsoProduct_hom_comp_π (Z := X.obj) k

omit [Preadditive T] in
private lemma opCoproductIsoProduct_inv_comp_ι_opObj (k : ℕ) :
    (opCoproductIsoProduct X.obj).inv ≫ (Sigma.ι X.obj k).op =
      Pi.π (fun n : ℕ ↦ X.op.obj (op n)) k :=
  opCoproductIsoProduct_inv_comp_ι (Z := X.obj) k

/-- The *sequence–difference map* `1 - s` of a sequence `X₀ → X₁ → ⋯`: the endomorphism
of `∐ X.obj` sending the `n`-th summand `Xₙ` to `ιₙ - φₙ ≫ ιₙ₊₁` (`ι_sequenceDifference`),
constructed by duality from `X.op.towerDifference`. Its cone in a pretriangulated category is a
Milnor homotopy colimit of `X`. -/
def sequenceDifference : (∐ X.obj) ⟶ (∐ X.obj) :=
  ((opCoproductIsoProduct X.obj).hom ≫ X.op.towerDifference ≫
    (opCoproductIsoProduct X.obj).inv).unop

private lemma sequenceDifference_op :
    X.sequenceDifference.op =
      (opCoproductIsoProduct X.obj).hom ≫ X.op.towerDifference ≫
        (opCoproductIsoProduct X.obj).inv :=
  rfl

@[reassoc (attr := simp)]
lemma ι_sequenceDifference (n : ℕ) :
    Sigma.ι X.obj n ≫ X.sequenceDifference =
      Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) :=
  Quiver.Hom.op_inj <| by
    rw [op_comp, sequenceDifference_op, Category.assoc, Category.assoc,
      X.opCoproductIsoProduct_inv_comp_ι_opObj, towerDifference_π, Preadditive.comp_sub,
      X.opCoproductIsoProduct_hom_comp_π_opObj,
      X.opCoproductIsoProduct_hom_comp_π_opObj_assoc]
    dsimp only [Functor.op_map, Quiver.Hom.unop_op]
    rw [← op_comp, op_sub]

private lemma towerDifference_eq_zero_of_sequenceDifference_comp_eq_zero {Y : T}
    {ψ : (∐ X.obj) ⟶ Y} (w : X.sequenceDifference ≫ ψ = 0) :
    (ψ.op ≫ (opCoproductIsoProduct X.obj).hom) ≫ X.op.towerDifference = 0 := by
  have wop := congrArg Quiver.Hom.op w
  rw [op_comp, op_zero, sequenceDifference_op] at wop
  simpa [Category.assoc] using wop =≫ (opCoproductIsoProduct X.obj).hom

/-- A morphism `ψ` out of `∐ X.obj` annihilates the sequence–difference map if and only if
its components `Sigma.ι X.obj n ≫ ψ` are compatible with the transition maps `Xₙ ⟶ Xₙ₊₁`. -/
lemma sequenceDifference_comp_eq_zero_iff {Y : T} (ψ : (∐ X.obj) ⟶ Y) :
    X.sequenceDifference ≫ ψ = 0 ↔
      ∀ n, X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) ≫ ψ =
        Sigma.ι X.obj n ≫ ψ := by
  have hop : X.sequenceDifference ≫ ψ = 0 ↔
      (ψ.op ≫ (opCoproductIsoProduct X.obj).hom) ≫ X.op.towerDifference = 0 := by
    refine ⟨X.towerDifference_eq_zero_of_sequenceDifference_comp_eq_zero, fun h ↦
      Quiver.Hom.op_inj ?_⟩
    rw [op_comp, op_zero, sequenceDifference_op]
    simp [← Category.assoc, h]
  rw [hop, X.op.comp_towerDifference_eq_zero_iff]
  refine forall_congr' fun n ↦ ?_
  rw [Category.assoc, Category.assoc, X.opCoproductIsoProduct_hom_comp_π_opObj_assoc,
    X.opCoproductIsoProduct_hom_comp_π_opObj, ← Category.assoc, ← op_comp]
  dsimp only [Functor.op_map, Quiver.Hom.unop_op]
  rw [← op_comp, ← op_comp]
  exact Quiver.Hom.op_inj.eq_iff

variable {X} in
/-- A morphism out of `∐ X.obj` annihilating the sequence–difference map defines a cocone over
`X`, with components `Sigma.ι X.obj n ≫ ψ`. -/
@[expose, simps pt]
def coconeOfSequenceDifference {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) : Cocone X where
  pt := Y
  ι := NatTrans.ofSequence (fun n ↦ Sigma.ι X.obj n ≫ ψ) fun n ↦ by
    simp [(X.sequenceDifference_comp_eq_zero_iff ψ).1 w n]

@[simp]
lemma coconeOfSequenceDifference_ι_app {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) (n : ℕ) :
    (coconeOfSequenceDifference ψ w).ι.app n = Sigma.ι X.obj n ≫ ψ := (rfl)

/-- If `X.sequenceDifference ≫ ψ = 0`, then the components `Sigma.ι X.obj n ≫ ψ` are
compatible with every composite transition `Xₙ ⟶ Xₘ` (`n ≤ m`). -/
lemma map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero {Y : T} {ψ : (∐ X.obj) ⟶ Y}
    (w : X.sequenceDifference ≫ ψ = 0) {n m : ℕ} (hnm : n ≤ m) :
    X.map (homOfLE hnm) ≫ Sigma.ι X.obj m ≫ ψ = Sigma.ι X.obj n ≫ ψ :=
  (coconeOfSequenceDifference ψ w).w (homOfLE hnm)

/-- The legs of any cocone over `X` annihilate the sequence–difference map. -/
@[reassoc (attr := simp)]
lemma sequenceDifference_desc_ι_app (c : Cocone X) :
    X.sequenceDifference ≫ Sigma.desc (fun n : ℕ ↦ c.ι.app n) = 0 := by
  ext n
  simp [ι_sequenceDifference_assoc, c.w]

variable {X} in
/-- A cokernel of the sequence–difference map is a colimit of the sequence: the colimit of a
sequence is the quotient of `∐ X.obj` by the image of `1 - s`. -/
def isColimitCoconeOfSequenceDifference {c : CokernelCofork X.sequenceDifference}
    (hc : IsColimit c) :
    IsColimit (coconeOfSequenceDifference c.π c.condition) := by
  have hc' : IsColimit (CokernelCofork.ofπ c.π c.condition) :=
    IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  have hforkOp := CokernelCofork.IsColimit.ofπOp c.π c.condition hc'
  let trans {W : Tᵒᵖ} (k : W ⟶ ∏ᶜ fun n ↦ X.op.obj (op n)) (hk : k ≫ X.op.towerDifference = 0) :
      KernelFork X.sequenceDifference.op :=
    KernelFork.ofι (k ≫ (opCoproductIsoProduct X.obj).inv) <| by
      rw [Category.assoc, sequenceDifference_op]; simp [reassoc_of% hk]
  let ιOp := c.π.op ≫ (opCoproductIsoProduct X.obj).hom
  have hιOp : ιOp ≫ X.op.towerDifference = 0 :=
    X.towerDifference_eq_zero_of_sequenceDifference_comp_eq_zero c.condition
  let kf : KernelFork X.op.towerDifference := KernelFork.ofι ιOp hιOp
  have hfork : IsLimit kf := by
    refine KernelFork.IsLimit.ofι _ _ (fun k hk ↦ hforkOp.lift (trans k hk))
      (fun k hk ↦ ?_) (fun k hk m hm ↦ ?_)
    · have hfac := hforkOp.fac (trans k hk) .zero
      dsimp only [trans, Fork.ofι_π_app, Functor.const_obj_obj] at hfac
      rw [← Category.assoc, hfac, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · refine Fork.IsLimit.hom_ext hforkOp ?_
      have hfac := hforkOp.fac (trans k hk) .zero
      dsimp only [trans, Fork.ofι_π_app, Functor.const_obj_obj] at hfac
      change m ≫ c.π.op = hforkOp.lift (trans k hk) ≫ c.π.op
      rw [hfac, Iso.eq_comp_inv]
      simpa [Category.assoc] using hm
  exact IsColimit.ofIsoColimit (isLimitConeOfTowerDifference hfork).unop
    (Cocone.ext (Iso.refl _) fun n ↦ by
      have hcomp : ((coneOfTowerDifference kf.ι kf.condition).unop.ι.app n ≫
          (Iso.refl _).hom).op = (Sigma.ι X.obj n ≫ c.π).op := by
        erw [Category.comp_id]
        change (coneOfTowerDifference kf.ι kf.condition).π.app (op n) =
          (Sigma.ι X.obj n ≫ c.π).op
        rw [coneOfTowerDifference_π_app]
        dsimp only [kf, ιOp, Fork.ι_ofι, unop_op]
        rw [Category.assoc, X.opCoproductIsoProduct_hom_comp_π_opObj, ← op_comp]
      exact Quiver.Hom.op_inj hcomp)

variable {X} in
/-- A colimit of a sequence is a cokernel of its sequence–difference map, through the morphism
out of `∐ X.obj` given by the colimit legs. -/
def isColimitCokernelCoforkOfIsColimit {c : Cocone X} (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (Sigma.desc fun n : ℕ ↦ c.ι.app n)
      (X.sequenceDifference_desc_ι_app c)) := by
  have hfork : IsLimit (KernelFork.ofι
      ((Sigma.desc fun n : ℕ ↦ c.ι.app n).op ≫ (opCoproductIsoProduct X.obj).hom)
      (by
        rw [desc_op_comp_opCoproductIsoProduct_hom]
        exact X.op.lift_π_app_towerDifference c.op)) :=
    IsLimit.ofIsoLimit (isLimitKernelForkOfIsLimit hc.op)
      (Fork.ext (Iso.refl _) (by simp [desc_op_comp_opCoproductIsoProduct_hom]))
  let trans {W : Tᵒᵖ} (k : W ⟶ op (∐ X.obj)) (hk : k ≫ X.sequenceDifference.op = 0) :
      KernelFork X.op.towerDifference :=
    KernelFork.ofι (k ≫ (opCoproductIsoProduct X.obj).hom) <| by
      have h : (opCoproductIsoProduct X.obj).hom ≫ X.op.towerDifference =
          X.sequenceDifference.op ≫ (opCoproductIsoProduct X.obj).hom := by
        simp [sequenceDifference_op, Category.assoc]
      rw [Category.assoc, h, reassoc_of% hk, zero_comp]
  have hforkOp : IsLimit (KernelFork.ofι (Sigma.desc fun n : ℕ ↦ c.ι.app n).op
      (by rw [← op_comp, sequenceDifference_desc_ι_app, op_zero])) := by
    refine KernelFork.IsLimit.ofι _ _ (fun k hk ↦ hfork.lift (trans k hk))
      (fun k hk ↦ ?_) (fun k hk m hm ↦ ?_)
    · have hfac := hfork.fac (trans k hk) .zero
      dsimp only [trans, Fork.ofι_π_app, Functor.const_obj_obj] at hfac
      refine (cancel_mono (opCoproductIsoProduct X.obj).hom).1 ?_
      rw [Category.assoc]
      exact hfac
    · refine Fork.IsLimit.hom_ext hfork ?_
      have hfac := hfork.fac (trans k hk) .zero
      dsimp only [trans, Fork.ofι_π_app, Functor.const_obj_obj] at hfac
      change m ≫ (Sigma.desc fun n ↦ c.ι.app n).op ≫ (opCoproductIsoProduct X.obj).hom =
        hfork.lift (trans k hk) ≫
          (Sigma.desc fun n ↦ c.ι.app n).op ≫ (opCoproductIsoProduct X.obj).hom
      rw [hfac, ← Category.assoc, hm]
  exact IsColimit.ofIsoColimit (KernelFork.IsLimit.ofιUnop _ _ hforkOp)
    (Cofork.ext (Iso.refl _) (by dsimp; exact Category.comp_id _))

/-- The sequence–difference map is natural in morphisms of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma sequenceDifference_naturality {X Y : ℕ ⥤ T} [HasCoproduct X.obj] [HasCoproduct Y.obj]
    (α : X ⟶ Y) :
    X.sequenceDifference ≫ Limits.Sigma.map (fun n ↦ α.app n) =
      Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference := by
  apply Quiver.Hom.op_inj
  have hpi : (Limits.Sigma.map fun n : ℕ ↦ α.app n).op ≫ (opCoproductIsoProduct X.obj).hom =
      (opCoproductIsoProduct Y.obj).hom ≫ Limits.Pi.map fun n ↦ (α.app n).op := by
    ext n
    simp [opCoproductIsoProduct_hom_comp_π, opCoproductIsoProduct_hom_comp_π_assoc]
  have hpi_inv : Limits.Pi.map (fun n ↦ (α.app n).op) ≫ (opCoproductIsoProduct X.obj).inv =
      (opCoproductIsoProduct Y.obj).inv ≫ (Limits.Sigma.map fun n ↦ α.app n).op := by
    rw [Iso.comp_inv_eq, Category.assoc, hpi, Iso.inv_hom_id_assoc]
  have hnat : Y.op.towerDifference ≫ Limits.Pi.map (fun n ↦ (α.app n).op) =
      Limits.Pi.map (fun n ↦ (α.app n).op) ≫ X.op.towerDifference :=
    towerDifference_naturality (NatTrans.op α)
  calc
    (X.sequenceDifference ≫ Limits.Sigma.map fun n ↦ α.app n).op
        = ((Limits.Sigma.map fun n ↦ α.app n).op ≫ (opCoproductIsoProduct X.obj).hom) ≫
            X.op.towerDifference ≫ (opCoproductIsoProduct X.obj).inv := by
          simp [op_comp, sequenceDifference_op, Category.assoc]
    _ = (opCoproductIsoProduct Y.obj).hom ≫
          (Limits.Pi.map (fun n ↦ (α.app n).op) ≫ X.op.towerDifference) ≫
            (opCoproductIsoProduct X.obj).inv := by
          rw [hpi, Category.assoc, Category.assoc]
    _ = (opCoproductIsoProduct Y.obj).hom ≫
          Y.op.towerDifference ≫
            (Limits.Pi.map (fun n ↦ (α.app n).op) ≫ (opCoproductIsoProduct X.obj).inv) := by
          rw [← hnat, Category.assoc]
    _ = (Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference).op := by
          rw [hpi_inv]
          simp [op_comp, sequenceDifference_op, Category.assoc]

end SequenceDifference

end CategoryTheory.Functor
