/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
* `CategoryTheory.Functor.map_ι_comp_map_sequenceDifference`,
  `CategoryTheory.Functor.sigmaComparison_comp_map_sequenceDifference`: compatibility with additive
  functors.
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

omit [Preadditive T] in
@[reassoc (attr := simp)]
private lemma opCoproductIsoProduct_inv_comp_ι_op (n : ℕ) :
    (opCoproductIsoProduct X.obj).inv ≫ (Sigma.ι X.obj n).op =
      Pi.π (fun k : ℕ ↦ X.op.obj (op k)) n :=
  opCoproductIsoProduct_inv_comp_ι X.obj n

omit [Preadditive T] in
@[reassoc]
private lemma opCoproductIsoProduct_hom_comp_π_op (n : ℕ) :
    (opCoproductIsoProduct X.obj).hom ≫ Pi.π (fun k : ℕ ↦ X.op.obj (op k)) n =
      (Sigma.ι X.obj n).op :=
  opCoproductIsoProduct_hom_comp_π n

@[reassoc (attr := simp)]
lemma ι_sequenceDifference (n : ℕ) :
    Sigma.ι X.obj n ≫ X.sequenceDifference =
      Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) :=
  Quiver.Hom.op_inj <| by
    simp only [op_comp, op_sub, sequenceDifference_op, Category.assoc,
      opCoproductIsoProduct_inv_comp_ι_op, X.op.towerDifference_π, Preadditive.comp_sub,
      opCoproductIsoProduct_hom_comp_π_op, opCoproductIsoProduct_hom_comp_π_op_assoc,
      Functor.op_map, Quiver.Hom.unop_op]

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
  refine ⟨fun h n ↦ ?_, fun h ↦ Limits.Sigma.hom_ext _ _ fun n ↦ ?_⟩
  · have h' := Sigma.ι X.obj n ≫= h
    simp only [ι_sequenceDifference_assoc, Preadditive.sub_comp, Category.assoc, comp_zero,
      sub_eq_zero] at h'
    exact h'.symm
  · simp [ι_sequenceDifference_assoc, Preadditive.sub_comp, h n]

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

private lemma coneOfTowerDifference_unop_ι_app {A : Tᵒᵖ}
    (ι : A ⟶ ∏ᶜ fun n : ℕ ↦ op (X.obj n)) (w : ι ≫ X.op.towerDifference = 0) (n : ℕ) :
    (X.op.coneOfTowerDifference ι w).unop.ι.app n =
      eqToHom (congrArg X.obj (unop_op n).symm) ≫ (ι ≫ Pi.π _ n).unop := by
  simp [Cone.unop_ι]

variable {X} in
/-- A cokernel of the sequence–difference map is a colimit of the sequence: the colimit of a
sequence is the quotient of `∐ X.obj` by the image of `1 - s`. -/
def isColimitCoconeOfSequenceDifference {c : CokernelCofork X.sequenceDifference}
    (hc : IsColimit c) :
    IsColimit (coconeOfSequenceDifference c.π c.condition) := by
  have hc' : IsColimit (CokernelCofork.ofπ c.π c.condition) :=
    IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  have hforkOp := CokernelCofork.IsColimit.ofπOp c.π c.condition hc'
  let ιOp := c.π.op ≫ (opCoproductIsoProduct X.obj).hom
  have hιOp : ιOp ≫ X.op.towerDifference = 0 :=
    X.towerDifference_eq_zero_of_sequenceDifference_comp_eq_zero c.condition
  have hfork : IsLimit (KernelFork.ofι ιOp hιOp) :=
    IsKernel.ofIso _ hforkOp (KernelFork.ofι ιOp hιOp) (opCoproductIsoProduct X.obj)
      (opCoproductIsoProduct X.obj) (Iso.refl _) (by simp [sequenceDifference_op, Category.assoc])
      (by simp [ιOp])
  exact IsColimit.ofIsoColimit (isLimitConeOfTowerDifference hfork).unop
    (Cocone.ext (Iso.refl _) fun n ↦ by
      rw [coneOfTowerDifference_unop_ι_app, eqToHom_refl, Category.id_comp]
      dsimp only [Cone.unop, coconeOfSequenceDifference]
      rw [Iso.refl_hom, Category.comp_id]
      exact Quiver.Hom.op_inj (by simp [ιOp, opCoproductIsoProduct_hom_comp_π]))

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
        exact X.op.lift_π_app_towerDifference c.op) :
      KernelFork (X.op.towerDifference : (∏ᶜ fun n : ℕ ↦ op (X.obj n)) ⟶ _)) :=
    IsLimit.ofIsoLimit (isLimitKernelForkOfIsLimit hc.op)
      (Fork.ext (Iso.refl _) (by simp [desc_op_comp_opCoproductIsoProduct_hom]))
  let kfOp : KernelFork X.sequenceDifference.op :=
    KernelFork.ofι (Sigma.desc fun n : ℕ ↦ c.ι.app n).op
      (by rw [← op_comp, sequenceDifference_desc_ι_app, op_zero])
  have hforkOp : IsLimit kfOp :=
    IsKernel.ofIso _ hfork kfOp (opCoproductIsoProduct X.obj).symm
      (opCoproductIsoProduct X.obj).symm (Iso.refl _)
      (by simp [sequenceDifference_op]) (by simp [kfOp])
  exact IsColimit.ofIsoColimit (KernelFork.IsLimit.ofιUnop _ _ hforkOp)
    (Cofork.ext (Iso.refl _) (by dsimp; exact Category.comp_id _))

/-- The sequence–difference map is natural in morphisms of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma sequenceDifference_naturality {X Y : ℕ ⥤ T} [HasCoproduct X.obj] [HasCoproduct Y.obj]
    (α : X ⟶ Y) :
    X.sequenceDifference ≫ Limits.Sigma.map (fun n ↦ α.app n) =
      Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference :=
  Limits.Sigma.hom_ext _ _ fun n ↦ by
    simp [ι_sequenceDifference_assoc, Preadditive.sub_comp, Preadditive.comp_sub,
      α.naturality_assoc]

/-- An additive functor `F` maps the `n`-th summand inclusion followed by `X.sequenceDifference`
to `F.map (Sigma.ι X.obj n) - F.map (X.map _) ≫ F.map (Sigma.ι X.obj (n + 1))`. -/
lemma map_ι_comp_map_sequenceDifference {D : Type*} [Category* D] [Preadditive D]
    (F : T ⥤ D) [F.Additive] (n : ℕ) :
    F.map (Sigma.ι X.obj n) ≫ F.map X.sequenceDifference =
      F.map (Sigma.ι X.obj n) -
        F.map (X.map (homOfLE (n.le_add_right 1))) ≫ F.map (Sigma.ι X.obj (n + 1)) := by
  rw [← F.map_comp, X.ι_sequenceDifference, F.map_sub, F.map_comp]

/-- An additive functor `F` intertwines `X.sequenceDifference` and `(X ⋙ F).sequenceDifference`
through `sigmaComparison F X.obj`. -/
@[reassoc]
lemma sigmaComparison_comp_map_sequenceDifference {D : Type*} [Category* D] [Preadditive D]
    (F : T ⥤ D) [F.Additive] [HasColimitsOfShape (Discrete ℕ) D] :
    sigmaComparison F X.obj ≫ F.map X.sequenceDifference =
      (X ⋙ F).sequenceDifference ≫ sigmaComparison F X.obj := by
  refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
  have hι (k : ℕ) : Sigma.ι (X ⋙ F).obj k ≫ sigmaComparison F X.obj = F.map (Sigma.ι X.obj k) :=
    ι_comp_sigmaComparison F X.obj k
  -- `Sigma.ι (fun b ↦ F.obj (X.obj b)) n` and `Sigma.ι (X ⋙ F).obj n` are definitionally equal
  -- by `Functor.comp_obj` and eta, which `simp`/`rw` cannot bridge across the dependent
  -- `HasCoproduct` instance; `change` aligns both sides with `(X ⋙ F).obj`.
  change Sigma.ι (X ⋙ F).obj n ≫ _ = Sigma.ι (X ⋙ F).obj n ≫ _
  rw [← Category.assoc, hι, map_ι_comp_map_sequenceDifference]
  simp [ι_sequenceDifference_assoc, Preadditive.sub_comp, hι]

end SequenceDifference

end CategoryTheory.Functor
