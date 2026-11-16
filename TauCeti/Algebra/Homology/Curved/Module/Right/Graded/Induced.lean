/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Adjunction.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.Algebra.Module.GradedModule.Prod
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Induced and coinduced curved differential graded right modules

Forgetting the differential of a curved differential graded right module gives a faithful exact
functor `forgetDifferential` to the abelian category of graded right modules. Following
Positselski, this functor admits both a left adjoint `G⁺` (`inducedFunctor`) and a right adjoint
`G⁻` (`coinducedFunctor`), both taking values in contractible curved right modules.

For a graded right `A`-module `X`, the induced curved module `induced h X` (`G⁺(X)`) has
underlying graded `R`-module `X ⊕ X{1}`—so a homogeneous element of degree `p` is a pair
`⟨x₀, x₁⟩` with `x₀ ∈ Xₚ` and `x₁ ∈ X_{p - 1}`—twisted right `A`-action
`⟨x₀, x₁⟩ · a = ⟨x₀ · a - (-1)^{|x₁|} x₁ · d(a), x₁ · a⟩`, and differential
`d⟨x₀, x₁⟩ = ⟨x₁ · w, x₀⟩`. The coinduced curved module `coinduced h Y` (`G⁻(Y)`) is
`G⁺(Y{-1})`, whose degree-`p` elements are pairs `⟨y₁, y₀⟩` with `y₁ ∈ Y_{p + 1}` and `y₀ ∈ Yₚ`.

* Every induced or coinduced curved module is contractible via `k⟨x₀, x₁⟩ = ⟨x₁, 0⟩`, hence zero
  in the curved homotopy category.
* After forgetting the differential, `induced h X` sits in a short exact sequence
  `0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` of graded right modules (`⟨x₀, 0⟩` and `⟨x₀, x₁⟩ ↦ x₁`), and
  `coinduced h Y` sits in `0 ⟶ Y{-1} ⟶ G⁻(Y) ⟶ Y ⟶ 0`, so `G⁺` and `G⁻` preserve both
  graded-projective and graded-injective objects.
* An epimorphism `X ↠ M` of graded right modules extends via the left adjunction to a surjective
  closed morphism `G⁺(X) ↠ M`, while a monomorphism `M ↪ Y` lifts via the right adjunction to an
  injective closed morphism `M ↪ G⁻(Y)`.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.induced`, `TauCeti.CurvedDGRightModuleCat.inducedFunctor`:
  the induced curved right module `G⁺(X)` and the left adjoint functor to `forgetDifferential`.
* `TauCeti.CurvedDGRightModuleCat.coinduced`, `TauCeti.CurvedDGRightModuleCat.coinducedFunctor`:
  the coinduced curved right module `G⁻(Y) = G⁺(Y{-1})` and the right adjoint functor to
  `forgetDifferential`.
* `TauCeti.CurvedDGRightModuleCat.inducedAdj`, `TauCeti.CurvedDGRightModuleCat.coinducedAdj`:
  the adjunctions `inducedFunctor h ⊣ forgetDifferential` and
  `forgetDifferential ⊣ coinducedFunctor h`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_induced` and
  `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinduced`: induced and coinduced curved modules
  vanish in the curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.shortExact_inducedι_inducedπ` and
  `TauCeti.CurvedDGRightModuleCat.shortExact_coinducedι_coinducedCounit`: the underlying graded
  modules of `G⁺(X)` and `G⁻(Y)` are extensions of `X{1}` by `X` and of `Y` by `Y{-1}`.
* `TauCeti.CurvedDGRightModuleCat.projective_toGradedModuleCat_induced` and
  `TauCeti.CurvedDGRightModuleCat.injective_toGradedModuleCat_coinduced`: `G⁺` preserves
  graded projectivity and `G⁻` preserves graded injectivity.
* `TauCeti.CurvedDGRightModuleCat.epi_inducedDesc` and
  `TauCeti.CurvedDGRightModuleCat.mono_coinducedLift`: graded epimorphisms (resp. monomorphisms)
  transpose to closed epimorphisms out of `G⁺(X)` (resp. closed monomorphisms into `G⁻(Y)`).

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 6.2 and Proof of Theorem 7.8(a).
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying GradedModuleCat.shift

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-! ### The twisted carrier `X ⊕ X{1}` -/

/-- Dedicated pair carrier for `G⁺(X)` so its twisted `Aᵐᵒᵖ`-module structure cannot collide with
the componentwise `Module Aᵐᵒᵖ (X × X)` instance. -/
@[ext]
private structure InducedCarrier (X : Type u) where
  fst : X
  snd : X

namespace InducedCarrier

private def toProd {X : Type u} (z : InducedCarrier X) : X × X := (z.fst, z.snd)

private theorem toProd_injective {X : Type u} : Function.Injective (toProd (X := X)) :=
  fun _ _ h ↦ ext (congrArg Prod.fst h) (congrArg Prod.snd h)

section AddModule

variable {X : Type u} [AddCommGroup X]

private instance : Zero (InducedCarrier X) := ⟨⟨0, 0⟩⟩
private instance : Add (InducedCarrier X) := ⟨fun y z ↦ ⟨y.fst + z.fst, y.snd + z.snd⟩⟩
private instance : Neg (InducedCarrier X) := ⟨fun z ↦ ⟨-z.fst, -z.snd⟩⟩
private instance : Sub (InducedCarrier X) := ⟨fun y z ↦ ⟨y.fst - z.fst, y.snd - z.snd⟩⟩
private instance : SMul ℕ (InducedCarrier X) := ⟨fun n z ↦ ⟨n • z.fst, n • z.snd⟩⟩
private instance : SMul ℤ (InducedCarrier X) := ⟨fun n z ↦ ⟨n • z.fst, n • z.snd⟩⟩

private instance : AddCommGroup (InducedCarrier X) :=
  toProd_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp] private theorem zero_fst : (0 : InducedCarrier X).fst = 0 := rfl
@[simp] private theorem zero_snd : (0 : InducedCarrier X).snd = 0 := rfl
@[simp] private theorem add_fst (y z : InducedCarrier X) : (y + z).fst = y.fst + z.fst := rfl
@[simp] private theorem add_snd (y z : InducedCarrier X) : (y + z).snd = y.snd + z.snd := rfl
@[simp] private theorem neg_fst (z : InducedCarrier X) : (-z).fst = -z.fst := rfl
@[simp] private theorem neg_snd (z : InducedCarrier X) : (-z).snd = -z.snd := rfl
@[simp] private theorem sub_fst (y z : InducedCarrier X) : (y - z).fst = y.fst - z.fst := rfl
@[simp] private theorem sub_snd (y z : InducedCarrier X) : (y - z).snd = y.snd - z.snd := rfl
@[simp] private theorem zsmul_fst (n : ℤ) (z : InducedCarrier X) : (n • z).fst = n • z.fst := rfl
@[simp] private theorem zsmul_snd (n : ℤ) (z : InducedCarrier X) : (n • z).snd = n • z.snd := rfl

variable [Module R X]

private instance : SMul R (InducedCarrier X) := ⟨fun r z ↦ ⟨r • z.fst, r • z.snd⟩⟩

@[simp] private theorem smul_fst (r : R) (z : InducedCarrier X) : (r • z).fst = r • z.fst := rfl
@[simp] private theorem smul_snd (r : R) (z : InducedCarrier X) : (r • z).snd = r • z.snd := rfl

private instance : Module R (InducedCarrier X) :=
  toProd_injective.module R ⟨⟨toProd, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

private def equivProd : InducedCarrier X ≃ₗ[R] X × X where
  toFun := toProd
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end AddModule

end InducedCarrier

section Construction

private theorem op_map_mul_smul_koszulTwist_of_mem (h : IsCurvedDGAlgebra 𝒜 d w)
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {r q : ℤ} {a : A} (ha : a ∈ 𝒜 r) (b : A) {x : X} (hx : x ∈ X.grading.piece q) :
    op (d (a * b)) • X.grading.koszulTwist 1 x =
      op b • (op (d a) • X.grading.koszulTwist 1 x) +
        op (d b) • X.grading.koszulTwist 1 (op a • x) := by
  have ha' : a ∈ (InternalGrading.ofDecomposition 𝒜).piece r := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hax : op a • x ∈ X.grading.piece (r + q) := by
    simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem
      (((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff r a).2 ha') hx
  have hsign : (q.negOnePow : ℤ) * (r.negOnePow : ℤ) = ((r + q).negOnePow : ℤ) := by
    rw [mul_comm, ← Units.val_mul, ← Int.negOnePow_add]
  rw [X.grading.koszulTwist_one_eq_zsmul hx, X.grading.koszulTwist_one_eq_zsmul hax,
    h.leibniz ha b, Units.smul_def]
  simp only [MulOpposite.op_add, add_smul, op_mul, mul_smul, op_smul, smul_assoc, smul_add,
    smul_comm (_ : Aᵐᵒᵖ) (_ : ℤ), ← mul_smul (q.negOnePow : ℤ) (r.negOnePow : ℤ), hsign]

private theorem op_map_mul_smul_koszulTwist (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a b : A) (x : X) :
    op (d (a * b)) • X.grading.koszulTwist 1 x =
      op b • (op (d a) • X.grading.koszulTwist 1 x) +
        op (d b) • X.grading.koszulTwist 1 (op a • x) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous ha =>
    induction x using DirectSum.Decomposition.inductionOn X.grading.piece with
    | zero => simp
    | homogeneous hx => exact op_map_mul_smul_koszulTwist_of_mem h ha.2 b hx.2
    | add x₁ x₂ ih₁ ih₂ =>
      simp only [map_add, smul_add, ih₁, ih₂]
      abel
  | add a₁ a₂ ih₁ ih₂ =>
    simp only [add_mul, map_add, MulOpposite.op_add, add_smul, smul_add, ih₁, ih₂]
    abel

@[instance_reducible]
private noncomputable def instSMulOpInducedCarrier (d : A →ₗ[R] A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    SMul Aᵐᵒᵖ (InducedCarrier X) where
  smul s z := ⟨s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd, s • z.snd⟩

@[simp]
private theorem smul_inducedCarrier_fst (d : A →ₗ[R] A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : InducedCarrier X) :
    (letI := instSMulOpInducedCarrier d X; (s • z).fst) =
      s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd :=
  rfl

@[simp]
private theorem smul_inducedCarrier_snd (d : A →ₗ[R] A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : InducedCarrier X) :
    (letI := instSMulOpInducedCarrier d X; (s • z).snd) = s • z.snd :=
  rfl

@[instance_reducible]
private noncomputable def instModuleOpInducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Module Aᵐᵒᵖ (InducedCarrier X) :=
  letI := instSMulOpInducedCarrier d X
  { one_smul := fun z ↦ by
      ext
      · simp [h.map_one_eq_zero]
      · simp
    mul_smul := fun s t z ↦ by
      ext
      · simp only [smul_inducedCarrier_fst, smul_inducedCarrier_snd, unop_mul,
          op_map_mul_smul_koszulTwist h X t.unop s.unop z.snd, op_unop, smul_sub, mul_smul]
        abel
      · exact mul_smul s t z.snd
    smul_zero := fun s ↦ by ext <;> simp
    smul_add := fun s y z ↦ by
      ext
      · simp only [smul_inducedCarrier_fst, InducedCarrier.add_fst, InducedCarrier.add_snd,
          smul_add, map_add]
        abel
      · exact smul_add s y.snd z.snd
    add_smul := fun s t z ↦ by
      ext
      · simp only [smul_inducedCarrier_fst, InducedCarrier.add_fst, MulOpposite.unop_add,
          map_add, MulOpposite.op_add, add_smul]
        abel
      · exact add_smul s t z.snd
    zero_smul := fun z ↦ by ext <;> simp }

private theorem instIsScalarTowerInducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    letI := instModuleOpInducedCarrier h X
    IsScalarTower R Aᵐᵒᵖ (InducedCarrier X) :=
  letI := instModuleOpInducedCarrier h X
  ⟨fun r s z ↦ by
    refine InducedCarrier.ext ?_ (smul_assoc r s z.snd)
    simp [smul_inducedCarrier_fst, unop_smul, op_smul, smul_assoc, smul_sub]⟩

private noncomputable def inducedInternalGrading
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InternalGrading R (InducedCarrier X) ℤ :=
  (X.grading.prod (X.shiftObj 1).grading).map (InducedCarrier.equivProd (R := R)).symm

private theorem mem_inducedInternalGrading_piece_iff
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (p : ℤ) (z : InducedCarrier X) :
    z ∈ (inducedInternalGrading X).piece p ↔
      z.fst ∈ X.grading.piece p ∧ z.snd ∈ X.grading.piece (p - 1) := by
  rw [inducedInternalGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.prod_piece]
  exact Iff.and Iff.rfl (X.mem_shiftObj_piece_iff 1 p z.snd)

private theorem instGradedSMulInducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    letI := instModuleOpInducedCarrier h X
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (inducedInternalGrading X).piece :=
  letI := instModuleOpInducedCarrier h X
  ⟨fun {r p} s z hs hz ↦ by
    rw [mem_inducedInternalGrading_piece_iff] at hz ⊢
    have hs' : s.unop ∈ 𝒜 r := by
      simpa only [InternalGrading.ofDecomposition_piece] using
        ((InternalGrading.ofDecomposition 𝒜).mem_opposite_piece_iff r s).1 hs
    have hds : op (d s.unop) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece (r + 1) :=
      ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff (r + 1) _).2
        (by simpa only [InternalGrading.ofDecomposition_piece] using h.map_mem hs')
    have hdeg₁ : (r + 1) + (p - 1) = r + p := by omega
    have hdeg₂ : r + (p - 1) = r + p - 1 := by omega
    refine ⟨Submodule.sub_mem _
      (by simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem hs hz.1) ?_, ?_⟩
    · simpa only [vadd_eq_add, hdeg₁] using
        SetLike.GradedSMul.smul_mem hds (X.grading.koszulTwist_mem_piece hz.2 1)
    · rw [smul_inducedCarrier_snd]
      simpa only [vadd_eq_add, hdeg₂] using SetLike.GradedSMul.smul_mem hs hz.2⟩

private noncomputable def inducedDiff (w : A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InducedCarrier X →ₗ[R] InducedCarrier X where
  toFun z := ⟨op w • z.snd, z.fst⟩
  map_add' y z := InducedCarrier.ext (smul_add (op w) y.snd z.snd) rfl
  map_smul' r z := InducedCarrier.ext (smul_comm (op w) r z.snd) rfl

@[simp]
private theorem inducedDiff_fst (w : A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier X) :
    (inducedDiff w X z).fst = op w • z.snd :=
  rfl

@[simp]
private theorem inducedDiff_snd (w : A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier X) :
    (inducedDiff w X z).snd = z.fst :=
  rfl

private theorem isCurvedDGRightModule_inducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    letI := instModuleOpInducedCarrier h X
    letI := instIsScalarTowerInducedCarrier h X
    letI := instGradedSMulInducedCarrier h X
    IsCurvedDGRightModule h (inducedInternalGrading X).piece (inducedDiff w X) := by
  let _ := instModuleOpInducedCarrier h X
  let _ := instIsScalarTowerInducedCarrier h X
  let _ := instGradedSMulInducedCarrier h X
  have hw : op w ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece 2 :=
    ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff 2 w).2
      (by simpa only [InternalGrading.ofDecomposition_piece] using h.curvature_mem)
  refine ⟨LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_, fun {p} {z} hz a ↦ ?_, fun z ↦ ?_⟩
  · rw [mem_inducedInternalGrading_piece_iff] at hz ⊢
    have hdeg : (2 : ℤ) + (p - 1) = p + 1 := by omega
    refine ⟨?_, by simpa only [inducedDiff_snd, add_sub_cancel_right] using hz.1⟩
    simpa only [inducedDiff_fst, vadd_eq_add, hdeg] using SetLike.GradedSMul.smul_mem hw hz.2
  · rw [mem_inducedInternalGrading_piece_iff] at hz
    ext
    · simp only [inducedDiff_fst, inducedDiff_snd, Units.smul_def, InducedCarrier.add_fst,
        InducedCarrier.zsmul_fst, smul_inducedCarrier_fst, smul_inducedCarrier_snd, unop_op,
        X.grading.koszulTwist_one_eq_zsmul hz.1, X.grading.koszulTwist_one_eq_zsmul hz.2,
        Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one, Units.val_neg, neg_smul, smul_neg,
        h.sq_eq a, MulOpposite.op_sub, op_mul, sub_smul, mul_smul, smul_sub,
        smul_comm (_ : Aᵐᵒᵖ) (_ : ℤ), ← mul_smul (p.negOnePow : ℤ) (p.negOnePow : ℤ),
        Int.units_coe_mul_self, one_smul]
      abel
    · simp only [inducedDiff_snd, Units.smul_def, InducedCarrier.add_snd,
        InducedCarrier.zsmul_snd, smul_inducedCarrier_fst, smul_inducedCarrier_snd, unop_op,
        X.grading.koszulTwist_one_eq_zsmul hz.2, Int.negOnePow_sub, Int.negOnePow_one, mul_neg,
        mul_one, Units.val_neg, neg_smul, smul_neg, smul_comm (_ : Aᵐᵒᵖ) (_ : ℤ)]
      abel
  · ext
    · simp [h.map_curvature]
    · simp

/-- The **induced curved right module** `G⁺(X)` of a graded right `A`-module `X`, with underlying
graded `R`-module `X ⊕ X{1}`, twisted right `A`-action
`⟨x₀, x₁⟩ · a = ⟨x₀ · a - (-1)^{|x₁|} x₁ · d(a), x₁ · a⟩`, and differential
`⟨x₀, x₁⟩ ↦ ⟨x₁ · w, x₀⟩`. -/
@[implicit_reducible]
noncomputable def induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{u, u, u} h :=
  letI := instModuleOpInducedCarrier h X
  letI := instIsScalarTowerInducedCarrier h X
  letI := instGradedSMulInducedCarrier h X
  CurvedDGRightModuleCat.of (isCurvedDGRightModule_inducedCarrier h X)

@[simp]
private theorem induced_grading (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (induced h X).grading = (inducedInternalGrading X).piece :=
  rfl

@[simp]
private theorem induced_add_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (y z : induced h X) :
    ((y + z : induced h X) : InducedCarrier X).fst =
      (y : InducedCarrier X).fst + (z : InducedCarrier X).fst :=
  rfl

@[simp]
private theorem induced_add_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (y z : induced h X) :
    ((y + z : induced h X) : InducedCarrier X).snd =
      (y : InducedCarrier X).snd + (z : InducedCarrier X).snd :=
  rfl

@[simp]
private theorem induced_smul_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : induced h X) :
    ((s • z : induced h X) : InducedCarrier X).fst =
      s • (z : InducedCarrier X).fst -
        op (d s.unop) • X.grading.koszulTwist 1 (z : InducedCarrier X).snd :=
  rfl

@[simp]
private theorem induced_smul_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : induced h X) :
    ((s • z : induced h X) : InducedCarrier X).snd = s • (z : InducedCarrier X).snd :=
  rfl

@[simp]
private theorem induced_differential_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : induced h X) :
    ((induced h X).differential z : InducedCarrier X).fst =
      op w • (z : InducedCarrier X).snd :=
  rfl

@[simp]
private theorem induced_differential_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : induced h X) :
    ((induced h X).differential z : InducedCarrier X).snd =
      (z : InducedCarrier X).fst :=
  rfl

/-- Every induced curved right module vanishes in the curved homotopy category. -/
theorem isZero_homotopy_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (induced h X)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  let k : induced h X →ₗ[Aᵐᵒᵖ] induced h X :=
    { toFun := fun z : InducedCarrier X ↦ (⟨z.snd, 0⟩ : InducedCarrier X)
      map_add' := fun (y : InducedCarrier X) (z : InducedCarrier X) ↦
        InducedCarrier.ext rfl (by simp)
      map_smul' := fun s (z : InducedCarrier X) ↦
        InducedCarrier.ext (by simp) (by simp) }
  refine ⟨⟨k, ?_⟩, fun z : InducedCarrier X ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p (z : InducedCarrier X) hz
    rw [induced_grading, mem_inducedInternalGrading_piece_iff] at hz ⊢
    dsimp only [k, LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact ⟨by simpa only [sub_eq_add_neg] using hz.2, Submodule.zero_mem _⟩
  · exact InducedCarrier.ext (by simp [k]) (by simp [k])

/-! ### The underlying graded extension `0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` -/

/-- The canonical graded inclusion `X ⟶ G⁺(X)` sending `x₀` to `⟨x₀, 0⟩`. -/
noncomputable def inducedι (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    X ⟶ toGradedModuleCat (induced h X) :=
  GradedModuleCat.ofHom
    { toFun := fun x ↦ (⟨x, 0⟩ : InducedCarrier X)
      map_add' := fun _ _ ↦ InducedCarrier.ext rfl (add_zero 0).symm
      map_smul' := fun s x ↦ InducedCarrier.ext
        (by rw [induced_smul_fst h X]; simp) (smul_zero s).symm }
    (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [toGradedModuleCat_piece, add_zero]
      exact (mem_inducedInternalGrading_piece_iff X p ⟨x, 0⟩).2 ⟨hx, Submodule.zero_mem _⟩)

@[simp]
private theorem inducedι_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (x : X) :
    ((inducedι h X).hom x : InducedCarrier X) = ⟨x, 0⟩ :=
  rfl

/-- The canonical graded projection `G⁺(X) ⟶ X{1}` sending `⟨x₀, x₁⟩` to `x₁`. -/
noncomputable def inducedπ (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (induced h X) ⟶ X.shiftObj 1 :=
  GradedModuleCat.ofHom
    { toFun := fun z : InducedCarrier X ↦ z.snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (LinearMap.isHomogeneous_def.2 fun p (z : InducedCarrier X) hz ↦ by
      rw [toGradedModuleCat_piece] at hz
      rw [add_zero, X.mem_shiftObj_piece_iff 1 p]
      exact ((mem_inducedInternalGrading_piece_iff X p z).1 hz).2)

@[simp]
private theorem inducedπ_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier X) :
    (inducedπ h X).hom z = z.snd :=
  rfl

/-- Composing `inducedι h X` with `inducedπ h X` is zero. -/
@[reassoc (attr := simp)]
theorem inducedι_comp_inducedπ (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedι h X ≫ inducedπ h X = 0 := by
  ext x
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, inducedι_hom_apply, inducedπ_hom_apply,
    GradedModuleCat.hom_zero, LinearMap.zero_apply]

/-- The canonical graded inclusion `X ⟶ G⁺(X)` is a monomorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Mono (inducedι h X) :=
  (GradedModuleCat.mono_iff_injective _).2 fun _ _ hxy ↦ by
    have hfst := congrArg InducedCarrier.fst hxy
    simpa only [inducedι_hom_apply] using hfst

/-- The canonical graded projection `G⁺(X) ⟶ X{1}` is an epimorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Epi (inducedπ h X) :=
  (GradedModuleCat.epi_iff_surjective _).2 fun x₁ ↦
    ⟨(⟨0, x₁⟩ : InducedCarrier X), inducedπ_hom_apply h X ⟨0, x₁⟩⟩

/-- After forgetting the differential, `G⁺(X)` sits in a short exact sequence
`0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` of graded right modules. -/
theorem shortExact_inducedι_inducedπ (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (inducedι h X) (inducedπ h X) (inducedι_comp_inducedπ h X)).ShortExact where
  mono_f := inferInstance
  epi_g := inferInstance
  exact := GradedModuleCat.exact_iff.2 fun z : InducedCarrier X ↦
    ⟨fun hz ↦ ⟨z.fst, InducedCarrier.ext
      (by dsimp only; rw [inducedι_hom_apply])
      (by
        dsimp only at hz ⊢
        rw [inducedι_hom_apply]
        rw [inducedπ_hom_apply] at hz
        exact hz.symm)⟩,
    by
      rintro ⟨x, rfl⟩
      dsimp only
      rw [inducedι_hom_apply, inducedπ_hom_apply]⟩

/-- If `X` is a projective graded right module, then `G⁺(X)` is graded-projective. -/
instance projective_toGradedModuleCat_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective X] :
    Projective (toGradedModuleCat (induced h X)) := by
  have hX1 : Projective (X.shiftObj 1) := GradedModuleCat.projective_shiftObj X 1
  exact projective_iff_hasProjectiveDimensionLT_one.2
    ((shortExact_inducedι_inducedπ h X).hasProjectiveDimensionLT_X₂ 1
      (projective_iff_hasProjectiveDimensionLT_one.1 inferInstance)
      (projective_iff_hasProjectiveDimensionLT_one.1 hX1))

/-- If `X` is an injective graded right module, then `G⁺(X)` is graded-injective. -/
instance injective_toGradedModuleCat_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective X] :
    Injective (toGradedModuleCat (induced h X)) := by
  have hX1 : Injective (X.shiftObj 1) := GradedModuleCat.injective_shiftObj X 1
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((shortExact_inducedι_inducedπ h X).hasInjectiveDimensionLT_X₂ 1
      (injective_iff_hasInjectiveDimensionLT_one.1 inferInstance)
      (injective_iff_hasInjectiveDimensionLT_one.1 hX1))

end Construction

/-! ### Left adjunction `G⁺ ⊣ forgetDifferential` -/

section InducedAdjunction

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private theorem differential_smul (M : CurvedDGRightModuleCat.{u, u, u} h) (s : Aᵐᵒᵖ) (m : M) :
    M.differential (s • m) =
      s • M.differential m +
        op (d s.unop) • (InternalGrading.ofDecomposition M.grading).koszulTwist 1 m := by
  rw [← op_unop s]
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | @homogeneous p hm =>
    have hm' : (hm : M) ∈ (InternalGrading.ofDecomposition M.grading).piece p := by
      simpa only [InternalGrading.ofDecomposition_piece] using hm.2
    rw [M.isCurvedDGRightModule.leibniz hm.2 s.unop, Units.smul_def, unop_op,
      (InternalGrading.ofDecomposition M.grading).koszulTwist_one_eq_zsmul hm',
      smul_comm (op (d s.unop) : Aᵐᵒᵖ) (p.negOnePow : ℤ)]
  | add m₁ m₂ ih₁ ih₂ =>
    simp only [smul_add, map_add, unop_op, ih₁, ih₂]
    abel

private theorem koszulTwist_one_hom_apply
    {P Q : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (u : P ⟶ Q) (x : P) :
    Q.grading.koszulTwist 1 (u.hom x) = u.hom (P.grading.koszulTwist 1 x) := by
  have hu : LinearMap.IsHomogeneous (u.hom.restrictScalars R) P.grading.piece Q.grading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ u.isHomogeneous.map_mem hy
  simpa using hu.koszulTwist_apply 1 x

private theorem toGradedModuleCat_grading (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (toGradedModuleCat M).grading = InternalGrading.ofDecomposition M.grading :=
  rfl

private abbrev toCurvedLinearMap {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) : X →ₗ[Aᵐᵒᵖ] M :=
  f.hom

/-- Transpose a graded morphism `X ⟶ M` to a closed morphism `G⁺(X) ⟶ M` via
`⟨x₀, x₁⟩ ↦ f(x₀) + d_M(f(x₁))`. -/
noncomputable def inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  have hfM (p : ℤ) (x : X) (hx : x ∈ X.grading.piece p) : toCurvedLinearMap f x ∈ M.grading p := by
    simpa only [toGradedModuleCat_piece] using GradedModuleCat.map_mem f hx
  closedHomOf (M := induced h X) (N := M)
    { toFun := fun z ↦
        toCurvedLinearMap f (z : InducedCarrier X).fst +
          M.differential (toCurvedLinearMap f (z : InducedCarrier X).snd)
      map_add' := fun y z ↦ by
        simp only [induced_add_fst, induced_add_snd, map_add]
        abel
      map_smul' := fun s z ↦ by
        simp only [RingHom.id_apply, induced_smul_fst, induced_smul_snd, map_sub,
          LinearMap.map_smul, differential_smul, smul_add]
        dsimp only [toCurvedLinearMap]
        rw [← toGradedModuleCat_grading M, koszulTwist_one_hom_apply f]
        abel }
    (fun p z hz ↦ by
      obtain ⟨hz₀, hz₁⟩ := (mem_inducedInternalGrading_piece_iff X p z).1 hz
      exact Submodule.add_mem _ (hfM p (z : InducedCarrier X).fst hz₀) (by
        simpa only [sub_add_cancel] using
          M.isCurvedDGRightModule.isHomogeneous.map_mem
            (hfM (p - 1) (z : InducedCarrier X).snd hz₁)))
    (fun z ↦ by
      simp [M.isCurvedDGRightModule.sq_eq, add_comm])

@[simp]
private theorem closedHom_inducedDesc_apply {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) (z : induced h X) :
    closedHom (inducedDesc f) z =
      toCurvedLinearMap f (z : InducedCarrier X).fst +
        M.differential (toCurvedLinearMap f (z : InducedCarrier X).snd) := by
  rw [inducedDesc, closedHom_closedHomOf]
  rfl

/-- Precomposing `inducedDesc f` with `inducedι h X` recovers `f`. -/
@[reassoc (attr := simp)]
theorem inducedι_comp_forgetDifferential_inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) :
    inducedι h X ≫ (forgetDifferential (h := h)).map (inducedDesc f) = f := by
  ext x
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom,
    closedHom_inducedDesc_apply, inducedι_hom_apply]
  simp

/-- Every closed morphism `G⁺(X) ⟶ M` is uniquely `inducedDesc` of its restriction along
`inducedι h X`. -/
@[simp]
theorem inducedDesc_unique {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    inducedDesc (inducedι h X ≫ (forgetDifferential (h := h)).map φ) = φ := by
  ext z
  let z₀ : induced h X := (⟨(z : InducedCarrier X).fst, 0⟩ : InducedCarrier X)
  let z₁ : induced h X := (⟨(z : InducedCarrier X).snd, 0⟩ : InducedCarrier X)
  have hz : z = z₀ + (induced h X).differential z₁ :=
    InducedCarrier.ext (by simp [z₀, z₁]) (by simp [z₀, z₁])
  rw [closedHom_inducedDesc_apply]
  conv_rhs => rw [hz]
  rw [map_add, ← differential_closedHom φ]
  dsimp only [toCurvedLinearMap, z₀, z₁]
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    forgetDifferential_map_hom]
  rfl

/-- Closed morphisms out of `G⁺(X)` are uniquely determined by their graded restrictions along
`inducedι h X`. -/
@[ext]
theorem induced_hom_ext {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {φ ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M}
    (hφψ : inducedι h X ≫ (forgetDifferential (h := h)).map φ =
      inducedι h X ≫ (forgetDifferential (h := h)).map ψ) :
    φ = ψ := by
  rw [← inducedDesc_unique φ, ← inducedDesc_unique ψ, hφψ]

/-- Descending `inducedι h X` itself yields the identity on `G⁺(X)`. -/
@[simp]
theorem inducedDesc_inducedι (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedDesc (M := induced h X) (inducedι h X) =
      𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X)) := by
  apply induced_hom_ext
  rw [inducedι_comp_forgetDifferential_inducedDesc,
    (forgetDifferential (h := h)).map_id
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X))]
  exact (Category.comp_id (inducedι h X)).symm

/-- Postcomposing `inducedDesc f` with a closed morphism `ψ : M ⟶ N` descends
`f ≫ (forgetDifferential (h := h)).map ψ`. -/
@[reassoc (attr := simp)]
theorem inducedDesc_comp {M N : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M)
    (ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    inducedDesc f ≫ ψ = inducedDesc (f ≫ (forgetDifferential (h := h)).map ψ) := by
  apply induced_hom_ext
  rw [Functor.map_comp, inducedι_comp_forgetDifferential_inducedDesc_assoc,
    inducedι_comp_forgetDifferential_inducedDesc]

/-- An epimorphism `X ↠ M` of graded right modules transposes to an epimorphism `G⁺(X) ↠ M` of
curved right modules. -/
instance epi_inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) [Epi f] : Epi (inducedDesc f) := by
  have : Epi (inducedι h X ≫ (forgetDifferential (h := h)).map (inducedDesc f)) := by
    rw [inducedι_comp_forgetDifferential_inducedDesc]
    infer_instance
  exact (forgetDifferential (h := h)).epi_of_epi_map (epi_of_epi (inducedι h X) _)

variable (h) in
/-- The **induced curved-module functor** `G⁺`, left adjoint to `forgetDifferential`. -/
@[expose, implicit_reducible]
noncomputable def inducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) :=
  Adjunction.leftAdjointOfEquiv
    (fun X M ↦
      { toFun := fun φ ↦ inducedι h X ≫ (forgetDifferential (h := h)).map φ
        invFun := fun f ↦ inducedDesc (M := ForgetEnrichment.to _ M) f
        left_inv := fun φ ↦ inducedDesc_unique (M := ForgetEnrichment.to _ M) φ
        right_inv := fun f ↦
          inducedι_comp_forgetDifferential_inducedDesc (M := ForgetEnrichment.to _ M) f })
    fun _ _ _ _ _ ↦ by simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]

/-- `inducedFunctor h` sends a graded right module `X` to `induced h X`. -/
@[simp]
theorem inducedFunctor_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedFunctor h).obj X =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) :=
  (rfl)

/-- `inducedFunctor h` maps `u : X ⟶ Y` to `inducedDesc (u ≫ inducedι h Y)`. -/
@[simp]
theorem inducedFunctor_map (h : IsCurvedDGAlgebra 𝒜 d w)
    {X Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece} (u : X ⟶ Y) :
    (inducedFunctor h).map u = inducedDesc (u ≫ inducedι h Y) := by
  dsimp only [inducedFunctor]
  rw [Adjunction.leftAdjointOfEquiv_map]
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, CategoryTheory.Functor.map_id]
  exact congrArg (fun v ↦ inducedDesc (u ≫ v)) (Category.comp_id (inducedι h Y))

/-- Precomposing `inducedDesc f` with `(inducedFunctor h).map u` descends `u ≫ f`. -/
@[reassoc]
theorem inducedFunctor_map_comp_inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (u : X ⟶ Y) (f : Y ⟶ toGradedModuleCat M) :
    (inducedFunctor h).map u ≫ inducedDesc f = inducedDesc (u ≫ f) := by
  simp

variable (h) in
/-- The adjunction `inducedFunctor h ⊣ forgetDifferential`. -/
noncomputable def inducedAdj : inducedFunctor h ⊣ forgetDifferential (h := h) :=
  Adjunction.adjunctionOfEquivLeft
    (fun X M ↦
      { toFun := fun φ ↦ inducedι h X ≫ (forgetDifferential (h := h)).map φ
        invFun := fun f ↦ inducedDesc (M := ForgetEnrichment.to _ M) f
        left_inv := fun φ ↦ inducedDesc_unique (M := ForgetEnrichment.to _ M) φ
        right_inv := fun f ↦
          inducedι_comp_forgetDifferential_inducedDesc (M := ForgetEnrichment.to _ M) f })
    fun _ _ _ _ _ ↦ by simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]

/-- The forward hom-equivalence of `inducedAdj h` precomposes with `inducedι`. -/
@[simp]
theorem inducedAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (φ : (inducedFunctor h).obj X ⟶ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    (inducedAdj h).homEquiv X (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) φ =
      inducedι h X ≫ (forgetDifferential (h := h)).map φ := by
  rw [inducedAdj, Adjunction.adjunctionOfEquivLeft, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse hom-equivalence of `inducedAdj h` is `inducedDesc`. -/
@[simp]
theorem inducedAdj_homEquiv_symm_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : X ⟶ toGradedModuleCat M) :
    ((inducedAdj h).homEquiv
        X (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)).symm f =
      inducedDesc f := by
  rw [inducedAdj, Adjunction.adjunctionOfEquivLeft, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of `inducedAdj h` at `X` is `inducedι h X`. -/
@[simp]
theorem inducedAdj_unit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedAdj h).unit.app X = inducedι h X := by
  rw [inducedAdj, Adjunction.adjunctionOfEquivLeft_unit_app]
  simp only [Equiv.coe_fn_mk, CategoryTheory.Functor.map_id]
  exact Category.comp_id (inducedι h X)

/-- The counit of `inducedAdj h` at `M` is `inducedDesc (𝟙 (toGradedModuleCat M))`. -/
@[simp]
theorem inducedAdj_counit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (inducedAdj h).counit.app (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      inducedDesc (𝟙 (toGradedModuleCat M)) := by
  rw [inducedAdj, Adjunction.adjunctionOfEquivLeft_counit_app]
  rfl

instance : (inducedFunctor h).IsLeftAdjoint :=
  (inducedAdj h).isLeftAdjoint

instance : (forgetDifferential (h := h)).IsRightAdjoint :=
  (inducedAdj h).isRightAdjoint

instance : (inducedFunctor h).Additive :=
  (inducedAdj h).left_adjoint_additive

instance : (inducedFunctor h).Linear R where
  map_smul {X Y} u r := by
    rw [inducedFunctor_map, inducedFunctor_map]
    apply induced_hom_ext
    simp

end InducedAdjunction

/-! ### Coinduced curved modules and the right adjunction `forgetDifferential ⊣ G⁻` -/

section CoinducedAdjunction

/-- The **coinduced curved right module** `G⁻(Y) = G⁺(Y{-1})` of a graded right `A`-module `Y`,
whose degree-`p` elements are pairs `⟨y₁, y₀⟩` with `y₁ ∈ Y_{p + 1}` and `y₀ ∈ Yₚ`. -/
@[implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{u, u, u} h :=
  induced h (Y.shiftObj (-1))

/-- `G⁻(Y)` is by definition `G⁺(Y{-1})`. -/
theorem coinduced_eq (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinduced h Y = induced h (Y.shiftObj (-1)) :=
  (rfl)

@[simp]
private theorem coinduced_add_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (y z : coinduced h Y) :
    ((y + z : coinduced h Y) : InducedCarrier Y).fst =
      (y : InducedCarrier Y).fst + (z : InducedCarrier Y).fst :=
  rfl

@[simp]
private theorem coinduced_add_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (y z : coinduced h Y) :
    ((y + z : coinduced h Y) : InducedCarrier Y).snd =
      (y : InducedCarrier Y).snd + (z : InducedCarrier Y).snd :=
  rfl

@[simp]
private theorem coinduced_smul_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : coinduced h Y) :
    ((s • z : coinduced h Y) : InducedCarrier Y).fst =
      s • (z : InducedCarrier Y).fst -
        op (d s.unop) • (Y.shiftObj (-1)).grading.koszulTwist 1 (z : InducedCarrier Y).snd :=
  rfl

@[simp]
private theorem coinduced_smul_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : coinduced h Y) :
    ((s • z : coinduced h Y) : InducedCarrier Y).snd = s • (z : InducedCarrier Y).snd :=
  rfl

@[simp]
private theorem coinduced_differential_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinduced h Y) :
    ((coinduced h Y).differential z : InducedCarrier Y).fst =
      op w • (z : InducedCarrier Y).snd :=
  rfl

@[simp]
private theorem coinduced_differential_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinduced h Y) :
    ((coinduced h Y).differential z : InducedCarrier Y).snd =
      (z : InducedCarrier Y).fst :=
  rfl

/-- Every coinduced curved right module vanishes in the curved homotopy category. -/
theorem isZero_homotopy_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinduced h Y)) :=
  isZero_homotopy_induced h (Y.shiftObj (-1))

/-- If `Y` is a projective graded right module, then `G⁻(Y)` is graded-projective. -/
instance projective_toGradedModuleCat_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective Y] :
    Projective (toGradedModuleCat (coinduced h Y)) := by
  have : Projective (Y.shiftObj (-1)) := GradedModuleCat.projective_shiftObj Y (-1)
  exact projective_toGradedModuleCat_induced h (Y.shiftObj (-1))

/-- If `Y` is an injective graded right module, then `G⁻(Y)` is graded-injective. -/
instance injective_toGradedModuleCat_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective Y] :
    Injective (toGradedModuleCat (coinduced h Y)) := by
  have : Injective (Y.shiftObj (-1)) := GradedModuleCat.injective_shiftObj Y (-1)
  exact injective_toGradedModuleCat_induced h (Y.shiftObj (-1))

/-- The canonical graded inclusion `Y{-1} ⟶ G⁻(Y)` sending `y₁` to `⟨y₁, 0⟩`. -/
noncomputable def coinducedι (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Y.shiftObj (-1) ⟶ toGradedModuleCat (coinduced h Y) :=
  inducedι h (Y.shiftObj (-1))

/-- The canonical graded counit `G⁻(Y) ⟶ Y` projecting `⟨y₁, y₀⟩` onto `y₀`. -/
noncomputable def coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinduced h Y) ⟶ Y :=
  inducedπ h (Y.shiftObj (-1)) ≫
    (GradedModuleCat.shift (InternalGrading.ofDecomposition 𝒜).opposite.piece).counitIso.hom.app Y

@[simp]
private theorem coinducedCounit_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier Y) :
    (coinducedCounit h Y).hom z = z.snd := by
  rw [coinducedCounit, GradedModuleCat.hom_comp, LinearMap.comp_apply, inducedπ_hom_apply]
  simp [GradedModuleCat.shift]

/-- The canonical graded inclusion `Y{-1} ⟶ G⁻(Y)` is a monomorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Mono (coinducedι h Y) :=
  inferInstanceAs (Mono (inducedι h (Y.shiftObj (-1))))

/-- The canonical graded counit `G⁻(Y) ⟶ Y` is an epimorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Epi (coinducedCounit h Y) := by
  rw [coinducedCounit]
  exact epi_comp _ _

/-- Composing `coinducedι h Y` with `coinducedCounit h Y` is zero. -/
@[reassoc (attr := simp)]
theorem coinducedι_comp_coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedι h Y ≫ coinducedCounit h Y = 0 := by
  rw [coinducedι, coinducedCounit, inducedι_comp_inducedπ_assoc, zero_comp]

/-- After forgetting the differential, `G⁻(Y)` sits in a short exact sequence
`0 ⟶ Y{-1} ⟶ G⁻(Y) ⟶ Y ⟶ 0` of graded right modules. -/
theorem shortExact_coinducedι_coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedι h Y) (coinducedCounit h Y)
      (coinducedι_comp_coinducedCounit h Y)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (shortExact_inducedι_inducedπ h (Y.shiftObj (-1)))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((GradedModuleCat.shift
      (InternalGrading.ofDecomposition 𝒜).opposite.piece).counitIso.app Y)
    (by simp [coinducedι]) (by simp [coinducedCounit])

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private noncomputable def coinducedLiftLinearMap {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) : M →ₗ[Aᵐᵒᵖ] coinduced h Y where
  toFun m := (⟨g.hom (M.differential m), g.hom m⟩ : InducedCarrier Y)
  map_add' m₁ m₂ := InducedCarrier.ext (by simp) (by simp)
  map_smul' s m := by
    refine InducedCarrier.ext ?_ (g.hom.map_smul s m)
    dsimp only
    rw [differential_smul, map_add, g.hom.map_smul, g.hom.map_smul, coinduced_smul_fst h Y]
    dsimp only
    rw [← toGradedModuleCat_grading M, ← koszulTwist_one_hom_apply g]
    simp [InternalGrading.koszulTwist_one_shift_one, sub_neg_eq_add]

@[simp]
private theorem coinducedLiftLinearMap_fst {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    (coinducedLiftLinearMap g m : InducedCarrier Y).fst = g.hom (M.differential m) :=
  rfl

@[simp]
private theorem coinducedLiftLinearMap_snd {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    (coinducedLiftLinearMap g m : InducedCarrier Y).snd = g.hom m :=
  rfl

/-- Transpose a graded morphism `M ⟶ Y` to a closed morphism `M ⟶ G⁻(Y)` via
`m ↦ ⟨g(d_M m), g(m)⟩`. -/
noncomputable def coinducedLift {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y) :=
  closedHomOf (coinducedLiftLinearMap g)
    (fun p m hm ↦ by
      have hdeg : p - 1 - -1 = p := by omega
      refine (mem_inducedInternalGrading_piece_iff (Y.shiftObj (-1)) p _).2 ⟨?_, ?_⟩
      · rw [coinducedLiftLinearMap_fst, Y.mem_shiftObj_piece_iff (-1) p, sub_neg_eq_add]
        exact GradedModuleCat.map_mem g (by
          simpa only [toGradedModuleCat_piece] using
            M.isCurvedDGRightModule.isHomogeneous.map_mem hm)
      · rw [coinducedLiftLinearMap_snd, Y.mem_shiftObj_piece_iff (-1) (p - 1)]
        simpa only [hdeg] using
          GradedModuleCat.map_mem g (by simpa only [toGradedModuleCat_piece] using hm))
    (fun m ↦ InducedCarrier.ext (by simp [M.isCurvedDGRightModule.sq_eq]) (by simp))

@[simp]
private theorem closedHom_coinducedLift_fst {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    ((closedHom (coinducedLift g) m : coinduced h Y) : InducedCarrier Y).fst =
      g.hom (M.differential m) := by
  rw [coinducedLift, closedHom_closedHomOf, coinducedLiftLinearMap_fst]

@[simp]
private theorem closedHom_coinducedLift_snd {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    ((closedHom (coinducedLift g) m : coinduced h Y) : InducedCarrier Y).snd = g.hom m := by
  rw [coinducedLift, closedHom_closedHomOf, coinducedLiftLinearMap_snd]

/-- Postcomposing `coinducedLift g` with `coinducedCounit h Y` recovers `g`. -/
@[reassoc (attr := simp)]
theorem forgetDifferential_coinducedLift_comp_coinducedCounit
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) :
    (forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y = g := by
  ext m
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom,
    coinducedCounit_hom_apply, closedHom_coinducedLift_snd]

/-- Every closed morphism `M ⟶ G⁻(Y)` is uniquely `coinducedLift` of its counit composite. -/
@[simp]
theorem coinducedLift_unique {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y)) :
    coinducedLift ((forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y) = φ := by
  ext m
  have hd := congrArg InducedCarrier.snd (differential_closedHom φ m)
  rw [coinduced_differential_snd] at hd
  refine InducedCarrier.ext ?_ ?_
  · rw [closedHom_coinducedLift_fst, GradedModuleCat.hom_comp, LinearMap.comp_apply,
      forgetDifferential_map_hom, coinducedCounit_hom_apply, hd]
    rfl
  · rw [closedHom_coinducedLift_snd, GradedModuleCat.hom_comp, LinearMap.comp_apply,
      forgetDifferential_map_hom, coinducedCounit_hom_apply]

/-- Closed morphisms into `G⁻(Y)` are uniquely determined by their graded composites with
`coinducedCounit h Y`. -/
@[ext]
theorem coinduced_hom_ext {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {φ ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y)}
    (hφψ : (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y =
      (forgetDifferential (h := h)).map ψ ≫ coinducedCounit h Y) :
    φ = ψ := by
  rw [← coinducedLift_unique φ, ← coinducedLift_unique ψ, hφψ]

/-- Lifting `coinducedCounit h Y` itself yields the identity on `G⁻(Y)`. -/
@[simp]
theorem coinducedLift_coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedLift (M := coinduced h Y) (coinducedCounit h Y) =
      𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y)) := by
  apply coinduced_hom_ext
  rw [forgetDifferential_coinducedLift_comp_coinducedCounit, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Precomposing `coinducedLift g` with a closed morphism `ψ : M' ⟶ M` lifts
`(forgetDifferential (h := h)).map ψ ≫ g`. -/
@[reassoc (attr := simp)]
theorem comp_coinducedLift {M' M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
    (g : toGradedModuleCat M ⟶ Y) :
    ψ ≫ coinducedLift g = coinducedLift ((forgetDifferential (h := h)).map ψ ≫ g) := by
  apply coinduced_hom_ext
  rw [Functor.map_comp, Category.assoc, forgetDifferential_coinducedLift_comp_coinducedCounit,
    forgetDifferential_coinducedLift_comp_coinducedCounit]

/-- A monomorphism `M ↪ Y` of graded right modules transposes to a monomorphism `M ↪ G⁻(Y)` of
curved right modules. -/
instance mono_coinducedLift {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) [Mono g] : Mono (coinducedLift g) := by
  have : Mono ((forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y) := by
    rw [forgetDifferential_coinducedLift_comp_coinducedCounit]
    infer_instance
  exact (forgetDifferential (h := h)).mono_of_mono_map (mono_of_mono _ (coinducedCounit h Y))

variable (h) in
/-- The **coinduced curved-module functor** `G⁻`, right adjoint to `forgetDifferential`. -/
@[expose, implicit_reducible]
noncomputable def coinducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) :=
  Adjunction.rightAdjointOfEquiv
    (fun M Y ↦
      { toFun := fun g ↦ coinducedLift (M := ForgetEnrichment.to _ M) g
        invFun := fun φ ↦ (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y
        left_inv := fun g ↦
          forgetDifferential_coinducedLift_comp_coinducedCounit (M := ForgetEnrichment.to _ M) g
        right_inv := fun φ ↦ coinducedLift_unique (M := ForgetEnrichment.to _ M) φ })
    fun _ _ _ _ _ ↦ (comp_coinducedLift _ _).symm

/-- `coinducedFunctor h` sends a graded right module `Y` to `coinduced h Y`. -/
@[simp]
theorem coinducedFunctor_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedFunctor h).obj Y =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y) :=
  (rfl)

/-- `coinducedFunctor h` maps `v : Y ⟶ Z` to `coinducedLift (coinducedCounit h Y ≫ v)`. -/
@[simp]
theorem coinducedFunctor_map (h : IsCurvedDGAlgebra 𝒜 d w)
    {Y Z : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece} (v : Y ⟶ Z) :
    (coinducedFunctor h).map v = coinducedLift (coinducedCounit h Y ≫ v) := by
  dsimp only [coinducedFunctor]
  rw [Adjunction.rightAdjointOfEquiv_map]
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Postcomposing `coinducedLift g` with `(coinducedFunctor h).map v` lifts `g ≫ v`. -/
@[reassoc]
theorem coinducedLift_comp_coinducedFunctor_map {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y Z : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (v : Y ⟶ Z) :
    coinducedLift g ≫ (coinducedFunctor h).map v = coinducedLift (g ≫ v) := by
  simp

variable (h) in
/-- The adjunction `forgetDifferential ⊣ coinducedFunctor h`. -/
noncomputable def coinducedAdj : forgetDifferential (h := h) ⊣ coinducedFunctor h :=
  Adjunction.adjunctionOfEquivRight
    (fun M Y ↦
      { toFun := fun g ↦ coinducedLift (M := ForgetEnrichment.to _ M) g
        invFun := fun φ ↦ (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y
        left_inv := fun g ↦
          forgetDifferential_coinducedLift_comp_coinducedCounit (M := ForgetEnrichment.to _ M) g
        right_inv := fun φ ↦ coinducedLift_unique (M := ForgetEnrichment.to _ M) φ })
    fun _ _ _ _ _ ↦ (comp_coinducedLift _ _).symm

/-- The forward hom-equivalence of `coinducedAdj h` is `coinducedLift`. -/
@[simp]
theorem coinducedAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) :
    (coinducedAdj h).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) Y g =
      coinducedLift g := by
  rw [coinducedAdj, Adjunction.adjunctionOfEquivRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse hom-equivalence of `coinducedAdj h` postcomposes with `coinducedCounit`. -/
@[simp]
theorem coinducedAdj_homEquiv_symm_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶ (coinducedFunctor h).obj Y) :
    ((coinducedAdj h).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) Y).symm φ =
      (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y := by
  rw [coinducedAdj, Adjunction.adjunctionOfEquivRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The counit of `coinducedAdj h` at `Y` is `coinducedCounit h Y`. -/
@[simp]
theorem coinducedAdj_counit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedAdj h).counit.app Y = coinducedCounit h Y := by
  rw [coinducedAdj, Adjunction.adjunctionOfEquivRight_counit_app]
  simp only [Equiv.coe_fn_symm_mk, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The unit of `coinducedAdj h` at `M` is `coinducedLift (𝟙 (toGradedModuleCat M))`. -/
@[simp]
theorem coinducedAdj_unit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (coinducedAdj h).unit.app (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      coinducedLift (𝟙 (toGradedModuleCat M)) := by
  rw [coinducedAdj, Adjunction.adjunctionOfEquivRight_unit_app]
  rfl

instance : (forgetDifferential (h := h)).IsLeftAdjoint :=
  (coinducedAdj h).isLeftAdjoint

instance : (coinducedFunctor h).IsRightAdjoint :=
  (coinducedAdj h).isRightAdjoint

instance : (coinducedFunctor h).Additive :=
  (coinducedAdj h).right_adjoint_additive

instance : (coinducedFunctor h).Linear R where
  map_smul {Y Z} v r := by
    rw [coinducedFunctor_map, coinducedFunctor_map]
    apply coinduced_hom_ext
    simp

end CoinducedAdjunction

end TauCeti.CurvedDGRightModuleCat
