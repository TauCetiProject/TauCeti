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
public import TauCeti.Algebra.Homology.Curved.Module.Right.Abelian
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.Algebra.Module.GradedModule.Prod

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
  `0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` of graded right modules (`⟨x₀, 0⟩` and `⟨x₀, x₁⟩ ↦ x₁`), so `G⁺`
  and `G⁻` preserve both graded-projective and graded-injective objects.
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
* `TauCeti.CurvedDGRightModuleCat.inducedShortComplex_shortExact`: the underlying graded module of
  `G⁺(X)` is an extension of `X{1}` by `X`.
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
  DGHomotopyCategory.of DGHomotopyCategory.underlying

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

private theorem koszulTwist_one_eq_zsmul {M : Type u} [AddCommGroup M] [Module R M]
    {G : InternalGrading R M ℤ} {x : M} {q : ℤ} (hx : x ∈ G.piece q) :
    G.koszulTwist 1 x = (q.negOnePow : ℤ) • x := by
  rw [G.koszulTwist_one_apply_of_mem hx, Int.cast_smul_eq_zsmul R]

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
  have hsign : (r.negOnePow : ℤ) * (q.negOnePow : ℤ) = ((r + q).negOnePow : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
  rw [koszulTwist_one_eq_zsmul hx, koszulTwist_one_eq_zsmul hax, h.leibniz ha b, Units.smul_def,
    MulOpposite.op_add, add_smul, op_mul (d a) b, mul_smul, op_smul, op_mul a (d b), smul_assoc,
    mul_smul, smul_comm (op a : Aᵐᵒᵖ) (q.negOnePow : ℤ),
    smul_comm (op (d b) : Aᵐᵒᵖ) (q.negOnePow : ℤ), ← mul_smul (r.negOnePow : ℤ) (q.negOnePow : ℤ),
    hsign, smul_comm ((r + q).negOnePow : ℤ) (op (d b) : Aᵐᵒᵖ)]

private theorem op_map_mul_smul_koszulTwist (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a b : A) (x : X) :
    op (d (a * b)) • X.grading.koszulTwist 1 x =
      op b • (op (d a) • X.grading.koszulTwist 1 x) +
        op (d b) • X.grading.koszulTwist 1 (op a • x) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
    rw [zero_mul, map_zero, MulOpposite.op_zero, zero_smul, zero_smul, map_zero, smul_zero,
      smul_zero, add_zero]
  | homogeneous ha =>
    induction x using DirectSum.Decomposition.inductionOn X.grading.piece with
    | zero => simp only [map_zero, smul_zero, add_zero]
    | homogeneous hx => exact op_map_mul_smul_koszulTwist_of_mem h ha.2 b hx.2
    | add x₁ x₂ ih₁ ih₂ =>
      simp only [map_add, smul_add, ih₁, ih₂]
      abel
  | add a₁ a₂ ih₁ ih₂ =>
    rw [add_mul, map_add, MulOpposite.op_add, add_smul, map_add, MulOpposite.op_add, add_smul,
      smul_add, MulOpposite.op_add, add_smul, map_add, smul_add, ih₁, ih₂]
    abel

private noncomputable def inducedSMul (d : A →ₗ[R] A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : InducedCarrier X) : InducedCarrier X :=
  ⟨s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd, s • z.snd⟩

@[instance_reducible]
private noncomputable def instModuleOpInducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Module Aᵐᵒᵖ (InducedCarrier X) :=
  { smul := inducedSMul d X
    one_smul := fun z ↦ InducedCarrier.ext
      (show (1 : Aᵐᵒᵖ) • z.fst - op (d (1 : Aᵐᵒᵖ).unop) • X.grading.koszulTwist 1 z.snd = z.fst by
        rw [unop_one, h.map_one_eq_zero, MulOpposite.op_zero, zero_smul, sub_zero, one_smul])
      (one_smul Aᵐᵒᵖ z.snd)
    mul_smul := fun s t z ↦ InducedCarrier.ext
      (show (s * t) • z.fst - op (d (s * t).unop) • X.grading.koszulTwist 1 z.snd =
          s • (t • z.fst - op (d t.unop) • X.grading.koszulTwist 1 z.snd) -
            op (d s.unop) • X.grading.koszulTwist 1 (t • z.snd) by
        rw [unop_mul, op_map_mul_smul_koszulTwist h X t.unop s.unop z.snd, smul_sub, mul_smul]
        simp only [op_unop]
        abel)
      (mul_smul s t z.snd)
    smul_zero := fun s ↦ InducedCarrier.ext
      (show s • (0 : X) - op (d s.unop) • X.grading.koszulTwist 1 0 = 0 by
        rw [smul_zero, map_zero, smul_zero, sub_zero])
      (smul_zero s)
    smul_add := fun s y z ↦ InducedCarrier.ext
      (show s • (y.fst + z.fst) - op (d s.unop) • X.grading.koszulTwist 1 (y.snd + z.snd) =
          (s • y.fst - op (d s.unop) • X.grading.koszulTwist 1 y.snd) +
            (s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd) by
        rw [smul_add, map_add, smul_add]
        abel)
      (smul_add s y.snd z.snd)
    add_smul := fun s t z ↦ InducedCarrier.ext
      (show (s + t) • z.fst - op (d (s + t).unop) • X.grading.koszulTwist 1 z.snd =
          (s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd) +
            (t • z.fst - op (d t.unop) • X.grading.koszulTwist 1 z.snd) by
        rw [MulOpposite.unop_add, map_add, MulOpposite.op_add, add_smul, add_smul]
        abel)
      (add_smul s t z.snd)
    zero_smul := fun z ↦ InducedCarrier.ext
      (show (0 : Aᵐᵒᵖ) • z.fst - op (d (0 : Aᵐᵒᵖ).unop) • X.grading.koszulTwist 1 z.snd = 0 by
        rw [MulOpposite.unop_zero, map_zero, MulOpposite.op_zero, zero_smul, zero_smul, sub_zero])
      (zero_smul Aᵐᵒᵖ z.snd) }

@[simp]
private theorem op_smul_inducedCarrier_fst (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : A) (z : InducedCarrier X) :
    (letI := instModuleOpInducedCarrier h X; (op a • z).fst) =
      op a • z.fst - op (d a) • X.grading.koszulTwist 1 z.snd :=
  rfl

@[simp]
private theorem smul_inducedCarrier_snd (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (s : Aᵐᵒᵖ) (z : InducedCarrier X) :
    (letI := instModuleOpInducedCarrier h X; (s • z).snd) = s • z.snd :=
  rfl

private theorem instIsScalarTowerInducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    letI := instModuleOpInducedCarrier h X
    IsScalarTower R Aᵐᵒᵖ (InducedCarrier X) :=
  letI := instModuleOpInducedCarrier h X
  ⟨fun r s z ↦ by
    refine InducedCarrier.ext ?_ (smul_assoc r s z.snd)
    -- Both sides expand through `inducedSMul` on the first coordinate.
    change (r • s) • z.fst - op (d (r • s).unop) • X.grading.koszulTwist 1 z.snd =
      r • (s • z.fst - op (d s.unop) • X.grading.koszulTwist 1 z.snd)
    rw [unop_smul, d.map_smul, op_smul, smul_assoc, smul_assoc, smul_sub]⟩

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
    refine ⟨Submodule.sub_mem _
      (by simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem hs hz.1) ?_, ?_⟩
    · simpa only [vadd_eq_add, show (r + 1) + (p - 1) = r + p by omega] using
        SetLike.GradedSMul.smul_mem hds (X.grading.koszulTwist_mem_piece hz.2 1)
    · rw [smul_inducedCarrier_snd h X]
      simpa only [vadd_eq_add, show r + (p - 1) = r + p - 1 by omega] using
        SetLike.GradedSMul.smul_mem hs hz.2⟩

private noncomputable def inducedDiff (w : A)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InducedCarrier X →ₗ[R] InducedCarrier X where
  toFun z := ⟨op w • z.snd, z.fst⟩
  map_add' y z := InducedCarrier.ext (smul_add (op w) y.snd z.snd) rfl
  map_smul' r z := InducedCarrier.ext (smul_comm (op w) r z.snd) rfl

private theorem negOnePow_sub_one (p : ℤ) : ((p - 1).negOnePow : ℤ) = -(p.negOnePow : ℤ) := by
  have hp : p = p - 1 + 1 := by omega
  conv_rhs => rw [hp, Int.negOnePow_succ, Units.val_neg, neg_neg]

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
    dsimp only [inducedDiff, LinearMap.coe_mk, AddHom.coe_mk]
    refine ⟨?_, by simpa only [add_sub_cancel_right] using hz.1⟩
    simpa only [vadd_eq_add, show (2 : ℤ) + (p - 1) = p + 1 by omega] using
      SetLike.GradedSMul.smul_mem hw hz.2
  · rw [mem_inducedInternalGrading_piece_iff] at hz
    have hdd : ((p.negOnePow : ℤ) * (p.negOnePow : ℤ)) = 1 := by
      rw [← Units.val_mul, ← Int.negOnePow_add, show p + p = 2 * p by ring,
        Int.negOnePow_even _ ⟨p, by ring⟩, Units.val_one]
    ext
    · dsimp only [inducedDiff, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Units.smul_def, InducedCarrier.add_fst, InducedCarrier.zsmul_fst,
        op_smul_inducedCarrier_fst h X, op_smul_inducedCarrier_fst h X,
        smul_inducedCarrier_snd h X, koszulTwist_one_eq_zsmul hz.1,
        koszulTwist_one_eq_zsmul hz.2, negOnePow_sub_one p, neg_smul, smul_neg, sub_neg_eq_add,
        h.sq_eq a, MulOpposite.op_sub, op_mul a w, op_mul w a, sub_smul, mul_smul, mul_smul,
        smul_comm (op (d a) : Aᵐᵒᵖ) (p.negOnePow : ℤ), smul_add, smul_sub]
      simp only [smul_comm (op w : Aᵐᵒᵖ) (p.negOnePow : ℤ),
        smul_comm (op a : Aᵐᵒᵖ) (p.negOnePow : ℤ),
        ← mul_smul (p.negOnePow : ℤ) (p.negOnePow : ℤ), hdd, one_smul]
      abel
    · dsimp only [inducedDiff, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Units.smul_def, InducedCarrier.add_snd, InducedCarrier.zsmul_snd,
        op_smul_inducedCarrier_fst h X, smul_inducedCarrier_snd h X,
        smul_inducedCarrier_snd h X, koszulTwist_one_eq_zsmul hz.2, negOnePow_sub_one p,
        neg_smul, smul_neg, sub_neg_eq_add, smul_comm (op (d a) : Aᵐᵒᵖ) (p.negOnePow : ℤ)]
  · ext
    · dsimp only [inducedDiff, LinearMap.coe_mk, AddHom.coe_mk]
      rw [op_smul_inducedCarrier_fst h X, h.map_curvature, MulOpposite.op_zero, zero_smul,
        sub_zero]
    · rfl

/-- The **induced curved right module** `G⁺(X)` of a graded right `A`-module `X`, with underlying
graded module `X ⊕ X{1}` and differential `⟨x₀, x₁⟩ ↦ ⟨x₁ · w, x₀⟩`. -/
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

/-- Every induced curved right module is contractible via `⟨x₀, x₁⟩ ↦ ⟨x₁, 0⟩`, hence zero in the
curved homotopy category. -/
theorem isZero_homotopy_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (induced h X)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  let k : induced h X →ₗ[Aᵐᵒᵖ] induced h X :=
    { toFun := fun z : InducedCarrier X ↦ (⟨z.snd, 0⟩ : InducedCarrier X)
      map_add' := fun (y : InducedCarrier X) (z : InducedCarrier X) ↦
        InducedCarrier.ext rfl (add_zero 0).symm
      map_smul' := fun s (z : InducedCarrier X) ↦ by
        refine InducedCarrier.ext ?_ (smul_zero s).symm
        -- On `⟨z.snd, 0⟩`, the Koszul-twisted correction term vanishes.
        change s • z.snd = s • z.snd - op (d s.unop) • X.grading.koszulTwist 1 0
        rw [map_zero, smul_zero, sub_zero] }
  refine ⟨⟨k, ?_⟩, fun z : InducedCarrier X ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p (z : InducedCarrier X) hz
    rw [induced_grading, mem_inducedInternalGrading_piece_iff] at hz ⊢
    dsimp only [k, LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact ⟨by simpa only [sub_eq_add_neg] using hz.2, Submodule.zero_mem _⟩
  · refine InducedCarrier.ext ?_ (add_zero z.snd)
    -- `d(k z) + k(d z) = ⟨0, z.snd⟩ + ⟨z.fst, 0⟩` on `InducedCarrier X`.
    change op w • (0 : X) + z.fst = z.fst
    rw [smul_zero, zero_add]

/-! ### The underlying graded extension `0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` -/

/-- The canonical graded inclusion `X ⟶ G⁺(X)` sending `x₀` to `⟨x₀, 0⟩`. -/
noncomputable def inducedι (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    X ⟶ toGradedModuleCat (induced h X) :=
  GradedModuleCat.ofHom
    { toFun := fun x ↦ (⟨x, 0⟩ : InducedCarrier X)
      map_add' := fun x y ↦ InducedCarrier.ext rfl (add_zero 0).symm
      map_smul' := fun s x ↦ by
        refine InducedCarrier.ext ?_ (smul_zero s).symm
        -- On `⟨x, 0⟩`, the Koszul-twisted correction term vanishes so the action is untwisted.
        change s • x = s • x - op (d s.unop) • X.grading.koszulTwist 1 0
        rw [map_zero, smul_zero, sub_zero] }
    (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [toGradedModuleCat_piece, add_zero]
      exact (mem_inducedInternalGrading_piece_iff X p ⟨x, 0⟩).2 ⟨hx, Submodule.zero_mem _⟩)

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

/-- Composing `inducedι h X` with `inducedπ h X` is zero. -/
@[reassoc (attr := simp)]
theorem inducedι_comp_inducedπ (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedι h X ≫ inducedπ h X = 0 :=
  GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The canonical graded inclusion `X ⟶ G⁺(X)` is a monomorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Mono (inducedι h X) :=
  (GradedModuleCat.mono_iff_injective _).2 fun _ _ hxy ↦
    congrArg InducedCarrier.fst (show (_ : InducedCarrier X) = _ from hxy)

/-- The canonical graded projection `G⁺(X) ⟶ X{1}` is an epimorphism. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Epi (inducedπ h X) :=
  (GradedModuleCat.epi_iff_surjective _).2 fun x₁ ↦ ⟨(⟨0, x₁⟩ : InducedCarrier X), rfl⟩

/-- After forgetting the differential, `G⁺(X)` sits in a short exact sequence
`0 ⟶ X ⟶ G⁺(X) ⟶ X{1} ⟶ 0` of graded right modules. -/
theorem inducedShortComplex_shortExact (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (inducedι h X) (inducedπ h X) (inducedι_comp_inducedπ h X)).ShortExact where
  mono_f := inferInstance
  epi_g := inferInstance
  exact := GradedModuleCat.exact_iff.2 fun z : InducedCarrier X ↦
    ⟨fun hz ↦ ⟨z.fst, InducedCarrier.ext rfl hz.symm⟩, by rintro ⟨x, rfl⟩; rfl⟩

/-- If `X` is a projective graded right module, then `G⁺(X)` is graded-projective. -/
theorem projective_toGradedModuleCat_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective X] :
    Projective (toGradedModuleCat (induced h X)) := by
  have : Projective (X.shiftObj 1) := GradedModuleCat.projective_shiftObj X 1
  exact projective_iff_hasProjectiveDimensionLT_one.2
    ((inducedShortComplex_shortExact h X).hasProjectiveDimensionLT_X₂ 1
      (projective_iff_hasProjectiveDimensionLT_one.1 ‹_›)
      (projective_iff_hasProjectiveDimensionLT_one.1 ‹_›))

/-- If `X` is an injective graded right module, then `G⁺(X)` is graded-injective. -/
theorem injective_toGradedModuleCat_induced (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective X] :
    Injective (toGradedModuleCat (induced h X)) := by
  have : Injective (X.shiftObj 1) := GradedModuleCat.injective_shiftObj X 1
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((inducedShortComplex_shortExact h X).hasInjectiveDimensionLT_X₂ 1
      (injective_iff_hasInjectiveDimensionLT_one.1 ‹_›)
      (injective_iff_hasInjectiveDimensionLT_one.1 ‹_›))

end Construction

/-! ### Left adjunction `G⁺ ⊣ forgetDifferential` -/

section InducedAdjunction

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private theorem map_differential_op_smul {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (fM : X →ₗ[Aᵐᵒᵖ] M) (hfM : ∀ p x, x ∈ X.grading.piece p → fM x ∈ M.grading p)
    (a : A) (x₁ : X) :
    M.differential (fM (op a • x₁)) =
      op a • M.differential (fM x₁) + op (d a) • fM (X.grading.koszulTwist 1 x₁) := by
  induction x₁ using DirectSum.Decomposition.inductionOn X.grading.piece with
  | zero => simp only [smul_zero, map_zero, add_zero]
  | homogeneous hx₁ =>
    rw [fM.map_smul, M.isCurvedDGRightModule.leibniz (hfM _ _ hx₁.2) a, Units.smul_def,
      koszulTwist_one_eq_zsmul hx₁.2, map_zsmul, smul_comm (op (d a) : Aᵐᵒᵖ) (Int.negOnePow _ : ℤ)]
  | add y₁ y₂ ih₁ ih₂ =>
    simp only [smul_add, map_add, ih₁, ih₂]
    abel

/-- Transpose a graded morphism `X ⟶ M` to a closed morphism `G⁺(X) ⟶ M` via
`⟨x₀, x₁⟩ ↦ f(x₀) + d_M(f(x₁))`. -/
noncomputable def inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  let fM : X →ₗ[Aᵐᵒᵖ] M := f.hom
  have hfM (p : ℤ) (x : X) (hx : x ∈ X.grading.piece p) : fM x ∈ M.grading p := by
    simpa only [toGradedModuleCat_piece] using GradedModuleCat.map_mem f hx
  closedHomOf (M := induced h X) (N := M)
    { toFun := fun z : InducedCarrier X ↦ fM z.fst + M.differential (fM z.snd)
      map_add' := fun (y : InducedCarrier X) (z : InducedCarrier X) ↦ by
        rw [InducedCarrier.add_fst, InducedCarrier.add_snd, fM.map_add, fM.map_add,
          M.differential.map_add]
        abel
      map_smul' := fun s (z : InducedCarrier X) ↦ by
        dsimp only [RingHom.id_apply]
        -- Rewrite `s = op s.unop` so the twisted action formula applies on the first coordinate.
        conv_lhs => rw [← op_unop s]
        rw [op_smul_inducedCarrier_fst h X, smul_inducedCarrier_snd h X, map_sub, fM.map_smul,
          fM.map_smul, map_differential_op_smul fM hfM s.unop z.snd, op_unop, smul_add]
        abel }
    (fun p (z : InducedCarrier X) hz ↦ by
      obtain ⟨hz₀, hz₁⟩ := (mem_inducedInternalGrading_piece_iff X p z).1 hz
      exact Submodule.add_mem _ (hfM p z.fst hz₀) (by
        simpa only [sub_add_cancel] using
          M.isCurvedDGRightModule.isHomogeneous.map_mem (hfM (p - 1) z.snd hz₁)))
    (fun z : InducedCarrier X ↦ by
      dsimp only [induced, CurvedDGRightModuleCat.of, inducedDiff, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_add, M.isCurvedDGRightModule.sq_eq, fM.map_smul, add_comm])

private theorem closedHom_inducedDesc_apply {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) (z : InducedCarrier X) :
    closedHom (inducedDesc f) z =
      (show M.carrier from f.hom z.fst) + M.differential (f.hom z.snd) := by
  dsimp only [inducedDesc]
  rw [closedHom_closedHomOf]
  rfl

/-- Precomposing `inducedDesc f` with `inducedι h X` recovers `f`. -/
@[simp]
theorem inducedι_comp_forgetDifferential_inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) :
    inducedι h X ≫ (forgetDifferential (h := h)).map (inducedDesc f) = f := by
  ext x
  -- Both sides evaluate `closedHom (inducedDesc f)` at `⟨x, 0⟩`.
  change closedHom (inducedDesc f) (⟨x, 0⟩ : InducedCarrier X) = (show M.carrier from f.hom x)
  rw [closedHom_inducedDesc_apply, map_zero, map_zero, add_zero]

/-- Every closed morphism `G⁺(X) ⟶ M` is uniquely `inducedDesc` of its restriction along
`inducedι h X`. -/
theorem inducedDesc_unique {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    inducedDesc (inducedι h X ≫ (forgetDifferential (h := h)).map φ) = φ := by
  ext (z : InducedCarrier X)
  rw [closedHom_inducedDesc_apply]
  let z₀ : (induced h X).carrier := (⟨z.fst, 0⟩ : InducedCarrier X)
  let z₁ : (induced h X).carrier := (⟨z.snd, 0⟩ : InducedCarrier X)
  have hz : (z : (induced h X).carrier) = z₀ + (induced h X).differential z₁ := by
    refine InducedCarrier.ext ?_ (zero_add z.snd).symm
    -- On `z₁ = ⟨z.snd, 0⟩`, the first coordinate of `d z₁` is `op w • 0`.
    change z.fst = z.fst + op w • (0 : X)
    rw [smul_zero, add_zero]
  conv_rhs => rw [hz]
  rw [map_add, ← differential_closedHom φ]
  rfl

/-- An epimorphism `X ↠ M` of graded right modules transposes to an epimorphism `G⁺(X) ↠ M` of
curved right modules. -/
theorem epi_inducedDesc {M : CurvedDGRightModuleCat.{u, u, u} h}
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : X ⟶ toGradedModuleCat M) [Epi f] : Epi (inducedDesc f) := by
  have : Epi (inducedι h X ≫ (forgetDifferential (h := h)).map (inducedDesc f)) := by
    rw [inducedι_comp_forgetDifferential_inducedDesc]
    infer_instance
  have hmap : Epi ((forgetDifferential (h := h)).map (inducedDesc f)) :=
    epi_of_epi (inducedι h X) ((forgetDifferential (h := h)).map (inducedDesc f))
  exact (forgetDifferential (h := h)).epi_of_epi_map hmap

variable (h) in
/-- The **induced curved-module functor** `G⁺`, left adjoint to `forgetDifferential`. -/
@[expose, implicit_reducible]
noncomputable def inducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj X := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X)
  map {X Y} u := inducedDesc (u ≫ inducedι h Y)
  map_id X := by
    refine Eq.trans ?_
      (inducedDesc_unique (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X))))
    congr 1
    rw [Category.id_comp, (forgetDifferential (h := h)).map_id
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X))]
    ext
    rfl
  map_comp {X Y Z} u v := by
    refine Eq.trans ?_
      (inducedDesc_unique (inducedDesc (u ≫ inducedι h Y) ≫ inducedDesc (v ≫ inducedι h Z)))
    congr 1
    rw [Functor.map_comp, ← Category.assoc, inducedι_comp_forgetDifferential_inducedDesc,
      Category.assoc, Category.assoc, inducedι_comp_forgetDifferential_inducedDesc]

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
    (inducedFunctor h).map u = inducedDesc (u ≫ inducedι h Y) :=
  (rfl)

variable (h) in
/-- The adjunction `inducedFunctor h ⊣ forgetDifferential`. -/
noncomputable def inducedAdj : inducedFunctor h ⊣ forgetDifferential (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M ↦
        { toFun := fun φ ↦ inducedι h X ≫ (forgetDifferential (h := h)).map φ
          invFun := fun f ↦ inducedDesc (M := ForgetEnrichment.to _ M) f
          left_inv := fun φ ↦ inducedDesc_unique (M := ForgetEnrichment.to _ M) φ
          right_inv := fun f ↦
            inducedι_comp_forgetDifferential_inducedDesc (M := ForgetEnrichment.to _ M) f }
      homEquiv_naturality_left_symm := fun {X' X M} u f ↦ by
        dsimp only [Equiv.coe_fn_symm_mk]
        refine Eq.trans ?_ (inducedDesc_unique (M := ForgetEnrichment.to _ M)
          ((inducedFunctor h).map u ≫ inducedDesc (M := ForgetEnrichment.to _ M) f))
        congr 1
        rw [Functor.map_comp, ← Category.assoc]
        dsimp only [inducedFunctor]
        rw [inducedι_comp_forgetDifferential_inducedDesc, Category.assoc,
          inducedι_comp_forgetDifferential_inducedDesc]
      homEquiv_naturality_right := fun {X M M'} φ ψ ↦ by
        -- Precomposition with `inducedι h X` associates with functoriality of `forgetDifferential`.
        change inducedι h X ≫ (forgetDifferential (h := h)).map (φ ≫ ψ) =
          (inducedι h X ≫ (forgetDifferential (h := h)).map φ) ≫
            (forgetDifferential (h := h)).map ψ
        rw [Functor.map_comp, Category.assoc] }

/-- The forward hom-equivalence of `inducedAdj h` precomposes with `inducedι`. -/
@[simp]
theorem inducedAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (φ : (inducedFunctor h).obj X ⟶ ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    (inducedAdj h).homEquiv X (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) φ =
      inducedι h X ≫ (forgetDifferential (h := h)).map φ := by
  delta inducedAdj
  rw [Adjunction.mkOfHomEquiv_homEquiv]
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
  delta inducedAdj
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of `inducedAdj h` at `X` is `inducedι h X`. -/
@[simp]
theorem inducedAdj_unit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (X : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedAdj h).unit.app X = inducedι h X := by
  delta inducedAdj
  rw [Adjunction.mkOfHomEquiv_unit_app]
  dsimp only [Equiv.coe_fn_mk]
  rw [(forgetDifferential (h := h)).map_id ((inducedFunctor h).obj X)]
  ext
  rfl

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

/-- Every coinduced curved right module vanishes in the curved homotopy category. -/
theorem isZero_homotopy_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinduced h Y)) :=
  isZero_homotopy_induced h (Y.shiftObj (-1))

/-- If `Y` is a projective graded right module, then `G⁻(Y)` is graded-projective. -/
theorem projective_toGradedModuleCat_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective Y] :
    Projective (toGradedModuleCat (coinduced h Y)) := by
  have : Projective (Y.shiftObj (-1)) := GradedModuleCat.projective_shiftObj Y (-1)
  exact projective_toGradedModuleCat_induced h (Y.shiftObj (-1))

/-- If `Y` is an injective graded right module, then `G⁻(Y)` is graded-injective. -/
theorem injective_toGradedModuleCat_coinduced (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective Y] :
    Injective (toGradedModuleCat (coinduced h Y)) := by
  have : Injective (Y.shiftObj (-1)) := GradedModuleCat.injective_shiftObj Y (-1)
  exact injective_toGradedModuleCat_induced h (Y.shiftObj (-1))

/-- The canonical graded counit `G⁻(Y) ⟶ Y` projecting `⟨y₁, y₀⟩` onto `y₀`. -/
noncomputable def coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinduced h Y) ⟶ Y :=
  GradedModuleCat.ofHom
    { toFun := fun z : InducedCarrier Y ↦ z.snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (LinearMap.isHomogeneous_def.2 fun p (z : InducedCarrier Y) hz ↦ by
      rw [toGradedModuleCat_piece] at hz
      have hz₁ := ((mem_inducedInternalGrading_piece_iff (Y.shiftObj (-1)) p z).1 hz).2
      rw [Y.mem_shiftObj_piece_iff (-1) (p - 1), show p - 1 - -1 = p + 0 by omega] at hz₁
      exact hz₁)

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private theorem map_differential_op_smul_coinduced {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (a : A) (m : M) :
    let gM : M →ₗ[Aᵐᵒᵖ] Y := g.hom
    gM (M.differential (op a • m)) =
      op a • gM (M.differential m) -
        op (d a) • (Y.shiftObj (-1)).grading.koszulTwist 1 (gM m) := by
  intro gM
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp only [smul_zero, map_zero, sub_zero]
  | homogeneous hm =>
    have hgm : gM hm.1 ∈ (Y.shiftObj (-1)).grading.piece (‹_› - 1) := by
      rw [Y.mem_shiftObj_piece_iff (-1) (_ - 1)]
      simpa only [show ‹_› - 1 - -1 = ‹_› by omega] using
        GradedModuleCat.map_mem g (by simpa only [toGradedModuleCat_piece] using hm.2)
    rw [M.isCurvedDGRightModule.leibniz hm.2 a, Units.smul_def, map_add, gM.map_smul,
      map_zsmul, gM.map_smul, koszulTwist_one_eq_zsmul hgm, negOnePow_sub_one, neg_smul,
      smul_neg, sub_neg_eq_add, smul_comm (op (d a) : Aᵐᵒᵖ) (Int.negOnePow _ : ℤ)]
  | add m₁ m₂ ih₁ ih₂ =>
    simp only [smul_add, map_add, ih₁, ih₂]
    abel

private noncomputable def coinducedLiftLinearMap {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) : M →ₗ[Aᵐᵒᵖ] coinduced h Y :=
  let gM : M →ₗ[Aᵐᵒᵖ] Y := g.hom
  { toFun := fun m ↦ (⟨gM (M.differential m), gM m⟩ : InducedCarrier Y)
    map_add' := fun m₁ m₂ ↦
      InducedCarrier.ext
        (by rw [M.differential.map_add, gM.map_add]; rfl)
        (gM.map_add m₁ m₂)
    map_smul' := fun s m ↦ by
      refine InducedCarrier.ext ?_ (gM.map_smul s m)
      dsimp only [RingHom.id_apply]
      -- Rewrite `s = op s.unop` so the twisted action formula matches the Leibniz sign.
      conv_lhs => rw [← op_unop s]
      conv_rhs => rw [← op_unop s]
      rw [op_smul_inducedCarrier_fst h (Y.shiftObj (-1))]
      exact map_differential_op_smul_coinduced g s.unop m }

@[simp]
private theorem coinducedLiftLinearMap_fst {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    (coinducedLiftLinearMap g m : InducedCarrier Y).fst =
      (g.hom : M →ₗ[Aᵐᵒᵖ] Y) (M.differential m) :=
  rfl

@[simp]
private theorem coinducedLiftLinearMap_snd {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    (coinducedLiftLinearMap g m : InducedCarrier Y).snd = (g.hom : M →ₗ[Aᵐᵒᵖ] Y) m :=
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
      refine (mem_inducedInternalGrading_piece_iff (Y.shiftObj (-1)) p _).2 ⟨?_, ?_⟩
      · rw [coinducedLiftLinearMap_fst, Y.mem_shiftObj_piece_iff (-1) p, sub_neg_eq_add]
        exact GradedModuleCat.map_mem g (by
          simpa only [toGradedModuleCat_piece] using
            M.isCurvedDGRightModule.isHomogeneous.map_mem hm)
      · rw [coinducedLiftLinearMap_snd, Y.mem_shiftObj_piece_iff (-1) (p - 1)]
        simpa only [show p - 1 - -1 = p by omega] using
          GradedModuleCat.map_mem g (by simpa only [toGradedModuleCat_piece] using hm))
    (fun m ↦ by
      refine InducedCarrier.ext ?_ rfl
      -- The first coordinate of `d_{G⁻} ⟨g(d m), g(m)⟩` is `g(m) · w = g(d(d m))`.
      change op w • (coinducedLiftLinearMap g m : InducedCarrier Y).snd =
        (coinducedLiftLinearMap g (M.differential m) : InducedCarrier Y).fst
      rw [coinducedLiftLinearMap_fst, coinducedLiftLinearMap_snd,
        M.isCurvedDGRightModule.sq_eq, LinearMap.map_smul])

private theorem closedHom_coinducedLift_apply {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) (m : M) :
    (closedHom (coinducedLift g) m : InducedCarrier Y) =
      ⟨g.hom (M.differential m), g.hom m⟩ := by
  dsimp only [coinducedLift]
  rw [closedHom_closedHomOf]
  rfl

/-- Postcomposing `coinducedLift g` with `coinducedCounit h Y` recovers `g`. -/
@[simp]
theorem forgetDifferential_coinducedLift_comp_coinducedCounit
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) :
    (forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y = g := by
  ext m
  -- Evaluating `coinducedCounit` projects onto the second coordinate of `coinducedLift g`.
  change (closedHom (coinducedLift g) m : InducedCarrier Y).snd = g.hom m
  rw [closedHom_coinducedLift_apply]

/-- Every closed morphism `M ⟶ G⁻(Y)` is uniquely `coinducedLift` of its counit composite. -/
theorem coinducedLift_unique {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y)) :
    coinducedLift ((forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y) = φ := by
  ext m
  refine InducedCarrier.ext ?_ ?_
  · rw [closedHom_coinducedLift_apply]
    exact (congrArg InducedCarrier.snd
      (show (closedHom φ (M.differential m) : InducedCarrier Y) = _ from
        (differential_closedHom φ m).symm))
  · rw [closedHom_coinducedLift_apply]
    rfl

/-- A monomorphism `M ↪ Y` of graded right modules transposes to a monomorphism `M ↪ G⁻(Y)` of
curved right modules. -/
theorem mono_coinducedLift {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) [Mono g] : Mono (coinducedLift g) := by
  have : Mono ((forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h Y) := by
    rw [forgetDifferential_coinducedLift_comp_coinducedCounit]
    infer_instance
  have hmap : Mono ((forgetDifferential (h := h)).map (coinducedLift g)) :=
    mono_of_mono ((forgetDifferential (h := h)).map (coinducedLift g)) (coinducedCounit h Y)
  exact (forgetDifferential (h := h)).mono_of_mono_map hmap

variable (h) in
/-- The **coinduced curved-module functor** `G⁻`, right adjoint to `forgetDifferential`. -/
@[expose, implicit_reducible]
noncomputable def coinducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj Y := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y)
  map {Y Z} v := coinducedLift (coinducedCounit h Y ≫ v)
  map_id Y := by
    refine Eq.trans ?_ (coinducedLift_unique (M := coinduced h Y)
      (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y))))
    congr 1
    rw [Category.comp_id, (forgetDifferential (h := h)).map_id
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y))]
    ext
    rfl
  map_comp {X Y Z} u v := by
    refine Eq.trans ?_ (coinducedLift_unique (M := coinduced h X)
      (coinducedLift (coinducedCounit h X ≫ u) ≫
        coinducedLift (coinducedCounit h Y ≫ v)))
    congr 1
    rw [Functor.map_comp, Category.assoc, forgetDifferential_coinducedLift_comp_coinducedCounit,
      ← Category.assoc ((forgetDifferential (h := h)).map _),
      forgetDifferential_coinducedLift_comp_coinducedCounit, Category.assoc]

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
    (coinducedFunctor h).map v = coinducedLift (coinducedCounit h Y ≫ v) :=
  (rfl)

variable (h) in
/-- The adjunction `forgetDifferential ⊣ coinducedFunctor h`. -/
noncomputable def coinducedAdj : forgetDifferential (h := h) ⊣ coinducedFunctor h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M Y ↦
        { toFun := fun g ↦ coinducedLift (M := ForgetEnrichment.to _ M) g
          invFun := fun φ ↦ (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y
          left_inv := fun g ↦
            forgetDifferential_coinducedLift_comp_coinducedCounit (M := ForgetEnrichment.to _ M) g
          right_inv := fun φ ↦ coinducedLift_unique (M := ForgetEnrichment.to _ M) φ }
      homEquiv_naturality_left_symm := fun {M' M Y} ψ φ ↦ by
        -- Both sides precompose `φ` with `(forgetDifferential (h := h)).map ψ`.
        change (forgetDifferential (h := h)).map (ψ ≫ φ) ≫ coinducedCounit h Y =
          (forgetDifferential (h := h)).map ψ ≫
            (forgetDifferential (h := h)).map φ ≫ coinducedCounit h Y
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {M Y Y'} g v ↦ by
        dsimp only [Equiv.coe_fn_mk]
        refine Eq.trans ?_ (coinducedLift_unique (M := ForgetEnrichment.to _ M)
          (coinducedLift (M := ForgetEnrichment.to _ M) g ≫
            (coinducedFunctor h).map v))
        congr 1
        rw [Functor.map_comp, Category.assoc]
        dsimp only [coinducedFunctor]
        rw [forgetDifferential_coinducedLift_comp_coinducedCounit,
          ← Category.assoc, forgetDifferential_coinducedLift_comp_coinducedCounit] }

/-- The forward hom-equivalence of `coinducedAdj h` is `coinducedLift`. -/
@[simp]
theorem coinducedAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ Y) :
    (coinducedAdj h).homEquiv
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) Y g =
      coinducedLift g := by
  delta coinducedAdj
  rw [Adjunction.mkOfHomEquiv_homEquiv]
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
  delta coinducedAdj
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The counit of `coinducedAdj h` at `Y` is `coinducedCounit h Y`. -/
@[simp]
theorem coinducedAdj_counit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (Y : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedAdj h).counit.app Y = coinducedCounit h Y := by
  delta coinducedAdj
  rw [Adjunction.mkOfHomEquiv_counit_app]
  dsimp only [Equiv.coe_fn_symm_mk]
  rw [(forgetDifferential (h := h)).map_id ((coinducedFunctor h).obj Y)]
  ext
  rfl

end CoinducedAdjunction

end TauCeti.CurvedDGRightModuleCat
