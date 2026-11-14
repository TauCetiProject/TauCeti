/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective
import Mathlib.CategoryTheory.Functor.EpiMono
import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# Induced curved right modules from graded right modules

To every graded right module $N$ over a curved differential graded algebra $(A, d, w)$, Positselski
associates an induced curved right module $G^+ N$. Over the ground ring its underlying module is
$N \oplus N$, graded with degree-$p$ piece $N_p \oplus N_{p - 1}$. Its twisted right $A$-action is
$$(x, y) \cdot a = (x \cdot a - (-1)^{|y|} y \cdot d a,\ y \cdot a),$$
and its curved differential is $D_+(x, y) = (y \cdot w, x)$. The graded Leibniz rule and
$d(1) = 0$ make the twisted action unital and associative, while the commutator curvature identity
$d^2 a = a w - w a$ and cycle identity $d w = 0$ yield the graded Leibniz rule and curvature
equation $D_+^2(x, y) = (x, y) \cdot w$.

Induction is left adjoint to forgetting the differential from curved right modules with closed
degree-zero morphisms to graded right modules, via $(x, y) \mapsto f(x) + d_M(f(y))$. Every $G^+ N$
is contractible in the curved homotopy category via $(x, y) \mapsto (y, 0)$ and sits in a graded
short exact sequence $0 \to N \to G^+ N \to N\{1\} \to 0$. Consequently $G^+ P$ is
graded-projective when $P$ is projective, giving closed projective covers.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.inducedObj` and `TauCeti.CurvedDGRightModuleCat.inducedEquiv`:
  the induced curved right module $G^+ N$ and its carrier equivalence with $N \times N$.
* `TauCeti.CurvedDGRightModuleCat.inducedInl`, `TauCeti.CurvedDGRightModuleCat.inducedSnd`: the
  graded inclusion $N \longrightarrow G^+ N$ and projection $G^+ N \longrightarrow N\{1\}$.
* `TauCeti.CurvedDGRightModuleCat.induced`, `TauCeti.CurvedDGRightModuleCat.inducedDesc`, and
  `TauCeti.CurvedDGRightModuleCat.inducedForgetDifferentialAdj`: the left-adjoint functor, adjunct
  closed morphism, and adjunction with forgetting the differential.

## Main results

* `TauCeti.CurvedDGRightModuleCat.shortExact_inducedInl_inducedSnd`: the graded short exact sequence
  $0 \longrightarrow N \longrightarrow G^+ N \longrightarrow N\{1\} \longrightarrow 0$.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.exists_epi_from_inducedObj_projective`: contractibility of $G^+ N$
  and closed epimorphisms from contractible graded-projective curved modules.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Lemma 7.7.
-/

public section

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uN u

section InducedObj

open MulOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Private wrapper around `N × N` carrying the twisted right `A`-module structure of `G⁺ N`
without colliding with the componentwise product `Aᵐᵒᵖ`-action on `N × N`. -/
@[ext]
private structure InducedCarrier (d : A →ₗ[R] A) (N : Type uN) where
  val : N × N

namespace InducedCarrier

section ModuleBase

variable {N : Type uN} [AddCommGroup N]

private instance : Zero (InducedCarrier d N) := ⟨⟨0⟩⟩
private instance : Add (InducedCarrier d N) := ⟨fun z₁ z₂ ↦ ⟨z₁.val + z₂.val⟩⟩
private instance : Neg (InducedCarrier d N) := ⟨fun z ↦ ⟨-z.val⟩⟩
private instance : Sub (InducedCarrier d N) := ⟨fun z₁ z₂ ↦ ⟨z₁.val - z₂.val⟩⟩
private instance : SMul ℕ (InducedCarrier d N) := ⟨fun n z ↦ ⟨n • z.val⟩⟩
private instance : SMul ℤ (InducedCarrier d N) := ⟨fun n z ↦ ⟨n • z.val⟩⟩

@[simp] private theorem val_zero : (0 : InducedCarrier d N).val = 0 := rfl
@[simp] private theorem val_add (z₁ z₂ : InducedCarrier d N) :
    (z₁ + z₂).val = z₁.val + z₂.val := rfl
@[simp] private theorem val_zsmul (n : ℤ) (z : InducedCarrier d N) :
    (n • z).val = n • z.val := rfl

private instance : AddCommGroup (InducedCarrier d N) :=
  Function.Injective.addCommGroup val (fun _ _ ↦ InducedCarrier.ext)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

variable [Module R N]

private instance : SMul R (InducedCarrier d N) := ⟨fun r z ↦ ⟨r • z.val⟩⟩
@[simp] private theorem val_smul (r : R) (z : InducedCarrier d N) : (r • z).val = r • z.val := rfl

private instance : Module R (InducedCarrier d N) :=
  Function.Injective.module R ⟨⟨val, rfl⟩, fun _ _ ↦ rfl⟩ (fun _ _ ↦ InducedCarrier.ext)
    fun _ _ ↦ rfl

private def valEquiv : InducedCarrier d N ≃ₗ[R] N × N :=
  { toFun := val, invFun := mk, left_inv _ := rfl, right_inv _ := rfl,
    map_add' _ _ := rfl, map_smul' _ _ := rfl }

@[simp] private theorem valEquiv_apply (z : InducedCarrier d N) : valEquiv (d := d) z = z.val := rfl

end ModuleBase

section TwistedAction

private noncomputable abbrev OppPiece (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :=
  (InternalGrading.ofDecomposition 𝒜).opposite.piece

private noncomputable instance (N : GradedModuleCat.{uN} (OppPiece 𝒜)) :
    SMul Aᵐᵒᵖ (InducedCarrier d N) where
  smul a z := ⟨(a • z.val.1 - op (d a.unop) • N.grading.koszulTwist 1 z.val.2, a • z.val.2)⟩

@[simp]
private theorem val_smul_op (N : GradedModuleCat.{uN} (OppPiece 𝒜)) (a : Aᵐᵒᵖ)
    (z : InducedCarrier d N) :
    (a • z).val = (a • z.val.1 - op (d a.unop) • N.grading.koszulTwist 1 z.val.2, a • z.val.2) :=
  rfl

private theorem op_mul_twist_eq (N : GradedModuleCat.{uN} (OppPiece 𝒜))
    (h : IsCurvedDGAlgebra 𝒜 d w) (a b : A) (y : N) :
    op b • (op (d a) • N.grading.koszulTwist 1 y) + op (d b) • N.grading.koszulTwist 1 (op a • y) =
      op (d (a * b)) • N.grading.koszulTwist 1 y := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous r a =>
    rcases a with ⟨a, ha⟩
    induction y using DirectSum.Decomposition.inductionOn N.grading.piece with
    | zero => simp
    | @homogeneous q y =>
      rcases y with ⟨y, hy⟩
      have hay : op a • y ∈ N.grading.piece (q + r) := op_smul_mem_of_mem_graded ha hy
      rw [N.grading.koszulTwist_one_apply_of_mem hy, N.grading.koszulTwist_one_apply_of_mem hay,
        h.leibniz ha b, Int.negOnePow_add]
      simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _)]
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
        rcases Int.units_eq_one_or r.negOnePow with hr | hr <;>
        simp [hq, hr, MulOpposite.op_add, MulOpposite.op_mul, add_smul, smul_add, mul_smul]
    | add _ _ hy₁ hy₂ => simp only [smul_add, map_add, ← hy₁, ← hy₂]; abel
  | add _ _ ha₁ ha₂ =>
    simp only [map_add, MulOpposite.op_add, add_mul, add_smul, smul_add, ← ha₁, ← ha₂]; abel

@[instance_reducible]
private noncomputable def moduleOp (N : GradedModuleCat.{uN} (OppPiece 𝒜))
    (h : IsCurvedDGAlgebra 𝒜 d w) : Module Aᵐᵒᵖ (InducedCarrier d N) where
  one_smul z := InducedCarrier.ext <|
    Prod.ext (by simp [val_smul_op, h.map_one_eq_zero]) (one_smul Aᵐᵒᵖ z.val.2)
  mul_smul b a z := by
    ext
    · simp only [val_smul_op, unop_mul, smul_sub]
      have ht := op_mul_twist_eq N h a.unop b.unop z.val.2
      simp only [op_unop] at ht; rw [mul_smul b a z.val.1, ← ht]; abel
    · exact mul_smul b a z.val.2
  smul_zero _ := by ext <;> simp [val_smul_op]
  smul_add a z₁ z₂ := by
    ext
    · simp only [val_smul_op, val_add, Prod.fst_add, Prod.snd_add, map_add, smul_add]; abel
    · exact smul_add a z₁.val.2 z₂.val.2
  add_smul a b z := by
    ext
    · simp only [val_smul_op, val_add, Prod.fst_add, unop_add, map_add, op_add, add_smul]; abel
    · exact add_smul a b z.val.2
  zero_smul _ := by ext <;> simp [val_smul_op]

private theorem scalarTower (N : GradedModuleCat.{uN} (OppPiece 𝒜)) (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h; IsScalarTower R Aᵐᵒᵖ (InducedCarrier d N) := by
  let := moduleOp N h; refine ⟨fun r a z ↦ ?_⟩; ext
  · simp only [val_smul_op, val_smul, Prod.smul_fst, unop_smul, d.map_smul, op_smul, smul_assoc,
      smul_sub]
  · exact smul_assoc r a z.val.2

private noncomputable def grading (N : GradedModuleCat.{uN} (OppPiece 𝒜)) :
    InternalGrading R (InducedCarrier d N) ℤ :=
  (N.grading.prod (N.shiftObj 1).grading).map (valEquiv (d := d)).symm

private theorem mem_grading_piece_iff (N : GradedModuleCat.{uN} (OppPiece 𝒜))
    {p : ℤ} {z : InducedCarrier d N} :
    z ∈ (grading (d := d) N).piece p ↔
      z.val.1 ∈ N.grading.piece p ∧ z.val.2 ∈ N.grading.piece (p - 1) := by
  rw [grading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm, valEquiv_apply,
    InternalGrading.prod_piece, Submodule.mem_prod, GradedModuleCat.mem_shiftObj_piece_iff]

private theorem gradedSMul (N : GradedModuleCat.{uN} (OppPiece 𝒜)) (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h; SetLike.GradedSMul (OppPiece 𝒜) (grading (d := d) N).piece := by
  let := moduleOp N h; refine ⟨fun {r p} a z ha hz ↦ ?_⟩
  have ha' : a.unop ∈ 𝒜 r := by
    rwa [← op_unop a, InternalGrading.op_mem_opposite_piece_iff,
      InternalGrading.ofDecomposition_piece] at ha
  rw [mem_grading_piece_iff] at hz ⊢
  rw [vadd_eq_add, add_comm r p, val_smul_op]; dsimp only; rw [← op_unop a]
  refine ⟨Submodule.sub_mem _ (op_smul_mem_of_mem_graded ha' hz.1) ?_, ?_⟩
  · simpa [show p - 1 + (r + 1) = p + r by omega] using
      op_smul_mem_of_mem_graded (h.map_mem ha') (N.grading.koszulTwist_mem_piece hz.2 1)
  · simpa [show p - 1 + r = p + r - 1 by omega] using op_smul_mem_of_mem_graded ha' hz.2

private noncomputable def differential (N : GradedModuleCat.{uN} (OppPiece 𝒜)) (w : A) :
    InducedCarrier d N →ₗ[R] InducedCarrier d N where
  toFun z := ⟨(op w • z.val.2, z.val.1)⟩
  map_add' z₁ z₂ := InducedCarrier.ext <| Prod.ext (smul_add (op w) z₁.val.2 z₂.val.2) rfl
  map_smul' r z := InducedCarrier.ext <| Prod.ext (smul_comm (op w) r z.val.2) rfl

@[simp]
private theorem val_differential (N : GradedModuleCat.{uN} (OppPiece 𝒜)) (w : A)
    (z : InducedCarrier d N) : (differential (d := d) N w z).val = (op w • z.val.2, z.val.1) := rfl

private theorem isCurvedDGRightModule (N : GradedModuleCat.{uN} (OppPiece 𝒜))
    (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h; letI := scalarTower N h; letI := gradedSMul N h
    IsCurvedDGRightModule h (grading (d := d) N).piece (differential (d := d) N w) := by
  let := moduleOp N h; let := scalarTower N h; let := gradedSMul N h
  refine ⟨LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_, fun {p z} hz a ↦ ?_, fun z ↦ ?_⟩
  · rw [mem_grading_piece_iff] at hz ⊢; rw [val_differential]
    exact ⟨by simpa [show p - 1 + 2 = p + 1 by omega] using
        op_smul_mem_of_mem_graded h.curvature_mem hz.2,
      by simpa [add_sub_cancel_right] using hz.1⟩
  · rw [mem_grading_piece_iff] at hz; ext
    · simp only [val_differential, val_smul_op, val_add, val_zsmul, Prod.fst_add, Prod.smul_fst,
        unop_op, N.grading.koszulTwist_one_apply_of_mem hz.1,
        N.grading.koszulTwist_one_apply_of_mem hz.2, h.sq_eq a, Int.negOnePow_sub,
        Int.negOnePow_one, Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _), Units.val_neg,
        mul_neg, mul_one]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simp [hp, op_sub, op_mul, sub_smul, mul_smul]
    · simp only [val_differential, val_smul_op, val_add, val_zsmul, Prod.snd_add, Prod.smul_snd,
        N.grading.koszulTwist_one_apply_of_mem hz.2, Int.negOnePow_sub, Int.negOnePow_one,
        Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _), Units.val_neg, mul_neg, mul_one]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp, sub_eq_add_neg]
  · exact InducedCarrier.ext <|
      Prod.ext (by simp [val_differential, val_smul_op, h.map_curvature]) rfl

end TwistedAction

end InducedCarrier

/-- The **induced curved right module** `G⁺ N` associated to a graded right module `N`. Over `R`
its carrier is `N × N` with degree-`p` piece `N_p × N_{p - 1}`, twisted right action
`(x, y) · a = (x · a - (-1)^{|y|} y · d a, y · a)`, and differential `(x, y) ↦ (y · w, x)`. -/
noncomputable def inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uN} h where
  carrier := InducedCarrier d N
  moduleOp := InducedCarrier.moduleOp N h
  scalarTower := InducedCarrier.scalarTower N h
  grading := (InducedCarrier.grading (d := d) N).piece
  gradedSMul := InducedCarrier.gradedSMul N h
  differential := InducedCarrier.differential (d := d) N w
  isCurvedDGRightModule := InducedCarrier.isCurvedDGRightModule N h

/-- The `R`-linear equivalence identifying the carrier of `inducedObj h N` with `N × N`. -/
noncomputable def inducedEquiv (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedObj h N ≃ₗ[R] N × N := by unfold inducedObj; exact InducedCarrier.valEquiv (d := d)

/-- Elements of `inducedObj h N` are determined by their two components in `N × N`. -/
@[ext]
theorem inducedObj_ext {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {z₁ z₂ : inducedObj h N} (h₁ : (inducedEquiv h N z₁).1 = (inducedEquiv h N z₂).1)
    (h₂ : (inducedEquiv h N z₁).2 = (inducedEquiv h N z₂).2) : z₁ = z₂ :=
  (inducedEquiv h N).injective (Prod.ext h₁ h₂)

/-- An element of `inducedObj h N` has degree `p` iff its components lie in `N_p` and `N_{p - 1}`.
-/
@[simp]
theorem mem_inducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : inducedObj h N} :
    z ∈ (inducedObj h N).grading p ↔ (inducedEquiv h N z).1 ∈ N.grading.piece p ∧
      (inducedEquiv h N z).2 ∈ N.grading.piece (p - 1) := by
  unfold inducedObj inducedEquiv; exact InducedCarrier.mem_grading_piece_iff N

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `inducedObj h N`, expressed in `N × N`. -/
@[simp]
theorem inducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : inducedObj h N) :
    inducedEquiv h N (a • z) =
      (a • (inducedEquiv h N z).1 - op (d a.unop) • N.grading.koszulTwist 1 (inducedEquiv h N z).2,
        a • (inducedEquiv h N z).2) := by unfold inducedObj inducedEquiv; rfl

/-- The curved differential on `inducedObj h N` sends `(x, y)` to `(y · w, x)`. -/
@[simp]
theorem inducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : inducedObj h N) :
    inducedEquiv h N ((inducedObj h N).differential z) =
      (op w • (inducedEquiv h N z).2, (inducedEquiv h N z).1) := by
  unfold inducedObj inducedEquiv; rfl

/-! ### Graded short exact sequence and projectivity -/

open CategoryTheory

/-- The natural graded right-module inclusion `N ⟶ U(G⁺ N)` sending `x` to `(x, 0)`. -/
noncomputable def inducedInl (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N ⟶ toGradedModuleCat (inducedObj h N) :=
  GradedModuleCat.ofHom
    ({ toFun x := (inducedEquiv h N).symm (x, 0)
       map_add' _ _ := (inducedEquiv h N).injective (by simp)
       map_smul' _ _ := (inducedEquiv h N).injective (by simp) } : N →ₗ[Aᵐᵒᵖ] inducedObj h N)
    (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      rw [toGradedModuleCat_piece, mem_inducedObj_grading_iff]; simpa using hx)

/-- The graded inclusion `inducedInl` sends `x` to `(x, 0)` in `N × N`. -/
@[simp]
theorem inducedEquiv_inducedInl_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (x : N) :
    inducedEquiv h N ((inducedInl h N).hom x) = (x, 0) :=
  (inducedEquiv h N).apply_symm_apply (x, 0)

/-- The natural graded right-module projection `U(G⁺ N) ⟶ N{1}` sending `(x, y)` to `y`. -/
noncomputable def inducedSnd (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (inducedObj h N) ⟶ N.shiftObj 1 :=
  GradedModuleCat.ofHom
    ({ toFun z := (inducedEquiv h N z).2, map_add' _ _ := by simp,
       map_smul' _ _ := by simp } : inducedObj h N →ₗ[Aᵐᵒᵖ] N)
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [toGradedModuleCat_piece, mem_inducedObj_grading_iff] at hz
      rw [GradedModuleCat.mem_shiftObj_piece_iff, add_zero]; exact hz.2)

/-- The graded projection `inducedSnd` extracts the second component in `N × N`. -/
@[simp]
theorem inducedSnd_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : inducedObj h N) :
    (dsimp% only ((inducedSnd h N).hom z)) = (inducedEquiv h N z).2 := by rw [inducedSnd]; rfl

/-- The graded inclusion into `G⁺ N` followed by the graded projection onto `N{1}` vanishes. -/
@[reassoc (attr := simp)]
theorem inducedInl_comp_inducedSnd (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedInl h N ≫ inducedSnd h N = 0 := by ext x; simp

/-- After forgetting the differential, `G⁺ N` sits in a short exact sequence
`0 ⟶ N ⟶ U(G⁺ N) ⟶ N{1} ⟶ 0` of graded right modules. -/
theorem shortExact_inducedInl_inducedSnd (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (inducedInl h N) (inducedSnd h N)
      (inducedInl_comp_inducedSnd h N)).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).2 fun _ _ hx ↦ by
    simpa using congrArg (fun z : inducedObj h N ↦ (inducedEquiv h N z).1) hx
  epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun y ↦
    ⟨(inducedEquiv h N).symm (0, y), by simp⟩
  exact := GradedModuleCat.exact_iff.2 fun z ↦ by
    simp only [inducedSnd_apply, Set.mem_range]
    refine ⟨fun hz ↦ ⟨(inducedEquiv h N z).1, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
    · exact inducedObj_ext (by rw [inducedEquiv_inducedInl_apply])
        (by rw [inducedEquiv_inducedInl_apply]; exact hz.symm)
    · rw [← hx, inducedEquiv_inducedInl_apply]

/-- If `P` is a projective graded right module, `U(G⁺ P)` is projective. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (P : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective P] :
    Projective (toGradedModuleCat (inducedObj h P)) := by
  have : Projective (P.shiftObj 1) := GradedModuleCat.projective_shiftObj P 1
  exact projective_iff_hasProjectiveDimensionLT_one.2
    ((shortExact_inducedInl_inducedSnd h P).hasProjectiveDimensionLT_X₂ 1 inferInstance
      inferInstance)

end InducedObj

/-! ### Functoriality, adjunction, contractibility, and projective covers -/

section Functor

open CategoryTheory CategoryTheory.Limits MulOpposite

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- The **induction functor** `N ↦ G⁺ N` from graded right modules to curved right modules with
closed degree-zero morphisms. -/
@[expose, implicit_reducible]
noncomputable def induced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N)
  map {N₁ N₂} f := closedHomOf
    { toFun z :=
        (inducedEquiv h N₂).symm (f.hom (inducedEquiv h N₁ z).1, f.hom (inducedEquiv h N₁ z).2)
      map_add' _ _ := (inducedEquiv h N₂).injective (by simp)
      map_smul' a z := (inducedEquiv h N₂).injective <| by
        have htw : N₂.grading.koszulTwist 1 (f.hom (inducedEquiv h N₁ z).2) =
            f.hom (N₁.grading.koszulTwist 1 (inducedEquiv h N₁ z).2) := by
          simpa using (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
            f.isHomogeneous.map_mem hx : LinearMap.IsHomogeneous (f.hom.restrictScalars R)
              N₁.grading.piece N₂.grading.piece 0).koszulTwist_apply 1 _
        simp [htw] }
    (fun p z hz ↦ by
      rw [mem_inducedObj_grading_iff] at hz ⊢
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
      exact ⟨by simpa using f.isHomogeneous.map_mem hz.1,
        by simpa using f.isHomogeneous.map_mem hz.2⟩)
    (fun z ↦ (inducedEquiv h N₂).injective (by simp))
  map_id N := closedHom_ext fun z ↦ (inducedEquiv h N).injective (by simp)
  map_comp f g := closedHom_ext fun z ↦ (inducedEquiv h _).injective (by simp)

/-- The induction functor sends a graded right module `N` to `inducedObj h N`. -/
@[simp]
theorem induced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (induced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) :=
  (rfl)

/-- On underlying pairs in `N × N`, `(induced h).map f` applies `f` componentwise. -/
@[simp]
theorem inducedEquiv_closedHom_induced_map_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : inducedObj h N₁) :
    inducedEquiv h N₂ (closedHom ((induced h).map f) z) =
      (f.hom (inducedEquiv h N₁ z).1, f.hom (inducedEquiv h N₁ z).2) := by
  dsimp only [induced]; rw [closedHom_closedHomOf]; exact (inducedEquiv h N₂).apply_symm_apply _

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (induced h).Additive where
  map_add := closedHom_ext fun z ↦ (inducedEquiv h _).injective <| by rw [closedHom_add]; simp

instance (h : IsCurvedDGAlgebra 𝒜 d w) : (induced h).Linear R where
  map_smul _ _ := closedHom_ext fun z ↦ (inducedEquiv h _).injective <| by rw [closedHom_smul]; simp

/-- The closed morphism `G⁺ N ⟶ M` adjunct to a morphism `f : N ⟶ U(M)` of graded right modules,
sending `(x, y)` to `f x + d_M (f y)`. -/
noncomputable def inducedDesc {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h} (f : N ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedHomOf
    { toFun z := HAdd.hAdd (α := M) (β := M) (f.hom (inducedEquiv h N z).1)
        (M.differential (f.hom (inducedEquiv h N z).2))
      map_add' _ _ := by simp only [map_add, Prod.fst_add, Prod.snd_add]; abel
      map_smul' a z := by
        have htw : (InternalGrading.ofDecomposition M.grading).koszulTwist 1
            (f.hom (inducedEquiv h N z).2) =
              f.hom (N.grading.koszulTwist 1 (inducedEquiv h N z).2) := by
          simpa using (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
            by simpa [toGradedModuleCat_piece] using f.isHomogeneous.map_mem hx :
              LinearMap.IsHomogeneous (f.hom.restrictScalars R) N.grading.piece
                (InternalGrading.ofDecomposition M.grading).piece 0).koszulTwist_apply 1 _
        simp only [RingHom.id_apply, inducedEquiv_smul, map_sub, LinearMap.map_smul,
          M.differential_smul, htw, smul_add]
        abel }
    (fun p z hz ↦ by
      rw [mem_inducedObj_grading_iff] at hz
      have hx : f.hom (inducedEquiv h N z).1 ∈ M.grading p := by
        simpa [toGradedModuleCat_piece] using f.isHomogeneous.map_mem hz.1
      have hy : f.hom (inducedEquiv h N z).2 ∈ M.grading (p - 1) := by
        simpa [toGradedModuleCat_piece] using f.isHomogeneous.map_mem hz.2
      exact Submodule.add_mem _ hx
        (by simpa [sub_add_cancel] using M.isCurvedDGRightModule.isHomogeneous.map_mem hy))
    (fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, M.isCurvedDGRightModule.sq_eq,
        inducedEquiv_differential, f.hom.map_smul, add_comm])

/-- Evaluating the adjunct closed morphism `inducedDesc f` sends `(x, y)` to `f x + d_M (f y)`. -/
@[simp]
theorem closedHom_inducedDesc_apply {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h} (f : N ⟶ toGradedModuleCat M) (z : inducedObj h N) :
    closedHom (inducedDesc f) z = HAdd.hAdd (α := M) (β := M) (f.hom (inducedEquiv h N z).1)
      (M.differential (f.hom (inducedEquiv h N z).2)) := by
  rw [inducedDesc, closedHom_closedHomOf]; rfl

/-- Precomposing `(forgetDifferential).map (inducedDesc f)` with `inducedInl` recovers `f`. -/
@[reassoc (attr := simp)]
theorem inducedInl_comp_forgetDifferential_map_inducedDesc {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h} (f : N ⟶ toGradedModuleCat M) :
    inducedInl h N ≫ (forgetDifferential (h := h)).map (inducedDesc f) = f := by
  ext x
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom]
  exact (closedHom_inducedDesc_apply f ((inducedInl h N).hom x)).trans (by simp)

/-- Forming `inducedDesc` from the restriction of `g : G⁺ N ⟶ M` along `inducedInl` recovers `g`.
-/
@[simp]
theorem inducedDesc_inducedInl_comp_forgetDifferential_map {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    inducedDesc (inducedInl h N ≫ (forgetDifferential (h := h)).map g) = g := by
  refine closedHom_ext fun z ↦ ?_
  rw [closedHom_inducedDesc_apply]
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom]
  have hz : z = (inducedEquiv h N).symm ((inducedEquiv h N z).1, 0) +
      (inducedObj h N).differential ((inducedEquiv h N).symm ((inducedEquiv h N z).2, 0)) :=
    inducedObj_ext (by simp) (by simp)
  have hi (x : N) : closedHom g ((inducedInl h N).hom x) =
      closedHom g ((inducedEquiv h N).symm (x, 0)) :=
    congrArg (closedHom g) ((inducedEquiv h N).injective (by simp))
  rw [hi, hi, differential_closedHom, ← map_add, ← hz]

/-- Induction `N ↦ G⁺ N` is left adjoint to forgetting the differential on curved right modules. -/
noncomputable def inducedForgetDifferentialAdj (h : IsCurvedDGAlgebra 𝒜 d w) :
    induced h ⊣ forgetDifferential (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv N M :=
        { toFun g := inducedInl h N ≫ (forgetDifferential (h := h)).map (X := (induced h).obj N) g
          invFun f := inducedDesc (M := ForgetEnrichment.to _ M) f
          left_inv g :=
            inducedDesc_inducedInl_comp_forgetDifferential_map (M := ForgetEnrichment.to _ M) g
          right_inv f :=
            inducedInl_comp_forgetDifferential_map_inducedDesc (M := ForgetEnrichment.to _ M) f }
      homEquiv_naturality_left_symm {_ _ M} _ _ := by
        dsimp only [induced]; exact closedHom_ext (N := ForgetEnrichment.to _ M) fun z ↦ by simp
      homEquiv_naturality_right _ _ := by simp }

/-- The forward adjunct of `inducedForgetDifferentialAdj` restricts along `inducedInl`. -/
@[simp]
theorem inducedForgetDifferentialAdj_homEquiv_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))
    (g : (induced h).obj N ⟶ M) :
    (inducedForgetDifferentialAdj h).homEquiv N M g =
      inducedInl h N ≫ (forgetDifferential (h := h)).map g := by
  rw [inducedForgetDifferentialAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl

/-- The reverse adjunct of `inducedForgetDifferentialAdj` is `inducedDesc`. -/
@[simp]
theorem inducedForgetDifferentialAdj_homEquiv_symm_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (M : CurvedDGRightModuleCat.{u, u, u} h) (f : N ⟶ toGradedModuleCat M) :
    ((inducedForgetDifferentialAdj h).homEquiv N
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)).symm f = inducedDesc f := by
  rw [inducedForgetDifferentialAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl

/-- The unit of `inducedForgetDifferentialAdj` at `N` is `inducedInl h N`. -/
@[simp]
theorem inducedForgetDifferentialAdj_unit_app (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedForgetDifferentialAdj h).unit.app N = inducedInl h N := by
  rw [inducedForgetDifferentialAdj, Adjunction.mkOfHomEquiv_unit_app, Equiv.coe_fn_mk,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The counit of `inducedForgetDifferentialAdj` at `M` is `inducedDesc (𝟙 (toGradedModuleCat M))`.
-/
@[simp]
theorem inducedForgetDifferentialAdj_counit_app_of (h : IsCurvedDGAlgebra 𝒜 d w)
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (inducedForgetDifferentialAdj h).counit.app
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
        inducedDesc (𝟙 (toGradedModuleCat M)) := by
  rw [inducedForgetDifferentialAdj, Adjunction.mkOfHomEquiv_counit_app, Equiv.coe_fn_symm_mk]; rfl

/-- Every induced curved right module `G⁺ N` is contractible, hence zero in the curved homotopy
category. -/
theorem isZero_homotopy_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (inducedObj h N)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  let k : inducedObj h N →ₗ[Aᵐᵒᵖ] inducedObj h N :=
    { toFun z := (inducedEquiv h N).symm ((inducedEquiv h N z).2, 0)
      map_add' _ _ := (inducedEquiv h N).injective (by simp)
      map_smul' _ _ := (inducedEquiv h N).injective (by simp) }
  refine ⟨⟨k, ?_⟩, fun z ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]; intro p z hz
    rw [mem_inducedObj_grading_iff] at hz ⊢; simpa [k, sub_eq_add_neg] using hz.2
  · apply inducedObj_ext <;> simp [k]

/-- For a projective graded right module `P`, `G⁺ P` is graded-projective. -/
theorem gradedProjective_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (P : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective P] :
    gradedProjective R h (DGHomotopyCategory.of R (inducedObj h P)) :=
  (gradedProjective_iff _).2 (inferInstanceAs (Projective (toGradedModuleCat (inducedObj h P))))

/-- Every curved right module `M` receives a closed epimorphism from `G⁺ P` for some projective
graded right module `P`. -/
theorem exists_epi_from_inducedObj_projective {h : IsCurvedDGAlgebra 𝒜 d w}
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (P : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
      (_ : Projective P)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h P) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M), Epi f := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
    rw [InternalGrading.ofDecomposition_piece]; infer_instance
  obtain ⟨P⟩ := @EnoughProjectives.presentation _ _
    GradedModuleCat.enoughProjectives.{u, u, u} (toGradedModuleCat M)
  exact ⟨P.p, inferInstance, ((inducedForgetDifferentialAdj h).homEquiv P.p
    (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)).symm P.f, inferInstance⟩

end Functor

end TauCeti.CurvedDGRightModuleCat
