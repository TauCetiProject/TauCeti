/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# Coinduced curved right modules from graded right modules

Dual to induction, every graded right module $N$ over a curved differential graded algebra
$(A, d, w)$ gives rise to a coinduced curved right module $G^- N$. Over the ground ring its
underlying module is $N \oplus N$, graded with degree-$p$ piece $N_p \oplus N_{p + 1}$. Its right
$A$-action is twisted on the second factor by the algebra differential and a Koszul sign:
$$(x, y) \cdot a = (x \cdot a,\ y \cdot a + (-1)^{|x|} x \cdot d a),$$
and its curved differential is $D_-(x, y) = (y, x \cdot w)$. Associativity of the twisted action
and the curved Leibniz rule follow from the Leibniz rule on $A$, the commutator curvature identity
$d^2 a = a w - w a$, and the cycle identity $d w = 0$.

Coinduction furnishes the right adjoint to forgetting the differential from curved right modules
with closed degree-zero morphisms to graded right modules: a graded morphism $M \longrightarrow N$
lifts to the closed morphism $M \longrightarrow G^- N$ given by $m \mapsto (f(m), f(d_M m))$.
Every coinduced curved module is contractible in the curved homotopy category via the odd
right-linear homotopy $(x, y) \mapsto (0, x)$. Moreover, after forgetting the differential,
$G^- N$ sits in a natural short exact sequence
$0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$
of graded right modules. Thus $G^- I$ is graded-injective whenever $I$ is injective, and every
curved right module embeds via a closed monomorphism into such a contractible graded-injective
curved module.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj`: the coinduced curved right module $G^- N$
  associated to a graded right module $N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedEquiv`: the ground-ring linear equivalence identifying
  the carrier of $G^- N$ with $N \times N$.
* `TauCeti.CurvedDGRightModuleCat.coinducedInr`, `TauCeti.CurvedDGRightModuleCat.coinducedFst`:
  the graded inclusion $N\{-1\} \longrightarrow G^- N$ and projection $G^- N \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.coinduced`: the right-adjoint functor from graded right modules
  to curved right modules with closed morphisms.
* `TauCeti.CurvedDGRightModuleCat.coinducedLift`: the closed morphism $M \longrightarrow G^- N$
  adjunct to a graded morphism $U(M) \longrightarrow N$.
* `TauCeti.CurvedDGRightModuleCat.forgetDifferentialCoinducedAdj`: the adjunction between
  forgetting the differential and coinduction.

## Main results

* `TauCeti.CurvedDGRightModuleCat.coinducedShortComplex_shortExact`: the graded short exact
  sequence $0 \longrightarrow N\{-1\} \longrightarrow G^- N \longrightarrow N \longrightarrow 0$.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: every coinduced curved right
  module is zero in the curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.exists_mono_to_coinducedObj_injective`: every curved right module
  admits a closed monomorphism into $G^- I$ for an injective graded right module $I$.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Lemma 7.7.
-/

public section

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uN u

section CoinducedObj

open MulOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Private wrapper around `N × N` carrying the twisted right `A`-module structure of `G⁻ N`
without colliding with the componentwise product `Aᵐᵒᵖ`-action on `N × N`. -/
@[ext]
private structure CoinducedCarrier (d : A →ₗ[R] A) (N : Type uN) where
  val : N × N

namespace CoinducedCarrier

section AddGroup

variable {N : Type uN}

private theorem val_injective : Function.Injective (CoinducedCarrier.val (d := d) (N := N)) :=
  fun _ _ ↦ CoinducedCarrier.ext

variable [AddCommGroup N]

private instance : Zero (CoinducedCarrier d N) := ⟨⟨0⟩⟩
private instance : Add (CoinducedCarrier d N) := ⟨fun z₁ z₂ ↦ ⟨z₁.val + z₂.val⟩⟩
private instance : Neg (CoinducedCarrier d N) := ⟨fun z ↦ ⟨-z.val⟩⟩
private instance : Sub (CoinducedCarrier d N) := ⟨fun z₁ z₂ ↦ ⟨z₁.val - z₂.val⟩⟩
private instance : SMul ℕ (CoinducedCarrier d N) := ⟨fun n z ↦ ⟨n • z.val⟩⟩
private instance : SMul ℤ (CoinducedCarrier d N) := ⟨fun n z ↦ ⟨n • z.val⟩⟩

@[simp] private theorem val_zero : (0 : CoinducedCarrier d N).val = 0 := rfl
@[simp] private theorem val_add (z₁ z₂ : CoinducedCarrier d N) :
    (z₁ + z₂).val = z₁.val + z₂.val := rfl
@[simp] private theorem val_neg (z : CoinducedCarrier d N) : (-z).val = -z.val := rfl
@[simp] private theorem val_sub (z₁ z₂ : CoinducedCarrier d N) :
    (z₁ - z₂).val = z₁.val - z₂.val := rfl
@[simp] private theorem val_nsmul (z : CoinducedCarrier d N) (n : ℕ) :
    (n • z).val = n • z.val := rfl
@[simp] private theorem val_zsmul (z : CoinducedCarrier d N) (n : ℤ) :
    (n • z).val = n • z.val := rfl

private instance : AddCommGroup (CoinducedCarrier d N) :=
  val_injective.addCommGroup _ val_zero val_add val_neg val_sub val_nsmul val_zsmul

end AddGroup

section ModuleBase

variable {N : Type uN} [AddCommGroup N] [Module R N]

private instance : SMul R (CoinducedCarrier d N) := ⟨fun r z ↦ ⟨r • z.val⟩⟩

@[simp] private theorem val_smul_base (r : R) (z : CoinducedCarrier d N) :
    (r • z).val = r • z.val := rfl

private instance : Module R (CoinducedCarrier d N) :=
  val_injective.module R ⟨⟨CoinducedCarrier.val, val_zero⟩, val_add⟩ val_smul_base

/-- The `R`-linear equivalence unwrapping `CoinducedCarrier`. -/
private def valEquiv : CoinducedCarrier d N ≃ₗ[R] N × N where
  toFun := CoinducedCarrier.val
  invFun := CoinducedCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem valEquiv_apply (z : CoinducedCarrier d N) :
    valEquiv (d := d) z = z.val := rfl
@[simp] private theorem valEquiv_symm_apply (z : N × N) :
    (valEquiv (d := d)).symm z = ⟨z⟩ := rfl

end ModuleBase

section TwistedAction

private noncomputable instance
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    SMul Aᵐᵒᵖ (CoinducedCarrier d N) where
  smul a z := ⟨(a • z.val.1, a • z.val.2 + op (d a.unop) • N.grading.koszulTwist 1 z.val.1)⟩

@[simp]
private theorem val_smul_op
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : CoinducedCarrier d N) :
    (a • z).val =
      (a • z.val.1, a • z.val.2 + op (d a.unop) • N.grading.koszulTwist 1 z.val.1) :=
  rfl

private theorem op_mul_twist_eq
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (h : IsCurvedDGAlgebra 𝒜 d w) (a b : A) (x : N) :
    op b • (op (d a) • N.grading.koszulTwist 1 x) +
        op (d b) • N.grading.koszulTwist 1 (op a • x) =
      op (d (a * b)) • N.grading.koszulTwist 1 x := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
    simp
  | @homogeneous r a =>
    rcases a with ⟨a, ha⟩
    induction x using DirectSum.Decomposition.inductionOn N.grading.piece with
    | zero =>
      simp
    | @homogeneous q x =>
      rcases x with ⟨x, hx⟩
      have hax : op a • x ∈ N.grading.piece (q + r) :=
        op_smul_mem_of_mem_graded ha hx
      rw [N.grading.koszulTwist_one_apply_of_mem hx, N.grading.koszulTwist_one_apply_of_mem hax,
        h.leibniz ha b, Int.negOnePow_add]
      simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _)]
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
        rcases Int.units_eq_one_or r.negOnePow with hr | hr <;>
        simp [hq, hr, MulOpposite.op_add, MulOpposite.op_mul, add_smul, smul_add, mul_smul]
    | add x₁ x₂ hx₁ hx₂ =>
      simp only [smul_add, map_add, ← hx₁, ← hx₂]
      abel
  | add a₁ a₂ ha₁ ha₂ =>
    simp only [map_add, MulOpposite.op_add, add_mul, add_smul, smul_add, ← ha₁, ← ha₂]
    abel

@[instance_reducible]
private noncomputable def moduleOp
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (h : IsCurvedDGAlgebra 𝒜 d w) :
    Module Aᵐᵒᵖ (CoinducedCarrier d N) where
  one_smul z := by
    ext
    · exact one_smul Aᵐᵒᵖ z.val.1
    · change (1 : Aᵐᵒᵖ) • z.val.2 + op (d 1) • N.grading.koszulTwist 1 z.val.1 = z.val.2
      rw [one_smul, h.map_one_eq_zero, MulOpposite.op_zero, zero_smul, add_zero]
  mul_smul b a z := by
    ext
    · exact mul_smul b a z.val.1
    · simp only [val_smul_op, unop_mul, smul_add]
      have ht := op_mul_twist_eq N h a.unop b.unop z.val.1
      simp only [op_unop] at ht
      rw [mul_smul b a z.val.2, ← ht]
      abel
  smul_zero a := by
    ext <;> simp [val_smul_op]
  smul_add a z₁ z₂ := by
    ext
    · exact smul_add a z₁.val.1 z₂.val.1
    · simp only [val_smul_op, val_add, Prod.fst_add, Prod.snd_add, map_add, smul_add]
      abel
  add_smul a b z := by
    ext
    · exact add_smul a b z.val.1
    · simp only [val_smul_op, val_add, Prod.snd_add, unop_add, map_add, MulOpposite.op_add,
        add_smul]
      abel
  zero_smul z := by
    ext <;> simp [val_smul_op]

private theorem scalarTower
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h
    IsScalarTower R Aᵐᵒᵖ (CoinducedCarrier d N) := by
  let := moduleOp N h
  refine ⟨fun r a z ↦ ?_⟩
  have hsmul (x : A) : r • op x = op (r • x) := by
    rw [Algebra.smul_def, Algebra.smul_def, MulOpposite.algebraMap_apply, ← MulOpposite.op_mul,
      Algebra.commutes]
  have hunop : (r • a).unop = r • a.unop := by
    conv_lhs => rw [← MulOpposite.op_unop a]
    rw [hsmul, MulOpposite.unop_op]
  ext
  · exact smul_assoc r a z.val.1
  · change (r • a) • z.val.2 + op (d (r • a).unop) • N.grading.koszulTwist 1 z.val.1 =
      r • (a • z.val.2 + op (d a.unop) • N.grading.koszulTwist 1 z.val.1)
    rw [smul_assoc, hunop, d.map_smul, ← hsmul, smul_assoc, smul_add]

/-- The internal grading on `CoinducedCarrier d N` with degree-`p` piece `N_p × N_{p + 1}`. -/
private noncomputable def grading
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InternalGrading R (CoinducedCarrier d N) :=
  (N.grading.prod (N.shiftObj (-1)).grading).map (valEquiv (d := d)).symm

private theorem mem_grading_piece_iff
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    {p : ℤ} {z : CoinducedCarrier d N} :
    z ∈ (grading (d := d) N).piece p ↔
      z.val.1 ∈ N.grading.piece p ∧ z.val.2 ∈ N.grading.piece (p + 1) := by
  rw [grading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm, valEquiv_apply,
    InternalGrading.prod_piece, Submodule.mem_prod, GradedModuleCat.mem_shiftObj_piece_iff,
    sub_neg_eq_add]

private theorem gradedSMul
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (grading (d := d) N).piece := by
  let := moduleOp N h
  refine ⟨fun {r p} a z ha hz ↦ ?_⟩
  have ha' : a.unop ∈ 𝒜 r := by
    rw [← MulOpposite.op_unop a, InternalGrading.op_mem_opposite_piece_iff,
      InternalGrading.ofDecomposition_piece] at ha
    exact ha
  rw [mem_grading_piece_iff] at hz ⊢
  rw [vadd_eq_add, add_comm r p, val_smul_op]
  dsimp only
  rw [← MulOpposite.op_unop a]
  refine ⟨op_smul_mem_of_mem_graded ha' hz.1, Submodule.add_mem _ ?_ ?_⟩
  · simpa [show p + 1 + r = p + r + 1 by omega] using op_smul_mem_of_mem_graded ha' hz.2
  · have hda : d a.unop ∈ 𝒜 (r + 1) := h.map_mem ha'
    have htw : N.grading.koszulTwist 1 z.val.1 ∈ N.grading.piece p :=
      N.grading.koszulTwist_mem_piece hz.1 1
    simpa [show p + (r + 1) = p + r + 1 by omega] using op_smul_mem_of_mem_graded hda htw

/-- The differential `(x, y) ↦ (y, x · w)` on `CoinducedCarrier d N`. -/
private noncomputable def differential
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (w : A) :
    CoinducedCarrier d N →ₗ[R] CoinducedCarrier d N where
  toFun z := ⟨(z.val.2, op w • z.val.1)⟩
  map_add' z₁ z₂ := by
    ext
    · rfl
    · exact smul_add (op w) z₁.val.1 z₂.val.1
  map_smul' r z := by
    ext
    · rfl
    · exact smul_comm (op w) r z.val.1

@[simp]
private theorem val_differential
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (w : A) (z : CoinducedCarrier d N) :
    (differential (d := d) N w z).val = (z.val.2, op w • z.val.1) :=
  rfl

private theorem isCurvedDGRightModule
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (h : IsCurvedDGAlgebra 𝒜 d w) :
    letI := moduleOp N h
    letI := scalarTower N h
    letI := gradedSMul N h
    IsCurvedDGRightModule h (grading (d := d) N).piece (differential (d := d) N w) := by
  let := moduleOp N h
  let := scalarTower N h
  let := gradedSMul N h
  refine ⟨LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_, fun {p z} hz a ↦ ?_, fun z ↦ ?_⟩
  · rw [mem_grading_piece_iff] at hz ⊢
    rw [val_differential]
    exact ⟨hz.2, by simpa [show p + 2 = p + 1 + 1 by omega] using
      op_smul_mem_of_mem_graded h.curvature_mem hz.1⟩
  · rw [mem_grading_piece_iff] at hz
    ext
    · change op a • z.val.2 + op (d a) • N.grading.koszulTwist 1 z.val.1 =
        op a • z.val.2 + p.negOnePow • (op (d a) • z.val.1)
      rw [N.grading.koszulTwist_one_apply_of_mem hz.1]
      simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _)]
    · change op w • (op a • z.val.1) =
        (op a • (op w • z.val.1) + op (d a) • N.grading.koszulTwist 1 z.val.2) +
          p.negOnePow • (op (d a) • z.val.2 + op (d (d a)) • N.grading.koszulTwist 1 z.val.1)
      rw [N.grading.koszulTwist_one_apply_of_mem hz.1, N.grading.koszulTwist_one_apply_of_mem hz.2,
        h.sq_eq a, Int.negOnePow_succ]
      simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _), Units.val_neg]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simp [hp, MulOpposite.op_sub, MulOpposite.op_mul, sub_smul, mul_smul]
  · ext
    · rfl
    · change op w • z.val.2 = op w • z.val.2 + op (d w) • N.grading.koszulTwist 1 z.val.1
      rw [h.map_curvature, MulOpposite.op_zero, zero_smul, add_zero]

end TwistedAction

end CoinducedCarrier

/-- The **coinduced curved right module** `G⁻ N` associated to a graded right module `N`. Over `R`
its carrier is `N × N` with degree-`p` piece `N_p × N_{p + 1}`, twisted right action
`(x, y) · a = (x · a, y · a + (-1)^{|x|} x · d a)`, and differential `(x, y) ↦ (y, x · w)`. -/
noncomputable def coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uN} h where
  carrier := CoinducedCarrier d N
  moduleOp := CoinducedCarrier.moduleOp N h
  scalarTower := CoinducedCarrier.scalarTower N h
  grading := (CoinducedCarrier.grading (d := d) N).piece
  gradedSMul := CoinducedCarrier.gradedSMul N h
  differential := CoinducedCarrier.differential (d := d) N w
  isCurvedDGRightModule := CoinducedCarrier.isCurvedDGRightModule N h

/-- The `R`-linear equivalence identifying the carrier of `coinducedObj h N` with `N × N`. -/
noncomputable def coinducedEquiv (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h N ≃ₗ[R] N × N := by
  unfold coinducedObj
  exact CoinducedCarrier.valEquiv (d := d)

/-- Elements of `coinducedObj h N` are determined by their two components in `N × N`. -/
@[ext]
theorem coinducedObj_ext {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {z₁ z₂ : coinducedObj h N}
    (h₁ : (coinducedEquiv h N z₁).1 = (coinducedEquiv h N z₂).1)
    (h₂ : (coinducedEquiv h N z₁).2 = (coinducedEquiv h N z₂).2) : z₁ = z₂ :=
  (coinducedEquiv h N).injective (Prod.ext h₁ h₂)

/-- An element of `coinducedObj h N` has degree `p` if and only if its components lie in `N_p` and
`N_{p + 1}`. -/
@[simp]
theorem mem_coinducedObj_grading_iff {h : IsCurvedDGAlgebra 𝒜 d w}
    {N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : coinducedObj h N} :
    z ∈ (coinducedObj h N).grading p ↔
      (coinducedEquiv h N z).1 ∈ N.grading.piece p ∧
        (coinducedEquiv h N z).2 ∈ N.grading.piece (p + 1) := by
  unfold coinducedObj coinducedEquiv
  exact CoinducedCarrier.mem_grading_piece_iff N

/-- Scalar multiplication by `a : Aᵐᵒᵖ` on `coinducedObj h N`, expressed in `N × N` via
`coinducedEquiv`. -/
@[simp]
theorem coinducedEquiv_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (z : coinducedObj h N) :
    coinducedEquiv h N (a • z) =
      (a • (coinducedEquiv h N z).1,
        a • (coinducedEquiv h N z).2 + op (d a.unop) • N.grading.koszulTwist 1
          (coinducedEquiv h N z).1) := by
  unfold coinducedObj coinducedEquiv
  rfl

/-- The twisted right action on `coinducedObj h N`, expressed in `N × N` via `coinducedEquiv`. -/
theorem coinducedEquiv_op_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : A) (z : coinducedObj h N) :
    coinducedEquiv h N (op a • z) =
      (op a • (coinducedEquiv h N z).1,
        op a • (coinducedEquiv h N z).2 + op (d a) • N.grading.koszulTwist 1
          (coinducedEquiv h N z).1) := by
  rw [coinducedEquiv_smul, unop_op]

/-- The curved differential on `coinducedObj h N` sends `(x, y)` to `(y, x · w)`. -/
@[simp]
theorem coinducedEquiv_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    coinducedEquiv h N ((coinducedObj h N).differential z) =
      ((coinducedEquiv h N z).2, op w • (coinducedEquiv h N z).1) := by
  unfold coinducedObj coinducedEquiv
  rfl

/-! ### Graded short exact sequence and injectivity -/

open CategoryTheory

/-- Underlying right-linear map `y ↦ (0, y)` into `coinducedObj h N`. -/
private noncomputable def coinducedInrLinear (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N →ₗ[Aᵐᵒᵖ] coinducedObj h N where
  toFun y := (coinducedEquiv h N).symm (0, y)
  map_add' y₁ y₂ := by
    apply (coinducedEquiv h N).injective
    simp
  map_smul' a y := by
    apply (coinducedEquiv h N).injective
    simp

/-- The natural graded right-module inclusion `N{-1} ⟶ U(G⁻ N)` sending `y` to `(0, y)`. -/
noncomputable def coinducedInr (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h N) :=
  GradedModuleCat.ofHom (coinducedInrLinear h N)
    (LinearMap.isHomogeneous_def.2 fun p y hy ↦ by
      rw [GradedModuleCat.mem_shiftObj_piece_iff, sub_neg_eq_add] at hy
      rw [toGradedModuleCat_piece, add_zero, mem_coinducedObj_grading_iff]
      simpa [coinducedInrLinear] using hy)

/-- The graded inclusion `coinducedInr` sends `y` to `(0, y)` in `N × N`. -/
@[simp]
theorem coinducedEquiv_coinducedInr_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (y : N) :
    coinducedEquiv h N ((coinducedInr h N).hom y) = (0, y) := by
  rw [coinducedInr]
  exact (coinducedEquiv h N).apply_symm_apply (0, y)

/-- Underlying right-linear map `(x, y) ↦ x` out of `coinducedObj h N`. -/
private noncomputable def coinducedFstLinear (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h N →ₗ[Aᵐᵒᵖ] N where
  toFun z := (coinducedEquiv h N z).1
  map_add' z₁ z₂ := by simp
  map_smul' a z := by simp

/-- The natural graded right-module projection `U(G⁻ N) ⟶ N` sending `(x, y)` to `x`. -/
noncomputable def coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  GradedModuleCat.ofHom (coinducedFstLinear h N)
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [toGradedModuleCat_piece, mem_coinducedObj_grading_iff] at hz
      rw [add_zero]
      exact hz.1)

/-- The graded projection `coinducedFst` extracts the first component in `N × N`. -/
@[simp]
theorem coinducedFst_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : coinducedObj h N) :
    (coinducedFst h N).hom z = (coinducedEquiv h N z).1 := by
  rw [coinducedFst]
  rfl

/-- The graded inclusion of `N{-1}` into `G⁻ N` followed by the graded projection onto `N`
vanishes. -/
@[reassoc (attr := simp)]
theorem coinducedInr_comp_coinducedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedInr h N ≫ coinducedFst h N = 0 := by
  ext y
  change (coinducedFst h N).hom ((coinducedInr h N).hom y) = 0
  rw [coinducedFst_apply, coinducedEquiv_coinducedInr_apply]

/-- After forgetting the differential, `G⁻ N` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ U(G⁻ N) ⟶ N ⟶ 0` of graded right modules. -/
theorem coinducedShortComplex_shortExact (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (ShortComplex.mk (coinducedInr h N) (coinducedFst h N)
      (coinducedInr_comp_coinducedFst h N)).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).2 fun y₁ y₂ hy ↦ by
    have h₂ := congrArg (fun z : coinducedObj h N ↦ (coinducedEquiv h N z).2) hy
    rw [coinducedEquiv_coinducedInr_apply, coinducedEquiv_coinducedInr_apply] at h₂
    exact h₂
  epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun x ↦
    ⟨(coinducedEquiv h N).symm (x, 0), by
      change (coinducedFst h N).hom ((coinducedEquiv h N).symm (x, 0)) = x
      rw [coinducedFst_apply, LinearEquiv.apply_symm_apply]⟩
  exact := GradedModuleCat.exact_iff.2 fun z ↦ by
    change (coinducedFst h N).hom z = 0 ↔ _
    rw [coinducedFst_apply]
    refine ⟨fun hz ↦ ⟨(coinducedEquiv h N z).2, ?_⟩, ?_⟩
    · apply coinducedObj_ext
      · rw [coinducedEquiv_coinducedInr_apply]
        exact hz.symm
      · rw [coinducedEquiv_coinducedInr_apply]
    · rintro ⟨y, rfl⟩
      rw [coinducedEquiv_coinducedInr_apply]

/-- If `I` is an injective graded right module, the underlying graded right module of `G⁻ I` is
injective. -/
instance (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{uN} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (coinducedObj h I)) := by
  have : Injective (I.shiftObj (-1)) := GradedModuleCat.injective_shiftObj I (-1)
  exact injective_iff_hasInjectiveDimensionLT_one.2
    ((coinducedShortComplex_shortExact h I).hasInjectiveDimensionLT_X₂ 1 inferInstance
      inferInstance)

end CoinducedObj

/-! ### Functoriality, adjunction, contractibility, and injective hulls -/

section Functor

open CategoryTheory CategoryTheory.Limits MulOpposite

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Underlying `Aᵐᵒᵖ`-linear map `(x, y) ↦ (f x, f y)` induced on `G⁻` by a graded morphism `f`. -/
private noncomputable def coinducedMapLinear (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) : coinducedObj h N₁ →ₗ[Aᵐᵒᵖ] coinducedObj h N₂ where
  toFun z :=
    (coinducedEquiv h N₂).symm (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2)
  map_add' z₁ z₂ := by
    apply (coinducedEquiv h N₂).injective
    simp
  map_smul' a z := by
    apply (coinducedEquiv h N₂).injective
    have hfR : LinearMap.IsHomogeneous (f.hom.restrictScalars R) N₁.grading.piece
        N₂.grading.piece 0 :=
      LinearMap.isHomogeneous_def.2 fun p x hx ↦ f.isHomogeneous.map_mem hx
    have htw := hfR.koszulTwist_apply 1 (coinducedEquiv h N₁ z).1
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.restrictScalars_apply] at htw
    simp [htw]

/-- Closed morphism `G⁻ N₁ ⟶ G⁻ N₂` induced by a morphism `f : N₁ ⟶ N₂` of graded right modules. -/
noncomputable def coinducedMap (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₁) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₂) :=
  closedHomOf (coinducedMapLinear h f)
    (fun p z hz ↦ by
      rw [mem_coinducedObj_grading_iff] at hz ⊢
      simp only [coinducedMapLinear, LinearMap.coe_mk, AddHom.coe_mk,
        LinearEquiv.apply_symm_apply]
      exact ⟨by simpa using f.isHomogeneous.map_mem hz.1,
        by simpa using f.isHomogeneous.map_mem hz.2⟩)
    (fun z ↦ by
      apply (coinducedEquiv h N₂).injective
      simp [coinducedMapLinear])

/-- On underlying pairs in `N × N`, `coinducedMap h f` applies `f` componentwise. -/
@[simp]
theorem coinducedEquiv_coinducedMap_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) (z : coinducedObj h N₁) :
    coinducedEquiv h N₂ (closedHom (coinducedMap h f) z) =
      (f.hom (coinducedEquiv h N₁ z).1, f.hom (coinducedEquiv h N₁ z).2) := by
  rw [coinducedMap, closedHom_closedHomOf]
  exact (coinducedEquiv h N₂).apply_symm_apply _

/-- The **coinduction functor** `N ↦ G⁻ N` from graded right modules to curved right modules with
closed degree-zero morphisms. -/
@[expose, implicit_reducible]
noncomputable def coinduced (h : IsCurvedDGAlgebra 𝒜 d w) :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)
  map f := coinducedMap h f
  map_id N := by
    apply closedHom_ext
    intro z
    apply (coinducedEquiv h N).injective
    simp
  map_comp f g := by
    apply closedHom_ext
    intro z
    apply (coinducedEquiv h _).injective
    simp

/-- The coinduction functor sends a graded right module `N` to `coinducedObj h N`. -/
@[simp]
theorem coinduced_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced h).obj N = ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

/-- The coinduction functor acts on morphisms by `coinducedMap`. -/
@[simp]
theorem coinduced_map (h : IsCurvedDGAlgebra 𝒜 d w)
    {N₁ N₂ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : N₁ ⟶ N₂) :
    (coinduced h).map f = coinducedMap h f :=
  (rfl)

/-- Underlying `Aᵐᵒᵖ`-linear map `m ↦ (f m, f (d_M m))` adjunct to a degree-zero right-linear map
`f : M →ₗ[Aᵐᵒᵖ] N`. -/
private noncomputable def coinducedLiftLinear {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) :
    M →ₗ[Aᵐᵒᵖ] coinducedObj h N where
  toFun m := (coinducedEquiv h N).symm (f m, f (M.differential m))
  map_add' m₁ m₂ := by
    apply (coinducedEquiv h N).injective
    simp
  map_smul' a m := by
    apply (coinducedEquiv h N).injective
    have hkey : ∀ x : M,
        f (M.differential (a • x)) =
          a • f (M.differential x) + op (d a.unop) • N.grading.koszulTwist 1 (f x) := by
      intro x
      induction x using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | @homogeneous q x =>
        rcases x with ⟨x, hx⟩
        have hfx : f x ∈ N.grading.piece q := by
          simpa using hf.map_mem hx
        have ha_eq : a = op a.unop := (MulOpposite.op_unop a).symm
        conv_lhs => rw [ha_eq]
        rw [N.grading.koszulTwist_one_apply_of_mem hfx,
          M.isCurvedDGRightModule.leibniz hx a.unop, ← ha_eq, map_add, LinearMap.map_smul,
          LinearMap.map_smul_of_tower f, LinearMap.map_smul]
        simp only [Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op _)]
      | add x₁ x₂ hx₁ hx₂ =>
        simp only [smul_add, map_add, hx₁, hx₂]
        abel
    simp [hkey]

@[simp]
private theorem coinducedEquiv_coinducedLiftLinear_apply {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) (m : M) :
    coinducedEquiv h N (coinducedLiftLinear f hf m) = (f m, f (M.differential m)) := by
  unfold coinducedLiftLinear
  exact (coinducedEquiv h N).apply_symm_apply _

/-- The closed morphism `M ⟶ G⁻ N` adjunct to a degree-zero right-linear map `f : M →ₗ[Aᵐᵒᵖ] N`,
sending `m` to `(f m, f (d_M m))`. -/
noncomputable def coinducedLift {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  closedHomOf (coinducedLiftLinear f hf)
    (fun p m hm ↦ by
      rw [mem_coinducedObj_grading_iff, coinducedEquiv_coinducedLiftLinear_apply]
      have hdm : M.differential m ∈ M.grading (p + 1) :=
        M.isCurvedDGRightModule.isHomogeneous.map_mem hm
      exact ⟨by simpa using hf.map_mem hm, by simpa using hf.map_mem hdm⟩)
    (fun m ↦ by
      apply (coinducedEquiv h N).injective
      rw [coinducedEquiv_differential, coinducedEquiv_coinducedLiftLinear_apply,
        coinducedEquiv_coinducedLiftLinear_apply, M.isCurvedDGRightModule.sq_eq, f.map_smul])

/-- Evaluating the adjunct closed morphism `coinducedLift f hf` sends `m` to
`(f m, f (d_M m))`. -/
@[simp]
theorem coinducedEquiv_closedHom_coinducedLift_apply {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0) (m : M) :
    coinducedEquiv h N (closedHom (coinducedLift f hf) m) = (f m, f (M.differential m)) := by
  unfold coinducedLift
  rw [closedHom_closedHomOf, coinducedEquiv_coinducedLiftLinear_apply]

/-- If `f : M →ₗ[Aᵐᵒᵖ] N` is an injective degree-zero right-linear map, its adjunct closed
morphism `coinducedLift f hf : M ⟶ G⁻ N` is a monomorphism in the closed category of curved right
modules. -/
theorem mono_coinducedLift_of_injective {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M →ₗ[Aᵐᵒᵖ] N) (hf : LinearMap.IsHomogeneous f M.grading N.grading.piece 0)
    (hinj : Function.Injective f) :
    Mono (coinducedLift f hf) :=
  ⟨fun {K} u₁ u₂ hu ↦ closedHom_ext fun x ↦ hinj <| by
    have h₁₂ := congrArg
      (fun k ↦ (coinducedEquiv h N (closedHom k x)).1) hu
    simpa only [closedHom_comp, LinearMap.comp_apply,
      coinducedEquiv_closedHom_coinducedLift_apply] using h₁₂⟩

private theorem isHomogeneous_from_gradedHom {h : IsCurvedDGAlgebra 𝒜 d w}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : toGradedModuleCat M ⟶ N) :
    LinearMap.IsHomogeneous (M := M) f.hom M.grading N.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
    have hm' : m ∈ (toGradedModuleCat M).grading.piece p := by
      rwa [toGradedModuleCat_piece]
    exact f.isHomogeneous.map_mem hm'

/-- Forgetting the differential on curved right modules is left adjoint to coinduction
`N ↦ G⁻ N`. -/
noncomputable def forgetDifferentialCoinducedAdj (h : IsCurvedDGAlgebra 𝒜 d w) :
    forgetDifferential (h := h) ⊣ coinduced h :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun f := coinducedLift (M := ForgetEnrichment.to _ M) f.hom
            (isHomogeneous_from_gradedHom f)
          invFun g := (forgetDifferential (h := h)).map g ≫ coinducedFst h N
          left_inv f := by
            ext m
            change (coinducedFst h N).hom (closedHom (coinducedLift
              (M := ForgetEnrichment.to _ M) f.hom (isHomogeneous_from_gradedHom f)) m) = f.hom m
            rw [coinducedFst_apply, coinducedEquiv_closedHom_coinducedLift_apply]
          right_inv g := by
            let g' : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
                (ForgetEnrichment.to _ M) ⟶
              ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) := g
            apply closedHom_ext
            intro m
            apply (coinducedEquiv h N).injective
            have hd := congrArg (fun z ↦ (coinducedEquiv h N z).1) (differential_closedHom g' m)
            rw [coinducedEquiv_differential] at hd
            simp only [coinducedEquiv_closedHom_coinducedLift_apply, GradedModuleCat.hom_comp,
              forgetDifferential_map_hom, LinearMap.comp_apply]
            exact Prod.ext rfl hd.symm }
      homEquiv_naturality_left_symm {M₁ M₂ N} k g := by
        dsimp only [Equiv.coe_fn_symm_mk]
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right {M N₁ N₂} f k := by
        apply closedHom_ext
        intro m
        apply (coinducedEquiv h N₂).injective
        dsimp only [Equiv.coe_fn_mk]
        rw [coinduced_map, closedHom_comp, LinearMap.comp_apply, coinducedEquiv_coinducedMap_apply,
          coinducedEquiv_closedHom_coinducedLift_apply,
          coinducedEquiv_closedHom_coinducedLift_apply, GradedModuleCat.hom_comp]
        rfl }

/-- Every coinduced curved right module `G⁻ N` is contractible, hence zero in the curved homotopy
category. -/
theorem isZero_homotopy_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h N)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  let k : coinducedObj h N →ₗ[Aᵐᵒᵖ] coinducedObj h N :=
    { toFun z := (coinducedEquiv h N).symm (0, (coinducedEquiv h N z).1)
      map_add' z₁ z₂ := by
        apply (coinducedEquiv h N).injective
        simp
      map_smul' a z := by
        apply (coinducedEquiv h N).injective
        simp }
  refine ⟨⟨k, ?_⟩, fun z ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p z hz
    rw [mem_coinducedObj_grading_iff] at hz ⊢
    simpa [k, show p + -1 + 1 = p by omega] using hz.1
  · apply coinducedObj_ext <;> simp [k]

/-- For an injective graded right module `I`, the coinduced curved module `G⁻ I` is
graded-injective. -/
theorem gradedInjective_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    gradedInjective R h (DGHomotopyCategory.of R (coinducedObj h I)) :=
  (gradedInjective_iff _).2 (inferInstanceAs (Injective (toGradedModuleCat (coinducedObj h I))))

/-- Every curved right module `M` admits a closed monomorphism into `G⁻ I` for some injective
graded right module `I`. -/
theorem exists_mono_to_coinducedObj_injective {h : IsCurvedDGAlgebra 𝒜 d w}
    (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
      (_ : Injective I)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h I)), Mono f := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
    rw [InternalGrading.ofDecomposition_piece]
    infer_instance
  obtain ⟨I⟩ := @EnoughInjectives.presentation _ _
    GradedModuleCat.enoughInjectives.{u, u, u} (toGradedModuleCat M)
  have : Injective I.J := I.injective
  have : Mono I.f := I.mono
  have hinj : Function.Injective (I.f.hom : M →ₗ[Aᵐᵒᵖ] I.J) :=
    (GradedModuleCat.mono_iff_injective I.f).1 inferInstance
  exact ⟨I.J, inferInstance, coinducedLift I.f.hom (isHomogeneous_from_gradedHom I.f),
    mono_coinducedLift_of_injective _ _ hinj⟩

end Functor

end TauCeti.CurvedDGRightModuleCat
