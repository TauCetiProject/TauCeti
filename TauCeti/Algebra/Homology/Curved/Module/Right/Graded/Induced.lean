/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
import TauCeti.Algebra.Module.GradedModule.Prod
import TauCeti.Algebra.Module.NatInt

/-!
# Freely induced curved differential graded right modules

For a curved differential graded algebra `(𝒜, d, w)` and a graded right module `N`, Positselski's
induction functor `G⁺` produces a curved right module `inducedObj h N` freely adjoining formal
differentials to `N`. Its underlying graded `R`-module is `N ⊕ N{1}` (with homogeneous piece
`Nₚ × Nₚ₋₁` in degree `p`), equipped with the twisted right `A`-action

`(x, y) · a = (x · a + (-1)^p (y · d a), y · a)` for `y ∈ Nₚ₋₁`

and the curved differential `d(x, y) = (y · w, x)`. The curvature axioms `d(d a) = a * w - w * a`,
`w ∈ 𝒜 2`, and `d w = 0` are precisely what make this twisted right action associative and
compatible with the graded right Leibniz rule and curvature square `d²(x, y) = (x, y) · w`.

This functor `induced` is left adjoint to `forgetDifferential`. Because `forgetDifferential` is
faithful, every counit component `G⁺(M♯) ⟶ M` is an epimorphism in the abelian closed category of
curved right modules. Moreover:

* `inducedObj h N` is contractible via the degree-`(-1)` right-linear homotopy `(x, y) ↦ (y, 0)`,
  hence zero in the curved homotopy category;
* after forgetting the differential, `inducedObj h N` sits in a short exact sequence
  `0 ⟶ N ⟶ (inducedObj h N)♯ ⟶ N{1} ⟶ 0` of graded right modules, so `inducedObj h P` is
  graded-projective whenever `P` is projective.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.inducedObj`: the freely induced curved right module `G⁺(N)`.
* `TauCeti.CurvedDGRightModuleCat.induced`: the left adjoint functor from graded right modules to
  the closed category of curved right modules.
* `TauCeti.CurvedDGRightModuleCat.inducedAdjForgetDifferential`: the adjunction
  `induced ⊣ forgetDifferential`.
* `TauCeti.CurvedDGRightModuleCat.inducedGradedShortComplex`: the graded short complex
  `N ⟶ (inducedObj h N)♯ ⟶ N{1}`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_inducedObj`: `inducedObj h N` is zero in the
  curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.inducedGradedShortComplex_shortExact`: the underlying graded
  module of `inducedObj h N` is an extension of `N{1}` by `N`.
* `TauCeti.CurvedDGRightModuleCat.projective_toGradedModuleCat_inducedObj`: `inducedObj h P` is
  graded-projective when `P` is projective.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6 (proof of
  Theorem 3.6).
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
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

section Carrier

/-- Private carrier of `G⁺(N)` wrapping `N × N` so its twisted right `A`-action does not conflict
with the componentwise product action. -/
@[ext]
private structure InducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) where
  fst : N
  snd : N

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

private instance : Zero (InducedCarrier h N) := ⟨⟨0, 0⟩⟩
private instance : Add (InducedCarrier h N) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private instance : Neg (InducedCarrier h N) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private instance : Sub (InducedCarrier h N) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private instance : SMul ℕ (InducedCarrier h N) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private instance : SMul ℤ (InducedCarrier h N) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩

private instance : AddCommGroup (InducedCarrier h N) :=
  Function.Injective.addCommGroup (fun z : InducedCarrier h N ↦ (z.fst, z.snd))
    (fun _ _ hxy ↦ InducedCarrier.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance : SMul R (InducedCarrier h N) := ⟨fun r z ↦ ⟨r • z.fst, r • z.snd⟩⟩

private instance : Module R (InducedCarrier h N) :=
  Function.Injective.module R
    { toFun := fun z : InducedCarrier h N ↦ (z.fst, z.snd)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ hxy ↦ InducedCarrier.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    (fun _ _ ↦ rfl)

@[simp]
private theorem inducedCarrier_zero_fst : (0 : InducedCarrier h N).fst = 0 := rfl
@[simp]
private theorem inducedCarrier_zero_snd : (0 : InducedCarrier h N).snd = 0 := rfl
@[simp]
private theorem inducedCarrier_add_fst (x y : InducedCarrier h N) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp]
private theorem inducedCarrier_add_snd (x y : InducedCarrier h N) :
    (x + y).snd = x.snd + y.snd := rfl
@[simp]
private theorem inducedCarrier_neg_fst (z : InducedCarrier h N) :
    (-z).fst = -z.fst := rfl
@[simp]
private theorem inducedCarrier_neg_snd (z : InducedCarrier h N) :
    (-z).snd = -z.snd := rfl
@[simp]
private theorem inducedCarrier_smul_fst (r : R) (z : InducedCarrier h N) :
    (r • z).fst = r • z.fst := rfl
@[simp]
private theorem inducedCarrier_smul_snd (r : R) (z : InducedCarrier h N) :
    (r • z).snd = r • z.snd := rfl

private def inducedProdEquiv : InducedCarrier h N ≃ₗ[R] N × (N.shiftObj 1) where
  toFun z := (z.fst, z.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def inducedGrading : InternalGrading R (InducedCarrier h N) ℤ :=
  (N.grading.prod (N.shiftObj 1).grading).map (inducedProdEquiv h N).symm

private theorem mem_inducedGrading_piece_iff (p : ℤ) (z : InducedCarrier h N) :
    z ∈ (inducedGrading h N).piece p ↔
      z.fst ∈ N.grading.piece p ∧ z.snd ∈ N.grading.piece (p - 1) := by
  rw [inducedGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.prod_piece, Submodule.mem_prod, N.mem_shiftObj_piece_iff]
  rfl

/-- Koszul twist `y ↦ (-1)^p y` for `y ∈ (N{1})ₚ = Nₚ₋₁`. -/
private noncomputable def inducedTwist : N →ₗ[R] N :=
  (N.shiftObj 1).grading.koszulTwist 1

private theorem inducedTwist_apply_of_mem_shift {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {p : ℤ} {y : N}
    (hy : y ∈ N.grading.piece (p - 1)) :
    inducedTwist N y = p.negOnePow • y := by
  have hy' : y ∈ (N.shiftObj 1).grading.piece p := (N.mem_shiftObj_piece_iff 1 p y).2 hy
  rw [inducedTwist, InternalGrading.koszulTwist_one_apply_of_mem _ hy',
    Int.cast_smul_eq_zsmul, ← Units.smul_def]

private theorem inducedTwist_apply_of_mem {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {p : ℤ} {x : N}
    (hx : x ∈ N.grading.piece p) :
    inducedTwist N x = -(p.negOnePow • x) := by
  have hx' : x ∈ N.grading.piece (p + 1 - 1) := by rwa [add_sub_cancel_right]
  rw [inducedTwist_apply_of_mem_shift hx', Int.negOnePow_add, Int.negOnePow_one, mul_neg, mul_one]
  rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp]

private theorem op_smul_comm_scalar {M : Type u} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] (r : R) (a : A) (x : M) :
    op a • (r • x) = r • (op a • x) := by
  calc op a • (r • x)
      = op a • ((r • (1 : Aᵐᵒᵖ)) • x) := by rw [smul_assoc, one_smul]
    _ = (op a * (r • (1 : Aᵐᵒᵖ))) • x := (mul_smul _ _ _).symm
    _ = (r • op a) • x := by
        congr 1
        apply unop_injective
        simp
    _ = r • (op a • x) := smul_assoc r (op a) x

private theorem inducedTwist_op_smul_of_mem {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (y : N) :
    inducedTwist N (op a • y) = q.negOnePow • (op a • inducedTwist N y) := by
  induction y using DirectSum.Decomposition.inductionOn N.grading.piece with
  | zero => simp
  | add y₁ y₂ hy₁ hy₂ => rw [smul_add, map_add, hy₁, hy₂, map_add, smul_add, smul_add]
  | @homogeneous p y =>
    have hay : op a • (y : N) ∈ N.grading.piece (p + q) :=
      op_smul_mem_of_mem_graded ha y.2
    rw [inducedTwist_apply_of_mem hay, inducedTwist_apply_of_mem y.2, Int.negOnePow_add]
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;> simp [hp, hq]

include h in
private theorem op_map_mul_smul_inducedTwist {a b : A} (y : N) :
    op (d (a * b)) • inducedTwist N y =
      op (d a * b) • inducedTwist N y + op (d b) • inducedTwist N (op a • y) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a₁ a₂ ha₁ ha₂ =>
    rw [add_mul, map_add, MulOpposite.op_add, add_smul, ha₁, ha₂, map_add, add_mul,
      MulOpposite.op_add, add_smul, MulOpposite.op_add, add_smul, map_add, smul_add]
    abel
  | @homogeneous q a =>
    rw [h.leibniz a.2 b, MulOpposite.op_add, add_smul, inducedTwist_op_smul_of_mem a.2 y]
    congr 1
    rcases Int.units_eq_one_or q.negOnePow with hq | hq <;> simp [hq, mul_smul]

private noncomputable instance : SMul Aᵐᵒᵖ (InducedCarrier h N) where
  smul s z := ⟨s • z.fst + op (d s.unop) • inducedTwist N z.snd, s • z.snd⟩

@[simp]
private theorem inducedCarrier_op_smul_fst (a : A) (z : InducedCarrier h N) :
    (op a • z).fst = op a • z.fst + op (d a) • inducedTwist N z.snd := rfl

@[simp]
private theorem inducedCarrier_op_smul_snd (a : A) (z : InducedCarrier h N) :
    (op a • z).snd = op a • z.snd := rfl

private noncomputable instance : Module Aᵐᵒᵖ (InducedCarrier h N) where
  one_smul z := InducedCarrier.ext
    (by
      rw [← MulOpposite.op_one, inducedCarrier_op_smul_fst, h.map_one_eq_zero,
        MulOpposite.op_zero, zero_smul, add_zero, MulOpposite.op_one, one_smul])
    (one_smul Aᵐᵒᵖ z.snd)
  mul_smul s t z := by
    obtain ⟨b, rfl⟩ := MulOpposite.op_surjective s
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective t
    refine InducedCarrier.ext ?_ (mul_smul (op b) (op a) z.snd)
    rw [← MulOpposite.op_mul, inducedCarrier_op_smul_fst, inducedCarrier_op_smul_fst,
      inducedCarrier_op_smul_snd, inducedCarrier_op_smul_fst, smul_add,
      ← mul_smul, ← mul_smul, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
      op_map_mul_smul_inducedTwist h N z.snd, add_assoc]
  smul_zero s := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    exact InducedCarrier.ext (by simp) (smul_zero (op a))
  smul_add s z₁ z₂ := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    refine InducedCarrier.ext ?_ (smul_add (op a) z₁.snd z₂.snd)
    simp only [inducedCarrier_op_smul_fst, inducedCarrier_add_fst, inducedCarrier_add_snd,
      map_add, smul_add]
    abel
  add_smul s t z := by
    obtain ⟨b, rfl⟩ := MulOpposite.op_surjective s
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective t
    refine InducedCarrier.ext ?_ (add_smul (op b) (op a) z.snd)
    rw [← MulOpposite.op_add, inducedCarrier_op_smul_fst, inducedCarrier_add_fst,
      inducedCarrier_op_smul_fst, inducedCarrier_op_smul_fst, map_add, MulOpposite.op_add,
      MulOpposite.op_add, add_smul, add_smul]
    abel
  zero_smul z := InducedCarrier.ext
    (by
      rw [← MulOpposite.op_zero, inducedCarrier_op_smul_fst, map_zero, MulOpposite.op_zero,
        zero_smul, zero_smul, add_zero, inducedCarrier_zero_fst])
    (zero_smul Aᵐᵒᵖ z.snd)

private instance : IsScalarTower R Aᵐᵒᵖ (InducedCarrier h N) where
  smul_assoc r s z := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    refine InducedCarrier.ext ?_ (smul_assoc r (op a) z.snd)
    have hop (x : A) : op (r • x) = r • op x := rfl
    rw [← hop a, inducedCarrier_op_smul_fst, inducedCarrier_smul_fst, inducedCarrier_op_smul_fst,
      map_smul, hop (d a), hop a, smul_add, smul_assoc, smul_assoc]

private instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (inducedGrading h N).piece where
  smul_mem {q p} s z hs hz := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at hs
    obtain ⟨hx, hy⟩ := (mem_inducedGrading_piece_iff h N p z).1 hz
    refine (mem_inducedGrading_piece_iff h N (q + p) (op a • z)).2 ⟨?_, ?_⟩
    · rw [inducedCarrier_op_smul_fst, add_comm q p]
      refine Submodule.add_mem _ (op_smul_mem_of_mem_graded hs hx) ?_
      rw [inducedTwist_apply_of_mem_shift hy]
      have hda : op (d a) • z.snd ∈ N.grading.piece (p + q) := by
        simpa [show p - 1 + (q + 1) = p + q by omega] using
          op_smul_mem_of_mem_graded (h.map_mem hs) hy
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simpa [hp] using Submodule.neg_mem _ hda
    · rw [inducedCarrier_op_smul_snd]
      simpa [show p - 1 + q = q + p - 1 by omega] using op_smul_mem_of_mem_graded hs hy

private noncomputable def inducedDifferential :
    InducedCarrier h N →ₗ[R] InducedCarrier h N where
  toFun z := ⟨op w • z.snd, z.fst⟩
  map_add' z₁ z₂ := InducedCarrier.ext (smul_add (op w) z₁.snd z₂.snd) rfl
  map_smul' r z := InducedCarrier.ext (op_smul_comm_scalar r w z.snd) rfl

private theorem isCurvedDGRightModule_induced :
    IsCurvedDGRightModule h (inducedGrading h N).piece (inducedDifferential h N) where
  isHomogeneous := LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
    obtain ⟨hx, hy⟩ := (mem_inducedGrading_piece_iff h N p z).1 hz
    refine (mem_inducedGrading_piece_iff h N (p + 1) (inducedDifferential h N z)).2 ⟨?_, ?_⟩
    · dsimp only [inducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      simpa [show p - 1 + 2 = p + 1 by omega] using
        op_smul_mem_of_mem_graded h.curvature_mem hy
    · dsimp only [inducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      rwa [add_sub_cancel_right]
  leibniz {p z} hz a := by
    obtain ⟨hx, hy⟩ := (mem_inducedGrading_piece_iff h N p z).1 hz
    have hσx : inducedTwist N z.fst = -(p.negOnePow • z.fst) := inducedTwist_apply_of_mem hx
    have hσy : inducedTwist N z.snd = p.negOnePow • z.snd := inducedTwist_apply_of_mem_shift hy
    refine InducedCarrier.ext ?_ ?_
    · dsimp only [inducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      have hsq : op (w * a) • z.snd + op (d (d a)) • z.snd = op (a * w) • z.snd := by
        rw [← add_smul, ← MulOpposite.op_add, h.sq_eq a, add_sub_cancel]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp
      · simp only [inducedCarrier_op_smul_fst, inducedCarrier_op_smul_snd,
          inducedCarrier_add_fst, hσx, hσy, hp, one_smul, smul_neg, ← mul_smul,
          ← MulOpposite.op_mul]
        rw [← hsq]
        abel
      · simp only [inducedCarrier_op_smul_fst, inducedCarrier_op_smul_snd,
          inducedCarrier_add_fst, inducedCarrier_neg_fst, hσx, hσy, hp,
          Units.neg_smul, one_smul, neg_neg, smul_neg, neg_add_rev, ← mul_smul,
          ← MulOpposite.op_mul]
        rw [← hsq]
        abel
    · dsimp only [inducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simp [hσy, hp]
  sq_eq z := InducedCarrier.ext
    (by simp [inducedDifferential, h.map_curvature])
    rfl

private noncomputable abbrev inducedObjCore : CurvedDGRightModuleCat.{u, u, u} h where
  carrier := InducedCarrier h N
  grading := (inducedGrading h N).piece
  differential := inducedDifferential h N
  isCurvedDGRightModule := isCurvedDGRightModule_induced h N

/-- **The freely induced curved right module** `G⁺(N)` on a graded right module `N`. -/
noncomputable def inducedObj : CurvedDGRightModuleCat.{u, u, u} h :=
  inducedObjCore h N

end Carrier

section Functor

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private theorem inducedTwist_map {N₁ N₂ : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} (φ : N₁ ⟶ N₂) (y : N₁) :
    inducedTwist N₂ (φ.hom y) = φ.hom (inducedTwist N₁ y) := by
  induction y using DirectSum.Decomposition.inductionOn N₁.grading.piece with
  | zero => simp
  | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
  | @homogeneous p y =>
    have hy₂ : φ.hom (y : N₁) ∈ N₂.grading.piece p := GradedModuleCat.map_mem φ y.2
    rw [inducedTwist_apply_of_mem hy₂, inducedTwist_apply_of_mem y.2, map_neg]
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp]

private noncomputable def inducedMap {N₁ N₂ : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} (φ : N₁ ⟶ N₂) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N₁) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N₂) := by
  let L : InducedCarrier h N₁ →ₗ[Aᵐᵒᵖ] InducedCarrier h N₂ :=
    { toFun z := ⟨φ.hom z.fst, φ.hom z.snd⟩
      map_add' z₁ z₂ := InducedCarrier.ext (φ.hom.map_add _ _) (φ.hom.map_add _ _)
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        refine InducedCarrier.ext ?_ (φ.hom.map_smul (op a) z.snd)
        simp only [RingHom.id_apply, inducedCarrier_op_smul_fst, map_add, φ.hom.map_smul,
          inducedTwist_map φ z.snd] }
  exact closedHomOf (M := inducedObjCore h N₁) (N := inducedObjCore h N₂) L
    (fun p z hz ↦ by
      obtain ⟨hx, hy⟩ := (mem_inducedGrading_piece_iff h N₁ p z).1 hz
      exact (mem_inducedGrading_piece_iff h N₂ p (L z)).2
        ⟨GradedModuleCat.map_mem φ hx, GradedModuleCat.map_mem φ hy⟩)
    (fun z ↦ InducedCarrier.ext (φ.hom.map_smul (op w) z.snd).symm rfl)

/-- **The induction functor** `G⁺` from graded right modules to the closed category of curved
right modules. -/
noncomputable def induced :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N)
  map := inducedMap
  map_id N := by
    unfold inducedMap inducedObj
    exact closedHom_ext fun z ↦ InducedCarrier.ext (by simp) (by simp)
  map_comp φ ψ := by
    unfold inducedMap inducedObj
    exact closedHom_ext fun z ↦ InducedCarrier.ext (by simp) (by simp)

/-- On objects, `induced` wraps `inducedObj` in the closed degree-zero category. -/
@[simp]
theorem induced_obj (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (induced (h := h)).obj N =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) :=
  (rfl)

private noncomputable def inducedHomTo {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {M : CurvedDGRightModuleCat.{u, u, u} h}
    (α : N ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M := by
  let α₀ : N →ₗ[Aᵐᵒᵖ] M := α.hom
  let L : InducedCarrier h N →ₗ[Aᵐᵒᵖ] M :=
    { toFun z := α₀ z.fst + M.differential (α₀ z.snd)
      map_add' z₁ z₂ := by
        simp only [inducedCarrier_add_fst, inducedCarrier_add_snd, map_add]
        abel
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        simp only [RingHom.id_apply, inducedCarrier_op_smul_fst, inducedCarrier_op_smul_snd,
          map_add, α₀.map_smul]
        have hy : ∀ y : N, α₀ (op (d a) • inducedTwist N y) +
            M.differential (op a • α₀ y) = op a • M.differential (α₀ y) := by
          intro y
          induction y using DirectSum.Decomposition.inductionOn N.grading.piece with
          | zero => simp
          | add y₁ y₂ hy₁ hy₂ =>
            simp only [map_add, smul_add] at hy₁ hy₂ ⊢
            calc α₀ (op (d a) • inducedTwist N y₁) + α₀ (op (d a) • inducedTwist N y₂) +
                  (M.differential (op a • α₀ y₁) + M.differential (op a • α₀ y₂))
                = (α₀ (op (d a) • inducedTwist N y₁) + M.differential (op a • α₀ y₁)) +
                    (α₀ (op (d a) • inducedTwist N y₂) + M.differential (op a • α₀ y₂)) := by
                  abel
              _ = op a • M.differential (α₀ y₁) + op a • M.differential (α₀ y₂) := by
                  rw [hy₁, hy₂]
          | @homogeneous p y =>
            have hαy : α₀ (y : N) ∈ M.grading p := by
              simpa only [toGradedModuleCat_piece] using GradedModuleCat.map_mem α y.2
            rw [inducedTwist_apply_of_mem y.2, smul_neg, map_neg, α₀.map_smul,
              M.isCurvedDGRightModule.leibniz hαy a]
            rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp]
        rw [smul_add, ← α₀.map_smul (op (d a)), ← hy z.snd, add_assoc] }
  exact closedHomOf (M := inducedObjCore h N) (N := M) L
    (fun p z hz ↦ by
      dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
      obtain ⟨hx, hy⟩ := (mem_inducedGrading_piece_iff h N p z).1 hz
      have hαx : α₀ z.fst ∈ M.grading p := by
        simpa only [toGradedModuleCat_piece] using GradedModuleCat.map_mem α hx
      have hαy : α₀ z.snd ∈ M.grading (p - 1) := by
        simpa only [toGradedModuleCat_piece] using GradedModuleCat.map_mem α hy
      exact Submodule.add_mem _ hαx (by
        simpa [sub_add_cancel] using M.isCurvedDGRightModule.isHomogeneous.map_mem hαy))
    (fun z ↦ by
      dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk, inducedObjCore, inducedDifferential]
      rw [map_add, M.isCurvedDGRightModule.sq_eq, α₀.map_smul, add_comm])

private noncomputable def inducedGradedInl (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    N ⟶ toGradedModuleCat (inducedObj h N) :=
  let L : N →ₗ[Aᵐᵒᵖ] InducedCarrier h N :=
    { toFun x := ⟨x, 0⟩
      map_add' x₁ x₂ := InducedCarrier.ext rfl (add_zero 0).symm
      map_smul' s x := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        exact InducedCarrier.ext (by simp) (smul_zero (op a)).symm }
  GradedModuleCat.ofHom (M := N) (N := toGradedModuleCat (inducedObjCore h N)) L
    (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [add_zero, toGradedModuleCat_piece]
      exact (mem_inducedGrading_piece_iff h N p (L x)).2 ⟨hx, Submodule.zero_mem _⟩)

private noncomputable def inducedHomFrom {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h N) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    N ⟶ toGradedModuleCat M := by
  let f₀ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObjCore h N) ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M := f
  exact GradedModuleCat.ofHom
    { toFun x := closedHom f₀ ⟨x, 0⟩
      map_add' x₁ x₂ := by
        have hadd : (⟨x₁ + x₂, (0 : N)⟩ : InducedCarrier h N) = ⟨x₁, 0⟩ + ⟨x₂, 0⟩ :=
          InducedCarrier.ext rfl (add_zero 0).symm
        rw [hadd, (closedHom f₀).map_add]
      map_smul' s x := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        have hsmul : (⟨op a • x, (0 : N)⟩ : InducedCarrier h N) = op a • ⟨x, 0⟩ :=
          InducedCarrier.ext (by simp) (by simp)
        simp only [RingHom.id_apply, hsmul, (closedHom f₀).map_smul] }
    (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [add_zero, toGradedModuleCat_piece]
      exact closedHom_mem f₀ ((mem_inducedGrading_piece_iff h N p ⟨x, 0⟩).2
        ⟨hx, Submodule.zero_mem _⟩))

private theorem inducedHomFrom_eq {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : (induced (h := h)).obj N ⟶ M) :
    inducedHomFrom f = inducedGradedInl h N ≫ (forgetDifferential (h := h)).map f :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- **The induction–forgetful adjunction** `induced ⊣ forgetDifferential`. -/
noncomputable def inducedAdjForgetDifferential :
    induced (h := h) ⊣ forgetDifferential (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv N M :=
        { toFun f := inducedHomFrom f
          invFun α := inducedHomTo α
          left_inv f := by
            dsimp only
            unfold induced at f ⊢
            unfold inducedObj at f ⊢
            unfold inducedHomTo inducedHomFrom
            apply closedHom_ext
            intro z
            let z₀ : InducedCarrier h N := ⟨z.snd, 0⟩
            have hz : (⟨z.fst, 0⟩ : InducedCarrier h N) +
                (inducedObjCore h N).differential z₀ = z :=
              InducedCarrier.ext (by simp [z₀, inducedObjCore, inducedDifferential])
                (by simp [z₀, inducedObjCore, inducedDifferential])
            have hd : M.differential (closedHom (M := inducedObjCore h N) (N := M) f z₀) =
                closedHom (M := inducedObjCore h N) (N := M) f
                  ((inducedObjCore h N).differential z₀) :=
              differential_closedHom (M := inducedObjCore h N) (N := M) f z₀
            simp only [closedHom_closedHomOf, LinearMap.coe_mk, AddHom.coe_mk]
            rw [show (⟨z.snd, (0 : N)⟩ : InducedCarrier h N) = z₀ from rfl, hd,
              ← map_add (closedHom (M := inducedObjCore h N) (N := M) f), hz]
          right_inv α := by
            dsimp only
            apply GradedModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            unfold inducedHomFrom inducedHomTo
            simp }
      homEquiv_naturality_left_symm {N' N M} φ α := by
        unfold induced
        dsimp only
        unfold inducedMap inducedHomTo inducedObj
        apply closedHom_ext
        intro z
        simp
      homEquiv_naturality_right {N M M'} f ψ :=
        (inducedHomFrom_eq (f ≫ ψ)).trans <|
          (congrArg (inducedGradedInl h N ≫ ·)
            ((forgetDifferential (h := h)).map_comp f ψ)).trans <|
            (Category.assoc _ _ _).symm.trans <|
              congrArg (· ≫ (forgetDifferential (h := h)).map ψ) (inducedHomFrom_eq f).symm }

end Functor

section Properties

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

/-- **Contractibility of `G⁺(N)`.** Every freely induced curved right module is zero in the curved
homotopy category, contracted by `(x, y) ↦ (y, 0)`. -/
theorem isZero_homotopy_inducedObj :
    IsZero (DGHomotopyCategory.of R (inducedObj h N)) := by
  unfold inducedObj
  rw [isZero_homotopy_iff_exists_contraction]
  let k : InducedCarrier h N →ₗ[Aᵐᵒᵖ] InducedCarrier h N :=
    { toFun z := ⟨z.snd, 0⟩
      map_add' z₁ z₂ := InducedCarrier.ext rfl (add_zero 0).symm
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        exact InducedCarrier.ext (by simp) (smul_zero (op a)).symm }
  refine ⟨⟨k, ?_⟩, fun z ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p z hz
    obtain ⟨_, hy⟩ := (mem_inducedGrading_piece_iff h N p z).1 hz
    exact (mem_inducedGrading_piece_iff h N (p + -1) (k z)).2
      ⟨by simpa [k, sub_eq_add_neg] using hy, Submodule.zero_mem _⟩
  · exact InducedCarrier.ext
      (by simp [k, inducedObjCore, inducedDifferential])
      (by simp [k, inducedObjCore, inducedDifferential])

private noncomputable def inducedGradedSnd :
    toGradedModuleCat (inducedObj h N) ⟶ N.shiftObj 1 := by
  unfold inducedObj
  let L : InducedCarrier h N →ₗ[Aᵐᵒᵖ] N :=
    { toFun z := z.snd
      map_add' _ _ := rfl
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        rfl }
  exact GradedModuleCat.ofHom L
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [add_zero, N.mem_shiftObj_piece_iff]
      rw [toGradedModuleCat_piece] at hz
      exact ((mem_inducedGrading_piece_iff h N p z).1 hz).2)

/-- The short complex `N ⟶ (inducedObj h N)♯ ⟶ N{1}` of graded right modules underlying `G⁺(N)`. -/
noncomputable def inducedGradedShortComplex :
    ShortComplex (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :=
  ShortComplex.mk (inducedGradedInl h N) (inducedGradedSnd h N)
    (by
      unfold inducedGradedInl inducedGradedSnd inducedObj
      exact GradedModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl)

/-- The left term of `inducedGradedShortComplex h N` is `N`. -/
@[simp]
theorem inducedGradedShortComplex_X₁ : (inducedGradedShortComplex h N).X₁ = N := (rfl)

/-- The middle term of `inducedGradedShortComplex h N` is the underlying graded module of
`inducedObj h N`. -/
@[simp]
theorem inducedGradedShortComplex_X₂ :
    (inducedGradedShortComplex h N).X₂ = toGradedModuleCat (inducedObj h N) := (rfl)

/-- The right term of `inducedGradedShortComplex h N` is the grading shift `N{1}`. -/
@[simp]
theorem inducedGradedShortComplex_X₃ : (inducedGradedShortComplex h N).X₃ = N.shiftObj 1 := (rfl)

/-- After forgetting the differential, `G⁺(N)` sits in a short exact sequence
`0 ⟶ N ⟶ (inducedObj h N)♯ ⟶ N{1} ⟶ 0` of graded right modules. -/
theorem inducedGradedShortComplex_shortExact :
    (inducedGradedShortComplex h N).ShortExact := by
  unfold inducedGradedShortComplex inducedGradedInl inducedGradedSnd inducedObj
  exact
    { mono_f := (GradedModuleCat.mono_iff_injective _).2 fun x₁ x₂ hxy ↦
        congrArg InducedCarrier.fst hxy
      epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun y ↦
        ⟨(⟨0, y⟩ : InducedCarrier h N), rfl⟩
      exact := GradedModuleCat.exact_iff.2 fun z ↦
        ⟨fun hz ↦ ⟨z.fst, InducedCarrier.ext rfl hz.symm⟩,
          by rintro ⟨x, rfl⟩; rfl⟩ }

/-- If `P` is a projective graded right module, then `G⁺(P)` is graded-projective. -/
instance projective_toGradedModuleCat_inducedObj [Projective N] :
    Projective (toGradedModuleCat (inducedObj h N)) := by
  rw [projective_iff_hasProjectiveDimensionLT_one, ← inducedGradedShortComplex_X₂]
  have h₁ : HasProjectiveDimensionLT (inducedGradedShortComplex h N).X₁ 1 := by
    rw [inducedGradedShortComplex_X₁]
    infer_instance
  have h₃ : HasProjectiveDimensionLT (inducedGradedShortComplex h N).X₃ 1 := by
    rw [inducedGradedShortComplex_X₃]
    infer_instance
  exact (inducedGradedShortComplex_shortExact h N).hasProjectiveDimensionLT_X₂ 1 h₁ h₃

/-- If `P` is a projective graded right module, then `G⁺(P)` belongs to `gradedProjective`. -/
theorem gradedProjective_inducedObj [Projective N] :
    gradedProjective R h (DGHomotopyCategory.of R (inducedObj h N)) :=
  (gradedProjective_iff _).2 (projective_toGradedModuleCat_inducedObj h N)

end Properties

end TauCeti.CurvedDGRightModuleCat
