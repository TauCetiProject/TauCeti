/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
import TauCeti.Algebra.Module.GradedModule.Prod
import TauCeti.Algebra.Module.NatInt

/-!
# Coinduced curved differential graded right modules

For a curved differential graded algebra `(𝒜, d, w)` and a graded right module `N`, Positselski's
coinduction functor `G⁻` produces a curved right module `coinducedObj h N` right adjoint to
forgetting the differential. Its underlying graded `R`-module is `N ⊕ N{-1}` (with homogeneous
piece `Nₚ × Nₚ₊₁` in degree `p`), equipped with the twisted right `A`-action

`(u, v) · a = (u · a, v · a + (-1)^p (u · d a))` for `u ∈ Nₚ`

and the curved differential `d(u, v) = (v, u · w)`. Given any curved right module `M` and graded
morphism `β : M♯ ⟶ N`, the corresponding closed morphism `M ⟶ G⁻(N)` sends `m` to
`(β m, β (d_M m))`.

Because `forgetDifferential` is faithful, every unit component `M ⟶ G⁻(M♯)` is a monomorphism in
the abelian closed category of curved right modules. Moreover:

* `coinducedObj h N` is contractible via the degree-`(-1)` right-linear homotopy `(u, v) ↦ (0, u)`,
  hence zero in the curved homotopy category;
* after forgetting the differential, `coinducedObj h N` sits in a short exact sequence
  `0 ⟶ N{-1} ⟶ (coinducedObj h N)♯ ⟶ N ⟶ 0` of graded right modules, so `coinducedObj h I` is
  graded-injective whenever `I` is injective.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.coinducedObj`: the coinduced curved right module `G⁻(N)`.
* `TauCeti.CurvedDGRightModuleCat.coinduced`: the right adjoint functor from graded right modules
  to the closed category of curved right modules.
* `TauCeti.CurvedDGRightModuleCat.forgetDifferentialAdjCoinduced`: the adjunction
  `forgetDifferential ⊣ coinduced`.
* `TauCeti.CurvedDGRightModuleCat.coinducedGradedShortComplex`: the graded short complex
  `N{-1} ⟶ (coinducedObj h N)♯ ⟶ N`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: `coinducedObj h N` is zero in the
  curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.coinducedGradedShortComplex_shortExact`: the underlying graded
  module of `coinducedObj h N` is an extension of `N` by `N{-1}`.
* `TauCeti.CurvedDGRightModuleCat.injective_toGradedModuleCat_coinducedObj`: `coinducedObj h I` is
  graded-injective when `I` is injective.

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

/-- Private carrier of `G⁻(N)` wrapping `N × N` so its twisted right `A`-action does not conflict
with the componentwise product action. -/
@[ext]
private structure CoinducedCarrier (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) where
  fst : N
  snd : N

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

private instance : Zero (CoinducedCarrier h N) := ⟨⟨0, 0⟩⟩
private instance : Add (CoinducedCarrier h N) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private instance : Neg (CoinducedCarrier h N) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private instance : Sub (CoinducedCarrier h N) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private instance : SMul ℕ (CoinducedCarrier h N) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private instance : SMul ℤ (CoinducedCarrier h N) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩

private instance : AddCommGroup (CoinducedCarrier h N) :=
  Function.Injective.addCommGroup (fun z : CoinducedCarrier h N ↦ (z.fst, z.snd))
    (fun _ _ hxy ↦ CoinducedCarrier.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance : SMul R (CoinducedCarrier h N) := ⟨fun r z ↦ ⟨r • z.fst, r • z.snd⟩⟩

private instance : Module R (CoinducedCarrier h N) :=
  Function.Injective.module R
    { toFun := fun z : CoinducedCarrier h N ↦ (z.fst, z.snd)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ hxy ↦ CoinducedCarrier.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    (fun _ _ ↦ rfl)

@[simp]
private theorem coinducedCarrier_zero_fst : (0 : CoinducedCarrier h N).fst = 0 := rfl
@[simp]
private theorem coinducedCarrier_zero_snd : (0 : CoinducedCarrier h N).snd = 0 := rfl
@[simp]
private theorem coinducedCarrier_add_fst (x y : CoinducedCarrier h N) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp]
private theorem coinducedCarrier_add_snd (x y : CoinducedCarrier h N) :
    (x + y).snd = x.snd + y.snd := rfl
@[simp]
private theorem coinducedCarrier_neg_fst (z : CoinducedCarrier h N) :
    (-z).fst = -z.fst := rfl
@[simp]
private theorem coinducedCarrier_neg_snd (z : CoinducedCarrier h N) :
    (-z).snd = -z.snd := rfl
@[simp]
private theorem coinducedCarrier_smul_fst (r : R) (z : CoinducedCarrier h N) :
    (r • z).fst = r • z.fst := rfl
@[simp]
private theorem coinducedCarrier_smul_snd (r : R) (z : CoinducedCarrier h N) :
    (r • z).snd = r • z.snd := rfl

private def coinducedProdEquiv : CoinducedCarrier h N ≃ₗ[R] N × (N.shiftObj (-1)) where
  toFun z := (z.fst, z.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def coinducedGrading : InternalGrading R (CoinducedCarrier h N) ℤ :=
  (N.grading.prod (N.shiftObj (-1)).grading).map (coinducedProdEquiv h N).symm

private theorem mem_coinducedGrading_piece_iff (p : ℤ) (z : CoinducedCarrier h N) :
    z ∈ (coinducedGrading h N).piece p ↔
      z.fst ∈ N.grading.piece p ∧ z.snd ∈ N.grading.piece (p + 1) := by
  rw [coinducedGrading, InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.prod_piece, Submodule.mem_prod, N.mem_shiftObj_piece_iff, sub_neg_eq_add]
  rfl

/-- Koszul twist `u ↦ (-1)^p u` for `u ∈ Nₚ`. -/
private noncomputable def coinducedTwist : N →ₗ[R] N :=
  N.grading.koszulTwist 1

private theorem coinducedTwist_apply_of_mem {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {p : ℤ} {u : N}
    (hu : u ∈ N.grading.piece p) :
    coinducedTwist N u = p.negOnePow • u := by
  rw [coinducedTwist, InternalGrading.koszulTwist_one_apply_of_mem _ hu,
    Int.cast_smul_eq_zsmul, ← Units.smul_def]

private theorem coinducedTwist_apply_of_mem_succ {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {p : ℤ} {v : N}
    (hv : v ∈ N.grading.piece (p + 1)) :
    coinducedTwist N v = -(p.negOnePow • v) := by
  rw [coinducedTwist_apply_of_mem hv, Int.negOnePow_add, Int.negOnePow_one, mul_neg, mul_one]
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

private theorem coinducedTwist_op_smul_of_mem {N : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (u : N) :
    coinducedTwist N (op a • u) = q.negOnePow • (op a • coinducedTwist N u) := by
  induction u using DirectSum.Decomposition.inductionOn N.grading.piece with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => rw [smul_add, map_add, hu₁, hu₂, map_add, smul_add, smul_add]
  | @homogeneous p u =>
    have hau : op a • (u : N) ∈ N.grading.piece (p + q) :=
      op_smul_mem_of_mem_graded ha u.2
    rw [coinducedTwist_apply_of_mem hau, coinducedTwist_apply_of_mem u.2,
      Int.negOnePow_add, mul_comm p.negOnePow, mul_smul]
    congr 1
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp]

include h in
private theorem op_map_mul_smul_coinducedTwist {a b : A} (u : N) :
    op (d (a * b)) • coinducedTwist N u =
      op (d a * b) • coinducedTwist N u + op (d b) • coinducedTwist N (op a • u) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a₁ a₂ ha₁ ha₂ =>
    rw [add_mul, map_add, MulOpposite.op_add, add_smul, ha₁, ha₂, map_add, add_mul,
      MulOpposite.op_add, add_smul, MulOpposite.op_add, add_smul, map_add, smul_add]
    abel
  | @homogeneous q a =>
    rw [h.leibniz a.2 b, MulOpposite.op_add, add_smul, coinducedTwist_op_smul_of_mem a.2 u]
    congr 1
    rcases Int.units_eq_one_or q.negOnePow with hq | hq <;> simp [hq, mul_smul]

private noncomputable instance : SMul Aᵐᵒᵖ (CoinducedCarrier h N) where
  smul s z := ⟨s • z.fst, s • z.snd + op (d s.unop) • coinducedTwist N z.fst⟩

@[simp]
private theorem coinducedCarrier_op_smul_fst (a : A) (z : CoinducedCarrier h N) :
    (op a • z).fst = op a • z.fst := rfl

@[simp]
private theorem coinducedCarrier_op_smul_snd (a : A) (z : CoinducedCarrier h N) :
    (op a • z).snd = op a • z.snd + op (d a) • coinducedTwist N z.fst := rfl

private noncomputable instance : Module Aᵐᵒᵖ (CoinducedCarrier h N) where
  one_smul z := CoinducedCarrier.ext
    (one_smul Aᵐᵒᵖ z.fst)
    (by
      rw [← MulOpposite.op_one, coinducedCarrier_op_smul_snd, h.map_one_eq_zero,
        MulOpposite.op_zero, zero_smul, add_zero, MulOpposite.op_one, one_smul])
  mul_smul s t z := by
    obtain ⟨b, rfl⟩ := MulOpposite.op_surjective s
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective t
    refine CoinducedCarrier.ext (mul_smul (op b) (op a) z.fst) ?_
    rw [← MulOpposite.op_mul, coinducedCarrier_op_smul_snd, coinducedCarrier_op_smul_snd,
      coinducedCarrier_op_smul_fst, coinducedCarrier_op_smul_snd, smul_add,
      ← mul_smul, ← mul_smul, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
      op_map_mul_smul_coinducedTwist h N z.fst, add_assoc]
  smul_zero s := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    exact CoinducedCarrier.ext (smul_zero (op a)) (by simp)
  smul_add s z₁ z₂ := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    refine CoinducedCarrier.ext (smul_add (op a) z₁.fst z₂.fst) ?_
    simp only [coinducedCarrier_op_smul_snd, coinducedCarrier_add_fst, coinducedCarrier_add_snd,
      map_add, smul_add]
    abel
  add_smul s t z := by
    obtain ⟨b, rfl⟩ := MulOpposite.op_surjective s
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective t
    refine CoinducedCarrier.ext (add_smul (op b) (op a) z.fst) ?_
    rw [← MulOpposite.op_add, coinducedCarrier_op_smul_snd, coinducedCarrier_add_snd,
      coinducedCarrier_op_smul_snd, coinducedCarrier_op_smul_snd, map_add, MulOpposite.op_add,
      MulOpposite.op_add, add_smul, add_smul]
    abel
  zero_smul z := CoinducedCarrier.ext (zero_smul Aᵐᵒᵖ z.fst)
    (by
      rw [← MulOpposite.op_zero, coinducedCarrier_op_smul_snd, map_zero, MulOpposite.op_zero,
        zero_smul, zero_smul, add_zero, coinducedCarrier_zero_snd])

private instance : IsScalarTower R Aᵐᵒᵖ (CoinducedCarrier h N) where
  smul_assoc r s z := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    refine CoinducedCarrier.ext (smul_assoc r (op a) z.fst) ?_
    have hop (x : A) : op (r • x) = r • op x := rfl
    rw [← hop a, coinducedCarrier_op_smul_snd, coinducedCarrier_smul_snd,
      coinducedCarrier_op_smul_snd, map_smul, hop (d a), hop a, smul_add, smul_assoc, smul_assoc]

private instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (coinducedGrading h N).piece where
  smul_mem {q p} s z hs hz := by
    obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
    rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at hs
    obtain ⟨hu, hv⟩ := (mem_coinducedGrading_piece_iff h N p z).1 hz
    refine (mem_coinducedGrading_piece_iff h N (q + p) (op a • z)).2 ⟨?_, ?_⟩
    · rw [coinducedCarrier_op_smul_fst, add_comm q p]
      exact op_smul_mem_of_mem_graded hs hu
    · rw [coinducedCarrier_op_smul_snd]
      refine Submodule.add_mem _ ?_ ?_
      · simpa [show p + 1 + q = q + p + 1 by omega] using op_smul_mem_of_mem_graded hs hv
      · rw [coinducedTwist_apply_of_mem hu]
        have hda : op (d a) • z.fst ∈ N.grading.piece (q + p + 1) := by
          simpa [show p + (q + 1) = q + p + 1 by omega] using
            op_smul_mem_of_mem_graded (h.map_mem hs) hu
        rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
          simpa [hp] using Submodule.neg_mem _ hda

private noncomputable def coinducedDifferential :
    CoinducedCarrier h N →ₗ[R] CoinducedCarrier h N where
  toFun z := ⟨z.snd, op w • z.fst⟩
  map_add' z₁ z₂ := CoinducedCarrier.ext rfl (smul_add (op w) z₁.fst z₂.fst)
  map_smul' r z := CoinducedCarrier.ext rfl (op_smul_comm_scalar r w z.fst)

private theorem isCurvedDGRightModule_coinduced :
    IsCurvedDGRightModule h (coinducedGrading h N).piece (coinducedDifferential h N) where
  isHomogeneous := LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
    obtain ⟨hu, hv⟩ := (mem_coinducedGrading_piece_iff h N p z).1 hz
    refine (mem_coinducedGrading_piece_iff h N (p + 1) (coinducedDifferential h N z)).2 ⟨hv, ?_⟩
    dsimp only [coinducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
    simpa [add_assoc] using op_smul_mem_of_mem_graded h.curvature_mem hu
  leibniz {p z} hz a := by
    obtain ⟨hu, hv⟩ := (mem_coinducedGrading_piece_iff h N p z).1 hz
    have hτu : coinducedTwist N z.fst = p.negOnePow • z.fst := coinducedTwist_apply_of_mem hu
    have hτv : coinducedTwist N z.snd = -(p.negOnePow • z.snd) :=
      coinducedTwist_apply_of_mem_succ hv
    refine CoinducedCarrier.ext ?_ ?_
    · dsimp only [coinducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simp [hτu, hp]
    · dsimp only [coinducedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
      have hsq : op (w * a) • z.fst + op (d (d a)) • z.fst = op (a * w) • z.fst := by
        rw [← add_smul, ← MulOpposite.op_add, h.sq_eq a, add_sub_cancel]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp
      · simp only [coinducedCarrier_op_smul_fst, coinducedCarrier_op_smul_snd,
          coinducedCarrier_add_snd, hτu, hτv, hp, one_smul, smul_neg, ← mul_smul,
          ← MulOpposite.op_mul]
        rw [← hsq]
        abel
      · simp only [coinducedCarrier_op_smul_fst, coinducedCarrier_op_smul_snd,
          coinducedCarrier_add_snd, coinducedCarrier_neg_snd, hτu, hτv,
          hp, Units.neg_smul, one_smul, neg_neg, smul_neg, neg_add_rev, ← mul_smul,
          ← MulOpposite.op_mul]
        rw [← hsq]
        abel
  sq_eq z := CoinducedCarrier.ext rfl (by simp [coinducedDifferential, h.map_curvature])

private noncomputable abbrev coinducedObjCore : CurvedDGRightModuleCat.{u, u, u} h where
  carrier := CoinducedCarrier h N
  grading := (coinducedGrading h N).piece
  differential := coinducedDifferential h N
  isCurvedDGRightModule := isCurvedDGRightModule_coinduced h N

/-- **The coinduced curved right module** `G⁻(N)` on a graded right module `N`. -/
noncomputable def coinducedObj : CurvedDGRightModuleCat.{u, u, u} h :=
  coinducedObjCore h N

end Carrier

section Functor

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private theorem coinducedTwist_map {N₁ N₂ : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} (φ : N₁ ⟶ N₂) (u : N₁) :
    coinducedTwist N₂ (φ.hom u) = φ.hom (coinducedTwist N₁ u) := by
  induction u using DirectSum.Decomposition.inductionOn N₁.grading.piece with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, hu₁, hu₂]
  | @homogeneous p u =>
    have hu₂ : φ.hom (u : N₁) ∈ N₂.grading.piece p := GradedModuleCat.map_mem φ u.2
    rw [coinducedTwist_apply_of_mem hu₂, coinducedTwist_apply_of_mem u.2]
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp]

private noncomputable def coinducedMap {N₁ N₂ : GradedModuleCat.{u}
    (InternalGrading.ofDecomposition 𝒜).opposite.piece} (φ : N₁ ⟶ N₂) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₁) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N₂) := by
  let L : CoinducedCarrier h N₁ →ₗ[Aᵐᵒᵖ] CoinducedCarrier h N₂ :=
    { toFun z := ⟨φ.hom z.fst, φ.hom z.snd⟩
      map_add' z₁ z₂ := CoinducedCarrier.ext (φ.hom.map_add _ _) (φ.hom.map_add _ _)
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        refine CoinducedCarrier.ext (φ.hom.map_smul (op a) z.fst) ?_
        simp only [RingHom.id_apply, coinducedCarrier_op_smul_snd, map_add, φ.hom.map_smul,
          coinducedTwist_map φ z.fst] }
  exact closedHomOf (M := coinducedObjCore h N₁) (N := coinducedObjCore h N₂) L
    (fun p z hz ↦ by
      obtain ⟨hu, hv⟩ := (mem_coinducedGrading_piece_iff h N₁ p z).1 hz
      exact (mem_coinducedGrading_piece_iff h N₂ p (L z)).2
        ⟨GradedModuleCat.map_mem φ hu, GradedModuleCat.map_mem φ hv⟩)
    (fun z ↦ CoinducedCarrier.ext rfl (φ.hom.map_smul (op w) z.fst).symm)

/-- **The coinduction functor** `G⁻` from graded right modules to the closed category of curved
right modules. -/
noncomputable def coinduced :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj N := ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)
  map := coinducedMap
  map_id N := by
    unfold coinducedMap coinducedObj
    exact closedHom_ext fun z ↦ CoinducedCarrier.ext (by simp) (by simp)
  map_comp φ ψ := by
    unfold coinducedMap coinducedObj
    exact closedHom_ext fun z ↦ CoinducedCarrier.ext (by simp) (by simp)

/-- On objects, `coinduced` wraps `coinducedObj` in the closed degree-zero category. -/
@[simp]
theorem coinduced_obj (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinduced (h := h)).obj N =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) :=
  (rfl)

private noncomputable def coinducedHomTo {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (β : toGradedModuleCat M ⟶ N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N) := by
  let β₀ : M →ₗ[Aᵐᵒᵖ] N := β.hom
  let L : M →ₗ[Aᵐᵒᵖ] CoinducedCarrier h N :=
    { toFun m := ⟨β₀ m, β₀ (M.differential m)⟩
      map_add' m₁ m₂ := CoinducedCarrier.ext (β₀.map_add _ _) (by simp [map_add])
      map_smul' s m := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        refine CoinducedCarrier.ext (β₀.map_smul (op a) m) ?_
        simp only [RingHom.id_apply, coinducedCarrier_op_smul_snd]
        induction m using DirectSum.Decomposition.inductionOn M.grading with
        | zero => simp
        | add m₁ m₂ hm₁ hm₂ =>
          simp only [smul_add, map_add] at hm₁ hm₂ ⊢
          rw [hm₁, hm₂]
          abel
        | @homogeneous p m =>
          have hβm : β₀ (m : M) ∈ N.grading.piece p :=
            GradedModuleCat.map_mem β (by simpa only [toGradedModuleCat_piece] using m.2)
          rw [M.isCurvedDGRightModule.leibniz m.2 a, map_add, β₀.map_smul,
            coinducedTwist_apply_of_mem hβm]
          rcases Int.units_eq_one_or p.negOnePow with hp | hp <;> simp [hp, β₀.map_smul] }
  exact closedHomOf (M := M) (N := coinducedObjCore h N) L
    (fun p m hm ↦ by
      have hβm : β₀ m ∈ N.grading.piece p :=
        GradedModuleCat.map_mem β (by simpa only [toGradedModuleCat_piece] using hm)
      have hdm : M.differential m ∈ M.grading (p + 1) :=
        M.isCurvedDGRightModule.isHomogeneous.map_mem hm
      have hβdm : β₀ (M.differential m) ∈ N.grading.piece (p + 1) :=
        GradedModuleCat.map_mem β (by simpa only [toGradedModuleCat_piece] using hdm)
      exact (mem_coinducedGrading_piece_iff h N p (L m)).2 ⟨hβm, hβdm⟩)
    (fun m ↦ CoinducedCarrier.ext rfl (by
      dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk, coinducedObjCore, coinducedDifferential]
      rw [M.isCurvedDGRightModule.sq_eq, β₀.map_smul]))

private noncomputable def coinducedGradedFst (h : IsCurvedDGAlgebra 𝒜 d w)
    (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h N) ⟶ N :=
  let L : CoinducedCarrier h N →ₗ[Aᵐᵒᵖ] N :=
    { toFun z := z.fst
      map_add' _ _ := rfl
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        rfl }
  GradedModuleCat.ofHom (M := toGradedModuleCat (coinducedObjCore h N)) (N := N) L
    (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
      rw [add_zero]
      rw [toGradedModuleCat_piece] at hz
      exact ((mem_coinducedGrading_piece_iff h N p z).1 hz).1)

private noncomputable def coinducedHomFrom {M : CurvedDGRightModuleCat.{u, u, u} h}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h N)) :
    toGradedModuleCat M ⟶ N := by
  let f₀ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObjCore h N) := f
  exact GradedModuleCat.ofHom
    { toFun m := (closedHom f₀ m).fst
      map_add' m₁ m₂ := congrArg CoinducedCarrier.fst ((closedHom f₀).map_add m₁ m₂)
      map_smul' s m := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        exact congrArg CoinducedCarrier.fst ((closedHom f₀).map_smul (op a) m) }
    (LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
      rw [add_zero]
      rw [toGradedModuleCat_piece] at hm
      exact ((mem_coinducedGrading_piece_iff h N p (closedHom f₀ m)).1 (closedHom_mem f₀ hm)).1)

private theorem coinducedHomFrom_eq
    {M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    {N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (f : M ⟶ (coinduced (h := h)).obj N) :
    coinducedHomFrom f = (forgetDifferential (h := h)).map f ≫ coinducedGradedFst h N :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- **The forgetful–coinduction adjunction** `forgetDifferential ⊣ coinduced`. -/
noncomputable def forgetDifferentialAdjCoinduced :
    forgetDifferential (h := h) ⊣ coinduced (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun β := coinducedHomTo β
          invFun f := coinducedHomFrom f
          left_inv β := by
            dsimp only
            apply GradedModuleCat.hom_ext
            apply LinearMap.ext
            intro m
            unfold coinducedHomFrom coinducedHomTo
            simp
          right_inv f := by
            dsimp only
            unfold coinduced at f ⊢
            unfold coinducedObj at f ⊢
            unfold coinducedHomTo coinducedHomFrom
            apply closedHom_ext
            intro m
            have hd : (coinducedObjCore h N).differential
                (closedHom (M := M) (N := coinducedObjCore h N) f m) =
                closedHom (M := M) (N := coinducedObjCore h N) f (M.differential m) :=
              differential_closedHom (M := M) (N := coinducedObjCore h N) f m
            have hd' : (closedHom (M := M) (N := coinducedObjCore h N) f m).snd =
                (closedHom (M := M) (N := coinducedObjCore h N) f (M.differential m)).fst :=
              congrArg CoinducedCarrier.fst hd
            simp only [closedHom_closedHomOf, LinearMap.coe_mk, AddHom.coe_mk]
            exact CoinducedCarrier.ext rfl hd'.symm }
      homEquiv_naturality_left_symm {M' M N} ψ f :=
        (coinducedHomFrom_eq (ψ ≫ f)).trans <|
          (congrArg (· ≫ coinducedGradedFst h N)
            ((forgetDifferential (h := h)).map_comp ψ f)).trans <|
            (Category.assoc _ _ _).trans <|
              congrArg ((forgetDifferential (h := h)).map ψ ≫ ·) (coinducedHomFrom_eq f).symm
      homEquiv_naturality_right {M N N'} β φ := by
        unfold coinduced
        dsimp only
        unfold coinducedMap coinducedHomTo coinducedObj
        exact closedHom_ext fun m ↦ CoinducedCarrier.ext (by simp) (by simp) }

end Functor

section Properties

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

/-- **Contractibility of `G⁻(N)`.** Every coinduced curved right module is zero in the curved
homotopy category, contracted by `(u, v) ↦ (0, u)`. -/
theorem isZero_homotopy_coinducedObj :
    IsZero (DGHomotopyCategory.of R (coinducedObj h N)) := by
  unfold coinducedObj
  rw [isZero_homotopy_iff_exists_contraction]
  let k : CoinducedCarrier h N →ₗ[Aᵐᵒᵖ] CoinducedCarrier h N :=
    { toFun z := ⟨0, z.fst⟩
      map_add' z₁ z₂ := CoinducedCarrier.ext (add_zero 0).symm rfl
      map_smul' s z := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        exact CoinducedCarrier.ext (smul_zero (op a)).symm (by simp) }
  refine ⟨⟨k, ?_⟩, fun z ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p z hz
    obtain ⟨hu, _⟩ := (mem_coinducedGrading_piece_iff h N p z).1 hz
    exact (mem_coinducedGrading_piece_iff h N (p + -1) (k z)).2
      ⟨Submodule.zero_mem _, by simpa [k] using hu⟩
  · exact CoinducedCarrier.ext
      (by simp [k, coinducedObjCore, coinducedDifferential])
      (by simp [k, coinducedObjCore, coinducedDifferential])

private noncomputable def coinducedGradedInr :
    N.shiftObj (-1) ⟶ toGradedModuleCat (coinducedObj h N) := by
  unfold coinducedObj
  let L : N →ₗ[Aᵐᵒᵖ] CoinducedCarrier h N :=
    { toFun v := ⟨0, v⟩
      map_add' v₁ v₂ := CoinducedCarrier.ext (add_zero 0).symm rfl
      map_smul' s v := by
        obtain ⟨a, rfl⟩ := MulOpposite.op_surjective s
        exact CoinducedCarrier.ext (smul_zero (op a)).symm (by simp) }
  exact GradedModuleCat.ofHom L
    (LinearMap.isHomogeneous_def.2 fun p v hv ↦ by
      rw [add_zero, toGradedModuleCat_piece]
      rw [N.mem_shiftObj_piece_iff, sub_neg_eq_add] at hv
      exact (mem_coinducedGrading_piece_iff h N p (L v)).2 ⟨Submodule.zero_mem _, hv⟩)

/-- The short complex `N{-1} ⟶ (coinducedObj h N)♯ ⟶ N` of graded right modules underlying
`G⁻(N)`. -/
noncomputable def coinducedGradedShortComplex :
    ShortComplex (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :=
  ShortComplex.mk (coinducedGradedInr h N) (coinducedGradedFst h N)
    (by
      unfold coinducedGradedInr coinducedGradedFst coinducedObj
      exact GradedModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl)

/-- The left term of `coinducedGradedShortComplex h N` is the grading shift `N{-1}`. -/
@[simp]
theorem coinducedGradedShortComplex_X₁ :
    (coinducedGradedShortComplex h N).X₁ = N.shiftObj (-1) := (rfl)

/-- The middle term of `coinducedGradedShortComplex h N` is the underlying graded module of
`coinducedObj h N`. -/
@[simp]
theorem coinducedGradedShortComplex_X₂ :
    (coinducedGradedShortComplex h N).X₂ = toGradedModuleCat (coinducedObj h N) := (rfl)

/-- The right term of `coinducedGradedShortComplex h N` is `N`. -/
@[simp]
theorem coinducedGradedShortComplex_X₃ : (coinducedGradedShortComplex h N).X₃ = N := (rfl)

/-- After forgetting the differential, `G⁻(N)` sits in a short exact sequence
`0 ⟶ N{-1} ⟶ (coinducedObj h N)♯ ⟶ N ⟶ 0` of graded right modules. -/
theorem coinducedGradedShortComplex_shortExact :
    (coinducedGradedShortComplex h N).ShortExact := by
  unfold coinducedGradedShortComplex coinducedGradedInr coinducedGradedFst coinducedObj
  exact
    { mono_f := (GradedModuleCat.mono_iff_injective _).2 fun v₁ v₂ hxy ↦
        congrArg CoinducedCarrier.snd hxy
      epi_g := (GradedModuleCat.epi_iff_surjective _).2 fun u ↦
        ⟨(⟨u, 0⟩ : CoinducedCarrier h N), rfl⟩
      exact := GradedModuleCat.exact_iff.2 fun z ↦
        ⟨fun hz ↦ ⟨z.snd, CoinducedCarrier.ext hz.symm rfl⟩,
          by rintro ⟨v, rfl⟩; rfl⟩ }

/-- If `I` is an injective graded right module, then `G⁻(I)` is graded-injective. -/
instance injective_toGradedModuleCat_coinducedObj [Injective N] :
    Injective (toGradedModuleCat (coinducedObj h N)) := by
  rw [injective_iff_hasInjectiveDimensionLT_one, ← coinducedGradedShortComplex_X₂]
  have h₁ : HasInjectiveDimensionLT (coinducedGradedShortComplex h N).X₁ 1 := by
    rw [coinducedGradedShortComplex_X₁]
    infer_instance
  have h₃ : HasInjectiveDimensionLT (coinducedGradedShortComplex h N).X₃ 1 := by
    rw [coinducedGradedShortComplex_X₃]
    infer_instance
  exact (coinducedGradedShortComplex_shortExact h N).hasInjectiveDimensionLT_X₂ 1 h₁ h₃

/-- If `I` is an injective graded right module, then `G⁻(I)` belongs to `gradedInjective`. -/
theorem gradedInjective_coinducedObj [Injective N] :
    gradedInjective R h (DGHomotopyCategory.of R (coinducedObj h N)) :=
  (gradedInjective_iff _).2 (injective_toGradedModuleCat_coinducedObj h N)

end Properties

end TauCeti.CurvedDGRightModuleCat
