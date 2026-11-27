/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Components
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Unit
import TauCeti.LinearAlgebra.Multilinear.Span

/-!
# Forgetting the grading of an `A∞` module in characteristic two

Tau Ceti's right `A∞` modules (`TauCeti.AInfinityRightModule`) are `ℤ`-graded, with operations
`m_{n+1}` of degree `1 - n` and Koszul signs in their Stasheff relations. Bordered Heegaard Floer
homology works instead over `𝔽₂` with algebras which carry no `ℤ`-grading, and its type `A`
modules are the ungraded `A∞` modules `TauCeti.UngradedAInfinityRightModule`, whose relations
have no signs. This file compares the two: over a ring of characteristic two, a `ℤ`-graded right
`A∞` module over a nonunital DG algebra `(A, d)` is an ungraded `A∞` module over `(A, d)` with the
same operations (`TauCeti.AInfinityRightModule.toUngraded`), the differential `d` being an
ungraded differential by `TauCeti.IsNonUnitalDGAlgebra.isUngradedDGAlgebra`. So every `ℤ`-graded
module over a `ℤ`-graded DG algebra over `𝔽₂` is a module of the ungraded theory, and the box
tensor products and twisted differentials of
`TauCeti.LowDimTopology.Bordered.TypeA.Basic` apply to it.

The comparison is the unsuspended module Stasheff equation `TauCeti.AInfinityRightModule.stasheff`.
Its signs are powers of `-1`, hence `1` in characteristic two, and over a DG algebra only the
unary and binary operations of the algebra are nonzero. The terms in which an operation of the
algebra of arity `s` collapses a block of inputs are therefore the differential terms for `s = 1`
and the product terms for `s = 2`, and the composite terms are those of the ungraded relation
(`TauCeti.AInfinityRightModule.stasheffSum_eq_ungradedStasheff`). The graded equation holds on
homogeneous inputs only, but the ungraded relation is multilinear in the algebra inputs and linear
in the module input, so it holds everywhere, since homogeneous elements span.

Forgetting the grading preserves strict units
(`TauCeti.AInfinityRightModule.StrictUnit.isStrictlyUnital_toUngraded`), and sends the regular
module of a DG algebra to the differential module of the algebra over itself
(`TauCeti.IsNonUnitalDGAlgebra.toUngraded_toRightModule`): its operations are the differential and
the right multiplication.

## Main definitions

* `TauCeti.AInfinityRightModule.ungradedAct`: the operations `m_{n+1}` of a right `A∞` module as
  multilinear maps in the algebra inputs with values in the endomorphisms of the module.
* `TauCeti.AInfinityRightModule.toUngraded`: in characteristic two, a right `A∞` module over a
  nonunital DG algebra as an ungraded `A∞` module.

## Main results

* `TauCeti.AInfinityRightModule.stasheffSum_eq_ungradedStasheff`: in characteristic two, the
  unsuspended module Stasheff expression over a DG algebra is the ungraded `A∞` relation.
* `TauCeti.AInfinityRightModule.StrictUnit.isStrictlyUnital_toUngraded`: a strict unit of the
  graded module makes the ungraded module strictly unital.
* `TauCeti.IsNonUnitalDGAlgebra.toUngraded_toRightModule`: the regular module of a DG algebra
  forgets to the algebra as a differential module over itself.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Section 2.1 (`A∞` modules over `𝔽₂`, with and without gradings).
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology Homotopy Appl. **3**
  (2001), 1–35, Section 4 (`A∞` modules and their sign conventions).
-/

public section

open Finset MulOpposite
open _root_.MultilinearMap (evalNat evalNat_def)

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

namespace AInfinityRightModule

/-! ### The operations as multilinear maps in the algebra inputs -/

section UngradedAct

variable {AA : AInfinityAlgebra R A} (MM : AInfinityRightModule AA M)

/-- The operation `m_{n+1}` of a right `A∞` module, with its `n` algebra inputs first: a
multilinear map in the algebra inputs with values in the linear endomorphisms of the module. This
is the form of the operations of an ungraded `A∞` module
(`TauCeti.UngradedAInfinityRightModule`). -/
noncomputable def ungradedAct (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M) where
  toFun a :=
    { toFun x := MM.m (n + 1) x a
      map_add' x y := by simp
      map_smul' c x := by simp }
  map_update_add' a i u v := LinearMap.ext fun x => (MM.m (n + 1) x).map_update_add a i u v
  map_update_smul' a i c u := LinearMap.ext fun x => (MM.m (n + 1) x).map_update_smul a i c u

@[simp]
theorem ungradedAct_apply (n : ℕ) (a : Fin n → A) (x : M) :
    MM.ungradedAct n a x = MM.m (n + 1) x a :=
  (rfl)

end UngradedAct

/-! ### The Stasheff relations in characteristic two -/

variable {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A} {h : IsNonUnitalDGAlgebra 𝒜 d} (MM : AInfinityRightModule h.toAInfinityAlgebra M)

/-- The operations only depend on the arity through its value. -/
private theorem evalNat_m_congr {k k' : ℕ} (hk : k = k') (x : M) (b : ℕ → A) :
    evalNat (MM.m k x) b = evalNat (MM.m k' x) b := by
  subst hk
  rfl

/-- The terms of the unsuspended Stasheff expression in which the algebra differential collapses
the input at position `p` are the differential terms of the ungraded relation. -/
private theorem evalNat_m_replaceBlock_one {n : ℕ} (p : Fin n) (x : M) (b : ℕ → A) :
    evalNat (MM.m (p + 1 + (n - p - 1) + 1) x)
        (replaceBlock b p 1 (evalNat (h.toAInfinityAlgebra.m 1) fun j ↦ b (p + j))) =
      MM.ungradedAct n (Function.update (fun i : Fin n => b i) p (d (b p))) x := by
  rw [evalNat_m_congr MM (by omega : (p : ℕ) + 1 + (n - p - 1) + 1 = n + 1), evalNat_def,
    ungradedAct_apply, MultilinearMap.evalNat_one,
    IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, Matrix.cons_val_zero, add_zero]
  rw [replaceBlock_one]
  congr 1
  funext i
  simp only [Function.update_apply, Fin.ext_iff]

/-- The terms of the unsuspended Stasheff expression in which the algebra product collapses the
inputs at positions `p` and `p + 1` are the product terms of the ungraded relation. -/
private theorem evalNat_m_replaceBlock_two {n : ℕ} (p : Fin n) (x : M) (b : ℕ → A) :
    evalNat (MM.m (p + 1 + (n + 1 - p - 2) + 1) x)
        (replaceBlock b p 2 (evalNat (h.toAInfinityAlgebra.m 2) fun j ↦ b (p + j))) =
      MM.ungradedAct n (Fin.contractNth p.castSucc (· * ·) fun i : Fin (n + 1) => b i) x := by
  rw [evalNat_m_congr MM (by omega : (p : ℕ) + 1 + (n + 1 - p - 2) + 1 = n + 1),
    evalNat_def, ungradedAct_apply, MultilinearMap.evalNat_two,
    IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, add_zero]
  congr 1
  funext i
  rcases lt_trichotomy (i : ℕ) p with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using hlt),
      replaceBlock_of_lt _ _ _ _ (by simpa using hlt), Fin.val_castSucc]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using heq)]
    simp only [Fin.val_castSucc, Fin.val_succ, heq, replaceBlock_self]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using hgt),
      replaceBlock_of_gt _ _ _ _ (by simpa using hgt), Fin.val_succ]
    congr 1

/-- The terms of the unsuspended Stasheff expression in which an algebra operation of arity
`s ≥ 3` collapses a block vanish: the DG algebra has no such operation. -/
private theorem evalNat_m_replaceBlock_of_three_le {n p s : ℕ} (hs : 3 ≤ s) (x : M) (b : ℕ → A) :
    evalNat (MM.m (p + 1 + (n - p - s) + 1) x)
        (replaceBlock b p s (evalNat (h.toAInfinityAlgebra.m s) fun j ↦ b (p + j))) = 0 := by
  rw [h.toAInfinityAlgebra_m_of_three_le hs, evalNat_def, evalNat_def]
  exact (MM.m (p + 1 + (n - p - s) + 1) x).map_coord_zero ⟨p, by omega⟩ (by simp)

/-- The inner sum of the unsuspended Stasheff expression over the arities `s` of the algebra
operation collapsing the block at position `p`: the differential term, and the product term when
there is an input after position `p`. -/
private theorem sum_Icc_evalNat_m_replaceBlock {n : ℕ} (p : Fin n) (x : M) (b : ℕ → A) :
    ∑ s ∈ Icc 1 (n - p), evalNat (MM.m (p + 1 + (n - p - s) + 1) x)
        (replaceBlock b p s (evalNat (h.toAInfinityAlgebra.m s) fun j ↦ b (p + j))) =
      evalNat (MM.m (p + 1 + (n - p - 1) + 1) x)
          (replaceBlock b p 1 (evalNat (h.toAInfinityAlgebra.m 1) fun j ↦ b (p + j))) +
        if (p : ℕ) + 1 < n then
          evalNat (MM.m (p + 1 + (n - p - 2) + 1) x)
            (replaceBlock b p 2 (evalNat (h.toAInfinityAlgebra.m 2) fun j ↦ b (p + j)))
        else 0 := by
  have hp := p.isLt
  split_ifs with hpn
  · refine Finset.sum_eq_add 1 2 (by norm_num) (fun s hs hs12 => ?_) (fun h1 => ?_) (fun h2 => ?_)
    · rw [Finset.mem_Icc] at hs
      exact MM.evalNat_m_replaceBlock_of_three_le (by omega) x b
    · exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h1
    · exact absurd (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩) h2
  · rw [show n - p = 1 by omega, Finset.Icc_self, Finset.sum_singleton, add_zero]

/-- **The Stasheff relations of a right `A∞` module over a DG algebra in characteristic two.**
Over a ring of characteristic two, the unsuspended module Stasheff expression of arity `n + 1`
(`TauCeti.AInfinityRightModule.stasheffSum`) of a right `A∞` module over a nonunital DG algebra
`(A, d)` is the ungraded `A∞` relation of length `n` of its operations, for every module input `x`
and algebra inputs `b 0, …, b (n - 1)` and whatever degrees are supplied: its signs are `1`, its
composite terms are the composite terms of the ungraded relation, and the algebra operations
collapsing a block are the differential and the product. -/
theorem stasheffSum_eq_ungradedStasheff [CharP R 2] (n : ℕ) (x : M) (e : ℤ) (deg : ℕ → ℤ)
    (b : ℕ → A) :
    stasheffSum h.toAInfinityAlgebra MM.m x e deg b n =
      ungradedStasheffComp MM.ungradedAct n (fun i : Fin n => b i) x +
        ungradedStasheffDiff MM.ungradedAct d n (fun i : Fin n => b i) x +
        ungradedStasheffMul MM.ungradedAct n (fun i : Fin n => b i) x := by
  -- In characteristic two every sign `(-1) ^ k` acts trivially.
  rw [stasheffSum_def]
  simp only [← negOnePow_smul_eq_negOnePowCast_smul,
    negOnePow_smul_eq_self_of_neg_one_eq_one (R := R) (CharTwo.neg_eq 1)]
  rw [add_assoc]
  congr 1
  · -- The composite terms agree on the nose.
    rw [ungradedStasheffComp_def]
    simp only [evalNat_def]
    exact (Fin.sum_univ_eq_sum_range (fun k => MM.ungradedAct (n - k) (fun l => b (k + l))
      (MM.ungradedAct k (fun l => b l) x)) (n + 1)).symm
  · -- The terms collapsing a block are the differential terms and the product terms.
    rw [Finset.sum_range (fun p => ∑ s ∈ Icc 1 (n - p), _),
      Finset.sum_congr rfl fun p _ => MM.sum_Icc_evalNat_m_replaceBlock p x b,
      Finset.sum_add_distrib, ungradedStasheffDiff_apply]
    congr 1
    · exact Finset.sum_congr rfl fun p _ => MM.evalNat_m_replaceBlock_one p x b
    · cases n with
      | zero => simp
      | succ n =>
        rw [Fin.sum_univ_castSucc, ungradedStasheffMul_succ_apply]
        simp only [Fin.val_last, lt_irrefl, ↓reduceIte, add_zero, Fin.val_castSucc,
          Nat.add_lt_add_iff_right, Fin.is_lt]
        refine Finset.sum_congr rfl fun p _ => ?_
        exact MM.evalNat_m_replaceBlock_two p x b

/-! ### The ungraded module -/

/-- **Forgetting the grading of a right `A∞` module in characteristic two.** Over a ring of
characteristic two, a `ℤ`-graded right `A∞` module over a nonunital DG algebra `(A, d)` is an
ungraded `A∞` module over `(A, d)` with the same operations: `m_{n+1}(x, a₁, …, aₙ)` is
`MM.m (n + 1) x a` (`TauCeti.AInfinityRightModule.toUngraded_act`). Its relations are the
unsuspended module Stasheff equations, whose signs disappear in characteristic two
(`TauCeti.AInfinityRightModule.stasheffSum_eq_ungradedStasheff`); they hold on homogeneous inputs,
hence on all inputs by multilinearity. -/
noncomputable def toUngraded [CharP R 2] : UngradedAInfinityRightModule d M where
  act := MM.ungradedAct
  stasheff n a x := by
    -- The relation, as a multilinear map in the algebra inputs.
    set Φ : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M) :=
      ungradedStasheffCompMultilinear MM.ungradedAct n +
        ungradedStasheffDiffMultilinear MM.ungradedAct d n +
        ungradedStasheffMulMultilinear MM.ungradedAct n with hΦ
    have hΦa (a : Fin n → A) (x : M) : Φ a x =
        ungradedStasheffComp MM.ungradedAct n a x + ungradedStasheffDiff MM.ungradedAct d n a x +
          ungradedStasheffMul MM.ungradedAct n a x := by
      simp only [hΦ, _root_.add_apply, LinearMap.add_apply,
        ungradedStasheffCompMultilinear_apply, ungradedStasheffDiffMultilinear_apply,
        ungradedStasheffMulMultilinear_apply]
    rw [← hΦa]
    -- On homogeneous algebra inputs, the relation is the graded Stasheff equation.
    have hhom (a : Fin n → A) (ha : a ∈ Set.univ.pi fun _ => ⋃ p, (𝒜 p : Set A)) : Φ a = 0 := by
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_iUnion, SetLike.mem_coe, forall_const] at ha
      choose deg hdeg using ha
      set b : ℕ → A := fun i => if hi : i < n then a ⟨i, hi⟩ else 0 with hb
      have hab : (fun i : Fin n => b i) = a := funext fun i => by simp [hb]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.zero_apply]
      induction x using DirectSum.Decomposition.inductionOn MM.grading.piece with
      | zero => exact map_zero _
      | @homogeneous e x =>
        have hst := MM.stasheff n x.property
          (fun i => if hi : i < n then deg ⟨i, hi⟩ else 0) b fun i hi => by
            simpa [hb, hi, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
              InternalGrading.ofDecomposition_piece] using hdeg ⟨i, hi⟩
        rwa [stasheffSum_eq_ungradedStasheff, hab, ← hΦa] at hst
      | add x x' hx hx' => rw [map_add, hx, hx', add_zero]
    -- Homogeneous elements span the algebra, so the relation holds on all inputs.
    have hspan := Φ.map_mem_span_image_pi (fun _ => ⋃ p, (𝒜 p : Set A)) (m := a)
      fun _ => by
        rw [← Submodule.iSup_eq_span, (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top]
        exact Submodule.mem_top
    rw [Submodule.span_eq_bot.2 (by rintro _ ⟨a', ha', rfl⟩; exact hhom a' ha')] at hspan
    rw [(Submodule.mem_bot R).1 hspan, LinearMap.zero_apply]

/-- The operation `m_{n+1}` of the ungraded module is the operation `m_{n+1}` of the graded
module. -/
@[simp]
theorem toUngraded_act [CharP R 2] (n : ℕ) (a : Fin n → A) (x : M) :
    (MM.toUngraded).act n a x = MM.m (n + 1) x a :=
  (rfl)

variable {MM} in
/-- **Forgetting the grading preserves strict units.** If `e` is a strict unit of a right `A∞`
module over a DG algebra, the ungraded module is strictly unital for `e`: its operations `m_{n+1}`,
`n ≥ 2`, vanish when one of the algebra inputs is `e`. -/
theorem StrictUnit.isStrictlyUnital_toUngraded [CharP R 2] {e : A} (he : MM.StrictUnit e) :
    (MM.toUngraded).IsStrictlyUnital fun _ : Unit => e :=
  (UngradedAInfinityRightModule.isStrictlyUnital_iff _).2 fun n hn a i _ hi =>
    LinearMap.ext fun x => he.m_eq_zero_of_eq_unit (by omega) x a hi

end AInfinityRightModule

/-! ### The regular module -/

namespace IsNonUnitalDGAlgebra

variable {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A}

/-- **The regular module of a DG algebra forgets to the algebra as a differential module over
itself.** In characteristic two, the ungraded module of the regular right `A∞` module of a
nonunital DG algebra `(A, d)` is `A` with `m₁ = d`, `m₂(x, a) = x * a` and no higher operations:
the differential module of the ungraded DG algebra `(A, d)` over itself. -/
theorem toUngraded_toRightModule [CharP R 2] (h : IsNonUnitalDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.toRightModule.toUngraded =
      h.isUngradedDGAlgebra.isUngradedDGRightModule.toUngradedAInfinityRightModule := by
  ext n a x
  rw [AInfinityRightModule.toUngraded_act, AInfinityAlgebra.m_toRightModule]
  match n with
  | 0 =>
    rw [IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_zero,
      toAInfinityAlgebra_m_one_apply, Fin.cons_zero]
  | 1 =>
    rw [IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one,
      toAInfinityAlgebra_m_two_apply, Fin.cons_zero, Fin.cons_one, op_smul_eq_mul]
  | n + 2 =>
    rw [IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_add_two,
      toAInfinityAlgebra_m_of_three_le h (by omega)]
    simp

end IsNonUnitalDGAlgebra

end TauCeti
