/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Strictification.Stasheff
public import TauCeti.Algebra.Module.GradedModule.Dual.Basic
-- Private: `MultilinearMap.curryMid` is used only to assemble the private unit-killing cochain.
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Arity-by-arity unit elimination on minimal `A∞` algebras

Let `𝒜` be a minimal `A∞` algebra over a commutative ring `R`, let `e` be a cohomological unit of
`𝒜`, and let `π ∈ 𝒜.grading.dualPiece 0` be a degree-zero linear retraction with `π e = 1`.
Suppose the Taylor map of `𝒜` already vanishes on every word of length `k ≠ 2` with `k ≤ m + 2`
containing `e`.

This module eliminates `e` from all `(m + 3)`-letter words without changing the grading,
minimality, or the Taylor map on words of length at most `m + 2`.  For each slot `0 ≤ j < m + 2`,
applying `TauCeti.AInfinityAlgebra.gauge` with a degree-zero cochain of arity `m + 2` that
evaluates `π` at slot `j` and duplicates `e` into `m_{m+3}(…, e, e, …)` kills `e` at slot `j` while
preserving its vanishing at all slots `< j`.  Once `e` is killed in the first `m + 2` positions,
`IsMinimal.taylor_of_tprod_last_eq_zero` forces vanishing in the final position `m + 2`
automatically.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.exists_strictUnit_step_of_mem_dualPiece`: eliminates `e` in
  arity `m + 3` by a gauge-induced `A∞` isomorphism whose Taylor map is `letter` up to length
  `m + 1`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003),
  Chapter 3, Section 3.2.
* P. Seidel, *Fukaya Categories and Picard--Lefschetz Theory*, Zurich Lectures in Advanced
  Mathematics (2008), Chapter I, Section 2.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

section UnitKilling

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### The position-by-position unit-killing cochain -/

private theorem taylor_curryMid_prefix_negOnePowCast (𝒜 : AInfinityAlgebra R A) (e : A) (m : ℕ)
    (j : Fin (m + 2)) (𝒟 : Fin (m + 2) → ℤ) (v : Fin (m + 2) → A) :
    ∀ k ≤ m + 2,
      (((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
        (PiTensorProduct.tprod R)).curryMid j.succ e)
          (fun r ↦ if r.1 < k then negOnePowCast R (𝒟 r) • v r else v r) =
        negOnePowCast R (∑ i ∈ Finset.range k, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0) •
          (((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
            (PiTensorProduct.tprod R)).curryMid j.succ e) v
  | 0, _ => by simp
  | k + 1, hk => by
    let M := ((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
      (PiTensorProduct.tprod R)).curryMid j.succ e
    let f : Fin (m + 2) → A := fun r ↦ if r.1 < k then negOnePowCast R (𝒟 r) • v r else v r
    have hupd : (fun r : Fin (m + 2) ↦ if r.1 < k + 1 then negOnePowCast R (𝒟 r) • v r else v r) =
        Function.update f ⟨k, hk⟩ (negOnePowCast R (𝒟 ⟨k, hk⟩) • v ⟨k, hk⟩) := by
      funext r
      by_cases hr : r = ⟨k, hk⟩
      · subst hr; simp [f]
      · have hrk : (r.1 < k + 1) ↔ r.1 < k := by
          have : r.1 ≠ k := fun h ↦ hr (Fin.ext h)
          omega
        simp [Function.update_of_ne hr, f, hrk]
    have hself : Function.update f ⟨k, hk⟩ (v ⟨k, hk⟩) = f :=
      Function.update_eq_self_iff.2 (by simp [f])
    rw [hupd, M.map_update_smul, RingHom.id_apply, hself,
      taylor_curryMid_prefix_negOnePowCast 𝒜 e m j 𝒟 v k (by omega), smul_smul,
      ← negOnePowCast_add, Finset.sum_range_succ, dite_eq_left (by omega : k < m + 2), add_comm]

private noncomputable def unitKillingMultilinear (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ A) A :=
  -((((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
      (PiTensorProduct.tprod R)).curryMid j.succ e).compLinearMap fun r : Fin (m + 2) ↦
        if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1
        else if r = j then LinearMap.toSpanSingleton R A e ∘ₗ π
        else LinearMap.id)

/-- The degree-zero suspended cochain concentrated in arity `m + 2` that eliminates `e` at slot `j`
of arity `m + 3`. -/
private noncomputable def unitKillingCochain (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) : ReducedTensorWords R A →ₗ[R] A :=
  PiTensorProduct.lift (unitKillingMultilinear 𝒜 e π m j) ∘ₗ
    component R A ⟨m + 2, by omega⟩

private theorem unitKillingCochain_of_of_ne (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {k : {k : ℕ // 0 < k}}
    (hk : k.1 ≠ m + 2) (x : TensorPower R k.1 A) :
    unitKillingCochain 𝒜 e π m j (of R A k x) = 0 := by
  rw [unitKillingCochain, LinearMap.comp_apply,
    component_of_of_ne R A (fun h ↦ hk (congrArg Subtype.val h)), map_zero]

private theorem unitKillingCochain_apply_eq_zero_of_mem_filtration (𝒜 : AInfinityAlgebra R A)
    (e : A) (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (m + 1)) : unitKillingCochain 𝒜 e π m j z = 0 := by
  have hle : filtration R A (m + 1) ≤ LinearMap.ker (unitKillingCochain 𝒜 e π m j) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    exact unitKillingCochain_of_of_ne 𝒜 e π m j (by omega) x
  exact hle hz

private theorem unitKillingCochain_comp_ofLetter (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) :
    unitKillingCochain 𝒜 e π m j ∘ₗ ofLetter R A = 0 :=
  LinearMap.ext fun a ↦ unitKillingCochain_apply_eq_zero_of_mem_filtration 𝒜 e π m j
    (filtration_monotone R A (by omega) (ofLetter_mem_filtration R A a))

private theorem unitKillingCochain_of_tprod (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) (z : Fin (m + 2) → A) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) =
      - (π (z j) • 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R
          (duplicateAt e j fun r ↦ if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1 (z r)
            else z r)))) := by
  let N := ((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
    (PiTensorProduct.tprod R)).curryMid j.succ e
  let v : Fin (m + 2) → A := fun r ↦
    if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r
  have harg : (fun r : Fin (m + 2) ↦
      (if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1
        else if r = j then LinearMap.toSpanSingleton R A e ∘ₗ π
        else LinearMap.id) (z r)) = Function.update v j (π (z j) • e) := by
    funext r
    by_cases hr : r = j
    · subst hr; simp [v]
    · rw [Function.update_of_ne hr]
      simp only [hr, ite_false, v]
      split_ifs <;> rfl
  have hN : N (Function.update v j (π (z j) • e)) = π (z j) • N (Function.update v j e) := by
    rw [N.map_update_smul, RingHom.id_apply]
  rw [unitKillingCochain, LinearMap.comp_apply, component_of, PiTensorProduct.lift.tprod,
    unitKillingMultilinear, neg_apply, MultilinearMap.compLinearMap_apply, harg, hN]
  simp only [N, duplicateAt_def, MultilinearMap.curryMid_apply_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, v]

private theorem unitKillingCochain_of_tprod_of_homogeneous (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {z : Fin (m + 2) → A}
    {𝒟 : Fin (m + 2) → ℤ}
    (hz : ∀ r : Fin (m + 2), r.1 < j.1 → z r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) =
      - (negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0) •
          π (z j) • 𝒜.taylor (of R A ⟨m + 3, by omega⟩
            (PiTensorProduct.tprod R (duplicateAt e j z)))) := by
  let N := ((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
    (PiTensorProduct.tprod R)).curryMid j.succ e
  rw [unitKillingCochain_of_tprod]
  congr 1
  have htwist : (fun r : Fin (m + 2) ↦
      if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r) =
      fun r ↦ if r.1 < j.1 then negOnePowCast R (𝒟 r) • z r else z r := by
    funext r
    split_ifs with hr
    · rw [(𝒜.grading.shift 1).koszulTwist_one_apply_of_mem (hz r hr), negOnePowCast_eq_intCast]
    · rfl
  have hN := taylor_curryMid_prefix_negOnePowCast 𝒜 e m j (Function.update 𝒟 j (-1))
    (Function.update z j e) j.1 (le_of_lt j.isLt)
  have hlhs : (fun r : Fin (m + 2) ↦ if r.1 < j.1 then
      negOnePowCast R (Function.update 𝒟 j (-1) r) • Function.update z j e r
      else Function.update z j e r) =
      Function.update
        (fun r : Fin (m + 2) ↦ if r.1 < j.1 then negOnePowCast R (𝒟 r) • z r else z r) j e := by
    funext r
    by_cases hr : r = j
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  have hsum : (∑ i ∈ Finset.range j.1,
      if h : i < m + 2 then Function.update 𝒟 j (-1) ⟨i, h⟩ else 0) =
      ∑ i ∈ Finset.range j.1, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0 :=
    Finset.sum_congr rfl fun i hi ↦ by
      rw [Finset.mem_range] at hi
      have hne : (⟨i, by omega⟩ : Fin (m + 2)) ≠ j := fun h ↦ Nat.ne_of_lt hi (congrArg Fin.val h)
      rw [dite_eq_left (by omega), dite_eq_left (by omega), Function.update_of_ne hne]
  rw [htwist]
  have hN' : 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R
      (duplicateAt e j fun r ↦ if r.1 < j.1 then negOnePowCast R (𝒟 r) • z r else z r))) =
      negOnePowCast R (∑ i ∈ Finset.range j.1, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0) •
        𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j z))) := by
    simpa only [hlhs, hsum, N, duplicateAt_def, MultilinearMap.curryMid_apply_apply,
      LinearMap.compMultilinearMap_apply, LinearMap.comp_apply] using hN
  rw [hN', smul_comm]

private theorem isHomogeneous_unitKillingCochain (𝒜 : AInfinityAlgebra R A) {e : A}
    (he : e ∈ 𝒜.grading.piece 0) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0)
    (m : ℕ) (j : Fin (m + 2)) :
    LinearMap.IsHomogeneous (unitKillingCochain 𝒜 e π m j)
      (gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  rw [add_zero]
  refine gradedPiece_induction
    (motive := fun w ↦ unitKillingCochain 𝒜 e π m j w ∈ (𝒜.grading.shift 1).piece D) hw
    (fun k hk 𝒟 z hz hD ↦ ?_)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact Submodule.add_mem _ hu hv)
    (fun c u _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  by_cases hkm : k = m + 2
  swap
  · rw [unitKillingCochain_of_of_ne 𝒜 e π m j hkm]
    exact Submodule.zero_mem _
  subst hkm
  rw [unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (fun r _ ↦ hz r)]
  by_cases h𝒟j : 𝒟 j = -1
  · have he' : e ∈ (𝒜.grading.shift 1).piece (-1) := by
      rwa [InternalGrading.shift_piece, neg_add_cancel]
    have hword : of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j z)) ∈
        gradedPiece (𝒜.grading.shift 1) (D - 1) := by
      rw [← hD, ← sum_duplicateAt_neg_one j h𝒟j]
      exact mem_gradedPiece_of_tprod (𝒜.grading.shift 1) (by omega) _ _
        (duplicateAt_mem_piece he' j hz)
    have htay := (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).map_mem hword
    rw [sub_add_cancel] at htay
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ htay))
  · have hzj : z j ∈ 𝒜.grading.piece (𝒟 j + 1) := by
      simpa only [InternalGrading.shift_piece] using hz j
    rw [𝒜.grading.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hπ hzj (by omega),
      zero_smul, smul_zero, neg_zero]
    exact Submodule.zero_mem _

private theorem unitKillingCochain_of_tprod_eq_zero_of_lt {𝒜 : AInfinityAlgebra R A} {e : A}
    (he : e ∈ 𝒜.grading.piece 0) (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2))
    (hIH : ∀ (x : Fin (m + 3) → A) (i : Fin (m + 3)), i.1 < j.1 → x i = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    (z : Fin (m + 2) → A) {i : Fin (m + 2)} (hij : i.1 < j.1) (hzi : z i = e) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) = 0 := by
  have he' : e ∈ (𝒜.grading.shift 1).piece (-1) := by
    rwa [InternalGrading.shift_piece, neg_add_cancel]
  rw [unitKillingCochain_of_tprod]
  set u : Fin (m + 3) → A := duplicateAt e j fun r ↦
    if r.1 < j.1 then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r
  have hui : u ⟨i.1, by omega⟩ = (-1 : R) • e := by
    dsimp only [u]
    rw [duplicateAt_apply, dite_eq_left hij]
    simp only [hij, ite_true, hzi, (𝒜.grading.shift 1).koszulTwist_one_apply_of_mem he']
    simp
  have hupd : u = Function.update u ⟨i.1, by omega⟩ ((-1 : R) • e) := by
    rw [← hui, Function.update_eq_self]
  rw [hupd, (PiTensorProduct.tprod R).map_update_smul, map_smul, map_smul,
    hIH _ ⟨i.1, by omega⟩ hij (Function.update_self _ _ _), smul_zero, smul_zero, neg_zero]

/-! ### Hochschild differential of `unitKillingCochain` -/

private theorem splice_two_m_add_three {m p : ℕ} (hp : p + 2 ≤ m + 3) (w : Fin (m + 3) → A)
    (v : A) :
    splice R w 0 (m + 3) p 2 v =
      of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R fun k : Fin (m + 2) ↦
        if _ : k.1 < p then w ⟨k.1, by omega⟩
        else if _ : k.1 = p then v
        else w ⟨k.1 + 1, by omega⟩) := by
  rw [splice_eq_of_tprod R w v two_pos hp (by omega)]
  refine of_tprod_congr R A _ (by omega) fun k ↦ ?_
  simp only [Fin.val_cast, zero_add]
  split_ifs with h₁ h₂
  · exact congrArg w (Fin.ext (by simp))
  · rfl
  · exact congrArg w (Fin.ext (by simp))

private theorem taylor_gradedCoderiv_unitKillingCochain (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
    𝒜.taylor (gradedCoderiv (𝒜.grading.shift 1) (unitKillingCochain 𝒜 e π m j) 0
        (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))) =
      𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![unitKillingCochain 𝒜 e π m j (subword R w 0 (m + 2)), w (Fin.last (m + 2))])) +
      𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![w 0, unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2))])) := by
  rw [gradedCoderiv_of_tprod_of_homogeneous _ _ 0 _ w 𝒟 hw]
  simp only [zero_mul, ← negOnePowCast_eq_intCast, negOnePowCast_zero, one_smul, map_sum]
  have hterm : ∀ p ∈ Finset.range (m + 3), ∀ d ∈ Finset.range (m + 4),
      𝒜.taylor (splice R w 0 (m + 3) p d (unitKillingCochain 𝒜 e π m j (subword R w p d))) =
        (if p = 0 ∧ d = m + 2 then
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![unitKillingCochain 𝒜 e π m j (subword R w 0 (m + 2)), w (Fin.last (m + 2))]))
         else 0) +
        (if p = 1 ∧ d = m + 2 then
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![w 0, unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2))]))
         else 0) := by
    intro p hp d hd
    rw [Finset.mem_range] at hp hd
    by_cases hfit : 0 < d ∧ p + d ≤ m + 3
    swap
    · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, ite_eq_right,
        add_zero]
    by_cases hdm : d = m + 2
    swap
    · have hφ0 : unitKillingCochain 𝒜 e π m j (subword R w p d) = 0 := by
        rw [subword_eq_of_tprod R w hfit.1 hfit.2]
        exact unitKillingCochain_of_of_ne 𝒜 e π m j hdm _
      simp (disch := omega) only [hφ0, splice_zero, map_zero, ite_eq_right, add_zero]
    subst hdm
    rcases Nat.eq_zero_or_pos p with rfl | hppos
    · rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (by omega), add_zero,
        splice_collapse_init_eq R (by omega : 0 < m + 2)]
    · obtain rfl : p = 1 := by omega
      rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl⟩, zero_add,
        splice_collapse_tail_eq R (by omega : 0 < m + 2)]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦ hterm p hp d hd]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

private theorem unitKillingCochain_barDifferential_of_tprod (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
    unitKillingCochain 𝒜 e π m j
        (𝒜.barDifferential (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))) =
      ∑ p ∈ Finset.range (m + 2),
        negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          unitKillingCochain 𝒜 e π m j
            (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2))) := by
  let φ := unitKillingCochain 𝒜 e π m j
  rw [barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ w 𝒟 hw]
  simp only [one_mul, map_sum, map_smul, ← negOnePowCast_eq_intCast]
  have hinner : ∀ p ∈ Finset.range (m + 3),
      (∑ d ∈ Finset.range (m + 4),
        negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          φ (splice R w 0 (m + 3) p d (𝒜.taylor (subword R w p d)))) =
        if p < m + 2 then
          negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
            φ (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))
        else 0 := by
    intro p hp
    rw [Finset.mem_range] at hp
    have hd : ∀ d ∈ Finset.range (m + 4),
        negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          φ (splice R w 0 (m + 3) p d (𝒜.taylor (subword R w p d))) =
        if d = 2 ∧ p < m + 2 then
          negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
            φ (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))
        else 0 := by
      intro d _
      by_cases hfit : 0 < d ∧ p + d ≤ m + 3
      swap
      · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
          ite_eq_right]
      by_cases hd2 : d = 2
      · subst hd2
        rw [ite_eq_left ⟨rfl, by omega⟩]
      · rw [splice_eq_of_tprod R w _ hfit.1 hfit.2 (by omega),
          unitKillingCochain_of_of_ne 𝒜 e π m j (by dsimp only; omega), smul_zero,
          ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl hd]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem unitKillingCochain_barDifferential_prefix {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) (π : Module.Dual R A) (m : ℕ)
    (j : Fin (m + 2))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) {i : Fin (m + 3)} (hij : i.1 ≤ j.1)
    (hwi : w i = e) :
    (∑ p ∈ Finset.range (i.1 + 1),
      negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
        unitKillingCochain 𝒜 e π m j (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))) =
      𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![w 0, unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2))])) := by
  have _hjn := j.isLt
  rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
  · have hw0 : w 0 = e := (congrArg w (Fin.ext hi0.symm)).trans hwi
    rw [hi0, Finset.sum_range_one, Finset.sum_range_zero, negOnePowCast_zero, one_smul,
      subword_two_eq R w (by omega), Fin.zero_eta, hw0,
      h𝒜.taylor_of_two_cohomologicalUnit_left he, h𝒜.taylor_of_two_cohomologicalUnit_left he,
      splice_two_succ_eq_subword R (by omega : 0 < m + 2) rfl w]
  · have htail : unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2)) = 0 := by
      rw [subword_eq_of_tprod R w (by omega) (by omega)]
      exact unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
        (i := ⟨i.1 - 1, by omega⟩) (by dsimp only; omega)
        ((congrArg w (Fin.ext (by simp; omega))).trans hwi)
    have hlen : Finset.range (i.1 + 1) = Finset.range ((i.1 - 1) + 1 + 1) :=
      congrArg Finset.range (by omega)
    rw [htail, (PiTensorProduct.tprod R).map_coord_zero (1 : Fin 2) rfl, map_zero, map_zero,
      hlen, Finset.sum_range_succ, Finset.sum_range_succ]
    have hpre : (∑ p ∈ Finset.range (i.1 - 1),
        negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          unitKillingCochain 𝒜 e π m j
            (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))) = 0 :=
      Finset.sum_eq_zero fun p hp ↦ by
        rw [Finset.mem_range] at hp
        rw [splice_two_m_add_three (by omega) w _,
          unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
            (i := ⟨i.1 - 1, by omega⟩) (by dsimp only; omega) (by
              dsimp only
              rw [dite_eq_right (by rw [Fin.val_mk]; omega),
                dite_eq_right (by rw [Fin.val_mk]; omega)]
              exact (congrArg w (Fin.ext (by simp; omega))).trans hwi),
          smul_zero]
    have hi_pred : (i.1 - 1) + 1 = i.1 := by omega
    have hi' : (⟨i.1 - 1 + 1, by omega⟩ : Fin (m + 3)) = i := Fin.ext (by simp; omega)
    rw [hpre, zero_add, hi_pred, subword_two_eq R w (by omega), hi', hwi,
      h𝒜.taylor_of_two_cohomologicalUnit_right he,
      𝒜.grading.koszulTwist_one_apply_of_mem
        (by simpa [InternalGrading.shift_piece] using hw ⟨i.1 - 1, by omega⟩),
      ← negOnePowCast_eq_intCast, splice_smul, map_smul, subword_two_eq R w (by omega), Fin.eta,
      hwi, h𝒜.taylor_of_two_cohomologicalUnit_left he,
      splice_two_succ_eq_splice_two_pred R hipos (by omega) w, smul_smul, ← negOnePowCast_add,
      ← add_smul]
    have hri : Finset.range i.1 = Finset.range ((i.1 - 1) + 1) :=
      congrArg Finset.range (by omega)
    have hS : (∑ r ∈ Finset.range i.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) =
        (∑ r ∈ Finset.range (i.1 - 1), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) +
          𝒟 ⟨i.1 - 1, by omega⟩ := by
      rw [hri, Finset.sum_range_succ, dite_eq_left (by omega)]
    rw [hS, ← add_assoc, negOnePowCast_add _ 1, negOnePowCast_one, mul_neg_one, neg_add_cancel,
      zero_smul]

private theorem hochschildDifferential_unitKillingCochain_of_lt {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) (π : Module.Dual R A) (m : ℕ)
    (j : Fin (m + 2))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) {i : Fin (m + 3)} (hij : i.1 < j.1)
    (hwi : w i = e) :
    𝒜.hochschildDifferential 0 (unitKillingCochain 𝒜 e π m j)
        (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) = 0 := by
  have _hjn := j.isLt
  rw [hochschildDifferential_eq_brace_sub, negOnePowCast_zero, one_smul, LinearMap.sub_apply,
    brace_def, brace_def, LinearMap.comp_apply, LinearMap.comp_apply, ← barDifferential_def,
    taylor_gradedCoderiv_unitKillingCochain 𝒜 e π m j hw,
    unitKillingCochain_barDifferential_of_tprod 𝒜 e π m j hw]
  have hinit : unitKillingCochain 𝒜 e π m j (subword R w 0 (m + 2)) = 0 := by
    rw [subword_eq_of_tprod R w (by omega) (by omega)]
    exact unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
      (i := ⟨i.1, by omega⟩) hij
      (by simp only [zero_add]; exact (congrArg w (Fin.ext rfl)).trans hwi)
  have hsplit : Finset.range (m + 2) = Finset.range ((i.1 + 1) + (m + 1 - i.1)) :=
    congrArg Finset.range (by omega)
  rw [hinit, (PiTensorProduct.tprod R).map_coord_zero (0 : Fin 2) rfl, map_zero, map_zero,
    zero_add, hsplit, Finset.sum_range_add,
    unitKillingCochain_barDifferential_prefix h𝒜 he π m j hIH hw (le_of_lt hij) hwi]
  have hpost : (∑ t ∈ Finset.range (m + 1 - i.1),
      negOnePowCast R (∑ r ∈ Finset.range (i.1 + 1 + t), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
        unitKillingCochain 𝒜 e π m j
          (splice R w 0 (m + 3) (i.1 + 1 + t) 2 (𝒜.taylor (subword R w (i.1 + 1 + t) 2)))) = 0 :=
    Finset.sum_eq_zero fun t ht ↦ by
      rw [Finset.mem_range] at ht
      rw [splice_two_m_add_three (by omega) w _,
        unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
          (i := ⟨i.1, by omega⟩) hij (by
            dsimp only
            rw [dite_eq_left (by rw [Fin.val_mk]; omega)]
            exact (congrArg w (Fin.ext rfl)).trans hwi),
        smul_zero]
  rw [hpost, add_zero, sub_self]

private theorem unitKillingCochain_splice_two_after {𝒜 : AInfinityAlgebra R A} {e : A}
    {π : Module.Dual R A} (hπe : π e = 1) (m : ℕ) (j : Fin (m + 2))
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j.castSucc = e) {s : ℕ}
    (hs : s < m + 1 - j.1) :
    unitKillingCochain 𝒜 e π m j
        (splice R w 0 (m + 3) (j.1 + 1 + s) 2 (𝒜.taylor (subword R w (j.1 + 1 + s) 2))) =
      -(negOnePowCast R (∑ r ∈ Finset.range j.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.1 + 1 + s + 1) 2
            (𝒜.taylor (subword R w (j.1 + 1 + s) 2)))) := by
  have _hjn := j.isLt
  have hS_eq : (∑ r ∈ Finset.range j.1, if h : r < m + 2 then 𝒟 (Fin.castSucc ⟨r, h⟩) else 0) =
      ∑ r ∈ Finset.range j.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0 :=
    Finset.sum_congr rfl fun r hr ↦ by
      rw [Finset.mem_range] at hr
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]
      rfl
  rw [splice_two_m_add_three (by omega) w _,
    unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (𝒟 := fun r ↦ 𝒟 r.castSucc)
      (fun r _ ↦ by
        rw [dite_eq_left (by omega)]
        exact hw _)]
  have hzj : (if _ : j.1 < j.1 + 1 + s then w ⟨j.1, by omega⟩
      else if _ : j.1 = j.1 + 1 + s then 𝒜.taylor (subword R w (j.1 + 1 + s) 2)
      else w ⟨j.1 + 1, by omega⟩) = e := by
    rw [dite_eq_left (by omega)]
    exact (congrArg w (Fin.ext rfl)).trans hwj
  rw [hzj, hπe, one_smul, hS_eq, ← splice_two_duplicateAt_after e j (by omega) (by omega) w _]

private theorem rescaled_stasheff_duplicateAt {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) (m : ℕ) (j : Fin (m + 2))
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j.castSucc = e)
    (h𝒟j : 𝒟 j.castSucc = -1) :
    (∑ s ∈ Finset.range (m + 1 - j.1),
      negOnePowCast R (∑ r ∈ Finset.range j.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
        negOnePowCast R
            (∑ r ∈ Finset.range (j.1 + 1 + s), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.1 + 1 + s + 1) 2
            (𝒜.taylor (subword R w (j.1 + 1 + s) 2)))) +
      (𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) +
        -(negOnePowCast R (∑ r ∈ Finset.range j.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![𝒜.taylor (subword R (duplicateAt e j.castSucc w) 0 (m + 3)),
              duplicateAt e j.castSucc w (Fin.last (m + 3))])))) = 0 := by
  have hjn := j.isLt
  let S : ℕ → ℤ := fun p ↦ ∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0
  have hst := h𝒜.taylor_barDifferential_duplicateAt he hlow j.castSucc
    (by simpa only [Fin.val_castSucc] using hIH) hw hwj h𝒟j
  have hsplit' : Finset.range (m + 2 - j.1) = Finset.range ((m + 1 - j.1) + 1) :=
    congrArg Finset.range (by omega)
  have hfin_j : (⟨j.1, by omega⟩ : Fin (m + 3)) = j.castSucc := Fin.ext rfl
  have hsp_succ := splice_two_duplicateAt_succ (R := R) (j := j.castSucc) (by simp) hwj
  simp only [Fin.val_castSucc] at hsp_succ
  rw [Fin.val_castSucc, hsplit', Finset.sum_range_succ', add_zero, add_zero,
    subword_two_eq R w (by omega), hfin_j, hwj, h𝒜.taylor_of_two_cohomologicalUnit_left he,
    hsp_succ] at hst
  have hmul := congrArg (fun x : A ↦ -(negOnePowCast R (S j.1) • x)) hst
  simp only [smul_zero, neg_zero, smul_add, smul_neg, Finset.smul_sum, neg_add_rev, neg_neg,
    ← Finset.sum_neg_distrib] at hmul
  have hsq : negOnePowCast R (S j.1) • negOnePowCast R (S j.1) •
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) =
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) := by
    rw [smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_eq_intCast,
      Int.negOnePow_even _ ⟨S j.1, two_mul _⟩]
    simp
  have hsum_eq : (∑ k ∈ Finset.range (m + 1 - j.1),
      negOnePowCast R (S j.1) • negOnePowCast R (S (j.1 + (k + 1))) •
        𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.1 + 1 + (k + 1)) 2
          (𝒜.taylor (subword R w (j.1 + (k + 1)) 2)))) =
      ∑ s ∈ Finset.range (m + 1 - j.1),
        negOnePowCast R (S j.1) • negOnePowCast R (S (j.1 + 1 + s)) •
          𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.1 + 1 + s + 1) 2
            (𝒜.taylor (subword R w (j.1 + 1 + s) 2))) :=
    Finset.sum_congr rfl fun s _ ↦ by
      have h₁ : j.1 + (s + 1) = j.1 + 1 + s := by omega
      have h₂ : j.1 + 1 + (s + 1) = j.1 + 1 + s + 1 := by omega
      rw [h₁, h₂]
  rw [hsq, hsum_eq] at hmul
  refine Eq.trans ?_ hmul
  abel

private theorem taylor_of_two_neg_smul_duplicateAt (𝒜 : AInfinityAlgebra R A) (e : A) {m : ℕ}
    (j : Fin (m + 2)) (w : Fin (m + 3) → A) (c : R) (u₀ : A) :
    𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![-(c • u₀), w (Fin.last (m + 2))])) =
      -(c • 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))]))) := by
  have _hjn := j.isLt
  have hv₁ : (![-(c • u₀), w (Fin.last (m + 2))] : Fin 2 → A) =
      Function.update (![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))] : Fin 2 → A) 0
        ((-c) • u₀) := by
    funext k; fin_cases k
    · simp [neg_smul]
    · simp only [Fin.mk_one, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Matrix.cons_val_one, Matrix.cons_val_zero, duplicateAt_apply, Fin.val_last,
        Fin.val_castSucc]
      rw [dite_eq_right (by omega), ite_eq_right (by omega)]
      exact congrArg w (Fin.ext (by simp))
  have hv₂ : Function.update (![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))] : Fin 2 → A)
      0 u₀ = ![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))] := by
    funext k; fin_cases k <;> simp
  have htprod : PiTensorProduct.tprod R (![-(c • u₀), w (Fin.last (m + 2))] : Fin 2 → A) =
      (-c) • PiTensorProduct.tprod R
        (![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))] : Fin 2 → A) := by
    rw [hv₁, (PiTensorProduct.tprod R).map_update_smul, hv₂, RingHom.id_apply]
  rw [htprod, map_smul, map_smul, neg_smul]

private theorem hochschildDifferential_unitKillingCochain_same {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπe : π e = 1) (m : ℕ) (j : Fin (m + 2))
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j.castSucc = e)
    (h𝒟j : 𝒟 j.castSucc = -1) :
    𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) +
      𝒜.hochschildDifferential 0 (unitKillingCochain 𝒜 e π m j)
        (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) = 0 := by
  have _hjn := j.isLt
  let S : ℕ → ℤ := fun p ↦ ∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0
  have hinit : unitKillingCochain 𝒜 e π m j (subword R w 0 (m + 2)) =
      -(negOnePowCast R (S j.1) • 𝒜.taylor (subword R (duplicateAt e j.castSucc w) 0 (m + 3))) := by
    rw [subword_eq_of_tprod R w (by omega) (by omega)]
    have hw_pre : (fun k : Fin (m + 2) ↦ w ⟨0 + k.1, by omega⟩) = fun r ↦ w r.castSucc :=
      funext fun _ ↦ congrArg w (Fin.ext (by simp))
    have hS_eq : (∑ r ∈ Finset.range j.1, if h : r < m + 2 then 𝒟 (Fin.castSucc ⟨r, h⟩) else 0) =
        S j.1 := Finset.sum_congr rfl fun r hr ↦ by
      rw [Finset.mem_range] at hr
      rw [dite_eq_left (by omega), dite_eq_left (by omega)]; rfl
    rw [hw_pre, unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (𝒟 := fun r ↦ 𝒟 r.castSucc)
      (fun r _ ↦ hw r.castSucc), hwj, hπe, one_smul, hS_eq, ← subword_init_duplicateAt_castSucc]
  have hsplit : Finset.range (m + 2) = Finset.range ((j.1 + 1) + (m + 1 - j.1)) :=
    congrArg Finset.range (by omega)
  have hpre := unitKillingCochain_barDifferential_prefix h𝒜 he π m j hIH hw
    (i := j.castSucc) le_rfl hwj
  rw [Fin.val_castSucc] at hpre
  rw [hochschildDifferential_eq_brace_sub, negOnePowCast_zero, one_smul, LinearMap.sub_apply,
    brace_def, brace_def, LinearMap.comp_apply, LinearMap.comp_apply, ← barDifferential_def,
    taylor_gradedCoderiv_unitKillingCochain 𝒜 e π m j hw,
    unitKillingCochain_barDifferential_of_tprod 𝒜 e π m j hw, hsplit, Finset.sum_range_add,
    hpre, Finset.sum_congr rfl fun s hs ↦ by
      rw [unitKillingCochain_splice_two_after hπe m j hw hwj (Finset.mem_range.1 hs), smul_neg,
        smul_comm],
    hinit, taylor_of_two_neg_smul_duplicateAt 𝒜 e j w, Finset.sum_neg_distrib]
  refine Eq.trans ?_ (rescaled_stasheff_duplicateAt h𝒜 he m j hlow hIH hw hwj h𝒟j)
  abel

/-! ### Gauge induction over input positions -/

private theorem exists_gauge_kill_slot {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal) {e : A}
    (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0)
    (hπe : π e = 1) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (j : Fin (m + 2))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0) :
    ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      (∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 + 1 → x k = e →
        𝒜'.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0) ∧
      (∀ z ∈ filtration R A (m + 1), g.taylor z = letter R A z) ∧
      g.IsIso ∧ g.linearPart = LinearMap.id := by
  let φ := unitKillingCochain 𝒜 e π m j
  have hφ := isHomogeneous_unitKillingCochain 𝒜 he.degree_zero hπ m j
  have hφ₁ := unitKillingCochain_comp_ofLetter 𝒜 e π m j
  have hφe : ∀ z ∈ filtration R A (m + 1), φ z = 0 := fun z hz ↦
    unitKillingCochain_apply_eq_zero_of_mem_filtration 𝒜 e π m j hz
  refine ⟨𝒜.gauge φ hφ hφ₁, 𝒜.gaugeHom φ hφ hφ₁, gauge_grading 𝒜 φ hφ hφ₁,
    h𝒜.isMinimal_gauge hφ hφ₁,
    fun z hz ↦ h𝒜.taylor_gauge_apply_of_mem_filtration_add_one hφ hφ₁ hφe hz,
    fun x k hk hxk ↦ ?_,
    fun z hz ↦ by rw [taylor_gaugeHom, LinearMap.add_apply, hφe z hz, add_zero],
    isIso_gaugeHom 𝒜 φ hφ hφ₁, linearPart_gaugeHom 𝒜 φ hφ hφ₁⟩
  refine of_tprod_mem_of_mem_piece (𝒜.grading.shift 1) he.mem_shift_one_piece
    (S := LinearMap.ker (𝒜.gauge φ hφ hφ₁).taylor) ⟨m + 3, by omega⟩ k
    (fun w 𝒟 hw hwk h𝒟k ↦ ?_) x hxk
  rw [LinearMap.mem_ker, h𝒜.taylor_gauge_apply_of_mem_filtration hφ hφ₁ hφe
    (of_mem_filtration R A (k := ⟨m + 3, by omega⟩) (by omega : m + 3 ≤ 2 * (m + 1) + 1) _)]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
  · rw [hIH w k hlt hwk, hochschildDifferential_unitKillingCochain_of_lt h𝒜 he π m j hIH hw hlt hwk,
      add_zero]
  · have hkj : k = j.castSucc := Fin.ext heq
    subst hkj
    exact hochschildDifferential_unitKillingCochain_same h𝒜 he hπe m j hlow hIH hw hwk h𝒟k

private theorem exists_gauge_kill_slots {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal) {e : A}
    (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0)
    (hπe : π e = 1) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0) :
    ∀ r ≤ m + 2, ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      (∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < r → x k = e →
        𝒜'.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0) ∧
      (∀ z ∈ filtration R A (m + 1), g.taylor z = letter R A z) ∧
      g.IsIso ∧ g.linearPart = LinearMap.id
  | 0, _ =>
    ⟨𝒜, AInfinityHom.id 𝒜, rfl, h𝒜, fun _ _ ↦ rfl,
      fun _ _ hk ↦ absurd hk (Nat.not_lt_zero _),
      fun _ _ ↦ by rw [AInfinityHom.taylor_id],
      AInfinityHom.isIso_id 𝒜, AInfinityHom.linearPart_id 𝒜⟩
  | r + 1, hr => by
    obtain ⟨𝒜₁, g₁, hG₁, hmin₁, htay₁, hIH₁, hg₁_filt, hg₁_iso, hg₁_lin⟩ :=
      exists_gauge_kill_slots h𝒜 he hπ hπe hlow r (by omega)
    have he₁ : 𝒜₁.CohomologicalUnit e :=
      h𝒜.cohomologicalUnit_of_taylor_eq hmin₁ hG₁
        (fun a b ↦ htay₁ _ (filtration_monotone R A (by omega : 2 ≤ m + 2)
          (of_mem_filtration R A (k := (2 : ℕ+)) le_rfl _))) he
    have hlow₁ : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
        (∃ s, x s = e) → 𝒜₁.taylor (of R A k (PiTensorProduct.tprod R x)) = 0 :=
      fun k hk2 hkle x hx ↦
        (htay₁ _ (of_mem_filtration R A hkle _)).trans (hlow k hk2 hkle x hx)
    obtain ⟨𝒜₂, g₂, hG₂, hmin₂, htay₂, hIH₂, hg₂_filt, hg₂_iso, hg₂_lin⟩ :=
      exists_gauge_kill_slot hmin₁ he₁ (hG₁ ▸ hπ) hπe hlow₁ ⟨r, hr⟩ hIH₁
    refine ⟨𝒜₂, g₁.comp g₂, hG₂.trans hG₁, hmin₂,
      fun z hz ↦ (htay₂ z hz).trans (htay₁ z hz), hIH₂, fun z hz ↦ ?_,
      hg₁_iso.comp hg₂_iso,
      by rw [AInfinityHom.linearPart_comp, hg₁_lin, hg₂_lin, LinearMap.comp_id]⟩
    have hbar : g₂.barMap z = z :=
      g₂.isCoalgHom_barMap.apply_eq_of_mem_filtration (isCoalgHom_id A)
        (fun w hw ↦ by
          rw [← LinearMap.comp_apply, ← AInfinityHom.taylor_def, hg₂_filt w hw,
            LinearMap.id_apply]) hz
    rw [AInfinityHom.taylor_def, AInfinityHom.barMap_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, hbar, ← LinearMap.comp_apply, ← AInfinityHom.taylor_def,
      hg₁_filt z hz]

/-- **Single-arity unit elimination on a minimal `A∞` algebra.**  Given a minimal `A∞` algebra `𝒜`,
a cohomological unit `e`, and a degree-zero linear retraction `π ∈ 𝒜.grading.dualPiece 0` with
`π e = 1`, if `𝒜.taylor` already vanishes on pure tensor words of length `k ≠ 2` with `k ≤ m + 2`
containing `e`, then there is a minimal `A∞` structure `𝒜'` on the same graded module and an `A∞`
isomorphism `g : 𝒜' ⟶ 𝒜` with `g.linearPart = id` such that `𝒜'` agrees with `𝒜` on words of length
at most `m + 2`, `g.taylor` is `letter` on words of length at most `m + 1`, and `𝒜'.taylor` vanishes
on pure tensor words of length `k ≠ 2` with `k ≤ m + 3` containing `e`. -/
theorem IsMinimal.exists_strictUnit_step_of_mem_dualPiece {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπ : π ∈ 𝒜.grading.dualPiece 0) (hπe : π e = 1) (m : ℕ)
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0) :
    ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      (∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 3 → ∀ x : Fin k.1 → A,
        (∃ r, x r = e) → 𝒜'.taylor (of R A k (PiTensorProduct.tprod R x)) = 0) ∧
      (∀ z ∈ filtration R A (m + 1), g.taylor z = letter R A z) ∧
      g.IsIso ∧ g.linearPart = LinearMap.id := by
  obtain ⟨𝒜', g, hG', hmin', htay', hIH', hg_filt, hg_iso, hg_lin⟩ :=
    exists_gauge_kill_slots h𝒜 he hπ hπe hlow (m + 2) le_rfl
  have he' : 𝒜'.CohomologicalUnit e :=
    h𝒜.cohomologicalUnit_of_taylor_eq hmin' hG'
      (fun a b ↦ htay' _ (filtration_monotone R A (by omega : 2 ≤ m + 2)
        (of_mem_filtration R A (k := (2 : ℕ+)) le_rfl _))) he
  have hlow' : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ s, x s = e) → 𝒜'.taylor (of R A k (PiTensorProduct.tprod R x)) = 0 :=
    fun k hk2 hkle x hx ↦ (htay' _ (of_mem_filtration R A hkle _)).trans (hlow k hk2 hkle x hx)
  refine ⟨𝒜', g, hG', hmin', htay', fun k hk2 hkle x ⟨s, hxs⟩ ↦ ?_, hg_filt, hg_iso, hg_lin⟩
  rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
  · exact hlow' k hk2 (by omega) x ⟨s, hxs⟩
  · obtain ⟨kval, hkpos⟩ := k
    dsimp only at hkeq
    subst hkeq
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ s.isLt) with hslt | hseq
    · exact hIH' x s hslt hxs
    · exact hmin'.taylor_of_tprod_last_eq_zero he' hlow' hIH' x
        ((congrArg x (Fin.ext hseq.symm)).trans hxs)

end UnitKilling

end TauCeti.AInfinityAlgebra
