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

Given a minimal `A∞` algebra `𝒜` over `R`, a cohomological unit `e`, and `π ∈ 𝒜.grading.dualPiece 0`
with `π e = 1` satisfying `KillsUnitUpTo 𝒜 e (m + 2)`, this module extends `KillsUnitUpTo` to
`m + 3` without changing the grading, minimality, or `taylor` on `filtration R A (m + 2)`. For each
slot `0 ≤ j < m + 2`, `TauCeti.AInfinityAlgebra.gauge` with a degree-zero cochain of arity `m + 2`
that evaluates `π` at `j` and duplicates `e` into `m_{m+3}(…, e, e, …)` kills `e` at slot `j` while
preserving `KillsUnitBeforeSlot` below `j`; `IsMinimal.taylor_of_tprod_last_eq_zero` then kills the
final slot `m + 2` automatically.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.exists_killsUnitUpTo_isIso_of_mem_dualPiece`: extends
  `KillsUnitUpTo e` from `m + 2` to `m + 3` via an `A∞` isomorphism whose Taylor map is `letter` on
  `filtration R A (m + 1)`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003), Ch. 3.
* P. Seidel, *Fukaya Categories and Picard--Lefschetz Theory* (2008), Chapter I, Section 2.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

section UnitKilling

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### The position-by-position unit-killing cochain -/

private noncomputable def unitKillingMultilinear (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ A) A :=
  -((((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
      (PiTensorProduct.tprod R)).curryMid j.succ e).compLinearMap fun r : Fin (m + 2) ↦
        if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1
        else if r = j then LinearMap.toSpanSingleton R A e ∘ₗ π else LinearMap.id)

/-- The degree-zero suspended cochain in arity `m + 2` that eliminates `e` at slot `j`. -/
private noncomputable def unitKillingCochain (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) : ReducedTensorWords R A →ₗ[R] A :=
  PiTensorProduct.lift (unitKillingMultilinear 𝒜 e π m j) ∘ₗ component R A ⟨m + 2, by omega⟩

private theorem unitKillingCochain_of_of_ne (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {k : {k : ℕ // 0 < k}} (hk : k.val ≠ m + 2)
    (x : TensorPower R k.val A) : unitKillingCochain 𝒜 e π m j (of R A k x) = 0 := by
  rw [unitKillingCochain, LinearMap.comp_apply,
    component_of_of_ne R A (fun h ↦ hk (congrArg Subtype.val h)), map_zero]

private theorem unitKillingCochain_apply_eq_zero_of_mem_filtration (𝒜 : AInfinityAlgebra R A)
    (e : A) (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (m + 1)) : unitKillingCochain 𝒜 e π m j z = 0 :=
  ((filtration_le_iff R A (p := LinearMap.ker (unitKillingCochain 𝒜 e π m j))).2 fun _ _ _ ⟨x, h⟩ ↦
    h ▸ unitKillingCochain_of_of_ne 𝒜 e π m j (by omega) x) hz

private theorem unitKillingCochain_comp_ofLetter (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) :
    unitKillingCochain 𝒜 e π m j ∘ₗ ofLetter R A = 0 :=
  LinearMap.ext fun a ↦ unitKillingCochain_apply_eq_zero_of_mem_filtration 𝒜 e π m j
    (filtration_monotone R A (by omega) (ofLetter_mem_filtration R A a))

private theorem unitKillingCochain_of_tprod (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) (z : Fin (m + 2) → A) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) =
      -(π (z j) • 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R
          (duplicateAt e j fun r ↦ if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1 (z r)
            else z r)))) := by
  let N := ((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
    (PiTensorProduct.tprod R)).curryMid j.succ e
  let v : Fin (m + 2) → A := fun r ↦
    if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r
  have harg : (fun r : Fin (m + 2) ↦ (if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1
      else if r = j then LinearMap.toSpanSingleton R A e ∘ₗ π else LinearMap.id) (z r)) =
      Function.update v j (π (z j) • e) := funext fun r ↦ by
    rcases eq_or_ne r j with rfl | hr
    · simp [v]
    · simp only [Function.update_of_ne hr, hr, ite_false, v]; split_ifs <;> rfl
  rw [unitKillingCochain, LinearMap.comp_apply, component_of, PiTensorProduct.lift.tprod,
    unitKillingMultilinear, neg_apply, MultilinearMap.compLinearMap_apply, harg,
    N.map_update_smul, RingHom.id_apply]
  simp only [N, duplicateAt_def, MultilinearMap.curryMid_apply_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, v]

private theorem unitKillingCochain_of_tprod_of_homogeneous (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {z : Fin (m + 2) → A} {𝒟 : Fin (m + 2) → ℤ}
    (hz : ∀ r : Fin (m + 2), r.val < j.val → z r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) =
      -(negOnePowCast R (∑ i ∈ Finset.range j.val, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0) •
          π (z j) • 𝒜.taylor (of R A ⟨m + 3, by omega⟩
            (PiTensorProduct.tprod R (duplicateAt e j z)))) := by
  let N := ((𝒜.taylor ∘ₗ of R A ⟨m + 3, by omega⟩).compMultilinearMap
    (PiTensorProduct.tprod R)).curryMid j.succ e
  let s : Finset (Fin (m + 2)) := Finset.univ.filter fun r ↦ r.val < j.val
  have harg : Function.update (fun r : Fin (m + 2) ↦
      if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r) j e =
      s.piecewise (fun r ↦ negOnePowCast R (𝒟 r) • Function.update z j e r)
        (Function.update z j e) := funext fun r ↦ by
    rcases lt_trichotomy r j with hlt | rfl | hgt
    · have hr : r.val < j.val := hlt
      simp only [s, Finset.piecewise, Finset.mem_filter, Finset.mem_univ, true_and, hr, ↓reduceIte,
        Function.update_of_ne hlt.ne]
      rw [(𝒜.grading.shift 1).koszulTwist_one_apply_of_mem (hz r hr), negOnePowCast_eq_intCast]
    · simp [s, Finset.piecewise]
    · simp [s, Finset.piecewise, Function.update_of_ne hgt.ne', lt_asymm hgt]
  have hsum : ∑ r ∈ s, 𝒟 r =
      ∑ i ∈ Finset.range j.val, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0 := by
    refine Finset.sum_nbij Fin.val (fun r hr ↦ Finset.mem_range.2 (Finset.mem_filter.1 hr).2)
      (fun _ _ _ _ h ↦ Fin.ext h) (fun i hi ↦ ?_) (fun r _ ↦ by simp)
    refine ⟨⟨i, lt_trans (Finset.mem_range.1 hi) j.isLt⟩, ?_, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_range.1 hi⟩)
  have hN := N.map_piecewise_smul (fun r ↦ negOnePowCast R (𝒟 r)) (Function.update z j e) s
  rw [← harg] at hN
  simp only [RingHom.id_apply, ← negOnePowCast_sum, hsum] at hN
  have hN' : 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R
      (duplicateAt e j fun r ↦
        if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r))) =
      negOnePowCast R (∑ i ∈ Finset.range j.val, if h : i < m + 2 then 𝒟 ⟨i, h⟩ else 0) •
        𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j z))) := by
    simpa only [N, duplicateAt_def, MultilinearMap.curryMid_apply_apply,
      LinearMap.compMultilinearMap_apply, LinearMap.comp_apply] using hN
  rw [unitKillingCochain_of_tprod, hN', smul_comm]

private theorem isHomogeneous_unitKillingCochain (𝒜 : AInfinityAlgebra R A) {e : A}
    (he : e ∈ 𝒜.grading.piece 0) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0) (m : ℕ)
    (j : Fin (m + 2)) : LinearMap.IsHomogeneous (unitKillingCochain 𝒜 e π m j)
      (gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]; intro D w hw; rw [add_zero]
  refine gradedPiece_induction
    (motive := fun w ↦ unitKillingCochain 𝒜 e π m j w ∈ (𝒜.grading.shift 1).piece D) hw
    (fun k hk 𝒟 z hz hD ↦ ?_)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact Submodule.add_mem _ hu hv)
    (fun c u _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  by_cases hkm : k = m + 2
  swap
  · simp [unitKillingCochain_of_of_ne 𝒜 e π m j (k := ⟨k, hk⟩) hkm]
  subst hkm
  rw [unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (fun r _ ↦ hz r)]
  by_cases h𝒟j : 𝒟 j = -1
  · have he' := 𝒜.grading.mem_shift_piece_neg_of_mem_zero 1 he
    have hsum : ∑ k : Fin (m + 3), duplicateAt (-1 : ℤ) j 𝒟 k = D - 1 := by
      rw [sum_duplicateAt j h𝒟j, hD, sub_eq_add_neg]
    have htay := (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).map_mem
      (hsum ▸ mem_gradedPiece_of_tprod (𝒜.grading.shift 1) (by omega) _ _
        (duplicateAt_mem_piece he' j hz) :
        of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j z)) ∈
          gradedPiece (𝒜.grading.shift 1) (D - 1))
    rw [sub_add_cancel] at htay
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ htay))
  · rw [𝒜.grading.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero hπ
      (by simpa only [InternalGrading.shift_piece] using hz j : z j ∈ 𝒜.grading.piece (𝒟 j + 1))
      (by omega), zero_smul, smul_zero, neg_zero]
    exact Submodule.zero_mem _

private theorem unitKillingCochain_of_tprod_eq_zero_of_lt {𝒜 : AInfinityAlgebra R A} {e : A}
    (he : e ∈ 𝒜.grading.piece 0) (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) (z : Fin (m + 2) → A) {i : Fin (m + 2)}
    (hij : i.val < j.val) (hzi : z i = e) :
    unitKillingCochain 𝒜 e π m j (of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R z)) = 0 := by
  have he' := 𝒜.grading.mem_shift_piece_neg_of_mem_zero 1 he
  rw [unitKillingCochain_of_tprod]
  set u : Fin (m + 3) → A := duplicateAt e j fun r ↦
    if r.val < j.val then (𝒜.grading.shift 1).koszulTwist 1 (z r) else z r
  have hui : u i.castSucc = (-1 : R) • e := by
    dsimp only [u]
    rw [duplicateAt_castSucc_of_lt _ _ hij, ite_eq_left hij, hzi,
      (𝒜.grading.shift 1).koszulTwist_one_apply_of_mem he']
    simp
  rw [← Function.update_eq_self i.castSucc u, hui, (PiTensorProduct.tprod R).map_update_smul,
    map_smul, map_smul,
    killsUnitBeforeSlot_iff.1 hIH _ i.castSucc hij (Function.update_self _ _ _),
    smul_zero, smul_zero, neg_zero]

/-! ### Hochschild differential of `unitKillingCochain` -/

private theorem taylor_gradedCoderiv_unitKillingCochain (𝒜 : AInfinityAlgebra R A) (e : A)
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
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
        (if p = 0 ∧ d = m + 2 then 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![unitKillingCochain 𝒜 e π m j (subword R w 0 (m + 2)), w (Fin.last (m + 2))])) else 0) +
        (if p = 1 ∧ d = m + 2 then 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![w 0, unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2))])) else 0) := by
    intro p hp d hd; rw [Finset.mem_range] at hp hd
    by_cases hfit : 0 < d ∧ p + d ≤ m + 3
    swap
    · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, ite_eq_right,
        add_zero]
    by_cases hdm : d = m + 2
    swap
    · have hφ0 : unitKillingCochain 𝒜 e π m j (subword R w p d) = 0 :=
        (subword_eq_of_tprod R w hfit.1 hfit.2).symm ▸ unitKillingCochain_of_of_ne 𝒜 e π m j hdm _
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
    (π : Module.Dual R A) (m : ℕ) (j : Fin (m + 2)) {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) :
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
    intro p hp; rw [Finset.mem_range] at hp
    have hd : ∀ d ∈ Finset.range (m + 4),
        negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          φ (splice R w 0 (m + 3) p d (𝒜.taylor (subword R w p d))) =
        if d = 2 ∧ p < m + 2 then
          negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
            φ (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))
        else 0 := fun d _ ↦ by
      by_cases hfit : 0 < d ∧ p + d ≤ m + 3
      swap
      · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
          ite_eq_right]
      by_cases hd2 : d = 2
      · subst hd2; rw [ite_eq_left ⟨rfl, by omega⟩]
      · rw [splice_eq_of_tprod R w _ hfit.1 hfit.2 (by omega),
          unitKillingCochain_of_of_ne 𝒜 e π m j (by dsimp only; omega), smul_zero,
          ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl hd]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs <;> first | rfl | omega
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  refine Finset.sum_congr (Finset.ext fun p ↦ ?_) fun _ _ ↦ rfl
  simp only [Finset.mem_filter, Finset.mem_range]; omega

private theorem unitKillingCochain_barDifferential_prefix {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) (π : Module.Dual R A) (m : ℕ)
    (j : Fin (m + 2)) (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) {i : Fin (m + 3)}
    (hij : i.val ≤ j.val) (hwi : w i = e) :
    (∑ p ∈ Finset.range (i.val + 1),
      negOnePowCast R (∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
        unitKillingCochain 𝒜 e π m j (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))) =
      𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![w 0, unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2))])) := by
  have _hjn := j.isLt
  rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
  · -- At `i = 0`, collapsing `[e, w₁]` leaves the tail subword, matching `m₂(e, φ(tail))`.
    have hw0 : w 0 = e := (congrArg w (Fin.ext hi0.symm)).trans hwi
    rw [hi0, Finset.sum_range_one, Finset.sum_range_zero, negOnePowCast_zero, one_smul,
      subword_two_eq R w (by omega), Fin.zero_eta, hw0,
      h𝒜.taylor_of_two_cohomologicalUnit_left he, h𝒜.taylor_of_two_cohomologicalUnit_left he,
      splice_two_succ_eq_subword R (by omega : 0 < m + 2) rfl w]
  · -- For `i > 0`, `φ` kills both the tail subword and collapses before `i - 1`, and the adjacent
    -- collapses at `i - 1` and `i` cancel around the interior unit `w i = e`.
    have htail : unitKillingCochain 𝒜 e π m j (subword R w 1 (m + 2)) = 0 := by
      rw [subword_eq_of_tprod R w (by omega) (by omega)]
      exact unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
        (i := ⟨i.val - 1, by omega⟩) (by dsimp only; omega)
        ((congrArg w (Fin.ext (by simp; omega))).trans hwi)
    have hcancel := h𝒜.negOnePowCast_smul_splice_two_add_succ_eq_zero he (n := m + 2)
      (p := i.val - 1) (x := w) (𝒟 := 𝒟) (by omega) (hw _)
      ((congrArg w (Fin.ext (by dsimp only; omega))).trans hwi)
    rw [htail, (PiTensorProduct.tprod R).map_coord_zero (1 : Fin 2) rfl, map_zero, map_zero,
      Finset.sum_range_succ, ← Nat.sub_add_cancel hipos, Finset.sum_range_succ,
      Finset.sum_eq_zero fun p hp ↦ by
        rw [Finset.mem_range] at hp
        rw [splice_two_eq_of_tprod R (by omega) w _,
          unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
            (i := ⟨i.val - 1, by omega⟩) (by dsimp only; omega) (by
              dsimp only; rw [dite_eq_right (by rw [Fin.val_mk]; omega),
                dite_eq_right (by rw [Fin.val_mk]; omega)]
              exact (congrArg w (Fin.ext (by simp; omega))).trans hwi),
          smul_zero],
      zero_add, ← map_smul, ← map_smul, ← map_add, hcancel, map_zero]

private theorem hochschildDifferential_unitKillingCochain_of_lt {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) (π : Module.Dual R A) (m : ℕ)
    (j : Fin (m + 2)) (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) {i : Fin (m + 3)}
    (hij : i.val < j.val) (hwi : w i = e) :
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
      (i := ⟨i.val, by omega⟩) hij
      (by simp only [zero_add]; exact (congrArg w (Fin.ext rfl)).trans hwi)
  rw [hinit, (PiTensorProduct.tprod R).map_coord_zero (0 : Fin 2) rfl, map_zero, map_zero,
    zero_add]
  conv_lhs =>
    rhs
    rw [← Nat.add_sub_of_le (Nat.succ_le_of_lt (Nat.lt_trans hij j.isLt)), Nat.succ_sub_succ,
      Finset.sum_range_add]
  rw [unitKillingCochain_barDifferential_prefix h𝒜 he π m j hIH hw (le_of_lt hij) hwi,
    Finset.sum_eq_zero fun t ht ↦ by
      rw [Finset.mem_range] at ht
      rw [splice_two_eq_of_tprod R (by omega) w _,
        unitKillingCochain_of_tprod_eq_zero_of_lt he.degree_zero π m j hIH _
          (i := ⟨i.val, by omega⟩) hij (by
            dsimp only; rw [dite_eq_left (by rw [Fin.val_mk]; omega)]
            exact (congrArg w (Fin.ext rfl)).trans hwi), smul_zero],
    add_zero, sub_self]

private theorem unitKillingCochain_splice_two_after {𝒜 : AInfinityAlgebra R A} {e : A}
    {π : Module.Dual R A} (hπe : π e = 1) (m : ℕ) (j : Fin (m + 2)) {w : Fin (m + 3) → A}
    {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r))
    (hwj : w j.castSucc = e) {s : ℕ} (hs : s < m + 1 - j.val) :
    unitKillingCochain 𝒜 e π m j
        (splice R w 0 (m + 3) (j.val + 1 + s) 2 (𝒜.taylor (subword R w (j.val + 1 + s) 2))) =
      -(negOnePowCast R (∑ r ∈ Finset.range j.val, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.val + 1 + s + 1) 2
            (𝒜.taylor (subword R w (j.val + 1 + s) 2)))) := by
  have _hjn := j.isLt
  have hwj' : w ⟨j.val, by omega⟩ = e := hwj
  rw [splice_two_eq_of_tprod R (by omega) w _,
    unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (𝒟 := fun r ↦ 𝒟 r.castSucc)
      (fun r _ ↦ by rw [dite_eq_left (by omega)]; exact hw _),
    dite_eq_left (by omega : j.val < j.val + 1 + s), hwj', hπe, one_smul,
    ← splice_two_duplicateAt_after R e j (by omega) (by omega) w _]
  congr 3
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.mem_range] at hr
  rw [dite_eq_left (by omega), dite_eq_left (by omega), Fin.castSucc_mk]

private theorem rescaled_stasheff_duplicateAt {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) (m : ℕ) (j : Fin (m + 2))
    (hlow : 𝒜.KillsUnitUpTo e (m + 2)) (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ} (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r))
    (hwj : w j.castSucc = e) (h𝒟j : 𝒟 j.castSucc = -1) :
    (∑ s ∈ Finset.range (m + 1 - j.val),
      negOnePowCast R (∑ r ∈ Finset.range j.val, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
        negOnePowCast R
            (∑ r ∈ Finset.range (j.val + 1 + s), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.val + 1 + s + 1) 2
            (𝒜.taylor (subword R w (j.val + 1 + s) 2)))) +
      (𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) +
        -(negOnePowCast R (∑ r ∈ Finset.range j.val, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![𝒜.taylor (subword R (duplicateAt e j.castSucc w) 0 (m + 3)),
              duplicateAt e j.castSucc w (Fin.last (m + 3))])))) = 0 := by
  have hjn := j.isLt
  let S : ℕ → ℤ := fun p ↦ ∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0
  have hst := h𝒜.taylor_barDifferential_duplicateAt he hlow j.castSucc
    (by simpa only [Fin.val_castSucc] using hIH) hw hwj h𝒟j
  have hsp_succ := splice_two_duplicateAt_succ R (j := j.castSucc) (by simp) hwj
  simp only [Fin.val_castSucc] at hsp_succ
  have hwj' : w ⟨j.val, by omega⟩ = e := hwj
  rw [Fin.val_castSucc, Nat.succ_sub (Nat.le_of_lt_succ j.isLt), Finset.sum_range_succ',
    add_zero, add_zero, subword_two_eq R w (by omega), hwj',
    h𝒜.taylor_of_two_cohomologicalUnit_left he, hsp_succ] at hst
  have hmul := congrArg (fun x : A ↦ -(negOnePowCast R (S j.val) • x)) hst
  simp only [smul_zero, neg_zero, smul_add, smul_neg, Finset.smul_sum, neg_add_rev, neg_neg,
    ← Finset.sum_neg_distrib] at hmul
  have hsq : negOnePowCast R (S j.val) • negOnePowCast R (S j.val) •
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) =
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) := by
    rw [smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_eq_intCast,
      Int.negOnePow_even _ ⟨S j.val, two_mul _⟩]; simp
  rw [hsq, Finset.sum_congr rfl fun s _ ↦ by
    rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.add_right_comm j.val s 1]] at hmul
  exact Eq.trans (by abel) hmul

private theorem taylor_of_two_neg_smul_duplicateAt (𝒜 : AInfinityAlgebra R A) (e : A) {m : ℕ}
    (j : Fin (m + 2)) (w : Fin (m + 3) → A) (c : R) (u₀ : A) :
    𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![-(c • u₀), w (Fin.last (m + 2))])) =
      -(c • 𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![u₀, duplicateAt e j.castSucc w (Fin.last (m + 3))]))) := by
  have hlast : duplicateAt e j.castSucc w (Fin.last (m + 3)) = w (Fin.last (m + 2)) := by
    rw [← Fin.succ_last]
    exact duplicateAt_succ_of_gt e w (Fin.castSucc_lt_last j)
  have hv₁ : (![-(c • u₀), w (Fin.last (m + 2))] : Fin 2 → A) =
      Function.update ![u₀, w (Fin.last (m + 2))] 0 ((-c) • u₀) := by
    ext k; fin_cases k <;> simp [neg_smul]
  have hupd : Function.update ![u₀, w (Fin.last (m + 2))] 0 u₀ = ![u₀, w (Fin.last (m + 2))] := by
    simp
  rw [hlast, hv₁, (PiTensorProduct.tprod R).map_update_smul, hupd, RingHom.id_apply, map_smul,
    map_smul, neg_smul]

private theorem hochschildDifferential_unitKillingCochain_same {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπe : π e = 1) (m : ℕ) (j : Fin (m + 2)) (hlow : 𝒜.KillsUnitUpTo e (m + 2))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j.castSucc = e)
    (h𝒟j : 𝒟 j.castSucc = -1) :
    𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) +
      𝒜.hochschildDifferential 0 (unitKillingCochain 𝒜 e π m j)
        (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) = 0 := by
  have _hjn := j.isLt
  let S : ℕ → ℤ := fun p ↦ ∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0
  let φ := unitKillingCochain 𝒜 e π m j
  -- Initial `(m + 2)`-collapse in `m ∘ gradedCoderiv φ`: duplicates `e` at slot `j` of the prefix.
  have hinit : φ (subword R w 0 (m + 2)) =
      -(negOnePowCast R (S j.val) •
          𝒜.taylor (subword R (duplicateAt e j.castSucc w) 0 (m + 3))) := by
    have hsub : subword R w 0 (m + 2) =
        of R A ⟨m + 2, by omega⟩ (PiTensorProduct.tprod R fun r : Fin (m + 2) ↦ w r.castSucc) := by
      rw [subword_eq_of_tprod R w (by omega) (by omega)]
      simp only [zero_add]
      rfl
    rw [hsub, unitKillingCochain_of_tprod_of_homogeneous 𝒜 e π m j (𝒟 := fun r ↦ 𝒟 r.castSucc)
        (fun r _ ↦ hw r.castSucc), hwj, hπe, one_smul, ← subword_init_duplicateAt_castSucc R]
    congr 3
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    rw [Finset.mem_range] at hr
    rw [dite_eq_left (by omega), dite_eq_left (by omega), Fin.castSucc_mk]
  -- Binary collapses of `b(w)` up to slot `j` match the tail `(m + 2)`-collapse.
  have hpre : (∑ p ∈ Finset.range (j.val + 1),
      negOnePowCast R (S p) • φ (splice R w 0 (m + 3) p 2 (𝒜.taylor (subword R w p 2)))) =
      𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![w 0, φ (subword R w 1 (m + 2))])) := by
    simpa only [Fin.val_castSucc] using
      unitKillingCochain_barDifferential_prefix h𝒜 he π m j hIH hw (i := j.castSucc) le_rfl hwj
  -- Binary collapses of `b(w)` after slot `j` commute with duplicating `e` at slot `j`.
  have hsuf : (∑ s ∈ Finset.range (m + 1 - j.val),
      negOnePowCast R (S (j.val + 1 + s)) •
        φ (splice R w 0 (m + 3) (j.val + 1 + s) 2 (𝒜.taylor (subword R w (j.val + 1 + s) 2)))) =
      -(∑ s ∈ Finset.range (m + 1 - j.val),
          negOnePowCast R (S j.val) • negOnePowCast R (S (j.val + 1 + s)) •
            𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.val + 1 + s + 1) 2
              (𝒜.taylor (subword R w (j.val + 1 + s) 2)))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [unitKillingCochain_splice_two_after hπe m j hw hwj (Finset.mem_range.1 hs), smul_neg,
      smul_comm]
  -- Assemble `δφ(w) = m(gradedCoderiv φ w) - φ(b w)` and match `rescaled_stasheff_duplicateAt`.
  have hdφ : 𝒜.hochschildDifferential 0 φ (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) =
      -(negOnePowCast R (S j.val) •
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![𝒜.taylor (subword R (duplicateAt e j.castSucc w) 0 (m + 3)),
              duplicateAt e j.castSucc w (Fin.last (m + 3))]))) +
        𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![w 0, φ (subword R w 1 (m + 2))])) -
      (𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![w 0, φ (subword R w 1 (m + 2))])) +
        -(∑ s ∈ Finset.range (m + 1 - j.val),
            negOnePowCast R (S j.val) • negOnePowCast R (S (j.val + 1 + s)) •
              𝒜.taylor (splice R (duplicateAt e j.castSucc w) 0 (m + 4) (j.val + 1 + s + 1) 2
                (𝒜.taylor (subword R w (j.val + 1 + s) 2))))) := by
    rw [hochschildDifferential_eq_brace_sub, negOnePowCast_zero, one_smul, LinearMap.sub_apply,
      brace_def, brace_def, LinearMap.comp_apply, LinearMap.comp_apply, ← barDifferential_def,
      taylor_gradedCoderiv_unitKillingCochain 𝒜 e π m j hw,
      unitKillingCochain_barDifferential_of_tprod 𝒜 e π m j hw]
    conv_lhs =>
      rhs
      rw [← Nat.add_sub_of_le (Nat.succ_le_of_lt j.isLt), Nat.succ_sub_succ, Finset.sum_range_add]
    rw [hpre, hsuf, hinit, taylor_of_two_neg_smul_duplicateAt 𝒜 e j w]
  rw [hdφ]
  exact Eq.trans (by abel) (rescaled_stasheff_duplicateAt h𝒜 he m j hlow hIH hw hwj h𝒟j)

/-! ### Gauge induction over input positions -/

private theorem exists_gauge_kill_slot {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal) {e : A}
    (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0)
    (hπe : π e = 1) {m : ℕ} (hlow : 𝒜.KillsUnitUpTo e (m + 2)) (j : Fin (m + 2))
    (hIH : 𝒜.KillsUnitBeforeSlot e (m + 3) j.val) :
    ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      𝒜'.KillsUnitBeforeSlot e (m + 3) (j.val + 1) ∧
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
    killsUnitBeforeSlot_iff.2 fun x k hk hxk ↦ ?_,
    fun z hz ↦ by rw [taylor_gaugeHom, LinearMap.add_apply, hφe z hz, add_zero],
    isIso_gaugeHom 𝒜 φ hφ hφ₁, linearPart_gaugeHom 𝒜 φ hφ hφ₁⟩
  refine of_tprod_mem_of_mem_piece (𝒜.grading.shift 1) he.mem_shift_one_piece
    (S := LinearMap.ker (𝒜.gauge φ hφ hφ₁).taylor) ⟨m + 3, by omega⟩ k
    (fun w 𝒟 hw hwk h𝒟k ↦ ?_) x hxk
  rw [LinearMap.mem_ker, h𝒜.taylor_gauge_apply_of_mem_filtration hφ hφ₁ hφe
    (of_mem_filtration R A (k := ⟨m + 3, by omega⟩) (by omega : m + 3 ≤ 2 * (m + 1) + 1) _)]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
  · rw [killsUnitBeforeSlot_iff.1 hIH w k hlt hwk,
      hochschildDifferential_unitKillingCochain_of_lt h𝒜 he π m j hIH hw hlt hwk, add_zero]
  · have hk' : k = j.castSucc := Fin.ext heq; subst hk'
    exact hochschildDifferential_unitKillingCochain_same h𝒜 he hπe m j hlow hIH hw hwk h𝒟k

private theorem exists_gauge_kill_slots {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal) {e : A}
    (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A} (hπ : π ∈ 𝒜.grading.dualPiece 0)
    (hπe : π e = 1) {m : ℕ} (hlow : 𝒜.KillsUnitUpTo e (m + 2)) :
    ∀ r ≤ m + 2, ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      𝒜'.KillsUnitBeforeSlot e (m + 3) r ∧
      (∀ z ∈ filtration R A (m + 1), g.taylor z = letter R A z) ∧
      g.IsIso ∧ g.linearPart = LinearMap.id
  | 0, _ => ⟨𝒜, .id 𝒜, rfl, h𝒜, fun _ _ ↦ rfl, 𝒜.killsUnitBeforeSlot_zero e _,
      fun _ _ ↦ by rw [AInfinityHom.taylor_id], AInfinityHom.isIso_id 𝒜,
      AInfinityHom.linearPart_id 𝒜⟩
  | r + 1, hr => by
    obtain ⟨𝒜₁, g₁, hG₁, hmin₁, htay₁, hIH₁, hg₁_filt, hg₁_iso, hg₁_lin⟩ :=
      exists_gauge_kill_slots h𝒜 he hπ hπe hlow r (by omega)
    have he₁ := h𝒜.cohomologicalUnit_of_m_two_eq hmin₁ hG₁
      (m_eq_of_taylor_eq_on_filtration hG₁ (by omega) htay₁) he
    obtain ⟨𝒜₂, g₂, hG₂, hmin₂, htay₂, hIH₂, hg₂_filt, hg₂_iso, hg₂_lin⟩ :=
      exists_gauge_kill_slot hmin₁ he₁ (hG₁ ▸ hπ) hπe (hlow.of_taylor_eq htay₁) ⟨r, hr⟩ hIH₁
    exact ⟨𝒜₂, g₁.comp g₂, hG₂.trans hG₁, hmin₂, fun z hz ↦ (htay₂ z hz).trans (htay₁ z hz), hIH₂,
      fun z hz ↦ (g₁.taylor_comp_apply_of_mem_filtration_of_taylor_eq_letter hg₂_filt hz).trans
        (hg₁_filt z hz), hg₁_iso.comp hg₂_iso,
      by rw [AInfinityHom.linearPart_comp, hg₁_lin, hg₂_lin, LinearMap.comp_id]⟩

/-- **Arity-`m + 3` unit elimination on a minimal `A∞` algebra.** Given a minimal `A∞` algebra `𝒜`,
a cohomological unit `e`, and `π ∈ 𝒜.grading.dualPiece 0` with `π e = 1`, if
`𝒜.KillsUnitUpTo e (m + 2)` holds, then there exist a minimal `A∞` structure `𝒜'` with the same
grading satisfying `𝒜'.KillsUnitUpTo e (m + 3)` and an `A∞` isomorphism `g : 𝒜' ⟶ 𝒜` with
`g.linearPart = id` agreeing with `𝒜` on `filtration (m + 2)` and with `letter` on
`filtration (m + 1)`. -/
theorem IsMinimal.exists_killsUnitUpTo_isIso_of_mem_dualPiece {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {π : Module.Dual R A}
    (hπ : π ∈ 𝒜.grading.dualPiece 0) (hπe : π e = 1) (m : ℕ) (hlow : 𝒜.KillsUnitUpTo e (m + 2)) :
    ∃ (𝒜' : AInfinityAlgebra R A) (g : AInfinityHom 𝒜' 𝒜),
      𝒜'.grading = 𝒜.grading ∧ 𝒜'.IsMinimal ∧
      (∀ z ∈ filtration R A (m + 2), 𝒜'.taylor z = 𝒜.taylor z) ∧
      𝒜'.KillsUnitUpTo e (m + 3) ∧
      (∀ z ∈ filtration R A (m + 1), g.taylor z = letter R A z) ∧
      g.IsIso ∧ g.linearPart = LinearMap.id := by
  obtain ⟨𝒜', g, hG', hmin', htay', hIH', hg_filt, hg_iso, hg_lin⟩ :=
    exists_gauge_kill_slots h𝒜 he hπ hπe hlow (m + 2) le_rfl
  have he' := h𝒜.cohomologicalUnit_of_m_two_eq hmin' hG'
    (m_eq_of_taylor_eq_on_filtration hG' (by omega) htay') he
  have hlow' := hlow.of_taylor_eq htay'
  refine ⟨𝒜', g, hG', hmin', htay', killsUnitUpTo_iff.2 fun k hk2 hkle x ⟨s, hxs⟩ ↦ ?_,
    hg_filt, hg_iso, hg_lin⟩
  rcases Nat.lt_or_eq_of_le hkle with hklt | hkeq
  · exact killsUnitUpTo_iff.1 hlow' k hk2 (by omega) x ⟨s, hxs⟩
  · obtain ⟨kval, _⟩ := k; dsimp only at hkeq; subst hkeq
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ s.isLt) with hslt | hseq
    · exact killsUnitBeforeSlot_iff.1 hIH' x s hslt hxs
    · exact hmin'.taylor_of_tprod_last_eq_zero he' hlow' hIH' x
        ((congrArg x (Fin.ext hseq.symm)).trans hxs)

end UnitKilling

end TauCeti.AInfinityAlgebra
