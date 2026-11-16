/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.UniversalCentralExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import TauCeti.GroupTheory.Commutator

/-!
# Central extensions and universal lifting for Steinberg groups

For an index type `ι` with at least five elements, every homomorphism `φ : St_ι(R) →* H` into a
group `H` lifts uniquely through any homomorphism `q : E →* H` whose kernel is central in `E` and
whose image contains the image of `φ`.

The lifting construction follows Milnor's proof of the Kervaire–Steinberg theorem:

1. Because `q.ker ≤ Subgroup.center E`, the commutator `⁅u, v⁆` of two lifts depends only on
   `q u` and `q v`.
2. When `j ≠ k` and `i ≠ l`, choosing a fifth index `m ∉ {i, j, k, l}` expresses `φ(xᵢⱼ(a))` as
   `⁅φ(xᵢₘ(a)), φ(xₘⱼ(1))⁆` where `xₖₗ(b)` commutes with both `xᵢₘ(a)` and `xₘⱼ(1)`. Any lift of
   `φ(xₖₗ(b))` therefore commutes with any lift of `φ(xᵢⱼ(a))`.
3. A commutator associativity identity shows that for any `k ∉ {i, j}`, the commutator
   `⁅u, v⁆` of lifts of `φ(xᵢₖ(a))` and `φ(xₖⱼ(b))` depends only on `i, j` and `a * b`.
4. Defining `yᵢⱼ(a) := ⁅u, v⁆` for arbitrary lifts of `φ(xᵢₖ(a))` and `φ(xₖⱼ(1))` yields elements
   of `E` satisfying all three Steinberg relations, hence a homomorphism `St_ι(R) →* E` lifting `φ`.
   Uniqueness follows from perfectness of `St_ι(R)`.

As immediate consequences:

* Every central extension of `St_ι(R)` splits uniquely when `5 ≤ ENat.card ι` (i.e., `St_ι(R)` is
  centrally closed).
* For finite `ι` with `5 ≤ Fintype.card ι`, if `ker (toGL ι R)` is central then
  `toElementary ι R : St_ι(R) →* E_ι(R)` is a universal central extension.
* In `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Stable`, combining this lifting
  theorem with centrality of `ker (toStableGL R)` establishes the Kervaire–Steinberg universal
  central extension theorem for `St(R) →* E_∞(R)`.

## Main definitions

* `TauCeti.SteinbergGroup.liftOfCentralExtension`: the unique lift `St_ι(R) →* E` of
  `φ : St_ι(R) →* H` across `q : E →* H` with `φ.range ≤ q.range` and `q.ker ≤ Subgroup.center E`,
  for `5 ≤ ENat.card ι`.

## Main results

* `TauCeti.SteinbergGroup.comp_liftOfCentralExtension`,
  `TauCeti.SteinbergGroup.liftOfCentralExtension_of_eq_commutatorElement`,
  `TauCeti.SteinbergGroup.liftOfCentralExtension_unique`,
  `TauCeti.SteinbergGroup.existsUnique_lift_of_ker_le_center`: existence, commutator formula, and
  uniqueness of lifts across central extensions.
* `TauCeti.SteinbergGroup.map_liftOfCentralExtension`: naturality of lifts with respect to
  morphisms of central extensions.
* `TauCeti.SteinbergGroup.existsUnique_section_of_isCentralExtension`,
  `TauCeti.SteinbergGroup.existsUnique_section_fin`: every central extension of `St_ι(R)`
  (`|ι| ≥ 5`) or `St_n(R)` (`n ≥ 5`) splits uniquely.
* `TauCeti.SteinbergGroup.isUniversalCentralExtension_toElementary_of_ker_le_center`: conditional
  finite-rank universal central extension theorem for `5 ≤ Fintype.card ι`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  §5, Theorem 5.10.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.
-/

public section

open scoped commutatorElement

namespace TauCeti

namespace SteinbergGroup

universe w u v

section Lifting

variable {ι : Type w} {R : Type u} [Ring R]
variable {H : Type*} [Group H] {E : Type v} [Group E]

/-- Distant lifts commute: if `j ≠ k` and `i ≠ l`, then any lifts `u, v ∈ E` of `φ(xᵢⱼ(a))` and
`φ(xₖₗ(b))` commute. This holds in particular when `(i, j) = (k, l)`. -/
private theorem commute_of_map_eq_of_distant {φ : SteinbergGroup ι R →* H} {q : E →* H}
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) {a b : R} {u v : E}
    (hu : q u = φ (of hij a)) (hv : q v = φ (of hkl b)) : Commute u v := by
  classical
  have hcard : ({i, j, k, l} : Finset ι).card ≤ 4 := by
    calc ({i, j, k, l} : Finset ι).card
        ≤ ({j, k, l} : Finset ι).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({k, l} : Finset ι).card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
      _ ≤ 2 + 1 + 1 := by gcongr; exact Finset.card_le_two
      _ = 4 := rfl
  have hlt : (({i, j, k, l} : Finset ι).card : ℕ∞) < ENat.card ι :=
    lt_of_le_of_lt (Nat.cast_le.mpr hcard)
      (lt_of_lt_of_le (Nat.cast_lt.mpr (by decide : 4 < 5)) hι)
  obtain ⟨m, hm⟩ := Finset.exists_notMem_of_card_lt_enatCard hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hm
  obtain ⟨hmi, hmj, hmk, hml⟩ := hm
  obtain ⟨u₁, hu₁⟩ := hsurj ⟨of hmi.symm a, rfl⟩
  obtain ⟨u₂, hu₂⟩ := hsurj ⟨of hmj 1, rfl⟩
  have hcomm_eq : q ⁅u₁, u₂⁆ = q u := by
    rw [map_commutatorElement, hu₁, hu₂, ← map_commutatorElement,
      commutatorElement_of hmi.symm hmj hij, mul_one, hu]
  have hz : ⁅u₁, u₂⁆⁻¹ * u ∈ Subgroup.center E := hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm_eq, inv_mul_cancel]
  have hvu₁ : ⁅v, u₁⁆ ∈ Subgroup.center E := hker <| by
    rw [MonoidHom.mem_ker, map_commutatorElement, hv, hu₁, ← map_commutatorElement,
      (commute_of hkl hmi.symm hil.symm hmk.symm b a).commutator_eq, map_one]
  have hvu₂ : ⁅v, u₂⁆ ∈ Subgroup.center E := hker <| by
    rw [MonoidHom.mem_ker, map_commutatorElement, hv, hu₂, ← map_commutatorElement,
      (commute_of hkl hmj hml.symm hjk.symm b 1).commutator_eq, map_one]
  have hvc : Commute v ⁅u₁, u₂⁆ := commute_commutatorElement_of_mem_center hvu₁ hvu₂
  have hvz : Commute v (⁅u₁, u₂⁆⁻¹ * u) := Subgroup.mem_center_iff.mp hz v
  have hvu : Commute v u := by
    simpa only [mul_inv_cancel_left] using hvc.mul_right hvz
  exact hvu.symm

/-- For pairwise distinct `i, j, k, l`, the commutator of lifts of `φ(xᵢₖ(a))` and `φ(xₖⱼ(b))`
equals the commutator of lifts of `φ(xᵢₗ(a * b))` and `φ(xₗⱼ(1))`. -/
private theorem commutatorElement_lift_eq_of_ne {φ : SteinbergGroup ι R →* H} {q : E →* H}
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k l : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (hil : i ≠ l) (hlj : l ≠ j)
    (hkl : k ≠ l) {a b : R} {u v u' v' : E}
    (hu : q u = φ (of hik a)) (hv : q v = φ (of hkj b))
    (hu' : q u' = φ (of hil (a * b))) (hv' : q v' = φ (of hlj 1)) :
    ⁅u, v⁆ = ⁅u', v'⁆ := by
  obtain ⟨m, hm⟩ := hsurj ⟨of hkl b, rfl⟩
  have hqm : q ⁅u, m⁆ = φ (of hil (a * b)) := by
    rw [map_commutatorElement, hu, hm, ← map_commutatorElement, commutatorElement_of hik hkl hil]
  have hmw : q ⁅m, v'⁆ = φ (of hkj b) := by
    rw [map_commutatorElement, hm, hv', ← map_commutatorElement,
      commutatorElement_of hkl hlj hkj, mul_one]
  have humw : q ⁅u, ⁅m, v'⁆⁆ = φ (of hij (a * b)) := by
    rw [map_commutatorElement, hu, hmw, ← map_commutatorElement,
      commutatorElement_of hik hkj hij]
  have huv' : Commute u v' :=
    commute_of_map_eq_of_distant hsurj hker hι hik hlj hkl hij hu hv'
  have h₁ : Commute ⁅u, m⁆ ⁅m, v'⁆ :=
    commute_of_map_eq_of_distant hsurj hker hι hil hkj hkl.symm hij hqm hmw
  have h₂ : Commute ⁅u, ⁅m, v'⁆⁆ ⁅m, v'⁆ :=
    commute_of_map_eq_of_distant hsurj hker hι hij hkj hkj.symm hij humw hmw
  calc ⁅u, v⁆
      = ⁅u, ⁅m, v'⁆⁆ := MonoidHom.commutatorElement_eq_of_ker_le_center hker rfl (hv.trans hmw.symm)
    _ = ⁅⁅u, m⁆, v'⁆ := (commutatorElement_assoc_of_commute huv' h₁ h₂).symm
    _ = ⁅u', v'⁆ := MonoidHom.commutatorElement_eq_of_ker_le_center hker (hqm.trans hu'.symm) rfl

/-- For any `k, l ∉ {i, j}` (possibly `k = l`), the commutator of lifts of `φ(xᵢₖ(a))` and
`φ(xₖⱼ(b))` equals the commutator of lifts of `φ(xᵢₗ(a * b))` and `φ(xₗⱼ(1))`. -/
private theorem commutatorElement_lift_eq {φ : SteinbergGroup ι R →* H} {q : E →* H}
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k l : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (hil : i ≠ l) (hlj : l ≠ j)
    {a b : R} {u v u' v' : E}
    (hu : q u = φ (of hik a)) (hv : q v = φ (of hkj b))
    (hu' : q u' = φ (of hil (a * b))) (hv' : q v' = φ (of hlj 1)) :
    ⁅u, v⁆ = ⁅u', v'⁆ := by
  by_cases hkl : k = l
  · subst hkl
    classical
    have hcard : ({i, j, k} : Finset ι).card ≤ 3 := by
      calc ({i, j, k} : Finset ι).card
          ≤ ({j, k} : Finset ι).card + 1 := Finset.card_insert_le _ _
        _ ≤ 2 + 1 := by gcongr; exact Finset.card_le_two
        _ = 3 := rfl
    have hlt : (({i, j, k} : Finset ι).card : ℕ∞) < ENat.card ι :=
      lt_of_le_of_lt (Nat.cast_le.mpr hcard)
        (lt_of_lt_of_le (Nat.cast_lt.mpr (by decide : 3 < 5)) hι)
    obtain ⟨m, hm⟩ := Finset.exists_notMem_of_card_lt_enatCard hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hm
    obtain ⟨hmi, hmj, hmk⟩ := hm
    obtain ⟨um, hum⟩ := hsurj ⟨of hmi.symm (a * b), rfl⟩
    obtain ⟨vm, hvm⟩ := hsurj ⟨of hmj 1, rfl⟩
    have h₁ : ⁅u, v⁆ = ⁅um, vm⁆ :=
      commutatorElement_lift_eq_of_ne hsurj hker hι hij hik hkj hmi.symm hmj hmk.symm hu hv hum hvm
    have h₂ : ⁅um, vm⁆ = ⁅u', v'⁆ := by
      have hu'' : q u' = φ (of hik ((a * b) * 1)) := by simpa only [mul_one] using hu'
      exact commutatorElement_lift_eq_of_ne hsurj hker hι hij hmi.symm hmj hik hkj hmk
        hum hvm hu'' hv'
    exact h₁.trans h₂
  · exact commutatorElement_lift_eq_of_ne hsurj hker hι hij hik hkj hil hlj hkl hu hv hu' hv'

/-- Auxiliary generator lift `yᵢⱼ(a) ∈ E`: chosen as `⁅u, v⁆` for a third index `k ∉ {i, j}` and
lifts `u, v` of `φ(xᵢₖ(a))` and `φ(xₖⱼ(1))`. -/
private noncomputable def liftGen (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hι : 5 ≤ ENat.card ι) {i j : ι} (_ : i ≠ j) (a : R) : E :=
  let h3 : ∃ k : ι, k ≠ i ∧ k ≠ j :=
    ENat.exists_ne_ne_of_three_le (le_trans (Nat.cast_le.mpr (by decide : 3 ≤ 5)) hι) i j
  let hk := Classical.choose_spec h3
  let u := Classical.choose (hsurj ⟨of hk.1.symm a, rfl⟩)
  let v := Classical.choose (hsurj ⟨of hk.2 1, rfl⟩)
  ⁅u, v⁆

private theorem map_liftGen (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hι : 5 ≤ ENat.card ι) {i j : ι} (hij : i ≠ j) (a : R) :
    q (liftGen φ q hsurj hι hij a) = φ (of hij a) := by
  dsimp only [liftGen]
  set h3 : ∃ k : ι, k ≠ i ∧ k ≠ j :=
    ENat.exists_ne_ne_of_three_le (le_trans (Nat.cast_le.mpr (by decide : 3 ≤ 5)) hι) i j
  have hk : Classical.choose h3 ≠ i ∧ Classical.choose h3 ≠ j := Classical.choose_spec h3
  have hu : q (Classical.choose (hsurj ⟨of hk.1.symm a, rfl⟩)) = φ (of hk.1.symm a) :=
    Classical.choose_spec (hsurj ⟨of hk.1.symm a, rfl⟩)
  have hv : q (Classical.choose (hsurj ⟨of hk.2 1, rfl⟩)) = φ (of hk.2 1) :=
    Classical.choose_spec (hsurj ⟨of hk.2 1, rfl⟩)
  rw [map_commutatorElement, hu, hv, ← map_commutatorElement,
    commutatorElement_of hk.1.symm hk.2 hij, mul_one]

private theorem liftGen_eq_commutatorElement (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) {a b : R} {u v : E}
    (hu : q u = φ (of hik a)) (hv : q v = φ (of hkj b)) :
    liftGen φ q hsurj hι hij (a * b) = ⁅u, v⁆ := by
  dsimp only [liftGen]
  set h3 : ∃ l : ι, l ≠ i ∧ l ≠ j :=
    ENat.exists_ne_ne_of_three_le (le_trans (Nat.cast_le.mpr (by decide : 3 ≤ 5)) hι) i j
  have hl : Classical.choose h3 ≠ i ∧ Classical.choose h3 ≠ j := Classical.choose_spec h3
  have hu' : q (Classical.choose (hsurj ⟨of hl.1.symm (a * b), rfl⟩)) = φ (of hl.1.symm (a * b)) :=
    Classical.choose_spec (hsurj ⟨of hl.1.symm (a * b), rfl⟩)
  have hv' : q (Classical.choose (hsurj ⟨of hl.2 1, rfl⟩)) = φ (of hl.2 1) :=
    Classical.choose_spec (hsurj ⟨of hl.2 1, rfl⟩)
  exact (commutatorElement_lift_eq hsurj hker hι hij hik hkj hl.1.symm hl.2 hu hv hu' hv').symm

private theorem liftGen_add (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j : ι} (hij : i ≠ j) (a b : R) :
    liftGen φ q hsurj hι hij a * liftGen φ q hsurj hι hij b =
      liftGen φ q hsurj hι hij (a + b) := by
  obtain ⟨k, hki, hkj⟩ :=
    ENat.exists_ne_ne_of_three_le (le_trans (Nat.cast_le.mpr (by decide : 3 ≤ 5)) hι) i j
  let u₁ := liftGen φ q hsurj hι hki.symm a
  let u₂ := liftGen φ q hsurj hι hki.symm b
  let v := liftGen φ q hsurj hι hkj 1
  have hu₁ : q u₁ = φ (of hki.symm a) := map_liftGen φ q hsurj hι hki.symm a
  have hu₂ : q u₂ = φ (of hki.symm b) := map_liftGen φ q hsurj hι hki.symm b
  have hv : q v = φ (of hkj 1) := map_liftGen φ q hsurj hι hkj 1
  have hu₁₂ : q (u₁ * u₂) = φ (of hki.symm (a + b)) := by
    rw [map_mul, hu₁, hu₂, ← map_mul, of_mul_of]
  have hsum : liftGen φ q hsurj hι hij (a + b) = ⁅u₁ * u₂, v⁆ := by
    simpa only [mul_one] using
      liftGen_eq_commutatorElement φ q hsurj hker hι hij hki.symm hkj hu₁₂ hv
  have ha : liftGen φ q hsurj hι hij a = ⁅u₁, v⁆ := by
    simpa only [mul_one] using
      liftGen_eq_commutatorElement φ q hsurj hker hι hij hki.symm hkj hu₁ hv
  have hb : liftGen φ q hsurj hι hij b = ⁅u₂, v⁆ := by
    simpa only [mul_one] using
      liftGen_eq_commutatorElement φ q hsurj hker hι hij hki.symm hkj hu₂ hv
  have hcu₁ : Commute u₁ (liftGen φ q hsurj hι hij b) :=
    commute_of_map_eq_of_distant hsurj hker hι hki.symm hij hki hij hu₁
      (map_liftGen φ q hsurj hι hij b)
  have hcab : Commute (liftGen φ q hsurj hι hij a) (liftGen φ q hsurj hι hij b) :=
    commute_of_map_eq_of_distant hsurj hker hι hij hij hij.symm hij
      (map_liftGen φ q hsurj hι hij a) (map_liftGen φ q hsurj hι hij b)
  rw [hsum, commutatorElement_mul_left_eq_conj_mul, ← ha, ← hb, hcu₁.eq,
    mul_inv_cancel_right, hcab.eq]

private theorem liftGen_comm (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) (a b : R) :
    Commute (liftGen φ q hsurj hι hij a) (liftGen φ q hsurj hι hkl b) :=
  commute_of_map_eq_of_distant hsurj hker hι hij hkl hjk hil
    (map_liftGen φ q hsurj hι hij a) (map_liftGen φ q hsurj hι hkl b)

private theorem liftGen_rel (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅liftGen φ q hsurj hι hij a, liftGen φ q hsurj hι hjk b⁆ =
      liftGen φ q hsurj hι hik (a * b) :=
  (liftGen_eq_commutatorElement φ q hsurj hker hι hik hij hjk
    (map_liftGen φ q hsurj hι hij a) (map_liftGen φ q hsurj hι hjk b)).symm

/-- **Central-extension lifting theorem for Steinberg groups**: if `ι` has at least five elements,
every homomorphism `φ : St_ι(R) →* H` lifts across any homomorphism `q : E →* H` with
`φ.range ≤ q.range` and `q.ker ≤ Subgroup.center E`. -/
noncomputable def liftOfCentralExtension (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι) :
    SteinbergGroup ι R →* E :=
  lift (fun hij a => liftGen φ q hsurj hι hij a)
    (fun hij a b => liftGen_add φ q hsurj hker hι hij a b)
    (fun hij hkl hjk hil a b => liftGen_comm φ q hsurj hker hι hij hkl hjk hil a b)
    (fun hij hjk hik a b => liftGen_rel φ q hsurj hker hι hij hjk hik a b)

private theorem liftOfCentralExtension_of (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j : ι} (hij : i ≠ j) (a : R) :
    liftOfCentralExtension φ q hsurj hker hι (of hij a) = liftGen φ q hsurj hι hij a :=
  lift_of _ (fun hij a b => liftGen_add φ q hsurj hker hι hij a b)
    (fun hij hkl hjk hil a b => liftGen_comm φ q hsurj hker hι hij hkl hjk hil a b)
    (fun hij hjk hik a b => liftGen_rel φ q hsurj hker hι hij hjk hik a b) hij a

/-- Composing `liftOfCentralExtension` with `q` recovers `φ`. -/
@[simp]
theorem comp_liftOfCentralExtension (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι) :
    q.comp (liftOfCentralExtension φ q hsurj hker hι) = φ := by
  refine hom_ext fun hij a => ?_
  rw [MonoidHom.comp_apply, liftOfCentralExtension_of, map_liftGen]

/-- Applying `q` to `liftOfCentralExtension φ q ... x` yields `φ x`. -/
@[simp]
theorem apply_liftOfCentralExtension (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    (x : SteinbergGroup ι R) :
    q (liftOfCentralExtension φ q hsurj hker hι x) = φ x :=
  DFunLike.congr_fun (comp_liftOfCentralExtension φ q hsurj hker hι) x

/-- On a root generator `xᵢⱼ(a * b)`, `liftOfCentralExtension` equals the commutator `⁅u, v⁆` of
any lifts `u` of `φ(xᵢₖ(a))` and `v` of `φ(xₖⱼ(b))` for any third index `k ∉ {i, j}`. -/
theorem liftOfCentralExtension_of_eq_commutatorElement (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) {a b : R} {u v : E}
    (hu : q u = φ (of hik a)) (hv : q v = φ (of hkj b)) :
    liftOfCentralExtension φ q hsurj hker hι (of hij (a * b)) = ⁅u, v⁆ := by
  rw [liftOfCentralExtension_of]
  exact liftGen_eq_commutatorElement φ q hsurj hker hι hij hik hkj hu hv

/-- Specialization of `liftOfCentralExtension_of_eq_commutatorElement` with `b = 1`: the lifted
generator `xᵢⱼ(a)` is the commutator `⁅u, v⁆` of any lifts of `φ(xᵢₖ(a))` and `φ(xₖⱼ(1))`. -/
theorem liftOfCentralExtension_of_eq_commutatorElement_one (φ : SteinbergGroup ι R →* H)
    (q : E →* H) (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E)
    (hι : 5 ≤ ENat.card ι) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) {a : R}
    {u v : E} (hu : q u = φ (of hik a)) (hv : q v = φ (of hkj 1)) :
    liftOfCentralExtension φ q hsurj hker hι (of hij a) = ⁅u, v⁆ := by
  simpa only [mul_one] using
    liftOfCentralExtension_of_eq_commutatorElement φ q hsurj hker hι hij hik hkj hu hv

/-- Any lift of `φ : St_ι(R) →* H` across a central homomorphism `q : E →* H` equals
`liftOfCentralExtension`. -/
theorem liftOfCentralExtension_unique (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι)
    {ψ : SteinbergGroup ι R →* E} (hψ : q.comp ψ = φ) :
    ψ = liftOfCentralExtension φ q hsurj hker hι := by
  have : Group.IsPerfect (SteinbergGroup ι R) :=
    isPerfect_of_three_le_enatCard (le_trans (Nat.cast_le.mpr (by decide : 3 ≤ 5)) hι)
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hker
    (hψ.trans (comp_liftOfCentralExtension φ q hsurj hker hι).symm)

/-- Existence and uniqueness of a lift of `φ : St_ι(R) →* H` across `q : E →* H` with
`φ.range ≤ q.range` and `q.ker ≤ Subgroup.center E` when `5 ≤ ENat.card ι`. -/
theorem existsUnique_lift_of_ker_le_center (φ : SteinbergGroup ι R →* H) (q : E →* H)
    (hsurj : φ.range ≤ q.range) (hker : q.ker ≤ Subgroup.center E) (hι : 5 ≤ ENat.card ι) :
    ∃! ψ : SteinbergGroup ι R →* E, q.comp ψ = φ :=
  ⟨liftOfCentralExtension φ q hsurj hker hι,
    comp_liftOfCentralExtension φ q hsurj hker hι,
    fun _ hψ => liftOfCentralExtension_unique φ q hsurj hker hι hψ⟩

/-- Naturality of `liftOfCentralExtension` with respect to a morphism `f : E₁ →* E₂` of central
extensions over `H`. -/
theorem map_liftOfCentralExtension {E₁ E₂ : Type*} [Group E₁] [Group E₂]
    (φ : SteinbergGroup ι R →* H) (q₁ : E₁ →* H) (q₂ : E₂ →* H) (f : E₁ →* E₂)
    (hf : q₂.comp f = q₁) (hsurj₁ : φ.range ≤ q₁.range) (hsurj₂ : φ.range ≤ q₂.range)
    (hker₁ : q₁.ker ≤ Subgroup.center E₁) (hker₂ : q₂.ker ≤ Subgroup.center E₂)
    (hι : 5 ≤ ENat.card ι) :
    f.comp (liftOfCentralExtension φ q₁ hsurj₁ hker₁ hι) =
      liftOfCentralExtension φ q₂ hsurj₂ hker₂ hι :=
  liftOfCentralExtension_unique φ q₂ hsurj₂ hker₂ hι <| by
    rw [← MonoidHom.comp_assoc, hf, comp_liftOfCentralExtension]

/-! ## Central closedness and finite-rank universal central extensions -/

/-- **Central closedness of Steinberg groups**: when `5 ≤ ENat.card ι`, every central extension of
`SteinbergGroup ι R` splits uniquely. -/
theorem existsUnique_section_of_isCentralExtension {q : E →* SteinbergGroup ι R}
    (hq : q.IsCentralExtension) (hι : 5 ≤ ENat.card ι) :
    ∃! s : SteinbergGroup ι R →* E, q.comp s = MonoidHom.id (SteinbergGroup ι R) :=
  existsUnique_lift_of_ker_le_center (MonoidHom.id (SteinbergGroup ι R)) q
    (by rw [MonoidHom.range_eq_top.mpr hq.surjective]; exact le_top)
    hq.ker_le_center hι

/-- Every central extension of `SteinbergGroup (Fin n) R` splits uniquely for `n ≥ 5`. -/
theorem existsUnique_section_fin {n : ℕ} (hn : 5 ≤ n) {q : E →* SteinbergGroup (Fin n) R}
    (hq : q.IsCentralExtension) :
    ∃! s : SteinbergGroup (Fin n) R →* E, q.comp s = MonoidHom.id (SteinbergGroup (Fin n) R) :=
  existsUnique_section_of_isCentralExtension hq (by simpa using hn)

/-- **Conditional finite-rank universal central extension**: for finite `ι` with
`5 ≤ Fintype.card ι`, if `ker (toGL ι R)` is central in `SteinbergGroup ι R`, then
`toElementary ι R : St_ι(R) →* E_ι(R)` is a universal central extension. -/
theorem isUniversalCentralExtension_toElementary_of_ker_le_center [Fintype ι] [DecidableEq ι]
    (hι : 5 ≤ Fintype.card ι) (hker : (toGL ι R).ker ≤ Subgroup.center (SteinbergGroup ι R)) :
    (toElementary ι R).IsUniversalCentralExtension.{v} where
  isCentralExtension := ⟨toElementary_surjective, (ker_toElementary (ι := ι) (R := R)).symm ▸ hker⟩
  existsUnique_comp_eq _ _ _ hq :=
    existsUnique_lift_of_ker_le_center (toElementary ι R) _
      (by rw [MonoidHom.range_eq_top.mpr hq.surjective]; exact le_top)
      hq.ker_le_center (by simpa [ENat.card_eq_coe_fintype_card] using hι)

end Lifting

end SteinbergGroup

end TauCeti
