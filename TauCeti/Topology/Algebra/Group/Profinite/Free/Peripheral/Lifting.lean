/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.ClosedSpan
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.Topology.Algebra.Group.Profinite.Free.Empty
import TauCeti.Topology.Algebra.Group.Profinite.Free.ResiduallyP
import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

/-!
# Lifting peripheral product identities

For a family `x` in a pro-`p` group and an exponent `u ∈ ℤ_p`, the peripheral defect is the ordered
product of chosen conjugates of the `u`-th powers of the entries of `x` and of its cusp.  Its
`n`-th level consists of the conjugators for which this product lies in the `n`-th term of the
closed lower central series.

For the basis of a finite-rank free pro-`p` group, every pair of conjugators lies at level one.
More importantly, a pair at any positive level can be corrected into one at the next level by
multiplying its conjugators by elements one step lower in the central series.  The correction at
the first basis element is kept trivial.  Iterating this result gives compatible approximate
solutions to the peripheral product identity.

In rank at least two no term of the closed lower central series of a free pro-`p` group is
trivial, so no single level reduces to the exact peripheral product identity merely because its
term `γ_n` vanishes. Passing from these approximate solutions to an exact one uses all the levels
at once, through compactness.

## Main definitions

* `TauCeti.Peripheral.defect`: the ordered peripheral product for chosen conjugators.
* `TauCeti.Peripheral.level`: the conjugators whose defect lies in a specified closed
  lower-central-series term.

## Main results

* `TauCeti.Peripheral.forall_mem_level_iff`: conjugators lie in every peripheral level exactly
  when their defect is trivial.
* `TauCeti.Peripheral.level_one_eq_univ`: every choice of conjugators has defect in `γ₁`.
* `TauCeti.Peripheral.exists_mem_level_succ`: a positive-level solution can be corrected to the
  next level while keeping the correction at the first basis element trivial.
* `TauCeti.Peripheral.closedLowerCentralSeries_ne_bot`: in rank at least two, no term of the
  closed lower central series is trivial.
-/

public section

namespace TauCeti

namespace Peripheral

open Subgroup
open scoped commutatorElement

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- The defect of conjugators `c` on a family `x` and `d` on its cusp: the ordered product of
the corresponding conjugates of their `u`-th powers. -/
noncomputable def defect (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p])
    (c : Fin r → F) (d : F) : F :=
  (List.ofFn fun i ↦ (c i)⁻¹ * hF.padicPow (x i) u * c i).prod *
    (d⁻¹ * hF.padicPow (cusp x) u * d)

/-- The peripheral defect is the ordered product of the conjugated powers of the family followed
by the conjugated power of its cusp. -/
theorem defect_def (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p])
    (c : Fin r → F) (d : F) :
    defect hF x u c d =
      (List.ofFn fun i ↦ (c i)⁻¹ * hF.padicPow (x i) u * c i).prod *
        (d⁻¹ * hF.padicPow (cusp x) u * d) :=
  (rfl)

/-- The peripheral defect is continuous as a function of all its conjugators. -/
theorem continuous_defect (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) :
    Continuous (fun cd : (Fin r → F) × F ↦ defect hF x u cd.1 cd.2) := by
  unfold defect
  apply Continuous.mul
  · simpa only [List.ofFn_eq_map] using
      continuous_list_prod (List.finRange r) fun i _ ↦ by fun_prop
  · fun_prop

/-- The `n`-th peripheral level is the set of conjugators whose defect lies in the `n`-th term
of the closed lower central series. -/
def level (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) (n : ℕ) :
    Set ((Fin r → F) × F) :=
  {cd | defect hF x u cd.1 cd.2 ∈ closedLowerCentralSeries F n}

/-- Membership in a peripheral level means exactly that the corresponding defect lies in the
specified closed lower-central-series term. -/
@[simp]
theorem mem_level_iff (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) (n : ℕ)
    (cd : (Fin r → F) × F) :
    cd ∈ level hF x u n ↔ defect hF x u cd.1 cd.2 ∈ closedLowerCentralSeries F n :=
  Iff.rfl

/-- Every peripheral level is closed. -/
theorem isClosed_level (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) (n : ℕ) :
    IsClosed (level hF x u n) :=
  (isClosed_closedLowerCentralSeries n).preimage (continuous_defect hF x u)

/-- The peripheral levels form a decreasing family. -/
theorem level_antitone (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) :
    Antitone (level hF x u) := by
  intro m n hmn cd hcd
  exact closedLowerCentralSeries_antitone hmn hcd

/-- A pair of conjugators lies in every peripheral level exactly when its defect is trivial: in
a pro-`p` group the terms of the closed lower central series have trivial intersection. -/
theorem forall_mem_level_iff (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p])
    (cd : (Fin r → F) × F) :
    (∀ n, cd ∈ level hF x u n) ↔ defect hF x u cd.1 cd.2 = 1 := by
  rw [← Subgroup.mem_bot, ← hF.iInf_closedLowerCentralSeries_eq_bot Fact.out, Subgroup.mem_iInf]
  simp only [mem_level_iff]

/-- Every choice of conjugators is in the first peripheral level.  In the topological
abelianization, conjugation disappears, `p`-adic powers become scalar multiplication, and the
classes of the family and its cusp sum to zero. -/
@[simp]
theorem level_one_eq_univ (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) :
    level hF x u 1 = Set.univ := by
  ext cd
  simp only [Set.mem_univ, iff_true, mem_level_iff]
  rw [closedLowerCentralSeries_def, ← gradedMkZero_eq_zero_iff]
  let _ := hF.gradedPieceModule 0 0
  simp [defect_def, cusp_def, List.sum_ofFn, ← Finset.smul_sum]

/-- Modulo `γ_{m+2}`, correcting the conjugators `c i` and `d` of the defect by `c' i` and `d'`
multiplies the defect by the product `(∏ i, b' i) * bz'` of the correction commutators
`b' i = ⁅(w i)⁻¹, (c' i)⁻¹⁆`, where `w i` is the conjugated power of the `i`-th entry, and the
cusp commutator `bz' = ⁅wz⁻¹, d'⁻¹⁆`, where `wz` is the conjugated power of the cusp. The
correction commutators `b' i` and `bz'` are assumed to lie in `γ_{m+1}`, which makes them central
modulo `γ_{m+2}`. -/
private theorem mk_defect_mul_correction (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]) (m : ℕ)
    (c c' : Fin r → F) (d d' : F)
    (b' : Fin r → pLowerCentralSeries 0 F (0 + m + 1))
    (bz' : pLowerCentralSeries 0 F (0 + m + 1))
    (hb' : ∀ i, (b' i : F) = ⁅((c i)⁻¹ * hF.padicPow (x i) u * c i)⁻¹, (c' i)⁻¹⁆)
    (hbz' : (bz' : F) = ⁅(d⁻¹ * hF.padicPow (cusp x) u * d)⁻¹, d'⁻¹⁆) :
    ((defect hF x u (fun i ↦ c i * c' i) (d * d') : F) :
        F ⧸ pLowerCentralSeries 0 F ((0 + m + 1) + 1)) =
      ((defect hF x u c d *
          (((List.ofFn b').prod * bz' : pLowerCentralSeries 0 F (0 + m + 1)) : F) : F) :
        F ⧸ pLowerCentralSeries 0 F ((0 + m + 1) + 1)) := by
  let w : Fin r → F := fun i ↦ (c i)⁻¹ * hF.padicPow (x i) u * c i
  let wz : F := d⁻¹ * hF.padicPow (cusp x) u * d
  have hfactor (i : Fin r) :
      (c i * c' i)⁻¹ * hF.padicPow (x i) u * (c i * c' i) = w i * (b' i : F) := by
    rw [hb' i, commutatorElement_def]
    simp only [w]
    group
  have hfactorCusp :
      (d * d')⁻¹ * hF.padicPow (cusp x) u * (d * d') = wz * (bz' : F) := by
    rw [hbz', commutatorElement_def]
    simp only [wz]
    group
  simp only [defect, hfactor, hfactorCusp]
  let N := pLowerCentralSeries 0 F ((0 + m + 1) + 1)
  have hBcoe : ((((List.ofFn b').prod * bz' : pLowerCentralSeries 0 F (0 + m + 1))) : F) =
      (List.ofFn fun i ↦ (b' i : F)).prod * bz' := by
    -- The coercion of an element of the subgroup `γ_{m+1}` to `F` is its subtype homomorphism;
    -- exposing it lets `map_mul` and `map_list_prod` push the coercion through the product.
    change (pLowerCentralSeries 0 F (0 + m + 1)).subtype ((List.ofFn b').prod * bz') = _
    rw [map_mul, map_list_prod, List.map_ofFn]
    rfl
  rw [hBcoe]
  -- Unfold the local abbreviation of the quotient subgroup and restate the goal as the equality
  -- in `F ⧸ N` of `∏ (w i * b' i) * (wz * bz')` with `((∏ w i) * wz) * ((∏ b' i) * bz')`, the
  -- shape to which the quotient multiplication lemmas below apply.
  change (((List.ofFn fun i ↦ w i * (b' i : F)).prod * (wz * bz') : F) : F ⧸ N) =
    ((((List.ofFn w).prod * wz) * ((List.ofFn fun i ↦ (b' i : F)).prod * bz') : F) : F ⧸ N)
  have hcen : ∀ i, (((b' i : F)) : F ⧸ N) ∈ Submonoid.center _ := fun i ↦
    Submonoid.mem_center_iff.mpr fun q ↦ by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact (commute_mk_of_mem_pLowerCentralSeries (b' i).2 g).eq
  have hsplit :
      (((List.ofFn fun i ↦ w i * (b' i : F)).prod : F) : F ⧸ N) =
        ((List.ofFn w).prod : F ⧸ N) * ((List.ofFn fun i ↦ (b' i : F)).prod : F ⧸ N) := by
    simp only [← QuotientGroup.mk'_apply, map_list_prod, List.ofFn_eq_map, List.map_map,
      Function.comp_def, map_mul]
    exact List.prod_map_mul_of_mem_center (List.finRange r)
      (fun i ↦ QuotientGroup.mk' N (w i)) (fun i ↦ QuotientGroup.mk' N (b' i))
      (fun i _ ↦ hcen i)
  have hbprod : (List.ofFn fun i ↦ (b' i : F)).prod ∈ pLowerCentralSeries 0 F (0 + m + 1) := by
    apply Subgroup.list_prod_mem
    intro t ht
    rw [List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    exact (b' i).2
  simp only [QuotientGroup.mk_mul, hsplit]
  exact (commute_mk_of_mem_pLowerCentralSeries hbprod wz).symm.mul_mul_mul_comm _ _

/-- The graded classes of the correction commutators sum to `u` times the sum of the graded
brackets of the classes of the peripheral tuple with the classes of the corrections. -/
private theorem sum_gradedMk_correction_eq {k : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (k + 1))) (u : ℤ_[p]ˣ) (m : ℕ)
    (c : Fin (k + 1) → F) (d : F) (q : Fin (k + 1) → pLowerCentralSeries 0 F m)
    (c' : Fin (k + 1) → F) (d' : F) (hc'0 : c' 0 = 1)
    (hc's : ∀ i : Fin k, c' i.succ = q i.castSucc) (hd' : d' = q (Fin.last k))
    (b' : Fin (k + 1) → pLowerCentralSeries 0 F (0 + m + 1))
    (bz' : pLowerCentralSeries 0 F (0 + m + 1))
    (hb' : ∀ i, (b' i : F) =
      ⁅((c i)⁻¹ * hF.padicPow (basis e i) u * c i)⁻¹, (c' i)⁻¹⁆)
    (hbz' : (bz' : F) = ⁅(d⁻¹ * hF.padicPow (cusp (basis e)) u * d)⁻¹, d'⁻¹⁆) :
    letI := hF.gradedPieceModule 0 0
    letI := hF.gradedPieceModule 0 m
    letI := hF.gradedPieceModule 0 (0 + m + 1)
    (∑ i, gradedMk 0 F (0 + m + 1) (b' i)) + gradedMk 0 F (0 + m + 1) bz' =
      (u : ℤ_[p]) • ∑ i, gradedBracket 0 F 0 m
        (gradedMkZero 0 F (peripheralTuple (basis e) i.succ)) (gradedMk 0 F m (q i)) := by
  let _ := hF.gradedPieceModule 0 0
  let _ := hF.gradedPieceModule 0 m
  let _ := hF.gradedPieceModule 0 (0 + m + 1)
  have hbzero : gradedMk 0 F (0 + m + 1) (b' 0) = 0 := by
    rw [gradedMk_eq_zero_iff]
    simp [hb', hc'0]
  have hbsucc (i : Fin k) :
      gradedMk 0 F (0 + m + 1) (b' i.succ) =
        (u : ℤ_[p]) • gradedBracket 0 F 0 m
          (gradedMkZero 0 F (basis e i.succ)) (gradedMk 0 F m (q i.castSucc)) := by
    rw [← hF.gradedMk_commutatorElement_inv_conj_padicPow_inv (basis e i.succ) (c i.succ)
      (q i.castSucc) (u : ℤ_[p])]
    congr 1
    exact Subtype.ext (by simp [hb', hc's])
  have hbzclass : gradedMk 0 F (0 + m + 1) bz' =
      (u : ℤ_[p]) • gradedBracket 0 F 0 m
        (gradedMkZero 0 F (cusp (basis e))) (gradedMk 0 F m (q (Fin.last k))) := by
    rw [← hF.gradedMk_commutatorElement_inv_conj_padicPow_inv (cusp (basis e)) d
      (q (Fin.last k)) (u : ℤ_[p])]
    congr 1
    exact Subtype.ext (by simp [hbz', hd'])
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [hbzero, zero_add]
  simp_rw [hbsucc]
  rw [hbzclass, ← Finset.smul_sum, ← smul_add]
  simp only [Fin.succ_castSucc, peripheralTuple_castSucc, Fin.succ_last,
    peripheralTuple_last]

/-- If the graded corrections solve the bracket equation in `gr_{m+1}`, then multiplying the defect
by the product of the correction commutators lands in `γ_{m+2}`. -/
private theorem defect_mul_correction_prod_mem {k : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (k + 1))) (u : ℤ_[p]ˣ) (m : ℕ)
    (c : Fin (k + 1) → F) (d : F) (q : Fin (k + 1) → pLowerCentralSeries 0 F m)
    (c' : Fin (k + 1) → F) (d' : F) (hc'0 : c' 0 = 1)
    (hc's : ∀ i : Fin k, c' i.succ = q i.castSucc) (hd' : d' = q (Fin.last k))
    (b' : Fin (k + 1) → pLowerCentralSeries 0 F (0 + m + 1))
    (bz' : pLowerCentralSeries 0 F (0 + m + 1))
    (hb' : ∀ i, (b' i : F) =
      ⁅((c i)⁻¹ * hF.padicPow (basis e i) u * c i)⁻¹, (c' i)⁻¹⁆)
    (hbz' : (bz' : F) = ⁅(d⁻¹ * hF.padicPow (cusp (basis e)) u * d)⁻¹, d'⁻¹⁆)
    (hdef : defect hF (basis e) u c d ∈ pLowerCentralSeries 0 F (0 + m + 1))
    (hy : letI := hF.gradedPieceModule 0 0
      letI := hF.gradedPieceModule 0 m
      letI := hF.gradedPieceModule 0 (0 + m + 1)
      (∑ i, gradedBracket 0 F 0 m
          (gradedMkZero 0 F (peripheralTuple (basis e) i.succ)) (gradedMk 0 F m (q i))) =
        -((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • gradedMk 0 F (0 + m + 1) ⟨defect hF (basis e) u c d, hdef⟩) :
    defect hF (basis e) u c d *
        (((List.ofFn b').prod * bz' : pLowerCentralSeries 0 F (0 + m + 1)) : F) ∈
      pLowerCentralSeries 0 F ((0 + m + 1) + 1) := by
  let _ := hF.gradedPieceModule 0 0
  let _ := hF.gradedPieceModule 0 m
  let _ := hF.gradedPieceModule 0 (0 + m + 1)
  have hcorr := sum_gradedMk_correction_eq hF e u m c d q c' d' hc'0 hc's hd' b' bz' hb' hbz'
  have hB : gradedMk 0 F (0 + m + 1) ((List.ofFn b').prod * bz') =
      -gradedMk 0 F (0 + m + 1) ⟨defect hF (basis e) u c d, hdef⟩ := by
    rw [gradedMk_mul, gradedMk_list_prod, List.map_ofFn, Function.comp_def, List.sum_ofFn, hcorr,
      hy, ← mul_smul]
    simp
  have hDB : gradedMk 0 F (0 + m + 1)
      (⟨defect hF (basis e) u c d, hdef⟩ * ((List.ofFn b').prod * bz')) = 0 := by
    rw [gradedMk_mul, hB, add_neg_cancel]
  exact gradedMk_eq_zero_iff.mp hDB

/-- The correction step of `exists_mem_level_succ` in positive rank: in rank `k + 1`, a pair of
conjugators at level `m + 1` can be corrected to a pair at level `m + 2` by corrections in `γ_m`,
the first correction being trivial. -/
private theorem exists_mem_level_succ_of_succ {k : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (k + 1))) (u : ℤ_[p]ˣ) (m : ℕ)
    (c : Fin (k + 1) → F) (d : F) (h : (c, d) ∈ level hF (basis e) (u : ℤ_[p]) (m + 1)) :
    ∃ (c' : Fin (k + 1) → F) (d' : F),
      (∀ i, c' i ∈ closedLowerCentralSeries F m) ∧
      d' ∈ closedLowerCentralSeries F m ∧
      (∀ h0 : 0 < k + 1, c' ⟨0, h0⟩ = 1) ∧
      ((fun i ↦ c i * c' i), d * d') ∈ level hF (basis e) (u : ℤ_[p]) (m + 1 + 1) := by
  -- Read the current defect in `gr_{m+1}` and use the peripheral tuple without its first entry
  -- as a finite topological generating family. Its bracket coefficients prescribe the
  -- corrections while leaving the first conjugator unchanged.
  have hdef : defect hF (basis e) u c d ∈ pLowerCentralSeries 0 F (m + 1) := by
    rw [← closedLowerCentralSeries_def]
    exact h
  let _ := hF.gradedPieceModule 0 0
  let _ := hF.gradedPieceModule 0 m
  let _ := hF.gradedPieceModule 0 (0 + m + 1)
  obtain ⟨y, hy⟩ := exists_sum_gradedBracket_eq_of_range m
    (peripheralTuple (basis e) ∘ Fin.succ)
    (topologicalClosure_closure_range_peripheralTuple_comp_succ e)
    (-((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • gradedMk 0 F (0 + m + 1)
      ⟨defect hF (basis e) u c d, by simpa using hdef⟩)
  choose q hq using fun i ↦ gradedMk_surjective m (y i)
  let c' : Fin (k + 1) → F := Fin.cases 1 (fun i ↦ q i.castSucc)
  let d' : F := q (Fin.last k)
  have hc' (i : Fin (k + 1)) : c' i ∈ pLowerCentralSeries 0 F m := by
    induction i using Fin.cases with
    | zero => exact one_mem _
    | succ i => exact (q i.castSucc).2
  have hd' : d' ∈ pLowerCentralSeries 0 F m := (q (Fin.last k)).2
  let b' : Fin (k + 1) → pLowerCentralSeries 0 F (0 + m + 1) := fun i ↦
    ⟨⁅((c i)⁻¹ * hF.padicPow (basis e i) u * c i)⁻¹, (c' i)⁻¹⁆,
      commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 _)
        (inv_mem (hc' i))⟩
  let bz' : pLowerCentralSeries 0 F (0 + m + 1) :=
    ⟨⁅(d⁻¹ * hF.padicPow (cusp (basis e)) u * d)⁻¹, d'⁻¹⁆,
      commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 _) (inv_mem hd')⟩
  have hdefB := defect_mul_correction_prod_mem hF e u m c d q c' d' rfl (fun _ ↦ rfl) rfl
    b' bz' (fun _ ↦ rfl) rfl (by simpa using hdef) (by simpa only [hq, Function.comp_apply]
      using hy)
  have hquot := mk_defect_mul_correction hF (basis e) u m c c' d d' b' bz'
    (fun _ ↦ rfl) rfl
  refine ⟨c', d', ?_, ?_, ?_, ?_⟩
  · intro i
    rw [closedLowerCentralSeries_def]
    simpa using hc' i
  · rw [closedLowerCentralSeries_def]
    simpa using hd'
  · intro _
    rfl
  · simp only [mem_level_iff]
    rw [closedLowerCentralSeries_def]
    have hqone := hquot.trans ((QuotientGroup.eq_one_iff _).mpr hdefB)
    have hmem := (QuotientGroup.eq_one_iff _).mp hqone
    simpa only [Nat.zero_add] using hmem

/-- A pair of conjugators whose defect lies in `γ_n`, for positive `n`, can be corrected so that
its defect lies in `γ_{n+1}`. The corrections lie in `γ_{n-1}`, and the correction at the first
basis element is trivial. The unit hypothesis on `u` is used to rescale the required graded
correction. -/
theorem exists_mem_level_succ (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin r)) (u : ℤ_[p]ˣ) (n : ℕ) (hn : 1 ≤ n)
    (c : Fin r → F) (d : F) (h : (c, d) ∈ level hF (basis e) (u : ℤ_[p]) n) :
    ∃ (c' : Fin r → F) (d' : F),
      (∀ i, c' i ∈ closedLowerCentralSeries F (n - 1)) ∧
      d' ∈ closedLowerCentralSeries F (n - 1) ∧
      (∀ h0 : 0 < r, c' ⟨0, h0⟩ = 1) ∧
      ((fun i ↦ c i * c' i), d * d') ∈ level hF (basis e) (u : ℤ_[p]) (n + 1) := by
  cases n with
  | zero => omega
  | succ m =>
    cases r with
    | zero =>
      let _ : Subsingleton F := e.toEquiv.subsingleton
      refine ⟨fun i ↦ Fin.elim0 i, 1, ?_, ?_, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · exact one_mem _
      · omega
      · simp only [mem_level_iff]
        have heq : defect hF (basis e) u (fun i ↦ c i * Fin.elim0 i) (d * 1) = 1 :=
          Subsingleton.elim _ _
        rw [heq]
        exact one_mem _
    | succ k => exact exists_mem_level_succ_of_succ hF e u m c d h

omit [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- **The closed lower central series of a free pro-`p` group of rank at least two never
vanishes.** For a group `F` presented as free pro-`p` on `r ≥ 2` generators, no term `γ_n` of its
closed lower central series is trivial. So no level `TauCeti.Peripheral.level` reduces to the
exact peripheral product identity merely because its term `γ_n` vanishes: the corrections of
`TauCeti.Peripheral.exists_mem_level_succ` control the defect at each finite stage only modulo a
nontrivial subgroup. -/
theorem closedLowerCentralSeries_ne_bot (e : F ≃ₜ* freeProP p (Fin r)) (hr : 2 ≤ r) (n : ℕ) :
    closedLowerCentralSeries F n ≠ ⊥ := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  rw [← e.symm.map_closedLowerCentralSeries_eq, Ne,
    map_eq_bot_iff_of_injective _ e.symm.injective]
  exact freeProP.closedLowerCentralSeries_ne_bot n

end Peripheral

end TauCeti
