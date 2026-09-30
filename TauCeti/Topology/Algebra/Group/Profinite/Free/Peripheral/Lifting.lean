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

## Main definitions

* `TauCeti.Peripheral.defect`: the ordered peripheral product for chosen conjugators.
* `TauCeti.Peripheral.level`: the conjugators whose defect lies in a specified closed
  lower-central-series term.

## Main results

* `TauCeti.Peripheral.level_one_eq_univ`: every choice of conjugators has defect in `γ₁`.
* `TauCeti.Peripheral.exists_mem_level_succ`: a positive-level solution can be corrected to the
  next level while keeping the correction at the first basis element trivial.
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
    | succ k =>
      -- Read the current defect in `gr_m` and use the peripheral tuple without its first entry
      -- as a finite topological generating family. Its bracket coefficients prescribe the
      -- corrections while leaving the first conjugator unchanged.
      have hdef : defect hF (basis e) u c d ∈ pLowerCentralSeries 0 F (m + 1) := by
        rw [← closedLowerCentralSeries_def]
        exact h
      let _ := hF.gradedPieceModule 0 0
      let _ := hF.gradedPieceModule 0 m
      let _ := hF.gradedPieceModule 0 (0 + m + 1)
      let _ : CompactSpace (pLowerCentralSeries 0 F m) :=
        isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries m).isCompact
      let _ : CompactSpace (gradedPiece 0 F m) := inferInstance
      let z : gradedPiece 0 F (0 + m + 1) :=
        gradedMk 0 F (0 + m + 1) ⟨defect hF (basis e) u c d, by simpa using hdef⟩
      obtain ⟨y, hy⟩ := exists_sum_gradedBracket_eq_of_range m
        (peripheralTuple (basis e) ∘ Fin.succ)
        (topologicalClosure_closure_range_peripheralTuple_comp_succ e)
        (-((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z)
      choose q hq using fun i ↦ gradedMk_surjective m (y i)
      let c' : Fin (k + 1) → F := Fin.cases 1 (fun i ↦ q i.castSucc)
      let d' : F := q (Fin.last k)
      have hc' (i : Fin (k + 1)) : c' i ∈ pLowerCentralSeries 0 F m := by
        induction i using Fin.cases with
        | zero => exact one_mem _
        | succ i => exact (q i.castSucc).2
      have hd' : d' ∈ pLowerCentralSeries 0 F m := (q (Fin.last k)).2
      let w : Fin (k + 1) → F := fun i ↦
        (c i)⁻¹ * hF.padicPow (basis e i) u * c i
      let wz : F := d⁻¹ * hF.padicPow (cusp (basis e)) u * d
      let b : Fin (k + 1) → F := fun i ↦ ⁅(w i)⁻¹, (c' i)⁻¹⁆
      let bz : F := ⁅wz⁻¹, (d')⁻¹⁆
      have hb (i : Fin (k + 1)) : b i ∈ pLowerCentralSeries 0 F (0 + m + 1) :=
        commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 (w i)⁻¹)
          (inv_mem (hc' i))
      have hbz : bz ∈ pLowerCentralSeries 0 F (0 + m + 1) :=
        commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero 0 wz⁻¹) (inv_mem hd')
      let b' : Fin (k + 1) → pLowerCentralSeries 0 F (0 + m + 1) :=
        fun i ↦ ⟨b i, hb i⟩
      let bz' : pLowerCentralSeries 0 F (0 + m + 1) := ⟨bz, hbz⟩
      -- Each modified conjugate differs from the old one by a commutator. In the graded piece,
      -- these commutators are the unit `u` times the chosen bracket corrections.
      have hbzero : gradedMk 0 F (0 + m + 1) (b' 0) = 0 := by
        rw [gradedMk_eq_zero_iff]
        simp [b', b, c']
      have hbsucc (i : Fin k) :
          gradedMk 0 F (0 + m + 1) (b' i.succ) =
            (u : ℤ_[p]) • gradedBracket 0 F 0 m
              (gradedMkZero 0 F (basis e i.succ)) (gradedMk 0 F m (q i.castSucc)) := by
        simpa only [b', b, w, c', Fin.cases_succ, Subgroup.coe_inv] using
          hF.gradedMk_commutatorElement_inv_conj_padicPow_inv (basis e i.succ) (c i.succ)
            (q i.castSucc) (u : ℤ_[p])
      have hbzclass : gradedMk 0 F (0 + m + 1) bz' =
          (u : ℤ_[p]) • gradedBracket 0 F 0 m
            (gradedMkZero 0 F (cusp (basis e))) (gradedMk 0 F m (q (Fin.last k))) := by
        simpa only [bz', bz, wz, d', Subgroup.coe_inv] using
          hF.gradedMk_commutatorElement_inv_conj_padicPow_inv (cusp (basis e)) d
            (q (Fin.last k)) (u : ℤ_[p])
      have hcorr :
          (∑ i, gradedMk 0 F (0 + m + 1) (b' i)) +
              gradedMk 0 F (0 + m + 1) bz' =
            (u : ℤ_[p]) •
              ∑ i, gradedBracket 0 F 0 m
                (gradedMkZero 0 F (peripheralTuple (basis e) i.succ))
                (gradedMk 0 F m (q i)) := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [hbzero, zero_add]
        simp_rw [hbsucc]
        rw [hbzclass, ← Finset.smul_sum, ← smul_add]
        simp only [Fin.succ_castSucc, peripheralTuple_castSucc, Fin.succ_last,
          peripheralTuple_last]
      have hyq :
          (∑ i, gradedBracket 0 F 0 m
              (gradedMkZero 0 F (peripheralTuple (basis e) i.succ))
              (gradedMk 0 F m (q i))) =
            -((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z := by
        simpa only [hq, Function.comp_apply] using hy
      let B : pLowerCentralSeries 0 F (0 + m + 1) := (List.ofFn b').prod * bz'
      have hB : gradedMk 0 F (0 + m + 1) B = -z := by
        -- Unfold the local correction product to expose `gradedMk_mul` and `gradedMk_list_prod`.
        change gradedMk 0 F (0 + m + 1) ((List.ofFn b').prod * bz') = -z
        rw [gradedMk_mul, gradedMk_list_prod, List.map_ofFn, Function.comp_def,
          List.sum_ofFn, hcorr, hyq, ← mul_smul]
        simp
      have hdefB : defect hF (basis e) u c d * (B : F) ∈
          pLowerCentralSeries 0 F ((0 + m + 1) + 1) := by
        have hbase : defect hF (basis e) u c d * (B : F) ∈
            pLowerCentralSeries 0 F (0 + m + 1) :=
          mul_mem (by simpa using hdef) B.2
        let DB : pLowerCentralSeries 0 F (0 + m + 1) :=
          ⟨defect hF (basis e) u c d * (B : F), hbase⟩
        have hDB : gradedMk 0 F (0 + m + 1) DB = 0 := calc
          gradedMk 0 F (0 + m + 1) ⟨defect hF (basis e) u c d * (B : F), hbase⟩ =
              z + gradedMk 0 F (0 + m + 1) B := by
            rw [← gradedMk_mul]
            rfl
          _ = 0 := by rw [hB, add_neg_cancel]
        exact (gradedMk_eq_zero_iff.mp hDB)
      have hfactor (i : Fin (k + 1)) :
          (c i * c' i)⁻¹ * hF.padicPow (basis e i) u * (c i * c' i) = w i * b i := by
        simp only [w, b]
        rw [commutatorElement_def]
        group
      have hfactorCusp :
          (d * d')⁻¹ * hF.padicPow (cusp (basis e)) u * (d * d') = wz * bz := by
        simp only [wz, bz]
        rw [commutatorElement_def]
        group
      -- Modulo the next central-series term, all correction commutators are central. Hence the
      -- interleaved corrected factors can be collected after the original defect.
      have hquot :
          ((defect hF (basis e) u (fun i ↦ c i * c' i) (d * d') : F) :
              F ⧸ pLowerCentralSeries 0 F ((0 + m + 1) + 1)) =
            ((defect hF (basis e) u c d * (B : F) : F) :
              F ⧸ pLowerCentralSeries 0 F ((0 + m + 1) + 1)) := by
        simp only [defect, hfactor, hfactorCusp]
        have hBcoe : (B : F) = (List.ofFn b).prod * bz := by
          -- Expose the local subtype-valued definition before mapping its product to `F`.
          rw [show B = (List.ofFn b').prod * bz' from rfl]
          -- Restate coercion as the subgroup homomorphism so its product map lemmas apply.
          change (pLowerCentralSeries 0 F (0 + m + 1)).subtype
              ((List.ofFn b').prod * bz') = _
          rw [map_mul, map_list_prod, List.map_ofFn]
          rfl
        rw [hBcoe]
        let N := pLowerCentralSeries 0 F ((0 + m + 1) + 1)
        -- Name the quotient and expose the four product blocks used in the central rearrangement.
        change (((List.ofFn fun i ↦ w i * b i).prod * (wz * bz) : F) : F ⧸ N) =
          ((((List.ofFn w).prod * wz) * ((List.ofFn b).prod * bz) : F) : F ⧸ N)
        have hcen : ∀ i, ((b i : F) : F ⧸ N) ∈ Submonoid.center _ := fun i ↦
          Submonoid.mem_center_iff.mpr fun q ↦ by
            obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
            exact (commute_mk_of_mem_pLowerCentralSeries (hb i) g).eq
        have hsplit :
            (((List.ofFn fun i ↦ w i * b i).prod : F) : F ⧸ N) =
              ((List.ofFn w).prod : F ⧸ N) * ((List.ofFn b).prod : F ⧸ N) := by
          rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_ofFn,
            ← QuotientGroup.mk'_apply, map_list_prod, List.map_ofFn,
            ← QuotientGroup.mk'_apply, map_list_prod, List.map_ofFn]
          simpa only [List.ofFn_eq_map, Function.comp_def, map_mul,
            QuotientGroup.mk'_apply] using
            List.prod_map_mul_of_mem_center (List.finRange (k + 1))
              (fun i ↦ ((w i : F) : F ⧸ N)) (fun i ↦ ((b i : F) : F ⧸ N))
              (fun i _ ↦ hcen i)
        simp only [QuotientGroup.mk_mul]
        rw [hsplit]
        have hbprod : (List.ofFn b).prod ∈ pLowerCentralSeries 0 F (0 + m + 1) := by
          apply Subgroup.list_prod_mem
          intro t ht
          rw [List.mem_ofFn] at ht
          obtain ⟨i, rfl⟩ := ht
          exact hb i
        have hcomm := commute_mk_of_mem_pLowerCentralSeries hbprod wz
        rw [mul_assoc ((List.ofFn w).prod : F ⧸ N) ((List.ofFn b).prod : F ⧸ N)
            ((wz : F ⧸ N) * (bz : F ⧸ N)),
          ← mul_assoc ((List.ofFn b).prod : F ⧸ N) (wz : F ⧸ N) (bz : F ⧸ N),
          ← hcomm.eq,
          mul_assoc (wz : F ⧸ N) ((List.ofFn b).prod : F ⧸ N) (bz : F ⧸ N),
          ← mul_assoc ((List.ofFn w).prod : F ⧸ N) (wz : F ⧸ N)
            (((List.ofFn b).prod : F ⧸ N) * (bz : F ⧸ N))]
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

end Peripheral

end TauCeti
