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
  rw [closedLowerCentralSeries_def]
  rw [← gradedMkZero_eq_zero_iff]
  let _ := hF.gradedPieceModule 0 0
  have hprod (l : List F) :
      gradedMkZero 0 F l.prod = (l.map (gradedMkZero 0 F)).sum := by
    let l' : List (pLowerCentralSeries 0 F 0) :=
      l.map fun g ↦ ⟨g, mem_pLowerCentralSeries_zero 0 g⟩
    have hlprod : (l'.prod : F) = l.prod := by
      change (pLowerCentralSeries 0 F 0).subtype l'.prod = l.prod
      rw [map_list_prod]
      simp only [l', List.map_map, Function.comp_def, Subgroup.subtype_apply]
      simp
    rw [← hlprod, ← gradedMk_zero, gradedMk_list_prod]
    simp only [l', List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro g _
    exact gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero 0 g⟩
  rw [defect, gradedMkZero_mul, hprod, List.map_ofFn,
    Function.comp_def]
  simp only [gradedMkZero_mul, gradedMkZero_inv, hF.gradedMkZero_padicPow, neg_add_cancel_comm]
  have hsum : (List.ofFn fun i ↦ u • gradedMkZero 0 F (x i)).sum =
      u • (List.ofFn fun i ↦ gradedMkZero 0 F (x i)).sum := by
    rw [List.ofFn_eq_map, List.ofFn_eq_map]
    -- Expose the composite map so `List.map_map` identifies the pointwise scalar action.
    change (List.map ((fun z ↦ u • z) ∘
      (fun i ↦ gradedMkZero 0 F (x i))) (List.finRange r)).sum = _
    rw [← List.map_map, ← List.smul_sum]
  rw [hsum, ← smul_add, cusp_def,
    gradedMkZero_inv, hprod, List.map_ofFn, Function.comp_def]
  simp

omit [Fact (Nat.Prime p)] [CompactSpace F] [TotallyDisconnectedSpace F] in
private theorem topologicalClosure_closure_range_tailPeripheral_basis
    {k : ℕ} (e : F ≃ₜ* freeProP p (Fin (k + 1))) :
    (Subgroup.closure (Set.range fun i : Fin (k + 1) ↦
      peripheralTuple (basis e) i.succ)).topologicalClosure = ⊤ := by
  let H := Subgroup.closure (Set.range fun i : Fin (k + 1) ↦
    peripheralTuple (basis e) i.succ)
  have hcusp : cusp (basis e) ∈ H := by
    apply Subgroup.subset_closure
    refine ⟨Fin.last k, ?_⟩
    -- Put the successor of the last index into the form expected by the `Fin.snoc` API.
    change peripheralTuple (basis e) (Fin.last k).succ = cusp (basis e)
    rw [Fin.succ_last, peripheralTuple_last]
  have hsucc (i : Fin k) : basis e i.succ ∈ H := by
    apply Subgroup.subset_closure
    refine ⟨i.castSucc, ?_⟩
    -- Put the successor-cast index into the form expected by the `Fin.snoc` API.
    change peripheralTuple (basis e) i.castSucc.succ = basis e i.succ
    rw [Fin.succ_castSucc, peripheralTuple_castSucc]
  have hzero : basis e 0 ∈ H := by
    have htail : (List.ofFn fun i : Fin k ↦ basis e i.succ).prod ∈ H := by
      apply Subgroup.list_prod_mem
      intro y hy
      rw [List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      exact hsucc i
    have hrel := prod_mul_cusp (basis e)
    rw [List.ofFn_succ, List.prod_cons] at hrel
    have heq : basis e 0 =
        ((List.ofFn fun i : Fin k ↦ basis e i.succ).prod * cusp (basis e))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa only [mul_assoc] using hrel
    rw [heq]
    exact H.inv_mem (H.mul_mem htail hcusp)
  have hbasis : Subgroup.closure (Set.range (basis e)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    induction i using Fin.cases with
    | zero => exact hzero
    | succ i => exact hsucc i
  apply top_le_iff.mp
  rw [← topologicalClosure_closure_range_basis e]
  exact Subgroup.topologicalClosure_mono hbasis

private theorem gradedMk_commutator_inv_conj_padicPow_inv
    (hF : IsProP p F) (m : ℕ) (y c : F) (q : pLowerCentralSeries 0 F m) (u : ℤ_[p]ˣ) :
    letI := hF.gradedPieceModule 0 0
    letI := hF.gradedPieceModule 0 m
    letI := hF.gradedPieceModule 0 (0 + m + 1)
    gradedMk 0 F (0 + m + 1)
        ⟨⁅(c⁻¹ * hF.padicPow y u * c)⁻¹, (q : F)⁻¹⁆,
          by simpa only [coe_inv] using
            commutator_mem_pLowerCentralSeries
              (mem_pLowerCentralSeries_zero 0 (c⁻¹ * hF.padicPow y u * c)⁻¹) q⁻¹.2⟩ =
      ((u : ℤ_[p]) • gradedBracket 0 F 0 m
        (gradedMkZero 0 F y) (gradedMk 0 F m q) : gradedPiece 0 F (0 + m + 1)) := by
  let _ := hF.gradedPieceModule 0 0
  let _ := hF.gradedPieceModule 0 m
  let _ := hF.gradedPieceModule 0 (0 + m + 1)
  calc
    _ = gradedMk 0 F (0 + m + 1)
        ⟨⁅(c⁻¹ * hF.padicPow y u * c)⁻¹, (q⁻¹ : pLowerCentralSeries 0 F m)⁆,
          commutator_mem_pLowerCentralSeries
            (mem_pLowerCentralSeries_zero 0 (c⁻¹ * hF.padicPow y u * c)⁻¹) q⁻¹.2⟩ := by
      congr 2
    _ = _ := by
      rw [← gradedBracket_gradedMk
        (⟨(c⁻¹ * hF.padicPow y u * c)⁻¹,
          mem_pLowerCentralSeries_zero 0 (c⁻¹ * hF.padicPow y u * c)⁻¹⟩ :
            pLowerCentralSeries 0 F 0) q⁻¹,
        gradedMk_zero, gradedMkZero_inv, gradedMkZero_mul, gradedMkZero_mul, gradedMkZero_inv,
        hF.gradedMkZero_padicPow, neg_add_cancel_comm, gradedMk_inv]
      simp only [map_neg, AddMonoidHom.neg_apply, neg_neg, hF.gradedBracket_smul_left]

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
        (fun i : Fin (k + 1) ↦ peripheralTuple (basis e) i.succ)
        (topologicalClosure_closure_range_tailPeripheral_basis e)
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
        simpa only [b', b, w, c', Fin.cases_succ] using
          gradedMk_commutator_inv_conj_padicPow_inv hF m (basis e i.succ) (c i.succ)
            (q i.castSucc) u
      have hbzclass : gradedMk 0 F (0 + m + 1) bz' =
          (u : ℤ_[p]) • gradedBracket 0 F 0 m
            (gradedMkZero 0 F (cusp (basis e))) (gradedMk 0 F m (q (Fin.last k))) := by
        simpa only [bz', bz, wz, d'] using
          gradedMk_commutator_inv_conj_padicPow_inv hF m (cusp (basis e)) d
            (q (Fin.last k)) u
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
        simpa only [hq] using hy
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
