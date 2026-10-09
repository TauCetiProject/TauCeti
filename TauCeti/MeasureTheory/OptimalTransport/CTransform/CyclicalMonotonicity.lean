/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclically monotone sets admit `c`-concave contact potentials

For a finite real cost `c`, a pair of potentials `φ` and `ψ` satisfying the Kantorovich dual
constraint `φ x + ψ y ≤ c (x, y)` meets it with equality on its contact set, and no finite
rearrangement of the targets of finitely many contact points can lower the total cost: a contact
set is `c`-cyclically monotone. This file proves the converse, which is the theorem of
Rockafellar and Rüschendorf: every `c`-cyclically monotone set is contained in the
`c`-superdifferential of a `c`-concave potential. Together the two directions characterise
cyclical monotonicity by the existence of a potential.

The potential is the explicit one of Rüschendorf's proof. Fix a base point `p` of the set `S`
and read a finite chain `p = w 0, w 1, …, w n` of points of `S` followed by a target `x` as the
telescoping quantity

`c (x, (w n).2) + ∑ i, c ((w (i + 1)).1, (w i).2) - ∑ i, c (w i)`;

the potential at `x` is the infimum of that quantity over all such chains. Closing a chain back
at the base point turns exactly that quantity into the cyclical-monotonicity inequality for the
cycle, so the infimum is `0` at the base point rather than `-∞`; and appending one further point
of `S` to a chain shows that the potential decreases by at most the corresponding cost
difference, which is what puts every point of `S` in the superdifferential. Away from `S` the
infimum can be `-∞`, so the potential is `EReal`-valued, as the `c`-transform interface
requires. Replacing it by its double `c`-transform makes it `c`-concave without
shrinking the superdifferential.

This is the algebraic half of the theory: no measure, topology, semicontinuity, or integrability
hypothesis appears, and the cost is an arbitrary real-valued function on a product of bare types.

## Main statements

* `TauCeti.isCyclicallyMonotone_contactSet` — the contact set of a dual feasible pair is
  `c`-cyclically monotone, with `TauCeti.isCyclicallyMonotone_cSuperdifferential` its
  specialisation to a potential and its own `c`-transform;
* `TauCeti.rockafellarPotential` — Rüschendorf's explicit potential of a set with a base point,
  and `TauCeti.IsCyclicallyMonotone.subset_cSuperdifferential_rockafellarPotential`, which puts a
  `c`-cyclically monotone set inside its `c`-superdifferential;
* `TauCeti.IsCyclicallyMonotone.exists_isCConcave_subset_cSuperdifferential` — **the theorem of
  Rockafellar and Rüschendorf**: a `c`-cyclically monotone set lies in the
  `c`-superdifferential of a `c`-concave potential;
* `TauCeti.isCyclicallyMonotone_iff_exists_isCConcave` — the resulting characterisation.

## Implementation notes

The potential is public, with its defining infimum over chains, because its explicit form is
what makes it measurable: on Polish spaces each strict sublevel set is a countable union of
projections of Borel sets of chains, which is how
`TauCeti.nullMeasurable_rockafellarPotential` integrates it in the dual attainment theorem. The
algebraic manipulations of individual chains stay private. The empty set is cyclically monotone
and has no base point, so the representation theorem gives it the `c`-transform of the zero
potential.

The extended-nonnegative counterpart of the first statement, for the dual pair of real
potentials used by the primal interface, is
`TauCeti.DualFeasible.isCyclicallyMonotone_dualContactSet`. The two live on different costs and
different potential types — `ℝ≥0∞` and `ℝ` there, `ℝ` and `EReal` here — and neither follows
from the other: the representation theorem below needs cancellative differences of costs, which
is why it is stated on the real side.

## References

* R. T. Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J.
  Math. 17 (1966), 497--510.
* L. Rüschendorf, *On c-optimal random variables*, Statist. Probab. Lett. 27 (1996), 267--270.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.3.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ} {S : Set (X × Y)}

/-! ### Contact sets are cyclically monotone -/

/-- The contact set of a dual feasible pair of potentials is `c`-cyclically monotone: at a
contact point both potentials are finite and their sum is the cost, so rearranging the targets
of finitely many contact points can only increase the total cost. -/
theorem isCyclicallyMonotone_contactSet {φ : X → EReal} {ψ : Y → EReal}
    (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal)) :
    IsCyclicallyMonotone c (contactSet c φ ψ) := by
  refine isCyclicallyMonotone_iff.2 fun n x y hmem σ => ?_
  set a : Fin n → ℝ := fun i => (φ (x i)).toReal
  set b : Fin n → ℝ := fun i => (ψ (y i)).toReal
  have hφ : ∀ i, φ (x i) = (a i : EReal) := fun i =>
    (EReal.coe_toReal (ne_top_left_of_mem_contactSet (hmem i))
      (ne_bot_left_of_mem_contactSet (hmem i))).symm
  have hψ : ∀ i, ψ (y i) = (b i : EReal) := fun i =>
    (EReal.coe_toReal (ne_top_right_of_mem_contactSet (hmem i))
      (ne_bot_right_of_mem_contactSet (hmem i))).symm
  have hc : ∀ i, c (x i, y i) = a i + b i := by
    intro i
    have h := hmem i
    rw [mk_mem_contactSet_iff, hφ i, hψ i, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact h.symm
  have key : ∀ i, a i + b (σ i) ≤ c (x i, y (σ i)) := by
    intro i
    have h := hfeas (x i) (y (σ i))
    rwa [hφ i, hψ (σ i), ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  calc ∑ i, c (x i, y i) = ∑ i, (a i + b i) := by simp only [hc]
    _ = ∑ i, a i + ∑ i, b i := Finset.sum_add_distrib
    _ = ∑ i, a i + ∑ i, b (σ i) := by rw [Equiv.sum_comp σ b]
    _ = ∑ i, (a i + b (σ i)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ i, c (x i, y (σ i)) := Finset.sum_le_sum fun i _ => key i

/-- The `c`-superdifferential of a potential is `c`-cyclically monotone. -/
theorem isCyclicallyMonotone_cSuperdifferential (c : X × Y → ℝ) (φ : X → EReal) :
    IsCyclicallyMonotone c (cSuperdifferential c φ) := by
  rw [cSuperdifferential_def]
  exact isCyclicallyMonotone_contactSet fun x y => add_cTransform_le c φ x y

/-! ### The Rockafellar potential -/

/-- The telescoping value of the chain `w 0, w 1, …, w n` of pairs followed by the target `x`:
`c (x, (w n).2) + ∑ i, c ((w (i + 1)).1, (w i).2) - ∑ i, c (w i)`. Rüschendorf's potential
`TauCeti.rockafellarPotential` is its infimum over chains in a fixed set. -/
def rockafellarChainValue (c : X × Y → ℝ) {n : ℕ} (w : Fin (n + 1) → X × Y) (x : X) : ℝ :=
  c (x, (w (Fin.last n)).2) + ∑ i : Fin n, c ((w i.succ).1, (w i.castSucc).2) - ∑ i, c (w i)

/-- Unfolding the telescoping chain value. -/
theorem rockafellarChainValue_def (c : X × Y → ℝ) {n : ℕ} (w : Fin (n + 1) → X × Y) (x : X) :
    rockafellarChainValue c w x = c (x, (w (Fin.last n)).2) +
      ∑ i : Fin n, c ((w i.succ).1, (w i.castSucc).2) - ∑ i, c (w i) := (rfl)

/-- The value of the one-point chain `p` followed by `x`. -/
private theorem rockafellarChainValue_const (c : X × Y → ℝ) (p : X × Y) (x : X) :
    rockafellarChainValue c (fun _ : Fin 1 => p) x = c (x, p.2) - c p := by
  simp [rockafellarChainValue]

/-- Appending one further point `q` to a chain and retargeting at `x` changes the chain value by
the cost difference `c (x, q.2) - c q`. This is the step that makes the potential decrease by at
most that difference. -/
private theorem rockafellarChainValue_snoc (c : X × Y → ℝ) {n : ℕ} (w : Fin (n + 1) → X × Y)
    (q : X × Y) (x : X) :
    rockafellarChainValue c (Fin.snoc w q) x =
      rockafellarChainValue c w q.1 + (c (x, q.2) - c q) := by
  set v : Fin (n + 2) → X × Y := Fin.snoc w q with hv
  have hstep : ∑ i : Fin (n + 1), c ((v i.succ).1, (v i.castSucc).2) =
      ∑ i : Fin n, c ((w i.succ).1, (w i.castSucc).2) + c (q.1, (w (Fin.last n)).2) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        simp only [hv, Fin.succ_castSucc, Fin.snoc_castSucc]
    · simp only [hv, Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
  have htotal : ∑ i : Fin (n + 2), c (v i) = ∑ i : Fin (n + 1), c (w i) + c q := by
    rw [Fin.sum_univ_castSucc]
    simp only [hv, Fin.snoc_castSucc, Fin.snoc_last]
  have hlast : v (Fin.last (n + 1)) = q := by simp [hv]
  rw [rockafellarChainValue, rockafellarChainValue, hlast, hstep, htotal]
  ring

/-- Closing a chain of points of a `c`-cyclically monotone set back at its own starting point
gives a nonnegative chain value: the inequality is the cyclical-monotonicity inequality for the
cyclic permutation of that cycle. -/
private theorem rockafellarChainValue_nonneg (hS : IsCyclicallyMonotone c S) {n : ℕ}
    {w : Fin (n + 1) → X × Y} (hw : ∀ i, w i ∈ S) : 0 ≤ rockafellarChainValue c w (w 0).1 := by
  have h := hS.sum_le (n + 1) (fun i => (w i).1) (fun i => (w i).2) (by simpa using hw)
    (finRotate (n + 1)).symm
  have hlhs : ∑ i, c ((w i).1, (w i).2) = ∑ i, c (w i) := by simp
  have hrhs : ∑ i, c ((w i).1, (w ((finRotate (n + 1)).symm i)).2) =
      c ((w 0).1, (w (Fin.last n)).2) + ∑ i : Fin n, c ((w i.succ).1, (w i.castSucc).2) := by
    rw [← Equiv.sum_comp (finRotate (n + 1))
      fun j => c ((w j).1, (w ((finRotate (n + 1)).symm j)).2)]
    simp only [Equiv.symm_apply_apply]
    rw [Fin.sum_univ_castSucc]
    simp [finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one, add_comm]
  rw [hlhs, hrhs] at h
  rw [rockafellarChainValue, sub_nonneg]
  exact h

/-- Rüschendorf's potential attached to a base point `p` of `S`: the infimum, over all finite
chains of points of `S` starting at `p`, of the telescoping chain value ending at `x`. -/
def rockafellarPotential (c : X × Y → ℝ) (S : Set (X × Y)) (p : X × Y) (x : X) : EReal :=
  ⨅ (n : ℕ) (w : Fin (n + 1) → X × Y) (_ : w 0 = p) (_ : ∀ i, w i ∈ S),
    (rockafellarChainValue c w x : EReal)

/-- Unfolding Rüschendorf's potential as an infimum over admissible chains. -/
theorem rockafellarPotential_def (c : X × Y → ℝ) (S : Set (X × Y)) (p : X × Y) (x : X) :
    rockafellarPotential c S p x = ⨅ (n : ℕ) (w : Fin (n + 1) → X × Y) (_ : w 0 = p)
      (_ : ∀ i, w i ∈ S), (rockafellarChainValue c w x : EReal) := (rfl)

/-- Every admissible chain bounds the potential from above. -/
theorem rockafellarPotential_le {p : X × Y} {n : ℕ} {w : Fin (n + 1) → X × Y}
    (hw0 : w 0 = p) (hw : ∀ i, w i ∈ S) (x : X) :
    rockafellarPotential c S p x ≤ (rockafellarChainValue c w x : EReal) :=
  iInf_le_of_le n <| iInf_le_of_le w <| iInf_le_of_le hw0 <| iInf_le _ hw

/-- A lower bound valid on every admissible chain bounds the potential from below. -/
theorem le_rockafellarPotential {p : X × Y} {x : X} {a : EReal}
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → X × Y), w 0 = p → (∀ i, w i ∈ S) →
      a ≤ (rockafellarChainValue c w x : EReal)) :
    a ≤ rockafellarPotential c S p x :=
  le_iInf fun n => le_iInf fun w => le_iInf fun hw0 => le_iInf fun hw => h n w hw0 hw

/-- The one-point chain bounds the potential by a real number, so it never takes the value `⊤`. -/
theorem rockafellarPotential_le_sub {p : X × Y} (hp : p ∈ S) (x : X) :
    rockafellarPotential c S p x ≤ ((c (x, p.2) - c p : ℝ) : EReal) := by
  refine le_of_le_of_eq (rockafellarPotential_le (w := fun _ : Fin 1 => p) rfl (fun _ => hp) x) ?_
  rw [rockafellarChainValue_const]

/-- The potential vanishes at the source coordinate of its base point; this is where cyclical
monotonicity is used, and it is what keeps the potential from being identically `⊥`. -/
@[simp]
theorem rockafellarPotential_self (hS : IsCyclicallyMonotone c S) {p : X × Y}
    (hp : p ∈ S) : rockafellarPotential c S p p.1 = 0 := by
  refine le_antisymm ?_ (le_rockafellarPotential fun n w hw0 hw => ?_)
  · simpa using rockafellarPotential_le_sub hp p.1
  · have h := rockafellarChainValue_nonneg hS hw
    rw [hw0] at h
    exact_mod_cast h

/-- The descent inequality: moving the target from `q.1` to `x` costs the potential at most the
cost difference along `q.2`. -/
theorem rockafellarPotential_le_add {p q : X × Y} (hq : q ∈ S) (x : X) :
    rockafellarPotential c S p x ≤
      rockafellarPotential c S p q.1 + ((c (x, q.2) - c q : ℝ) : EReal) := by
  rw [← EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  refine le_rockafellarPotential fun n w hw0 hw => ?_
  have hsnoc0 : (Fin.snoc w q : Fin (n + 2) → X × Y) 0 = p := by
    rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
    exact hw0
  have hsnocmem : ∀ i, (Fin.snoc w q : Fin (n + 2) → X × Y) i ∈ S := by
    refine Fin.lastCases ?_ ?_
    · simpa using hq
    · intro i
      simpa using hw i
  have h := rockafellarPotential_le (c := c) hsnoc0 hsnocmem x
  rw [rockafellarChainValue_snoc] at h
  calc rockafellarPotential c S p x - ((c (x, q.2) - c q : ℝ) : EReal)
      ≤ ((rockafellarChainValue c w q.1 + (c (x, q.2) - c q) : ℝ) : EReal) -
        ((c (x, q.2) - c q : ℝ) : EReal) := EReal.sub_le_sub h le_rfl
    _ = (rockafellarChainValue c w q.1 : EReal) := by rw [← EReal.coe_sub]; norm_num

/-- **Rüschendorf's potential is a contact potential.** Every point of a `c`-cyclically monotone
set lies in the `c`-superdifferential of the potential attached to any base point of the set. -/
theorem IsCyclicallyMonotone.subset_cSuperdifferential_rockafellarPotential
    (hS : IsCyclicallyMonotone c S) {p : X × Y} (hp : p ∈ S) :
    S ⊆ cSuperdifferential c (rockafellarPotential c S p) := by
  set φ := rockafellarPotential c S p with hφdef
  have hstep : ∀ q ∈ S, ∀ x : X, φ x ≤ φ q.1 + ((c (x, q.2) - c q : ℝ) : EReal) :=
    fun q hq x => rockafellarPotential_le_add hq x
  rintro ⟨x, y⟩ hxy
  have htop : φ x ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top _) (rockafellarPotential_le_sub hp x)
  have hzero : φ p.1 = 0 := rockafellarPotential_self hS hp
  have hbot : φ x ≠ ⊥ := by
    intro hbot
    have h := hstep (x, y) hxy p.1
    rw [hbot, hzero] at h
    simp at h
  set b : ℝ := (φ x).toReal with hbdef
  have hb : φ x = (b : EReal) := (EReal.coe_toReal htop hbot).symm
  have hle : ∀ x' : X, ((c (x, y) : EReal)) - φ x ≤ (c (x', y) : EReal) - φ x' := by
    intro x'
    have h := hstep (x, y) hxy x'
    rw [hb] at h ⊢
    have hcoe : ((c (x', y) : EReal)) -
        ((b + (c (x', y) - c (x, y)) : ℝ) : EReal) = (c (x, y) : EReal) - (b : EReal) := by
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
      ring
    calc (c (x, y) : EReal) - (b : EReal)
        = ((c (x', y) : ℝ) : EReal) - ((b + (c (x', y) - c (x, y)) : ℝ) : EReal) := hcoe.symm
      _ ≤ ((c (x', y) : ℝ) : EReal) - φ x' := by
          refine EReal.sub_le_sub le_rfl ?_
          rw [EReal.coe_add]
          exact h
  have htrans : cTransform c φ y = (c (x, y) : EReal) - φ x :=
    le_antisymm (cTransform_le c φ x y) (le_cTransform fun x' => hle x')
  exact mem_cSuperdifferential_of_cTransform_eq hb htrans

/-! ### The representation theorem -/

/-- **The theorem of Rockafellar and Rüschendorf.** Every `c`-cyclically monotone set is
contained in the `c`-superdifferential of a `c`-concave potential: there is a `φ` with
`φ x + φᶜ y = c (x, y)` at every point `(x, y)` of the set, where `φᶜ` is the infimal
`c`-transform of `φ`. -/
theorem IsCyclicallyMonotone.exists_isCConcave_subset_cSuperdifferential
    (hS : IsCyclicallyMonotone c S) :
    ∃ φ : X → EReal, IsCConcave c φ ∧ S ⊆ cSuperdifferential c φ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · exact ⟨cTransformSymm c 0, isCConcave_cTransformSymm c 0, Set.empty_subset _⟩
  set φ := rockafellarPotential c S p with hφdef
  have hsub : S ⊆ cSuperdifferential c φ := hS.subset_cSuperdifferential_rockafellarPotential hp
  refine ⟨cTransformSymm c (cTransform c φ), isCConcave_cTransformSymm _ _, fun z hz => ?_⟩
  have hz' : z ∈ contactSet c φ (cTransform c φ) := by
    rw [← cSuperdifferential_def]
    exact hsub hz
  have h := contactSet_subset_contactSet_cTransformSymm_cTransform
    (fun x y => add_cTransform_le c φ x y) hz'
  rwa [cSuperdifferential_def, cTransform_cTransformSymm_cTransform]

/-- **Cyclical monotonicity is exactly a contact-set condition.** A set of pairs is
`c`-cyclically monotone if and only if it lies in the `c`-superdifferential of some `c`-concave
potential. -/
theorem isCyclicallyMonotone_iff_exists_isCConcave (c : X × Y → ℝ) (S : Set (X × Y)) :
    IsCyclicallyMonotone c S ↔ ∃ φ : X → EReal, IsCConcave c φ ∧ S ⊆ cSuperdifferential c φ :=
  ⟨fun hS => hS.exists_isCConcave_subset_cSuperdifferential,
    fun ⟨_, _, hsub⟩ => (isCyclicallyMonotone_cSuperdifferential _ _).mono hsub⟩

end TauCeti

end

end
