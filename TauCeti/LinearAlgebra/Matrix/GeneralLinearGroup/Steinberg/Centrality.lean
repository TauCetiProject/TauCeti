/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic
import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.RowColumn

/-!
# Centrality of `ker (St(R) →* GL_∞(R))`

For an associative unital ring `R`, the canonical homomorphism
`TauCeti.SteinbergGroup.toStableGL : St(R) →* GL_∞(R)` has image the stable elementary subgroup
`E_∞(R)`. Every element `z ∈ ker (St(R) →* GL_∞(R))` comes from `Stₙ(R)` for some `n`. Inside
`St_{n + 1}(R)`, the stabilized subgroup `Stₙ(R)` normalizes the `n`-th column root subgroup
`Pₙ = ⟨x_{in}(a) | i < n⟩`, the range of `TauCeti.IndexedSteinbergGroup.colHom`, on which `toGL`
is injective (`TauCeti.IndexedSteinbergGroup.toGL_comp_colHom_injective`). Hence `z` centralizes
`Pₙ`, and by opposite-ring inverse-transpose duality (`IndexedSteinbergGroup.transposeOp`) it also
centralizes the `n`-th row root subgroup `⟨x_{nj}(b) | j < n⟩`, and therefore every generator
`x_{pq}(b) = ⁅x_{pn}(b), x_{nq}(1)⁆` with `p, q < n`.

## Main results

* `TauCeti.SteinbergGroup.ker_toStableGL_le_center`: `ker (toStableGL R)` lies in the center of
  `St(R)`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Theorem 5.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1.
-/

public section

noncomputable section

open Matrix Subgroup

open scoped commutatorElement

namespace TauCeti

universe u

/-! ## Centrality of `ker (toStableGL R)` -/

namespace SteinbergGroup

section Center

variable {R : Type u} [Ring R]

/-- Stabilization `Stₙ(R) →* St_{n + 1}(R)` lands in the normalizer of the column root subgroup at
the new last index, since every generator `x_{ij}(c)` with `i, j < n` normalizes it
(`TauCeti.IndexedSteinbergGroup.x_mem_normalizer_range_colHom`). -/
private theorem range_stabilize_le_normalizer_colHom (n : ℕ) :
    (stabilize (Nat.le_succ n) (R := R)).range ≤
      Subgroup.normalizer ((IndexedSteinbergGroup.colHom (R := R) (Fin.last n)).range :
        Set (IndexedSteinbergGroup (Fin (n + 1)) R)) := by
  have hcastEmb : Fin.castLEEmb (Nat.le_succ n) = Fin.castSuccEmb := by
    ext p
    simp
  rw [IndexedSteinbergGroup.range_le_iff]
  intro i j hij c
  simp only [stabilize, hcastEmb, IndexedSteinbergGroup.mapIndex_x, Fin.castSuccEmb_apply]
  exact IndexedSteinbergGroup.x_mem_normalizer_range_colHom _ (Fin.castSucc_lt_last i).ne
    (Fin.castSucc_lt_last j).ne c

/-- Any element of `Stₙ(R)` in the kernel of `toGL` commutes, after stabilizing to `St_{n + 1}(R)`,
with every column generator `x_{p, n}(b)` (`p < n`). -/
private theorem commute_stabilize_col {n : ℕ} {u : IndexedSteinbergGroup (Fin n) R}
    (hu : IndexedSteinbergGroup.toGL u = 1) (p : Fin n) (b : R) :
    Commute (stabilize (Nat.le_succ n) u)
      (IndexedSteinbergGroup.x (Fin.castSucc_lt_last p).ne b) := by
  have hinf : (IndexedSteinbergGroup.toGL (ι := Fin (n + 1)) (R := R)).ker ⊓
      (IndexedSteinbergGroup.colHom (R := R) (Fin.last n)).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hker, ⟨v, rfl⟩⟩
    have hv : v = 1 := IndexedSteinbergGroup.toGL_comp_colHom_injective (Fin.last n)
      (by simpa using hker)
    rw [hv, map_one, Subgroup.mem_bot]
  have hle := inf_normalizer_le_centralizer_of_inf_eq_bot Subgroup.le_normalizer_of_normal hinf
  have hker_u : stabilize (Nat.le_succ n) u ∈
      (IndexedSteinbergGroup.toGL (ι := Fin (n + 1)) (R := R)).ker := by
    rw [MonoidHom.mem_ker, IndexedSteinbergGroup.toGL_mapIndex_castLE, hu, map_one]
  have hmem : stabilize (Nat.le_succ n) u ∈
      Subgroup.centralizer ((IndexedSteinbergGroup.colHom (R := R) (Fin.last n)).range :
        Set (IndexedSteinbergGroup (Fin (n + 1)) R)) :=
    hle ⟨hker_u, range_stabilize_le_normalizer_colHom n ⟨u, rfl⟩⟩
  exact (Subgroup.mem_centralizer_iff.mp hmem _
    (IndexedSteinbergGroup.x_mem_range_colHom ⟨p.castSucc, (Fin.castSucc_lt_last p).ne⟩ b)).symm

/-- **Milnor's centrality theorem (`K₂(R) ≤ Z(St(R))`).** The kernel of `toStableGL R` lies in the
center of `SteinbergGroup R`. -/
theorem ker_toStableGL_le_center :
    (toStableGL R).ker ≤ Subgroup.center (SteinbergGroup R) := by
  intro z hz
  obtain ⟨m, u, rfl⟩ := exists_ofFin z
  have htop : Subgroup.centralizer {ofFin R m u} = ⊤ := by
    rw [IndexedSteinbergGroup.subgroup_eq_top_iff]
    intro p q hpq b
    let n := max m (max p q + 1)
    have hmn : m ≤ n := le_max_left _ _
    have hp : p < n := by omega
    have hq : q < n := by omega
    let u' : IndexedSteinbergGroup (Fin n) R := stabilize hmn u
    have hu' : IndexedSteinbergGroup.toGL u' = 1 := by
      apply StableGeneralLinearGroup.of_injective n
      rw [← toStableGL_ofFin, ofFin_stabilize, map_one]
      exact hz
    have hu'_op : IndexedSteinbergGroup.toGL (IndexedSteinbergGroup.transposeOp u') = 1 := by
      apply Units.ext
      simp [IndexedSteinbergGroup.coe_toGL_transposeOp, hu']
    have hcp : Commute (stabilize (Nat.le_succ n) u')
        (IndexedSteinbergGroup.x (Fin.castSucc_lt_last ⟨p, hp⟩).ne b) :=
      commute_stabilize_col hu' ⟨p, hp⟩ b
    have hcq_op : Commute (stabilize (Nat.le_succ n) (IndexedSteinbergGroup.transposeOp u'))
        (IndexedSteinbergGroup.x (Fin.castSucc_lt_last ⟨q, hq⟩).ne (MulOpposite.op (-1 : R))) :=
      commute_stabilize_col hu'_op ⟨q, hq⟩ (MulOpposite.op (-1))
    have hcq : Commute (stabilize (Nat.le_succ n) u')
        (IndexedSteinbergGroup.x (Fin.castSucc_lt_last ⟨q, hq⟩).ne.symm (1 : R)) := by
      have h := hcq_op.map (IndexedSteinbergGroup.transposeOp (ι := Fin (n + 1)) (R := R)).symm
      rw [← IndexedSteinbergGroup.transposeOp_mapIndex, MulEquiv.symm_apply_apply,
        IndexedSteinbergGroup.transposeOp_symm_x, MulOpposite.unop_op, neg_neg] at h
      exact h
    have hcomm_fin : Commute (stabilize (Nat.le_succ n) u')
        ⁅IndexedSteinbergGroup.x (Fin.castSucc_lt_last ⟨p, hp⟩).ne b,
          IndexedSteinbergGroup.x (Fin.castSucc_lt_last ⟨q, hq⟩).ne.symm (1 : R)⁆ := by
      rw [commutatorElement_def]
      exact ((hcp.mul_right hcq).mul_right hcp.inv_right).mul_right hcq.inv_right
    have hpq_fin : (⟨p, hp⟩ : Fin n).castSucc ≠ (⟨q, hq⟩ : Fin n).castSucc := fun h ↦
      hpq (congrArg Fin.val h)
    rw [IndexedSteinbergGroup.commutatorElement_x _ _ hpq_fin, mul_one] at hcomm_fin
    have hcomm := hcomm_fin.map (ofFin R (n + 1))
    rw [ofFin_stabilize, ofFin_stabilize, ofFin_x] at hcomm
    simp only [Fin.val_castSucc] at hcomm
    rw [Subgroup.mem_centralizer_iff]
    intro _ hw
    rw [Set.mem_singleton_iff.mp hw]
    exact hcomm
  refine Subgroup.mem_center_iff.mpr fun w ↦ ?_
  have hw : w ∈ Subgroup.centralizer {ofFin R m u} := htop ▸ Subgroup.mem_top w
  exact (Subgroup.mem_centralizer_iff.mp hw (ofFin R m u) rfl).symm

end Center

end SteinbergGroup

end TauCeti
