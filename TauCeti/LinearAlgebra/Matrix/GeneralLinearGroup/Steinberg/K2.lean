/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import TauCeti.GroupTheory.Commutator

/-!
# Milnor's algebraic `K₂` and centrality of `ker (St(R) →* GL_∞(R))`

For an associative unital ring `R`, the canonical homomorphism
`TauCeti.SteinbergGroup.toStableGL : St(R) →* GL_∞(R)` has image the stable elementary subgroup
`E_∞(R)`. Every element `z ∈ ker (St(R) →* GL_∞(R))` comes from `Stₙ(R)` for some `n`. Inside
`St_{n + 1}(R)`, the stabilized subgroup `Stₙ(R)` normalizes the `n`-th column root subgroup
`Pₙ = ⟨x_{in}(a) | i < n⟩`, on which `toGL` is injective via upper block unipotent matrices in
`GL_{n + 1}(R)`. Hence `z` centralizes `Pₙ`, and by opposite-ring inverse-transpose duality
(`IndexedSteinbergGroup.transposeOp`) it also centralizes the `n`-th row root subgroup
`⟨x_{nj}(b) | j < n⟩`, and therefore every generator `x_{pq}(b) = ⁅x_{pn}(b), x_{nq}(1)⁆` with
`p, q < n`.

Thus **Milnor's algebraic `K₂(R) := ker (St(R) →* GL_∞(R))`** lies in the center of `St(R)` and is a
commutative group, functorial in `R`, fitting into the exact sequence
`1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.

## Main definitions

* `TauCeti.AlgebraicK2`: Milnor's algebraic `K₂(R) := ker (St(R) →* GL_∞(R))`.
* `TauCeti.AlgebraicK2.map`: the homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism.

## Main results

* `TauCeti.SteinbergGroup.ker_toStableGL_le_center`: `ker (toStableGL R)` lies in the center of
  `St(R)`.
* `TauCeti.AlgebraicK2.instCommGroup`: `AlgebraicK2 R` is a commutative group.
* `TauCeti.AlgebraicK2.map_id`, `TauCeti.AlgebraicK2.map_comp`, `TauCeti.AlgebraicK2.map_map`:
  functoriality of `AlgebraicK2`.
* `TauCeti.AlgebraicK2.mulExact_subtype_toStableGL`: exactness at `St(R)` of
  `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.

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

private theorem colHomFin_pairwise (n : ℕ) :
    Pairwise fun i j : Fin n ↦ ∀ a b : Multiplicative R,
      Commute (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last i).ne a)
        (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last j).ne b) := by
  intro i j _ a b
  simp only [IndexedSteinbergGroup.xHom_apply]
  exact IndexedSteinbergGroup.commute_x
    (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne
    (Fin.castSucc_lt_last j).ne.symm (Fin.castSucc_lt_last i).ne.symm a.toAdd b.toAdd

/-- The homomorphism `(Fin n → Multiplicative R) →* St_{n + 1}(R)` assembling the commuting column
root subgroups `x_{i, n}` (`i < n`). -/
private def colHomFin (n : ℕ) :
    (Fin n → Multiplicative R) →* IndexedSteinbergGroup (Fin (n + 1)) R :=
  MonoidHom.noncommPiCoprod
    (fun i : Fin n ↦ IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last i).ne)
    (colHomFin_pairwise n)

/-- The upper block unipotent homomorphism `(Fin n → Multiplicative R) →* GL (Fin (n + 1)) R`
placing a column vector in the last column. -/
private def upperColGLHom (n : ℕ) :
    (Fin n → Multiplicative R) →* GL (Fin (n + 1)) R where
  toFun f := (finSumFinEquiv (m := n) (n := 1)).reindexGL R
    (Matrix.upperBlockGL (Matrix.of fun i (_ : Fin 1) ↦ (f i).toAdd))
  map_one' := by
    have h0 : (Matrix.of fun (i : Fin n) (_ : Fin 1) ↦
        (((1 : Fin n → Multiplicative R) i).toAdd : R)) = 0 := by
      ext
      simp only [Pi.one_apply, toAdd_one, Matrix.of_apply, Matrix.zero_apply]
    rw [h0, Matrix.upperBlockGL_zero, map_one]
  map_mul' f g := by
    have hadd : (Matrix.of fun i (_ : Fin 1) ↦ ((f * g) i).toAdd) =
        (Matrix.of fun i (_ : Fin 1) ↦ (f i).toAdd) +
          (Matrix.of fun i (_ : Fin 1) ↦ (g i).toAdd) := by
      ext i _
      exact toAdd_mul (f i) (g i)
    rw [hadd, Matrix.upperBlockGL_add, map_mul]

private theorem upperColGLHom_apply (n : ℕ) (f : Fin n → Multiplicative R) :
    upperColGLHom n f = (finSumFinEquiv (m := n) (n := 1)).reindexGL R
      (Matrix.upperBlockGL (Matrix.of fun i (_ : Fin 1) ↦ (f i).toAdd)) :=
  (rfl)

private theorem upperColGLHom_injective (n : ℕ) :
    Function.Injective (upperColGLHom (R := R) n) := by
  intro f g hfg
  rw [upperColGLHom_apply, upperColGLHom_apply] at hfg
  have hblk := ((finSumFinEquiv (m := n) (n := 1)).reindexGL R).injective hfg
  ext i
  have hentry := congrArg (fun u : GL (Fin n ⊕ Fin 1) R ↦
    (u : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) (Sum.inl i) (Sum.inr 0)) hblk
  simpa [Matrix.coe_upperBlockGL] using hentry

private theorem toGL_comp_colHomFin (n : ℕ) :
    (IndexedSteinbergGroup.toGL (R := R)).comp (colHomFin n) = upperColGLHom n := by
  refine MonoidHom.pi_ext fun i a ↦ ?_
  rw [MonoidHom.comp_apply, colHomFin, MonoidHom.noncommPiCoprod_mulSingle,
    IndexedSteinbergGroup.xHom_apply, IndexedSteinbergGroup.toGL_x, upperColGLHom_apply]
  have hblk : Matrix.upperBlockGL (Matrix.of fun k (_ : Fin 1) ↦
      ((Pi.mulSingle i a : Fin n → Multiplicative R) k).toAdd) =
      transvectionUnit (Sum.inl_ne_inr (a := i) (b := (0 : Fin 1))) a.toAdd := by
    apply Units.ext
    ext (p | p) (q | q) <;>
      simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply, Matrix.single_apply,
        Pi.mulSingle_apply, Fin.eq_zero, apply_ite Multiplicative.toAdd, eq_comm]
  rw [hblk, Equiv.reindexGL_transvectionUnit]
  have hi_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inl i) = i.castSucc := by ext; simp
  have hj_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inr 0) = Fin.last n := by ext; simp
  simp only [hi_eq, hj_eq]

private theorem mem_range_colHomFin {n : ℕ} (i : Fin n) (a : R) :
    IndexedSteinbergGroup.x (Fin.castSucc_lt_last i).ne a ∈ (colHomFin (R := R) n).range := by
  refine ⟨Pi.mulSingle i (Multiplicative.ofAdd a), ?_⟩
  rw [colHomFin, MonoidHom.noncommPiCoprod_mulSingle, IndexedSteinbergGroup.xHom_apply,
    toAdd_ofAdd]

private theorem range_stabilize_le_normalizer_colHomFin (n : ℕ) :
    (stabilize (Nat.le_succ n) (R := R)).range ≤
      Subgroup.normalizer ((colHomFin (R := R) n).range :
        Set (IndexedSteinbergGroup (Fin (n + 1)) R)) := by
  have hcastEmb : Fin.castLEEmb (Nat.le_succ n) = Fin.castSuccEmb := by
    ext p
    simp
  have hconj : ∀ {i j : Fin n} (hij : i ≠ j) (c : R),
      ((colHomFin (R := R) n).range).map
        (MulAut.conj (stabilize (Nat.le_succ n) (IndexedSteinbergGroup.x hij c))) ≤
        (colHomFin (R := R) n).range := by
    intro i j hij c
    have hrange : (colHomFin (R := R) n).range =
        ⨆ k : Fin n, (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last k).ne).range :=
      MonoidHom.noncommPiCoprod_range _
    rw [hrange, Subgroup.map_iSup]
    refine iSup_le fun k ↦ ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    simp only [stabilize, hcastEmb, IndexedSteinbergGroup.xHom_apply,
      IndexedSteinbergGroup.mapIndex_x, Fin.castSuccEmb_apply, MonoidHom.coe_ofClass,
      MulAut.conj_apply]
    by_cases hjk : j = k
    · subst hjk
      rw [IndexedSteinbergGroup.x_mul_x_mul_inv (Fin.castSucc_injective n |>.ne hij)
        (Fin.castSucc_lt_last j).ne (Fin.castSucc_lt_last i).ne, ← hrange]
      exact mul_mem (mem_range_colHomFin i (c * a.toAdd)) (mem_range_colHomFin j a.toAdd)
    · have hcomm := IndexedSteinbergGroup.commute_x
        (Fin.castSucc_injective n |>.ne hij) (Fin.castSucc_lt_last k).ne
        (Fin.castSucc_injective n |>.ne hjk) (Fin.castSucc_lt_last i).ne.symm c a.toAdd
      rw [hcomm.eq, mul_inv_cancel_right, ← hrange]
      exact mem_range_colHomFin k a.toAdd
  rw [IndexedSteinbergGroup.range_le_iff]
  intro i j hij c
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hconj hij c) fun y hy ↦ ?_
  refine ⟨(stabilize (Nat.le_succ n) (IndexedSteinbergGroup.x hij c))⁻¹ * y *
    stabilize (Nat.le_succ n) (IndexedSteinbergGroup.x hij c), ?_,
    by rw [MonoidHom.coe_ofClass, MulAut.conj_apply]; group⟩
  have hinv : (stabilize (Nat.le_succ n) (IndexedSteinbergGroup.x hij c))⁻¹ =
      stabilize (Nat.le_succ n) (IndexedSteinbergGroup.x hij (-c)) := by
    rw [← map_inv, IndexedSteinbergGroup.x_inv]
  have hmem := hconj hij (-c) ⟨y, hy, rfl⟩
  simpa only [SetLike.mem_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, ← hinv, inv_inv] using
    hmem

/-- Any element of `Stₙ(R)` in the kernel of `toGL` commutes, after stabilizing to `St_{n + 1}(R)`,
with every column generator `x_{p, n}(b)` (`p < n`). -/
private theorem commute_stabilize_col {n : ℕ} {u : IndexedSteinbergGroup (Fin n) R}
    (hu : IndexedSteinbergGroup.toGL u = 1) (p : Fin n) (b : R) :
    Commute (stabilize (Nat.le_succ n) u)
      (IndexedSteinbergGroup.x (Fin.castSucc_lt_last p).ne b) := by
  have hinf : (IndexedSteinbergGroup.toGL (ι := Fin (n + 1)) (R := R)).ker ⊓
      (colHomFin (R := R) n).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hker, ⟨f, rfl⟩⟩
    have hf : upperColGLHom n f = 1 := by
      rw [← toGL_comp_colHomFin, MonoidHom.comp_apply]
      exact hker
    have hf1 : f = 1 := upperColGLHom_injective n (hf.trans (map_one _).symm)
    rw [hf1, map_one, Subgroup.mem_bot]
  have hle := inf_normalizer_le_centralizer_of_inf_eq_bot Subgroup.le_normalizer_of_normal hinf
  have hker_u : stabilize (Nat.le_succ n) u ∈
      (IndexedSteinbergGroup.toGL (ι := Fin (n + 1)) (R := R)).ker := by
    rw [MonoidHom.mem_ker, IndexedSteinbergGroup.toGL_mapIndex_castLE, hu, map_one]
  have hmem : stabilize (Nat.le_succ n) u ∈
      Subgroup.centralizer ((colHomFin (R := R) n).range :
        Set (IndexedSteinbergGroup (Fin (n + 1)) R)) :=
    hle ⟨hker_u, range_stabilize_le_normalizer_colHomFin n ⟨u, rfl⟩⟩
  exact (Subgroup.mem_centralizer_iff.mp hmem _ (mem_range_colHomFin p b)).symm

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

/-! ## Algebraic `K₂` -/

variable (R : Type u) [Ring R]

/-- **Algebraic `K₂`** of a ring `R`: the kernel of the canonical homomorphism
`St(R) →* GL_∞(R)`. By `TauCeti.SteinbergGroup.ker_toStableGL_le_center`, `K₂(R)` is central in
`St(R)` and hence a commutative group. -/
abbrev AlgebraicK2 : Type u :=
  (SteinbergGroup.toStableGL R).ker

namespace AlgebraicK2

/-- Algebraic `K₂(R)` is a commutative group, because `ker (St(R) →* GL_∞(R))` is central in
`St(R)`. -/
instance instCommGroup : CommGroup (AlgebraicK2 R) :=
  { (inferInstance : Group (SteinbergGroup.toStableGL R).ker) with
    mul_comm := fun a b ↦ Subtype.ext <|
      (Subgroup.mem_center_iff.mp (SteinbergGroup.ker_toStableGL_le_center (R := R) b.property)
        a.val) }

/-- Exactness at `St(R)` of `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`: the kernel of
`St(R) →* GL_∞(R)` equals the image of the subgroup inclusion `K₂(R) →* St(R)`. -/
theorem mulExact_subtype_toStableGL :
    Function.MulExact
      ((SteinbergGroup.toStableGL R).ker.subtype : AlgebraicK2 R →* SteinbergGroup R)
      (SteinbergGroup.toStableGL R) := by
  rw [MonoidHom.mulExact_iff, Subgroup.range_subtype]

variable {R} {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism `f : R →+* S`, restricting
`IndexedSteinbergGroup.map f` to the kernels. -/
def map (f : R →+* S) : AlgebraicK2 R →* AlgebraicK2 S :=
  ((IndexedSteinbergGroup.map f).comp (SteinbergGroup.toStableGL R).ker.subtype).codRestrict _
    fun x ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        SteinbergGroup.toStableGL_map, MonoidHom.mem_ker.mp x.property, map_one]

/-- The underlying element in `St(S)` of `AlgebraicK2.map f x` is
`IndexedSteinbergGroup.map f x`. -/
@[simp]
theorem coe_map_apply (f : R →+* S) (x : AlgebraicK2 R) :
    (map f x : SteinbergGroup S) = IndexedSteinbergGroup.map f x :=
  (rfl)

/-- The identity ring homomorphism induces the identity of algebraic `K₂`. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (AlgebraicK2 R) := by
  ext x
  simp

/-- Algebraic `K₂` is functorial in ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp

/-- Applying `AlgebraicK2.map f` followed by `AlgebraicK2.map g` equals
`AlgebraicK2.map (g.comp f)`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : AlgebraicK2 R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

end AlgebraicK2

end TauCeti
