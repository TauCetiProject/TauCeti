/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable.BlockSum

/-!
# Relative algebraic `K₁` of a two-sided ideal

Let `I` be a two-sided ideal of an associative unital ring `R`. The **congruence subgroup**
`GL_∞(R, I)` is the kernel of reduction `GL_∞(R) → GL_∞(R ⧸ I)`: the invertible matrices congruent
to the identity modulo `I`. The **relative elementary subgroup** `E_∞(R, I)` is the normal closure
of the elementary matrices `e_{ij}(a) = 1 + a E_{ij}` with `a ∈ I`; taking the normal closure in
`GL_∞(R)` or in `E_∞(R)` gives the same subgroup. It lies in `E_∞(R) ∩ GL_∞(R, I)`.

The **relative Whitehead lemma** identifies `E_∞(R, I)` with the commutator subgroup
`⁅GL_∞(R, I), GL_∞(R)⁆`. If `u ≡ 1` modulo `I`, every factor of Whitehead's factorization
`u ⊕ u⁻¹ = U(u) L(-u⁻¹) U(u) U(-1) L(1) U(-1)` into block unipotent matrices agrees modulo
`E_∞(R, I)` with the corresponding factor for `u = 1`, so `u ⊕ u⁻¹ ∈ E_∞(R, I)`; the commutator of
`u` with `v` is then the commutator of `u ⊕ u⁻¹` with `v ⊕ 1`. Conversely
`e_{ij}(a) = ⁅e_{ik}(a), e_{kj}(1)⁆` for a third index `k`.

Consequently the **relative `K₁`**, `K₁(R, I) = GL_∞(R, I) / E_∞(R, I)`, is an abelian group. It
is functorial in morphisms of pairs `(R, I) → (S, J)`, that is ring homomorphisms `f` with
`f(I) ⊆ J`, and maps to `K₁(R)`. The sequence `K₁(R, I) → K₁(R) → K₁(R ⧸ I)` is exact at `K₁(R)`:
a class killed in `K₁(R ⧸ I)` has an elementary image, which lifts to an elementary matrix over
`R`, and correcting by that lift gives a representative congruent to `1`. The map
`K₁(R, I) → K₁(R)` need not be injective, so `K₁(R, I)` is not defined as the kernel. For `I = R`
it is an isomorphism, and `K₁(R, 0)` is trivial.

## Main definitions

* `TauCeti.StableGeneralLinearGroup.congruenceSubgroup`: the congruence subgroup `GL_∞(R, I)`.
* `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup`: the relative elementary subgroup
  `E_∞(R, I)`.
* `TauCeti.idealAlgebraicK1`: the relative `K₁(R, I) = GL_∞(R, I) / E_∞(R, I)`, a commutative
  group.
* `TauCeti.idealAlgebraicK1.mk`: the class in `K₁(R, I)` of a matrix congruent to `1`.
* `TauCeti.idealAlgebraicK1.toAlgebraicK1`: the forgetful map `K₁(R, I) → K₁(R)`.
* `TauCeti.idealAlgebraicK1.map`: functoriality in morphisms of pairs.

## Main results

* `TauCeti.StableGeneralLinearGroup.of_mem_congruenceSubgroup_iff`: an invertible matrix lies in
  `GL_∞(R, I)` exactly when it is entrywise congruent to the identity modulo `I`.
* `TauCeti.StableGeneralLinearGroup.ker_map`: the kernel of `GL_∞(R) → GL_∞(S)` along any ring
  homomorphism `f` is `GL_∞(R, ker f)`.
* `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_eq_map_normalClosure`: `E_∞(R, I)`
  is also the normal closure in `E_∞(R)`.
* `TauCeti.StableGeneralLinearGroup.commutator_congruenceSubgroup_top`: the relative Whitehead
  lemma `⁅GL_∞(R, I), GL_∞(R)⁆ = E_∞(R, I)`.
* `TauCeti.idealAlgebraicK1.mulExact_toAlgebraicK1_map`: exactness of
  `K₁(R, ker f) → K₁(R) → K₁(S)` at `K₁(R)` for a surjective ring homomorphism `f`, and
  `TauCeti.idealAlgebraicK1.mulExact_toAlgebraicK1_map_mk'` for the quotient map `R → R ⧸ I`.
* `TauCeti.idealAlgebraicK1.toAlgebraicK1_bijective_top`,
  `TauCeti.idealAlgebraicK1.instSubsingletonBot`: `K₁(R, R) ≅ K₁(R)` and `K₁(R, 0) = 0`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Relative Whitehead Lemma 2.1, Definition 2.2 and
  Proposition 2.3.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §4.
-/

public section

noncomputable section

open Matrix TwoSidedIdeal

open scoped commutatorElement

namespace TauCeti

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

namespace StableGeneralLinearGroup

/-! ### The congruence subgroup -/

/-- The image in `GL_∞(R)` of an invertible matrix lies in the kernel of the homomorphism induced
by a ring homomorphism `f` exactly when the matrix is entrywise congruent to the identity modulo
the kernel of `f`. -/
theorem of_mem_ker_map_iff (f : R →+* S) {n : ℕ} {u : GL (Fin n) R} :
    of R n u ∈ (map f).ker ↔
      ∀ i j, (u : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ ker f := by
  rw [MonoidHom.mem_ker, map_of, ← map_one (of S n), (of_injective n).eq_iff, Units.ext_iff,
    ← Matrix.ext_iff]
  refine forall₂_congr fun i j ↦ ?_
  rw [mem_ker, map_sub, sub_eq_zero]
  simp [Matrix.one_apply, apply_ite f]

/-- The **congruence subgroup** `GL_∞(R, I)` of a two-sided ideal `I`: the kernel of the reduction
`GL_∞(R) → GL_∞(R ⧸ I)`. -/
def congruenceSubgroup (I : TwoSidedIdeal R) : Subgroup (StableGeneralLinearGroup R) :=
  (map I.ringCon.mk').ker

variable {I J : TwoSidedIdeal R}

/-- An element of `GL_∞(R)` lies in `GL_∞(R, I)` exactly when it reduces to the identity modulo
`I`. -/
theorem mem_congruenceSubgroup_iff {x : StableGeneralLinearGroup R} :
    x ∈ congruenceSubgroup I ↔ map I.ringCon.mk' x = 1 :=
  MonoidHom.mem_ker

instance (I : TwoSidedIdeal R) : (congruenceSubgroup I).Normal :=
  MonoidHom.normal_ker _

/-- An invertible matrix lies in `GL_∞(R, I)` exactly when it is entrywise congruent to the
identity modulo `I`. -/
theorem of_mem_congruenceSubgroup_iff {n : ℕ} {u : GL (Fin n) R} :
    of R n u ∈ congruenceSubgroup I ↔
      ∀ i j, (u : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
  rw [congruenceSubgroup, of_mem_ker_map_iff, ker_ringCon_mk']

/-- The kernel of the homomorphism `GL_∞(R) → GL_∞(S)` induced by a ring homomorphism `f` is the
congruence subgroup of the kernel of `f`. -/
theorem ker_map (f : R →+* S) : (map f).ker = congruenceSubgroup (ker f) := by
  ext x
  obtain ⟨n, u, rfl⟩ := exists_of x
  rw [of_mem_ker_map_iff, of_mem_congruenceSubgroup_iff]

/-- The congruence subgroup grows with the ideal. -/
theorem congruenceSubgroup_mono (h : I ≤ J) : congruenceSubgroup I ≤ congruenceSubgroup J := by
  intro x hx
  obtain ⟨n, u, rfl⟩ := exists_of x
  rw [of_mem_congruenceSubgroup_iff] at hx ⊢
  exact fun i j ↦ h (hx i j)

/-- Only the identity is congruent to the identity modulo the zero ideal. -/
@[simp]
theorem congruenceSubgroup_bot : congruenceSubgroup (⊥ : TwoSidedIdeal R) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  simp only [of_mem_congruenceSubgroup_iff, mem_bot, sub_eq_zero] at hx
  rw [show u = 1 from Units.ext (Matrix.ext hx), map_one]

/-- Every element is congruent to the identity modulo the unit ideal. -/
@[simp]
theorem congruenceSubgroup_top : congruenceSubgroup (⊤ : TwoSidedIdeal R) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  exact of_mem_congruenceSubgroup_iff.2 fun _ _ ↦ trivial

/-- A morphism of pairs `(R, I) → (S, J)` carries `GL_∞(R, I)` into `GL_∞(S, J)`. -/
theorem map_congruenceSubgroup_le {J : TwoSidedIdeal S} (f : R →+* S) (h : I ≤ J.comap f) :
    (congruenceSubgroup I).map (map f) ≤ congruenceSubgroup J := by
  refine Subgroup.map_le_iff_le_comap.2 fun x hx ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  rw [of_mem_congruenceSubgroup_iff] at hx
  rw [Subgroup.mem_comap, map_of, of_mem_congruenceSubgroup_iff]
  intro i j
  simpa [Matrix.one_apply, apply_ite f] using (mem_comap f).1 (h (hx i j))

/-! ### The relative elementary subgroup -/

/-- The **relative elementary subgroup** `E_∞(R, I)`: the normal closure in `GL_∞(R)` of the
elementary matrices `e_{ij}(a)` with `a ∈ I`. By
`TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_eq_map_normalClosure` it is also the
normal closure in `E_∞(R)`. -/
def relativeElementarySubgroup (I : TwoSidedIdeal R) : Subgroup (StableGeneralLinearGroup R) :=
  Subgroup.normalClosure {g | ∃ p, ∃ a ∈ I, stableTransvection p a = g}

instance (I : TwoSidedIdeal R) : (relativeElementarySubgroup I).Normal :=
  Subgroup.normalClosure_normal

/-- `E_∞(R, I)` is contained in a normal subgroup exactly when every elementary matrix with
parameter in `I` is. -/
theorem relativeElementarySubgroup_le_iff {H : Subgroup (StableGeneralLinearGroup R)} [H.Normal] :
    relativeElementarySubgroup I ≤ H ↔ ∀ p, ∀ a ∈ I, stableTransvection p a ∈ H := by
  rw [relativeElementarySubgroup, ← Subgroup.normalClosure_subset_iff]
  constructor
  · exact fun h p a ha ↦ h ⟨p, a, ha, rfl⟩
  · rintro h _ ⟨p, a, ha, rfl⟩
    exact h p a ha

/-- An elementary matrix `e_{ij}(a)` with `a ∈ I` lies in `E_∞(R, I)`. -/
theorem stableTransvection_mem_relativeElementarySubgroup (p : {p : ℕ × ℕ // p.1 ≠ p.2})
    {a : R} (ha : a ∈ I) : stableTransvection p a ∈ relativeElementarySubgroup I :=
  Subgroup.subset_normalClosure ⟨p, a, ha, rfl⟩

/-- An elementary matrix of finite size with parameter in `I` lies in `E_∞(R, I)`. -/
theorem of_transvectionUnit_mem_relativeElementarySubgroup {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {a : R} (ha : a ∈ I) : of R n (transvectionUnit hij a) ∈ relativeElementarySubgroup I := by
  rw [← stableTransvection_eq_of ⟨(i, j), Fin.val_injective.ne hij⟩ a i.isLt j.isLt]
  exact stableTransvection_mem_relativeElementarySubgroup _ ha

/-- The relative elementary subgroup grows with the ideal. -/
theorem relativeElementarySubgroup_mono (h : I ≤ J) :
    relativeElementarySubgroup I ≤ relativeElementarySubgroup J :=
  relativeElementarySubgroup_le_iff.2 fun p _ ha ↦
    stableTransvection_mem_relativeElementarySubgroup p (h ha)

/-- Relative elementary matrices are stably elementary. -/
theorem relativeElementarySubgroup_le_elementarySubgroup :
    relativeElementarySubgroup I ≤ elementarySubgroup R :=
  relativeElementarySubgroup_le_iff.2 fun p a _ ↦ stableTransvection_mem_elementarySubgroup p a

/-- Relative elementary matrices are congruent to the identity. -/
theorem relativeElementarySubgroup_le_congruenceSubgroup :
    relativeElementarySubgroup I ≤ congruenceSubgroup I := by
  refine relativeElementarySubgroup_le_iff.2 fun p a ha ↦ ?_
  have ha' : I.ringCon.mk' a = 0 := by rwa [← mem_ker, ker_ringCon_mk']
  rw [mem_congruenceSubgroup_iff, map_stableTransvection, ha', stableTransvection_zero]

/-- For the zero ideal, the relative elementary subgroup is trivial. -/
@[simp]
theorem relativeElementarySubgroup_bot : relativeElementarySubgroup (⊥ : TwoSidedIdeal R) = ⊥ :=
  eq_bot_iff.2 <| relativeElementarySubgroup_le_iff.2 fun p a ha ↦ by
    rw [(mem_bot (R := R)).1 ha, stableTransvection_zero]
    exact one_mem _

/-- For the unit ideal, the relative elementary subgroup is the stable elementary subgroup. -/
@[simp]
theorem relativeElementarySubgroup_top :
    relativeElementarySubgroup (⊤ : TwoSidedIdeal R) = elementarySubgroup R := by
  refine le_antisymm relativeElementarySubgroup_le_elementarySubgroup fun x hx ↦ ?_
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hx
  refine (TauCeti.elementarySubgroup_le_iff
    (H := (relativeElementarySubgroup ⊤).comap (of R n))).2 (fun i j hij a ↦ ?_) hu
  exact of_transvectionUnit_mem_relativeElementarySubgroup hij trivial

/-- A morphism of pairs `(R, I) → (S, J)` carries `E_∞(R, I)` into `E_∞(S, J)`. -/
theorem map_relativeElementarySubgroup_le {J : TwoSidedIdeal S} (f : R →+* S)
    (h : I ≤ J.comap f) :
    (relativeElementarySubgroup I).map (map f) ≤ relativeElementarySubgroup J := by
  refine Subgroup.map_le_iff_le_comap.2 (relativeElementarySubgroup_le_iff.2 fun p a ha ↦ ?_)
  rw [Subgroup.mem_comap, map_stableTransvection]
  exact stableTransvection_mem_relativeElementarySubgroup p ((mem_comap f).1 (h ha))

/-- The normal closure defining `E_∞(R, I)` may be taken in `E_∞(R)` instead of `GL_∞(R)`: on
each finite stage, conjugation by an element of `GL_∞(R)` is conjugation by an element of
`E_∞(R)`. -/
theorem relativeElementarySubgroup_eq_map_normalClosure :
    relativeElementarySubgroup I =
      (Subgroup.normalClosure ((elementarySubgroup R).subtype ⁻¹'
        {g | ∃ p, ∃ a ∈ I, stableTransvection p a = g})).map (elementarySubgroup R).subtype := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx ↦ ?_)
    (Subgroup.map_le_iff_le_comap.2 (Subgroup.normalClosure_le_normal
      fun _ hx ↦ Subgroup.subset_normalClosure hx))
  obtain ⟨t, ⟨p, a, ha, rfl⟩, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc
  obtain ⟨e, he, hge⟩ := exists_mem_elementarySubgroup_forall_mul_mul_inv_eq g
    (max p.val.1 p.val.2 + 1)
  have ht : (⟨_, stableTransvection_mem_elementarySubgroup p a⟩ : elementarySubgroup R) ∈
      Subgroup.normalClosure ((elementarySubgroup R).subtype ⁻¹'
        {g | ∃ p, ∃ a ∈ I, stableTransvection p a = g}) :=
    Subgroup.subset_normalClosure ⟨p, a, ha, rfl⟩
  refine ⟨_, Subgroup.normalClosure_normal.conj_mem _ ht ⟨e, he⟩, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [stableTransvection_eq_of (n := max p.val.1 p.val.2 + 1) p a (by omega) (by omega)]
  exact hge _

/-! ### The relative Whitehead lemma -/

/-- Block unipotent matrices whose block has entries in `I` are relative elementary. -/
private theorem ofEquiv_blockGL_mem_relativeElementarySubgroup {m k : Type*} [Fintype m]
    [DecidableEq m] [Fintype k] [DecidableEq k] {n : ℕ} (e : m ⊕ k ≃ Fin n)
    {X : Matrix m k R} {Y : Matrix k m R} (hX : ∀ i j, X i j ∈ I) (hY : ∀ i j, Y i j ∈ I) :
    ofEquiv R e (upperBlockGL X) ∈ relativeElementarySubgroup I ∧
      ofEquiv R e (lowerBlockGL Y) ∈ relativeElementarySubgroup I := by
  have hmem {a b : m ⊕ k} (hab : a ≠ b) {c : R} (hc : c ∈ I) :
      ofEquiv R e (transvectionUnit hab c) ∈ relativeElementarySubgroup I := by
    rw [ofEquiv_apply, Equiv.reindexGL_transvectionUnit]
    exact of_transvectionUnit_mem_relativeElementarySubgroup _ hc
  constructor
  · rw [matrix_eq_sum_single X]
    refine Finset.sum_induction _ (fun Z ↦ ofEquiv R e (upperBlockGL Z) ∈ _)
      (fun Z W hZ hW ↦ by simpa only [upperBlockGL_add, map_mul] using mul_mem hZ hW)
      (by simp) fun a _ ↦ Finset.sum_induction _ (fun Z ↦ ofEquiv R e (upperBlockGL Z) ∈ _)
      (fun Z W hZ hW ↦ by simpa only [upperBlockGL_add, map_mul] using mul_mem hZ hW)
      (by simp) fun b _ ↦ ?_
    rw [upperBlockGL_single]
    exact hmem _ (hX a b)
  · rw [matrix_eq_sum_single Y]
    refine Finset.sum_induction _ (fun Z ↦ ofEquiv R e (lowerBlockGL Z) ∈ _)
      (fun Z W hZ hW ↦ by simpa only [lowerBlockGL_add, map_mul] using mul_mem hZ hW)
      (by simp) fun a _ ↦ Finset.sum_induction _ (fun Z ↦ ofEquiv R e (lowerBlockGL Z) ∈ _)
      (fun Z W hZ hW ↦ by simpa only [lowerBlockGL_add, map_mul] using mul_mem hZ hW)
      (by simp) fun b _ ↦ ?_
    rw [lowerBlockGL_single]
    exact hmem _ (hY a b)

/-- **Whitehead's matrix of a congruence matrix is relative elementary.** If `u` is congruent to
the identity modulo `I`, then `u ⊕ u⁻¹` lies in `E_∞(R, I)`. -/
theorem ofEquiv_fromBlocksGL_inv_mem_relativeElementarySubgroup {n : ℕ} {u : GL (Fin n) R}
    (hu : of R n u ∈ congruenceSubgroup I) :
    ofEquiv R finSumFinEquiv (fromBlocksGL (u, u⁻¹)) ∈ relativeElementarySubgroup I := by
  let q := (QuotientGroup.mk' (relativeElementarySubgroup I)).comp
    (ofEquiv R (finSumFinEquiv (m := n) (n := n)))
  -- Block unipotent matrices with congruent blocks agree modulo `E_∞(R, I)`.
  have hU {X Y : Matrix (Fin n) (Fin n) R} (h : ∀ i j, X i j - Y i j ∈ I) :
      q (upperBlockGL X) = q (upperBlockGL Y) := by
    rw [← div_eq_one, ← map_div, div_eq_mul_inv, upperBlockGL_inv, ← upperBlockGL_add,
      ← sub_eq_add_neg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (ofEquiv_blockGL_mem_relativeElementarySubgroup _ (Y := 0) h (by simp)).1
  have hL {X Y : Matrix (Fin n) (Fin n) R} (h : ∀ i j, X i j - Y i j ∈ I) :
      q (lowerBlockGL X) = q (lowerBlockGL Y) := by
    rw [← div_eq_one, ← map_div, div_eq_mul_inv, lowerBlockGL_inv, ← lowerBlockGL_add,
      ← sub_eq_add_neg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (ofEquiv_blockGL_mem_relativeElementarySubgroup _ (X := 0) (by simp) h).2
  have hu' : of R n u⁻¹ ∈ congruenceSubgroup I := by
    rw [map_inv]
    exact inv_mem hu
  rw [of_mem_congruenceSubgroup_iff] at hu hu'
  have hneg (i j : Fin n) : (-(↑u⁻¹ : Matrix (Fin n) (Fin n) R)) i j -
      (-1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
    rw [Matrix.neg_apply, Matrix.neg_apply, neg_sub_neg, ← neg_sub]
    exact neg_mem (hu' i j)
  -- Compare Whitehead's factorization of `u ⊕ u⁻¹` with that of `1 ⊕ 1⁻¹ = 1`.
  have h1 := fromBlocksGL_inv_eq_upperBlockGL_mul (1 : GL (Fin n) R)
  rw [inv_one, Units.val_one, ← Prod.one_eq_mk, map_one] at h1
  have hq : q (fromBlocksGL (u, u⁻¹)) = 1 := by
    rw [fromBlocksGL_inv_eq_upperBlockGL_mul]
    simp only [map_mul, hU hu, hL hneg]
    simp only [← map_mul, ← h1, map_one]
  rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq

/-- **Relative Whitehead lemma.** The commutator of an element of `GL_∞(R, I)` with any element of
`GL_∞(R)` lies in `E_∞(R, I)`. -/
theorem commutatorElement_mem_relativeElementarySubgroup {g : StableGeneralLinearGroup R}
    (hg : g ∈ congruenceSubgroup I) (h : StableGeneralLinearGroup R) :
    ⁅g, h⁆ ∈ relativeElementarySubgroup I := by
  obtain ⟨n, u, v, rfl, rfl⟩ := exists_of₂ g h
  -- The image of a matrix `w` of size `n` is that of `w ⊕ 1` of size `n + n`.
  have hblock (w : GL (Fin n) R) :
      of R n w = ofEquiv R finSumFinEquiv (fromBlocksGL (w, (1 : GL (Fin n) R))) := by
    rw [ofEquiv_apply, ← stabilizeGL_eq_reindexGL_fromBlocksGL, of_stabilizeGL]
  have hc : ⁅fromBlocksGL (u, u⁻¹), fromBlocksGL (v, (1 : GL (Fin n) R))⁆ =
      fromBlocksGL (⁅u, v⁆, 1) := by
    rw [← map_commutatorElement]
    simp [commutatorElement_def]
  have hu := ofEquiv_fromBlocksGL_inv_mem_relativeElementarySubgroup hg
  rw [← map_commutatorElement, hblock, ← hc, map_commutatorElement]
  exact Subgroup.commutator_le_left _ ⊤ (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top _))

/-- **Relative Whitehead lemma** (Weibel III.2.1). The relative elementary subgroup `E_∞(R, I)` is
the commutator subgroup `⁅GL_∞(R, I), GL_∞(R)⁆`. -/
theorem commutator_congruenceSubgroup_top :
    ⁅congruenceSubgroup I, ⊤⁆ = relativeElementarySubgroup I := by
  refine le_antisymm (Subgroup.commutator_le.2 fun g hg h _ ↦
    commutatorElement_mem_relativeElementarySubgroup hg h)
    (relativeElementarySubgroup_le_iff.2 fun ⟨(i, j), hij⟩ a ha ↦ ?_)
  -- `e_{ij}(a) = ⁅e_{ik}(a), e_{kj}(1)⁆` for the index `k = i + j + 1`.
  have hik : i ≠ i + j + 1 := by omega
  have hkj : i + j + 1 ≠ j := by omega
  rw [← mul_one a, ← commutatorElement_stableTransvection hik hkj hij]
  exact Subgroup.commutator_mem_commutator
    (relativeElementarySubgroup_le_congruenceSubgroup
      (stableTransvection_mem_relativeElementarySubgroup _ ha)) (Subgroup.mem_top _)

/-- The commutator subgroup of `GL_∞(R, I)` lies in `E_∞(R, I)`. -/
theorem commutator_congruenceSubgroup_le :
    ⁅congruenceSubgroup I, congruenceSubgroup I⁆ ≤ relativeElementarySubgroup I :=
  (Subgroup.commutator_mono le_rfl le_top).trans commutator_congruenceSubgroup_top.le

end StableGeneralLinearGroup

/-! ### Relative `K₁` -/

open StableGeneralLinearGroup

variable (I : TwoSidedIdeal R)

/-- The **relative algebraic `K₁`** of a two-sided ideal `I`: the quotient
`K₁(R, I) = GL_∞(R, I) / E_∞(R, I)` of the congruence subgroup by the relative elementary
subgroup. It is a commutative group by the relative Whitehead lemma. -/
abbrev idealAlgebraicK1 : Type _ :=
  congruenceSubgroup I ⧸ (relativeElementarySubgroup I).subgroupOf (congruenceSubgroup I)

namespace idealAlgebraicK1

/-- `K₁(R, I)` is commutative: the commutator subgroup of `GL_∞(R, I)` lies in `E_∞(R, I)`. -/
instance instCommGroup : CommGroup (idealAlgebraicK1 I) where
  __ := QuotientGroup.Quotient.group _
  mul_comm x y := by
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := commutator_congruenceSubgroup_le (I := I)
      (Subgroup.commutator_mem_commutator (inv_mem y.property) (inv_mem x.property))
    simpa [commutatorElement_def, mul_assoc] using h

/-- The class in `K₁(R, I)` of an element of `GL_∞(R, I)`. -/
def mk : congruenceSubgroup I →* idealAlgebraicK1 I :=
  QuotientGroup.mk' _

/-- The coercion of `GL_∞(R, I)` into the quotient `K₁(R, I)` is the quotient map `mk`. -/
@[simp]
theorem coe_eq_mk (g : congruenceSubgroup I) : (g : idealAlgebraicK1 I) = mk I g :=
  (rfl)

variable {I}

/-- Every class in `K₁(R, I)` is the class of an element of `GL_∞(R, I)`. -/
theorem mk_surjective : Function.Surjective (mk I) :=
  QuotientGroup.mk'_surjective _

/-- The class of an element of `GL_∞(R, I)` is trivial exactly when it is relative elementary. -/
theorem mk_eq_one_iff {g : congruenceSubgroup I} :
    mk I g = 1 ↔ (g : StableGeneralLinearGroup R) ∈ relativeElementarySubgroup I :=
  (QuotientGroup.eq_one_iff g).trans Subgroup.mem_subgroupOf

/-- Every class in `K₁(R, I)` is the class of an invertible matrix of finite size which is
congruent to the identity modulo `I`. -/
theorem exists_mk_of (x : idealAlgebraicK1 I) :
    ∃ (n : ℕ) (u : GL (Fin n) R) (hu : of R n u ∈ congruenceSubgroup I), mk I ⟨_, hu⟩ = x := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := mk_surjective x
  obtain ⟨n, u, rfl⟩ := exists_of g
  exact ⟨n, u, hg, rfl⟩

/-- Two homomorphisms out of `K₁(R, I)` agree when they agree on the classes of `GL_∞(R, I)`. -/
theorem hom_ext {G : Type*} [Monoid G] {φ ψ : idealAlgebraicK1 I →* G}
    (h : φ.comp (mk I) = ψ.comp (mk I)) : φ = ψ :=
  QuotientGroup.monoidHom_ext _ h

variable (I) in
/-- The forgetful homomorphism `K₁(R, I) → K₁(R)`, induced by the inclusion
`GL_∞(R, I) ⊆ GL_∞(R)`. -/
def toAlgebraicK1 : idealAlgebraicK1 I →* AlgebraicK1 R :=
  QuotientGroup.lift _ (Group.Abelianization.of.comp (congruenceSubgroup I).subtype)
    fun g hg ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, AlgebraicK1.ker_of]
      exact relativeElementarySubgroup_le_elementarySubgroup (Subgroup.mem_subgroupOf.1 hg)

/-- The forgetful map sends the class of `g ∈ GL_∞(R, I)` to the class of `g` in `K₁(R)`. -/
@[simp]
theorem toAlgebraicK1_mk (g : congruenceSubgroup I) :
    toAlgebraicK1 I (mk I g) = Group.Abelianization.of (g : StableGeneralLinearGroup R) :=
  (rfl)

/-- **Exactness of `K₁(R, I) → K₁(R) → K₁(S)` at `K₁(R)`** for a surjective ring homomorphism
`f` with kernel `I`: a class of `K₁(R)` dies in `K₁(S)` exactly when it comes from `K₁(R, I)`. -/
theorem mulExact_toAlgebraicK1_map {f : R →+* S} (hf : Function.Surjective f) :
    Function.MulExact (toAlgebraicK1 (ker f)) (AlgebraicK1.map f) := by
  intro y
  constructor
  · -- The image of `x` is elementary; correct `x` by an elementary lift of that image.
    intro hy
    obtain ⟨x, rfl⟩ := Group.Abelianization.surjective_of _ y
    rw [AlgebraicK1.map_of, ← MonoidHom.mem_ker, AlgebraicK1.ker_of,
      ← map_elementarySubgroup_eq_of_surjective f hf] at hy
    obtain ⟨e, he, hex⟩ := hy
    have hxe : x * e⁻¹ ∈ congruenceSubgroup (ker f) := by
      rw [← ker_map, MonoidHom.mem_ker, map_mul, map_inv, hex, mul_inv_cancel]
    have he1 : Group.Abelianization.of e = 1 := by
      rwa [← MonoidHom.mem_ker, AlgebraicK1.ker_of]
    exact ⟨mk _ ⟨_, hxe⟩, by simp [he1]⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨g, hg⟩, rfl⟩ := mk_surjective z
    rw [← ker_map, MonoidHom.mem_ker] at hg
    simp [hg]

/-- **Exactness of `K₁(R, I) → K₁(R) → K₁(R ⧸ I)` at `K₁(R)`.** -/
theorem mulExact_toAlgebraicK1_map_mk' :
    Function.MulExact (toAlgebraicK1 I) (AlgebraicK1.map I.ringCon.mk') := by
  have h := mulExact_toAlgebraicK1_map I.ringCon.mk'_surjective
  rwa [ker_ringCon_mk'] at h

/-- `K₁(R, 0)` is trivial. -/
instance instSubsingletonBot : Subsingleton (idealAlgebraicK1 (⊥ : TwoSidedIdeal R)) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨⟨g, hg⟩, rfl⟩ := mk_surjective x
  obtain ⟨⟨h, hh⟩, rfl⟩ := mk_surjective y
  rw [congruenceSubgroup_bot, Subgroup.mem_bot] at hg hh
  subst hg hh
  rfl

/-- For the unit ideal, the forgetful map `K₁(R, R) → K₁(R)` is an isomorphism. -/
theorem toAlgebraicK1_bijective_top :
    Function.Bijective (toAlgebraicK1 (⊤ : TwoSidedIdeal R)) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨g, rfl⟩ := mk_surjective x
    rw [toAlgebraicK1_mk, ← MonoidHom.mem_ker, AlgebraicK1.ker_of,
      ← relativeElementarySubgroup_top] at hx
    exact mk_eq_one_iff.2 hx
  · obtain ⟨x, rfl⟩ := Group.Abelianization.surjective_of _ y
    exact ⟨mk _ ⟨x, by simp⟩, toAlgebraicK1_mk _⟩

/-! ### Functoriality -/

variable {J : TwoSidedIdeal S} {K : TwoSidedIdeal T}

/-- The homomorphism `K₁(R, I) → K₁(S, J)` induced by a morphism of pairs, a ring homomorphism
`f` with `f(I) ⊆ J`. -/
def map (f : R →+* S) (h : I ≤ J.comap f) : idealAlgebraicK1 I →* idealAlgebraicK1 J :=
  QuotientGroup.map _ _
    (((StableGeneralLinearGroup.map f).comp (congruenceSubgroup I).subtype).codRestrict _
      fun g ↦ map_congruenceSubgroup_le f h ⟨g, g.property, rfl⟩)
    fun g hg ↦ map_relativeElementarySubgroup_le f h ⟨g, Subgroup.mem_subgroupOf.1 hg, rfl⟩

/-- The induced map sends the class of `g` to the class of its image in `GL_∞(S, J)`. -/
@[simp]
theorem map_mk (f : R →+* S) (h : I ≤ J.comap f) (g : congruenceSubgroup I) :
    map f h (mk I g) = mk J ⟨StableGeneralLinearGroup.map f g,
      map_congruenceSubgroup_le f h ⟨g, g.property, rfl⟩⟩ :=
  (rfl)

/-- The identity ring homomorphism induces the identity of `K₁(R, I)`. -/
@[simp]
theorem map_id : map (RingHom.id R) (fun _ hx ↦ (mem_comap _).2 hx) =
    MonoidHom.id (idealAlgebraicK1 I) := by
  refine hom_ext (MonoidHom.ext fun g ↦ ?_)
  simp

/-- The induced maps on relative `K₁` compose according to the ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    map (g.comp f) (fun _ hx ↦ (mem_comap _).2 ((mem_comap g).1 (hg ((mem_comap f).1 (hf hx))))) =
      (map g hg).comp (map f hf) := by
  refine hom_ext (MonoidHom.ext fun x ↦ ?_)
  simp

/-- The forgetful map to `K₁` is natural in morphisms of pairs. -/
theorem toAlgebraicK1_map (f : R →+* S) (h : I ≤ J.comap f) (x : idealAlgebraicK1 I) :
    toAlgebraicK1 J (map f h x) = AlgebraicK1.map f (toAlgebraicK1 I x) := by
  obtain ⟨g, rfl⟩ := mk_surjective x
  simp

end idealAlgebraicK1

end TauCeti
