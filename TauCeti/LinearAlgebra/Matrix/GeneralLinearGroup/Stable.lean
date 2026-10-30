/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# The stable general linear group and the stable elementary subgroup

For a possibly noncommutative ring `A`, an invertible matrix of size `m` becomes one of any size
`n ≥ m` by placing it in the upper left block and completing it by the identity matrix,
`u ↦ u ⊕ 1`. These stabilization maps form a directed system of groups, whose direct limit is the
**stable general linear group** `GL_∞(A) = ⋃ₙ GL n A`. The images of the elementary subgroups
`E n A` generate the **stable elementary subgroup** `E_∞(A)`.

The main result is the stable identification `E_∞(A) = ⁅GL_∞(A), GL_∞(A)⁆` of the elementary
subgroup with the commutator subgroup, assembled from the finite-size facts in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Elementary.lean`: elementary matrices are
commutators in size at least three, and Whitehead's lemma makes every stabilized commutator
elementary. In particular `E_∞(A)` is normal and the quotient `GL_∞(A) / E_∞(A)`, algebraic `K₁`,
is abelian.

## Main definitions

* `Matrix.stabilize`: a square matrix of size `m` placed in the upper left block of size `n ≥ m`,
  completed by the identity matrix.
* `TauCeti.stabilizeGL`: the stabilization homomorphism `GL (Fin m) A →* GL (Fin n) A`.
* `TauCeti.StableGL`: the stable general linear group `GL_∞(A)`, the direct limit of the
  `GL (Fin n) A` along the stabilization maps, with the canonical maps `TauCeti.StableGL.of` and
  the universal property `TauCeti.StableGL.lift`.
* `TauCeti.stableElementarySubgroup`: the stable elementary subgroup `E_∞(A)`.

## Main results

* `TauCeti.stabilizeGL_eq_reindexGL_fromBlocksGL`: stabilization is `u ↦ u ⊕ 1`, reindexed along
  any equivalence `Fin m ⊕ κ ≃ Fin n` extending the inclusion of `Fin m`.
* `Matrix.stabilize_succ`: stabilization by one size is `Matrix.blockSucc`.
* `TauCeti.StableGL.of_injective`: each `GL (Fin n) A` embeds in `GL_∞(A)`.
* `TauCeti.mem_stableElementarySubgroup_iff`: the elements of `E_∞(A)` are the images of
  elementary matrices.
* `TauCeti.stableElementarySubgroup_eq_commutator`: `E_∞(A) = ⁅GL_∞(A), GL_∞(A)⁆`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  §3, Lemma 3.1 and Proposition 3.2.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.1,
  Definition 2.1.1 and Proposition 2.1.4.
-/

public section

open Matrix

open scoped commutatorElement

namespace Matrix

variable {A : Type*} {m n k : ℕ}

section ZeroOne

variable [Zero A] [One A]

/-- The **stabilization** of a square matrix of size `m` to size `n`: the matrix is placed in the
upper left block, and the remaining entries are those of the identity matrix. It is used for
`m ≤ n`, where it is the block diagonal matrix `M ⊕ 1`
(`Matrix.stabilize_eq_reindex_fromBlocks`). -/
def stabilize (n : ℕ) (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin n) (Fin n) A :=
  of fun a b ↦
    if hab : (a : ℕ) < m ∧ (b : ℕ) < m then M ⟨a, hab.1⟩ ⟨b, hab.2⟩
    else (1 : Matrix (Fin n) (Fin n) A) a b

/-- The entries of a stabilized matrix: those of the matrix in the upper left block, and those of
the identity matrix elsewhere. -/
theorem stabilize_apply (M : Matrix (Fin m) (Fin m) A) (a b : Fin n) :
    stabilize n M a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then M ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else (1 : Matrix (Fin n) (Fin n) A) a b :=
  (rfl)

/-- The upper left block of a stabilized matrix is the original matrix. -/
@[simp]
theorem stabilize_apply_castLE (h : m ≤ n) (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    stabilize n M (i.castLE h) (j.castLE h) = M i j := by
  simp [stabilize_apply]

/-- Stabilization to the same size is the identity. -/
@[simp]
theorem stabilize_self (M : Matrix (Fin m) (Fin m) A) : stabilize m M = M := by
  ext a b
  simp [stabilize_apply]

/-- Stabilizing twice is stabilizing once. -/
@[simp]
theorem stabilize_stabilize (hmn : m ≤ n) (M : Matrix (Fin m) (Fin m) A) :
    stabilize k (stabilize n M) = stabilize k M := by
  ext a b
  simp only [stabilize_apply, one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- Stabilization is injective. -/
theorem stabilize_injective (h : m ≤ n) :
    Function.Injective (stabilize (A := A) (m := m) n) := fun M N hMN ↦ by
  ext i j
  simpa using congrFun₂ hMN (i.castLE h) (j.castLE h)

/-- **Stabilization is `M ↦ M ⊕ 1`.** For any equivalence `e : Fin m ⊕ κ ≃ Fin n` extending the
inclusion of `Fin m`, the stabilization of `M` is the block diagonal matrix `M ⊕ 1` reindexed
along `e`. -/
theorem stabilize_eq_reindex_fromBlocks {κ : Type*} [DecidableEq κ]
    (h : m ≤ n) (e : Fin m ⊕ κ ≃ Fin n) (he : ∀ i, e (Sum.inl i) = i.castLE h)
    (M : Matrix (Fin m) (Fin m) A) :
    stabilize n M = reindex e e (fromBlocks M 0 0 1) := by
  -- the indices coming from `κ` are exactly those at least `m`
  have hκ (c : κ) : ¬ (e (Sum.inr c) : ℕ) < m := fun hc ↦ by
    simpa using e.injective ((he ⟨_, hc⟩).trans (Fin.ext rfl)).symm
  ext a b
  obtain ⟨a | a, rfl⟩ := e.surjective a <;> obtain ⟨b | b, rfl⟩ := e.surjective b
  · rw [reindex_apply, submatrix_apply, e.symm_apply_apply, e.symm_apply_apply, he, he]
    simp
  · simp [stabilize_apply, hκ]
  · simp [stabilize_apply, hκ]
  · simp [stabilize_apply, hκ, one_apply]

end ZeroOne

/-- Stabilization by one size is `Matrix.blockSucc`. -/
theorem stabilize_succ [Semiring A] (M : Matrix (Fin m) (Fin m) A) :
    stabilize (m + 1) M = blockSucc M := by
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [stabilize_apply, one_apply, Fin.ext_iff] <;> omega

end Matrix

namespace TauCeti

variable (A : Type*) [Ring A] {m n k : ℕ}

/-! ## Stabilization of invertible matrices -/

/-- The **stabilization homomorphism** `GL (Fin m) A →* GL (Fin n) A` for `m ≤ n`, placing an
invertible matrix in the upper left block and completing it by the identity matrix. -/
def stabilizeGL (h : m ≤ n) : GL (Fin m) A →* GL (Fin n) A :=
  ((finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).reindexGL A).toMonoidHom.comp
    (fromBlocksGL.comp (MonoidHom.inl (GL (Fin m) A) (GL (Fin (n - m)) A)))

variable {A}

/-- The matrix underlying a stabilized invertible matrix is the stabilized matrix. -/
@[simp]
theorem coe_stabilizeGL (h : m ≤ n) (u : GL (Fin m) A) :
    (stabilizeGL A h u : Matrix (Fin n) (Fin n) A) =
      stabilize n (u : Matrix (Fin m) (Fin m) A) := by
  rw [stabilize_eq_reindex_fromBlocks h (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h)))
    fun i ↦ Fin.ext rfl]
  simp [stabilizeGL, reindex_apply]

/-- **Stabilization is `u ↦ u ⊕ 1`**, reindexed along any equivalence `Fin m ⊕ κ ≃ Fin n`
extending the inclusion of `Fin m`. -/
theorem stabilizeGL_eq_reindexGL_fromBlocksGL {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : m ≤ n) (e : Fin m ⊕ κ ≃ Fin n) (he : ∀ i, e (Sum.inl i) = i.castLE h)
    (u : GL (Fin m) A) : stabilizeGL A h u = e.reindexGL A (fromBlocksGL (u, 1)) :=
  Units.ext (by simp [stabilize_eq_reindex_fromBlocks h e he, reindex_apply])

/-- Stabilization to the same size is the identity. -/
@[simp]
theorem stabilizeGL_self (u : GL (Fin m) A) : stabilizeGL A le_rfl u = u :=
  Units.ext (by simp)

/-- Stabilizing twice is stabilizing once. -/
@[simp]
theorem stabilizeGL_stabilizeGL (hmn : m ≤ n) (hnk : n ≤ k) (u : GL (Fin m) A) :
    stabilizeGL A hnk (stabilizeGL A hmn u) = stabilizeGL A (hmn.trans hnk) u :=
  Units.ext (by simp [stabilize_stabilize hmn])

/-- Stabilization is injective. -/
theorem stabilizeGL_injective (h : m ≤ n) : Function.Injective (stabilizeGL A h) :=
  fun u v huv ↦ Units.ext (stabilize_injective h (by simpa using congrArg Units.val huv))

/-- Stabilization preserves elementary matrices. -/
theorem stabilizeGL_mem_elementarySubgroup (h : m ≤ n) {e : GL (Fin m) A}
    (he : e ∈ elementarySubgroup (Fin m) A) :
    stabilizeGL A h e ∈ elementarySubgroup (Fin n) A :=
  Equiv.reindexGL_mem_elementarySubgroup _
    (map_elementarySubgroup_le_elementarySubgroup ⟨e, he, rfl⟩)

instance : DirectedSystem (fun n : ℕ ↦ GL (Fin n) A) (fun _ _ h ↦ stabilizeGL A h) where
  map_self _ u := stabilizeGL_self u
  map_map _ _ _ hij hjk u := stabilizeGL_stabilizeGL hij hjk u

/-! ## The stable general linear group -/

variable (A) in
/-- The **stable general linear group** `GL_∞(A)`: the direct limit of the groups `GL (Fin n) A`
along the stabilization maps `u ↦ u ⊕ 1`. -/
def StableGL : Type _ :=
  DirectLimit (fun n : ℕ ↦ GL (Fin n) A) (fun _ _ h ↦ stabilizeGL A h)

noncomputable instance : Group (StableGL A) :=
  inferInstanceAs (Group (DirectLimit (fun n : ℕ ↦ GL (Fin n) A) (fun _ _ h ↦ stabilizeGL A h)))

namespace StableGL

variable (A) in
/-- The canonical homomorphism `GL (Fin n) A →* GL_∞(A)`. -/
def of (n : ℕ) : GL (Fin n) A →* StableGL A where
  toFun u := ⟦⟨n, u⟩⟧
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ stabilizeGL A h) n).symm
  map_mul' u v := (DirectLimit.mul_def (f := fun _ _ h ↦ stabilizeGL A h) n u v).symm

/-- The canonical homomorphism sends an invertible matrix to its class in the direct limit. -/
private theorem of_apply (n : ℕ) (u : GL (Fin n) A) :
    of A n u = (⟦⟨n, u⟩⟧ : DirectLimit (fun n : ℕ ↦ GL (Fin n) A) (fun _ _ h ↦ stabilizeGL A h)) :=
  (rfl)

/-- The canonical homomorphisms are compatible with stabilization. -/
@[simp]
theorem of_stabilizeGL (h : m ≤ n) (u : GL (Fin m) A) : of A n (stabilizeGL A h u) = of A m u := by
  rw [of_apply, of_apply]
  exact DirectLimit.mk_apply (F := fun n : ℕ ↦ GL (Fin n) A) (f := fun _ _ h ↦ stabilizeGL A h)
    m n u h

/-- The canonical homomorphisms are compatible with stabilization. -/
@[simp]
theorem of_comp_stabilizeGL (h : m ≤ n) : (of A n).comp (stabilizeGL A h) = of A m :=
  MonoidHom.ext (of_stabilizeGL h)

/-- Every element of `GL_∞(A)` comes from an invertible matrix of some finite size. -/
theorem exists_of (x : StableGL A) : ∃ n u, of A n u = x := by
  obtain ⟨n, u, rfl⟩ := DirectLimit.exists_eq_mk (fun _ _ h ↦ stabilizeGL A h) x
  exact ⟨n, u, of_apply n u⟩

/-- Any two elements of `GL_∞(A)` come from invertible matrices of a common finite size. -/
theorem exists_of₂ (x y : StableGL A) : ∃ n u v, of A n u = x ∧ of A n v = y := by
  obtain ⟨n, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (fun _ _ h ↦ stabilizeGL A h) x y
  exact ⟨n, u, v, of_apply n u, of_apply n v⟩

/-- Each `GL (Fin n) A` embeds in `GL_∞(A)`. -/
theorem of_injective (n : ℕ) : Function.Injective (of A n) := by
  refine (injective_iff_map_eq_one _).2 fun u hu ↦ ?_
  rw [of_apply] at hu
  obtain ⟨k, h, hk⟩ := (DirectLimit.exists_eq_one _).1 hu
  exact stabilizeGL_injective h (hk.trans (map_one _).symm)

/-- Two homomorphisms out of `GL_∞(A)` agreeing on every `GL (Fin n) A` are equal. -/
theorem hom_ext {G : Type*} [Group G] {f g : StableGL A →* G}
    (h : ∀ n, f.comp (of A n) = g.comp (of A n)) : f = g := by
  ext x
  obtain ⟨n, u, rfl⟩ := exists_of x
  exact DFunLike.congr_fun (h n) u

variable {G : Type*} [Group G] (φ : ∀ n, GL (Fin n) A →* G)
  (hφ : ∀ m n (h : m ≤ n) u, φ n (stabilizeGL A h u) = φ m u)

/-- **The universal property of `GL_∞(A)`.** Homomorphisms out of the groups `GL (Fin n) A`
compatible with stabilization induce a homomorphism out of `GL_∞(A)`. -/
noncomputable def lift : StableGL A →* G where
  toFun := DirectLimit.lift _ (fun n u ↦ φ n u) fun m n h u ↦ (hφ m n h u).symm
  map_one' := by
    rw [show (1 : StableGL A) = of A 0 1 from (map_one _).symm]
    exact map_one (φ 0)
  map_mul' x y := by
    obtain ⟨n, u, v, rfl, rfl⟩ := exists_of₂ x y
    rw [← map_mul]
    exact map_mul (φ n) u v

/-- The homomorphism induced on `GL_∞(A)` restricts to the given ones. -/
@[simp]
theorem lift_of (n : ℕ) (u : GL (Fin n) A) : lift φ hφ (of A n u) = φ n u :=
  (rfl)

/-- The homomorphism induced on `GL_∞(A)` restricts to the given ones. -/
@[simp]
theorem lift_comp_of (n : ℕ) : (lift φ hφ).comp (of A n) = φ n :=
  MonoidHom.ext (lift_of φ hφ n)

end StableGL

/-! ## The stable elementary subgroup -/

variable (A) in
/-- The **stable elementary subgroup** `E_∞(A)` of `GL_∞(A)`: the subgroup generated by the images
of the elementary subgroups of the `GL (Fin n) A`. -/
noncomputable def stableElementarySubgroup : Subgroup (StableGL A) :=
  ⨆ n, (elementarySubgroup (Fin n) A).map (StableGL.of A n)

/-- The images of the elementary subgroups increase with the size. -/
theorem map_of_elementarySubgroup_mono (h : m ≤ n) :
    (elementarySubgroup (Fin m) A).map (StableGL.of A m) ≤
      (elementarySubgroup (Fin n) A).map (StableGL.of A n) := by
  rintro _ ⟨e, he, rfl⟩
  exact ⟨_, stabilizeGL_mem_elementarySubgroup h he, StableGL.of_stabilizeGL h e⟩

/-- **The elements of `E_∞(A)`** are the images of elementary matrices of some finite size. -/
theorem mem_stableElementarySubgroup_iff {x : StableGL A} :
    x ∈ stableElementarySubgroup A ↔
      ∃ n, ∃ e ∈ elementarySubgroup (Fin n) A, StableGL.of A n e = x := by
  rw [stableElementarySubgroup, Subgroup.mem_iSup_of_directed
    (Monotone.directed_le fun _ _ ↦ map_of_elementarySubgroup_mono)]
  simp [Subgroup.mem_map]

/-- The image of an elementary matrix lies in `E_∞(A)`. -/
theorem of_mem_stableElementarySubgroup {n : ℕ} {e : GL (Fin n) A}
    (he : e ∈ elementarySubgroup (Fin n) A) :
    StableGL.of A n e ∈ stableElementarySubgroup A :=
  mem_stableElementarySubgroup_iff.2 ⟨n, e, he, rfl⟩

variable (A) in
/-- **The stable elementary subgroup is the commutator subgroup**, `E_∞(A) = ⁅GL_∞(A), GL_∞(A)⁆`.
An elementary matrix is a commutator once stabilized to size at least three, and by Whitehead's
lemma a commutator of size `n` becomes elementary once stabilized to size `2n`. -/
theorem stableElementarySubgroup_eq_commutator :
    stableElementarySubgroup A = commutator (StableGL A) := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (Subgroup.commutator_le.2 fun x _ y _ ↦ ?_)
  · rintro _ ⟨e, he, rfl⟩
    -- stabilize to size `n + 3`, where elementary matrices are commutators
    have hcomm : stabilizeGL A (Nat.le_add_right n 3) e ∈ commutator (GL (Fin (n + 3)) A) :=
      elementarySubgroup_le_commutator (by simp)
        (stabilizeGL_mem_elementarySubgroup _ he)
    have hle : (commutator (GL (Fin (n + 3)) A)).map (StableGL.of A (n + 3)) ≤
        commutator (StableGL A) := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    rw [← StableGL.of_stabilizeGL (Nat.le_add_right n 3)]
    exact hle ⟨_, hcomm, rfl⟩
  · obtain ⟨n, u, v, rfl, rfl⟩ := StableGL.exists_of₂ x y
    -- stabilize to size `n + n`, where Whitehead's lemma makes the commutator elementary
    rw [← map_commutatorElement, ← StableGL.of_stabilizeGL (Nat.le_add_right n n),
      stabilizeGL_eq_reindexGL_fromBlocksGL _ finSumFinEquiv fun i ↦ Fin.ext rfl]
    exact of_mem_stableElementarySubgroup (Equiv.reindexGL_mem_elementarySubgroup _
      (fromBlocksGL_commutatorElement_mem_elementarySubgroup u v))

instance : (stableElementarySubgroup A).Normal := by
  rw [stableElementarySubgroup_eq_commutator]
  infer_instance

end TauCeti
