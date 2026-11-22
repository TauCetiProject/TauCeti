/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import TauCeti.Algebra.Colimit.DirectLimit
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# The stable general linear group and algebraic `K₁`

For a possibly noncommutative ring `A` and `m ≤ n`, stabilization places an invertible
`m × m` matrix `u` in the upper left corner of an `n × n` matrix and fills the rest with the
identity, `u ↦ u ⊕ 1`. These homomorphisms form a directed system of groups indexed by `ℕ`, and
the **stable general linear group** `GL_∞(A)` is its direct limit. The **stable elementary
subgroup** `E_∞(A)` is the union of the images of the elementary subgroups `E n A`.

The finite-size relations of `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary`
become exact statements in the limit: `E_∞(A)` is a normal subgroup of `GL_∞(A)`, and it is the
commutator subgroup of `GL_∞(A)`. Hence algebraic `K₁(A) = GL_∞(A) / E_∞(A)` is an abelian group,
the abelianization of `GL_∞(A)`. Homomorphisms on invertible matrices which are compatible with
stabilization and take values in an abelian group, such as Connes' odd pairing with cyclic
cohomology, factor through it. A ring homomorphism, applied to the entries of invertible matrices,
induces a homomorphism of algebraic `K₁`, functorially.

At a finite size with two distinct indices, the invertible matrices commuting with every
elementary matrix are the scalar matrices with central entry. A stabilization `u ⊕ 1` of
larger size has a diagonal entry `1`, so in the limit only the identity commutes with `E_∞(A)`:
the centralizer of `E_∞(A)`, and with it the center of `GL_∞(A)`, is trivial.

## Main definitions

* `TauCeti.stabilizeGL`: the stabilization homomorphism `GL (Fin m) A →* GL (Fin n) A`,
  `u ↦ u ⊕ 1`, for `m ≤ n`.
* `TauCeti.StableGeneralLinearGroup`: the direct limit `GL_∞(A)` of the groups `GL (Fin n) A`.
* `TauCeti.StableGeneralLinearGroup.of`: the canonical homomorphism `GL (Fin n) A →* GL_∞(A)`.
* `TauCeti.StableGeneralLinearGroup.lift`: the universal property of `GL_∞(A)`, for families of
  homomorphisms compatible with stabilization.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup`: the stable elementary subgroup
  `E_∞(A)`.
* `TauCeti.StableGeneralLinearGroup.map`: the homomorphism `GL_∞(A) →* GL_∞(B)` induced by a ring
  homomorphism.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroupMap`: the induced homomorphism
  `E_∞(A) →* E_∞(B)` on stable elementary subgroups.
* `TauCeti.stableTransvection`: the elementary matrix `1 + a E_{ij}` in `GL_∞(A)`.
* `TauCeti.AlgebraicK1`: algebraic `K₁(A)`, the abelianization of `GL_∞(A)`.
* `TauCeti.AlgebraicK1.mk`: the class in `K₁(A)` of an invertible matrix.
* `TauCeti.AlgebraicK1.lift`: the universal property of `K₁(A)`, for families of homomorphisms
  to a commutative group compatible with stabilization.
* `TauCeti.AlgebraicK1.ofUnits`: the homomorphism `Aˣ →* K₁(A)`, `u ↦ [(u)]`.
* `TauCeti.AlgebraicK1.quotientElementarySubgroupEquiv`: `GL_∞(A) / E_∞(A) ≃* K₁(A)`.
* `TauCeti.AlgebraicK1.map`: the homomorphism `K₁(A) →* K₁(B)` induced by a ring homomorphism.

## Main results

* `TauCeti.stabilizeGL_apply`, `TauCeti.coe_stabilizeGL_apply`: block and entry formulas for a
  stabilized matrix.
* `TauCeti.StableGeneralLinearGroup.mem_elementarySubgroup_iff`: an element of `GL_∞(A)` is
  stably elementary exactly when it is represented by an elementary matrix of some size.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup_normal`: `E_∞(A)` is normal.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup_eq_commutator`: `E_∞(A)` is the
  commutator subgroup of `GL_∞(A)`.
* `TauCeti.StableGeneralLinearGroup.centralizer_elementarySubgroup`,
  `TauCeti.StableGeneralLinearGroup.center_eq_bot`: the centralizer of `E_∞(A)` in `GL_∞(A)`,
  and hence the center of `GL_∞(A)`, is trivial.
* `TauCeti.AlgebraicK1.mk_eq_one_iff`, `TauCeti.AlgebraicK1.ker_mk`,
  `TauCeti.AlgebraicK1.ker_mk_eq_iSup`: kernel of `AlgebraicK1.mk` at finite size.
* `TauCeti.AlgebraicK1.map_id`, `TauCeti.AlgebraicK1.map_comp`, `TauCeti.AlgebraicK1.map_map`:
  functoriality of algebraic `K₁`.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroupMap_surjective`: surjective ring maps
  induce surjective homomorphisms of stable elementary subgroups.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup_isPerfect`: `E_∞(A)` is a perfect group.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  §3, Lemma 3.1 (Whitehead) and the definition of `K₁` following it.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.1, Definition
  2.1.1 and Proposition 2.1.4.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

variable (A : Type*) [Ring A]

/-! ## Stabilization -/

/-- The **stabilization homomorphism** `u ↦ u ⊕ 1` from `GL (Fin m) A` to `GL (Fin n) A`, for
`m ≤ n`: the image of `u` agrees with `u` on the first `m` rows and columns and with the
identity matrix elsewhere. -/
def stabilizeGL {m n : ℕ} (h : m ≤ n) : GL (Fin m) A →* GL (Fin n) A :=
  ((finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).reindexGL A).toMonoidHom.comp
    (fromBlocksGL.comp (MonoidHom.inl (GL (Fin m) A) (GL (Fin (n - m)) A)))

variable {A}

/-- Stabilizing `u : GL (Fin m) A` to `GL (Fin n) A` for `h : m ≤ n` is the block-diagonal matrix
`u ⊕ 1`, reindexed along `Fin m ⊕ Fin (n - m) ≃ Fin n`. -/
theorem stabilizeGL_apply {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    stabilizeGL A h u =
      (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))).reindexGL A
        (fromBlocksGL (u, (1 : GL (Fin (n - m)) A))) :=
  (rfl)

/-- The entries of a stabilized matrix: those of `u` in the first `m` rows and columns, and
those of the identity matrix elsewhere. -/
theorem coe_stabilizeGL_apply {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) (i j : Fin n) :
    (stabilizeGL A h u : Matrix (Fin n) (Fin n) A) i j =
      if hij : (i : ℕ) < m ∧ (j : ℕ) < m then u ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin n) (Fin n) A) i j := by
  set e := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [stabilizeGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MonoidHom.inl_apply, Equiv.coe_reindexGL, coe_fromBlocksGL, submatrix_apply,
    Matrix.one_apply, e.apply_eq_iff_eq]
  rcases i with i | i <;> rcases j with j | j <;> simp [e, Matrix.one_apply]

/-- Stabilization to the same size is the identity. -/
@[simp]
theorem stabilizeGL_refl (n : ℕ) : stabilizeGL A (le_refl n) = MonoidHom.id (GL (Fin n) A) := by
  ext u i j
  simp [coe_stabilizeGL_apply]

/-- Stabilizations compose. -/
@[simp]
theorem stabilizeGL_stabilizeGL {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (u : GL (Fin k) A) :
    stabilizeGL A hmn (stabilizeGL A hkm u) = stabilizeGL A (hkm.trans hmn) u := by
  ext i j
  simp only [coe_stabilizeGL_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- Stabilization is injective: the stabilized matrix contains `u` as its upper left block. -/
theorem stabilizeGL_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (stabilizeGL A h) := by
  intro u v huv
  ext i j
  have := congr($(congrArg Units.val huv) (Fin.castLE h i) (Fin.castLE h j))
  simpa [coe_stabilizeGL_apply] using this

/-- Stabilizing `u` to size `m + k` is the block diagonal matrix `u ⊕ 1`, reindexed along
`Fin m ⊕ Fin k ≃ Fin (m + k)`. -/
theorem stabilizeGL_eq_reindexGL_fromBlocksGL (m k : ℕ) (u : GL (Fin m) A) :
    stabilizeGL A (Nat.le_add_right m k) u = finSumFinEquiv.reindexGL A (fromBlocksGL (u, 1)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [coe_stabilizeGL_apply, Matrix.one_apply, Fin.ext_iff] <;> omega

/-- Stabilization sends an elementary matrix to the elementary matrix with the same parameter at
the same pair of indices. -/
theorem stabilizeGL_transvectionUnit {m n : ℕ} (h : m ≤ n) {i j : Fin m} (hij : i ≠ j) (a : A) :
    stabilizeGL A h (transvectionUnit hij a) =
      transvectionUnit ((Fin.castLE_injective h).ne hij) a := by
  ext p q
  simp only [coe_stabilizeGL_apply, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
    Matrix.one_apply, single_apply, Fin.ext_iff, Fin.val_castLE]
  split_ifs <;> first | rfl | omega | simp_all

/-- Stabilization `u ↦ u ⊕ 1` does not change the determinant of an invertible matrix over a
commutative ring. -/
@[simp]
theorem det_stabilizeGL {R : Type*} [CommRing R] {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) R) :
    GeneralLinearGroup.det (stabilizeGL R h u) = GeneralLinearGroup.det u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL]
  ext
  simp [GeneralLinearGroup.val_det_apply, det_fromBlocks_zero₂₁]

/-- Stabilization maps the elementary subgroup into the elementary subgroup. -/
theorem map_stabilizeGL_elementarySubgroup_le {m n : ℕ} (h : m ≤ n) :
    (elementarySubgroup (Fin m) A).map (stabilizeGL A h) ≤ elementarySubgroup (Fin n) A := by
  refine Subgroup.map_le_iff_le_comap.2 (elementarySubgroup_le_iff.2 fun i j hij a ↦ ?_)
  rw [Subgroup.mem_comap, stabilizeGL_transvectionUnit]
  exact transvectionUnit_mem_elementarySubgroup _ _

/-- The stabilizations form a directed system of groups. -/
instance : DirectedSystem (fun n : ℕ ↦ GL (Fin n) A) fun _ _ h ↦ stabilizeGL A h where
  map_self u := by simp
  map_map _ _ _ hij hjk u := stabilizeGL_stabilizeGL hij hjk u

variable (A) in
/-- The **stable general linear group** `GL_∞(A)`: the direct limit of the groups `GL (Fin n) A`
along the stabilizations `u ↦ u ⊕ 1`. -/
abbrev StableGeneralLinearGroup : Type _ :=
  DirectLimit (fun n : ℕ ↦ GL (Fin n) A) fun _ _ h ↦ stabilizeGL A h

namespace StableGeneralLinearGroup

variable (A) in
/-- The canonical homomorphism from `GL (Fin n) A` to the stable general linear group. -/
def of (n : ℕ) : GL (Fin n) A →* StableGeneralLinearGroup A :=
  DirectLimit.Monoid.of _ (fun _ _ h ↦ stabilizeGL A h) n

/-- The canonical homomorphism sends `u` to its class in the direct limit. -/
private theorem of_apply (n : ℕ) (u : GL (Fin n) A) : of A n u = ⟦⟨n, u⟩⟧ :=
  DirectLimit.Monoid.of_apply (G := fun n : ℕ ↦ GL (Fin n) A) (f := fun _ _ h ↦ stabilizeGL A h) n u

/-- The canonical homomorphisms are compatible with stabilization. -/
@[simp]
theorem of_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    of A n (stabilizeGL A h u) = of A m u :=
  DirectLimit.Monoid.of_f (G := fun n : ℕ ↦ GL (Fin n) A) (f := fun _ _ h ↦ stabilizeGL A h) h u

/-- The canonical homomorphisms are compatible with stabilization. -/
theorem of_comp_stabilizeGL {m n : ℕ} (h : m ≤ n) : (of A n).comp (stabilizeGL A h) = of A m :=
  MonoidHom.ext (of_stabilizeGL h)

/-- The canonical homomorphisms are injective. -/
theorem of_injective (n : ℕ) : Function.Injective (of A n) := by
  intro u v huv
  rw [of_apply, of_apply] at huv
  exact DirectLimit.mk_injective _ (fun _ _ h ↦ stabilizeGL_injective h) n huv

/-- Every element of the stable general linear group comes from an invertible matrix of some
size. -/
theorem exists_of (x : StableGeneralLinearGroup A) : ∃ n u, of A n u = x := by
  obtain ⟨n, u, rfl⟩ := DirectLimit.exists_eq_mk (fun _ _ h ↦ stabilizeGL A h) x
  exact ⟨n, u, of_apply n u⟩

/-- Any two elements of the stable general linear group come from invertible matrices of a
common size. -/
theorem exists_of₂ (x y : StableGeneralLinearGroup A) :
    ∃ n u v, of A n u = x ∧ of A n v = y := by
  obtain ⟨n, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (fun _ _ h ↦ stabilizeGL A h) x y
  exact ⟨n, u, v, of_apply n u, of_apply n v⟩

/-- Homomorphisms out of the stable general linear group agree when they agree on each
`GL (Fin n) A`. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {f g : StableGeneralLinearGroup A →* G}
    (h : ∀ n, f.comp (of A n) = g.comp (of A n)) : f = g :=
  DirectLimit.Monoid.hom_ext h

/-- The **universal property of `GL_∞(A)`**: a family of homomorphisms out of the groups
`GL (Fin n) A` which is compatible with stabilization induces a homomorphism out of the stable
general linear group. -/
def lift {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) :
    StableGeneralLinearGroup A →* G :=
  DirectLimit.Monoid.lift _ (fun _ _ h ↦ stabilizeGL A h) f hf

/-- The homomorphism induced by a compatible family restricts to the family. -/
@[simp]
theorem lift_of {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) (n : ℕ) (u : GL (Fin n) A) :
    lift f hf (of A n u) = f n u :=
  DirectLimit.Monoid.lift_of f hf n u

/-! ## The stable elementary subgroup -/

variable (A) in
/-- The **stable elementary subgroup** `E_∞(A)` of `GL_∞(A)`: the union of the images of the
elementary subgroups of `GL (Fin n) A`. -/
def elementarySubgroup : Subgroup (StableGeneralLinearGroup A) :=
  ⨆ n, (TauCeti.elementarySubgroup (Fin n) A).map (of A n)

/-- The images of the elementary subgroups increase with the size. -/
private theorem monotone_map_elementarySubgroup :
    Monotone fun n ↦ (TauCeti.elementarySubgroup (Fin n) A).map (of A n) := by
  intro m n h
  dsimp only
  rw [← of_comp_stabilizeGL h, ← Subgroup.map_map]
  exact Subgroup.map_mono (map_stabilizeGL_elementarySubgroup_le h)

/-- An element of `GL_∞(A)` is stably elementary exactly when it comes from an elementary matrix
of some size. -/
theorem mem_elementarySubgroup_iff {x : StableGeneralLinearGroup A} :
    x ∈ elementarySubgroup A ↔
      ∃ n, ∃ u ∈ TauCeti.elementarySubgroup (Fin n) A, of A n u = x := by
  rw [elementarySubgroup, Subgroup.mem_iSup_of_directed monotone_map_elementarySubgroup.directed_le]
  simp only [Subgroup.mem_map]

/-- Elementary matrices are stably elementary. -/
theorem of_mem_elementarySubgroup {n : ℕ} {u : GL (Fin n) A}
    (hu : u ∈ TauCeti.elementarySubgroup (Fin n) A) : of A n u ∈ elementarySubgroup A :=
  mem_elementarySubgroup_iff.2 ⟨n, u, hu, rfl⟩

/-- An invertible matrix is stably elementary exactly when some stabilization of it is
elementary. -/
theorem of_mem_elementarySubgroup_iff {n : ℕ} {u : GL (Fin n) A} :
    of A n u ∈ elementarySubgroup A ↔
      ∃ k, ∃ h : n ≤ k, stabilizeGL A h u ∈ TauCeti.elementarySubgroup (Fin k) A := by
  refine ⟨fun hu ↦ ?_, fun ⟨k, h, hu⟩ ↦ of_stabilizeGL h u ▸ of_mem_elementarySubgroup hu⟩
  obtain ⟨m, v, hv, hvu⟩ := mem_elementarySubgroup_iff.1 hu
  obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
  rw [← of_stabilizeGL hmk, ← of_stabilizeGL hnk] at hvu
  exact ⟨k, hnk, of_injective k hvu ▸ map_stabilizeGL_elementarySubgroup_le hmk ⟨v, hv, rfl⟩⟩

/-- An invertible matrix `u` whose block diagonal stabilization `u ⊕ 1` of size `n + n` is
elementary is stably elementary. -/
private theorem of_mem_elementarySubgroup_of_fromBlocksGL {n : ℕ} {u : GL (Fin n) A}
    (hu : fromBlocksGL (u, 1) ∈ TauCeti.elementarySubgroup (Fin n ⊕ Fin n) A) :
    of A n u ∈ elementarySubgroup A := by
  rw [← of_stabilizeGL (Nat.le_add_right n n), stabilizeGL_eq_reindexGL_fromBlocksGL]
  exact of_mem_elementarySubgroup
    (finSumFinEquiv.map_reindexGL_elementarySubgroup (A := A) ▸ ⟨_, hu, rfl⟩)

/-- **The stable elementary subgroup is normal.** This is Whitehead's lemma in the limit: a
conjugate `g e g⁻¹` becomes elementary after stabilization. -/
instance elementarySubgroup_normal : (elementarySubgroup A).Normal where
  conj_mem x hx g := by
    obtain ⟨m, e, he, rfl⟩ := mem_elementarySubgroup_iff.1 hx
    obtain ⟨n, g, rfl⟩ := exists_of g
    -- Move `g` and `e` to a common size `k`.
    obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    rw [← of_stabilizeGL hmk e, ← of_stabilizeGL hnk g, ← map_inv, ← map_mul, ← map_mul]
    exact of_mem_elementarySubgroup_of_fromBlocksGL (fromBlocksGL_conj_mem_elementarySubgroup _
      (map_stabilizeGL_elementarySubgroup_le hmk ⟨e, he, rfl⟩))

/-- The commutator subgroup of `GL_∞(A)` is contained in the stable elementary subgroup. -/
theorem commutator_le_elementarySubgroup :
    commutator (StableGeneralLinearGroup A) ≤ elementarySubgroup A := by
  refine Subgroup.commutator_le.2 fun x _ y _ ↦ ?_
  obtain ⟨n, u, v, rfl, rfl⟩ := exists_of₂ x y
  rw [← map_commutatorElement]
  exact of_mem_elementarySubgroup_of_fromBlocksGL
    (fromBlocksGL_commutatorElement_mem_elementarySubgroup u v)

/-- **The stable elementary subgroup `E_∞(A)` is perfect**: it equals its own commutator
subgroup. -/
instance elementarySubgroup_isPerfect : Group.IsPerfect (elementarySubgroup A) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) fun x hx ↦ ?_
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hx
  -- Stabilize to size `n + 3`, where `E (n + 3) A` is perfect.
  rw [← of_stabilizeGL (Nat.le_add_right n 3)]
  have h : stabilizeGL A (Nat.le_add_right n 3) u ∈
      ⁅TauCeti.elementarySubgroup (Fin (n + 3)) A, TauCeti.elementarySubgroup (Fin (n + 3)) A⁆ := by
    rw [commutator_elementarySubgroup_self (by simp)]
    exact map_stabilizeGL_elementarySubgroup_le (A := A) (Nat.le_add_right n 3) ⟨u, hu, rfl⟩
  have hle : (TauCeti.elementarySubgroup (Fin (n + 3)) A).map (of A (n + 3)) ≤
      elementarySubgroup A := by
    rintro _ ⟨v, hv, rfl⟩
    exact of_mem_elementarySubgroup hv
  exact Subgroup.map_le_iff_le_comap.1 ((Subgroup.map_commutator _ _ _).trans_le
    (Subgroup.commutator_mono hle hle)) h

/-- **The stable elementary subgroup is the commutator subgroup** of `GL_∞(A)`: every commutator
is stably elementary, and every elementary matrix of size at least three is a commutator of
elementary matrices. -/
theorem elementarySubgroup_eq_commutator :
    elementarySubgroup A = commutator (StableGeneralLinearGroup A) :=
  le_antisymm
    ((Subgroup.commutator_eq_self (H := elementarySubgroup A)).symm.trans_le
      (Subgroup.commutator_mono le_top le_top))
    commutator_le_elementarySubgroup

/-- **The quotient `GL_∞(A) / E_∞(A)` is commutative**, since `E_∞(A)` contains the commutator
subgroup of `GL_∞(A)`. -/
instance instIsMulCommutativeQuotientElementarySubgroup :
    IsMulCommutative (StableGeneralLinearGroup A ⧸ elementarySubgroup A) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr commutator_le_elementarySubgroup

/-- **The centralizer of the stable elementary subgroup is trivial**: only the identity of
`GL_∞(A)` commutes with every stably elementary element. -/
@[simp]
theorem centralizer_elementarySubgroup :
    Subgroup.centralizer (elementarySubgroup A : Set (StableGeneralLinearGroup A)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  -- Pass to `v = u ⊕ 1` of size `n + 2`: it commutes with every elementary matrix of that size,
  -- so it is a central scalar matrix, and its last diagonal entry is `1`.
  rw [← of_stabilizeGL (Nat.le_add_right n 2)] at hx ⊢
  set v := stabilizeGL A (Nat.le_add_right n 2) u
  have hv : v ∈ Subgroup.centralizer
      (TauCeti.elementarySubgroup (Fin (n + 2)) A : Set (GL (Fin (n + 2)) A)) :=
    Subgroup.mem_centralizer_iff.2 fun e he ↦ of_injective (n + 2) <| by
      simpa only [map_mul] using Subgroup.mem_centralizer_iff.1 hx _ (of_mem_elementarySubgroup he)
  obtain ⟨c, -, hc⟩ := TauCeti.mem_centralizer_elementarySubgroup_iff.1 hv
  -- The last diagonal entry of `v = u ⊕ 1` is `1`, so the scalar `c` is `1`.
  have hc1 : c = 1 := by
    simpa [v, coe_stabilizeGL_apply] using congr($hc (Fin.last (n + 1)) (Fin.last (n + 1)))
  have hv1 : v = 1 := Units.ext (by simp [← hc, hc1])
  rw [hv1, map_one]

/-- The center of the stable general linear group `GL_∞(A)` is trivial. -/
@[simp]
theorem center_eq_bot : Subgroup.center (StableGeneralLinearGroup A) = ⊥ :=
  eq_bot_iff.2 <| (Subgroup.center_le_centralizer _).trans centralizer_elementarySubgroup.le

end StableGeneralLinearGroup

/-! ## Stable transvections -/

/-- The elementary matrix `e_{ij}(a) = 1 + a E_{ij}` as an element of `GL_∞(A)`, formed at size
`max i j + 1` and mapped into `TauCeti.StableGeneralLinearGroup A`. -/
def stableTransvection (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : A) :
    StableGeneralLinearGroup A :=
  StableGeneralLinearGroup.of A (max p.val.1 p.val.2 + 1)
    (transvectionUnit (i := (⟨p.val.1, by omega⟩ : Fin (max p.val.1 p.val.2 + 1)))
      (j := ⟨p.val.2, by omega⟩) (fun h ↦ p.property (congrArg Fin.val h)) a)

/-- Forming `e_{ij}(a)` at any size `n` exceeding both `i` and `j` gives the same element of
`GL_∞(A)`. -/
theorem stableTransvection_eq_of (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : A)
    {n : ℕ} (hi : p.val.1 < n) (hj : p.val.2 < n) :
    stableTransvection p a =
      StableGeneralLinearGroup.of A n
        (transvectionUnit (i := ⟨p.val.1, hi⟩) (j := ⟨p.val.2, hj⟩)
          (fun h ↦ p.property (congrArg Fin.val h)) a) := by
  have hle : max p.val.1 p.val.2 + 1 ≤ n := by omega
  rw [stableTransvection, ← StableGeneralLinearGroup.of_stabilizeGL hle,
    stabilizeGL_transvectionUnit]

@[simp]
theorem stableTransvection_zero (p : {p : ℕ × ℕ // p.1 ≠ p.2}) :
    stableTransvection p (0 : A) = 1 := by
  simp [stableTransvection]

@[simp]
theorem stableTransvection_add (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a b : A) :
    stableTransvection p (a + b) = stableTransvection p a * stableTransvection p b := by
  simp [stableTransvection, transvectionUnit_add]

@[simp]
theorem stableTransvection_inv (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : A) :
    (stableTransvection p a)⁻¹ = stableTransvection p (-a) := by
  simp [stableTransvection, ← map_inv]

/-- Distinct ring parameters give distinct stable transvections. -/
theorem stableTransvection_injective (p : {p : ℕ × ℕ // p.1 ≠ p.2}) :
    Function.Injective (stableTransvection (A := A) p) := by
  intro a b hab
  exact transvectionUnit_injective _ (StableGeneralLinearGroup.of_injective _ hab)

/-- Stable transvections at non-chaining index pairs commute in `GL_∞(A)`. -/
theorem commute_stableTransvection {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : A) :
    Commute (stableTransvection ⟨(i, j), hij⟩ a) (stableTransvection ⟨(k, l), hkl⟩ b) := by
  let N := max (max i j) (max k l) + 1
  have hi : i < N := by omega
  have hj : j < N := by omega
  have hk : k < N := by omega
  have hl : l < N := by omega
  rw [stableTransvection_eq_of ⟨(i, j), hij⟩ a hi hj,
    stableTransvection_eq_of ⟨(k, l), hkl⟩ b hk hl]
  exact (commute_transvectionUnit
    (i := (⟨i, hi⟩ : Fin N)) (j := ⟨j, hj⟩) (k := ⟨k, hk⟩) (l := ⟨l, hl⟩)
    (fun h ↦ hij (congrArg Fin.val h)) (fun h ↦ hkl (congrArg Fin.val h))
    (fun h ↦ hjk (congrArg Fin.val h)) (fun h ↦ hli (congrArg Fin.val h)) a b).map
      (StableGeneralLinearGroup.of A N)

/-- **The Chevalley commutator relation** for stable transvections in `GL_∞(A)`. -/
theorem commutatorElement_stableTransvection {i j k : ℕ} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : A) :
    ⁅stableTransvection ⟨(i, j), hij⟩ a, stableTransvection ⟨(j, k), hjk⟩ b⁆ =
      stableTransvection ⟨(i, k), hik⟩ (a * b) := by
  let N := max (max i j) k + 1
  have hi : i < N := by omega
  have hj : j < N := by omega
  have hk : k < N := by omega
  rw [stableTransvection_eq_of ⟨(i, j), hij⟩ a hi hj,
    stableTransvection_eq_of ⟨(j, k), hjk⟩ b hj hk,
    stableTransvection_eq_of ⟨(i, k), hik⟩ (a * b) hi hk,
    ← map_commutatorElement, commutatorElement_transvectionUnit]

/-- Every stable transvection lies in the stable elementary subgroup `E_∞(A)`. -/
theorem stableTransvection_mem_elementarySubgroup (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : A) :
    stableTransvection p a ∈ StableGeneralLinearGroup.elementarySubgroup A :=
  StableGeneralLinearGroup.of_mem_elementarySubgroup (transvectionUnit_mem_elementarySubgroup _ a)

/-! ## Algebraic `K₁` -/

variable (A) in
/-- **Algebraic `K₁`** of a ring `A`: the quotient `GL_∞(A) / E_∞(A)` of the stable general
linear group by the stable elementary subgroup. Since `E_∞(A)` is the commutator subgroup
(`TauCeti.StableGeneralLinearGroup.elementarySubgroup_eq_commutator`), this is the
abelianization of `GL_∞(A)`, and it is defined as such. -/
abbrev AlgebraicK1 : Type _ :=
  Group.Abelianization (StableGeneralLinearGroup A)

namespace AlgebraicK1

variable (A) in
/-- The class in algebraic `K₁` of an invertible matrix. -/
def mk (n : ℕ) : GL (Fin n) A →* AlgebraicK1 A :=
  Group.Abelianization.of.comp (StableGeneralLinearGroup.of A n)

/-- The class of an invertible matrix is unchanged by stabilization. -/
@[simp]
theorem mk_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    mk A n (stabilizeGL A h u) = mk A m u := by
  simp [mk]

/-- Every class in algebraic `K₁` is the class of an invertible matrix of some size. -/
theorem exists_mk (x : AlgebraicK1 A) : ∃ n u, mk A n u = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨n, u, rfl⟩ := StableGeneralLinearGroup.exists_of y
  exact ⟨n, u, rfl⟩

/-- The kernel of the projection `GL_∞(A) → K₁(A)` is the stable elementary subgroup. -/
theorem ker_of :
    (Group.Abelianization.of : StableGeneralLinearGroup A →* AlgebraicK1 A).ker =
      StableGeneralLinearGroup.elementarySubgroup A := by
  rw [Group.Abelianization.ker_of, StableGeneralLinearGroup.elementarySubgroup_eq_commutator]

/-- The class of an invertible matrix in algebraic `K₁` is trivial exactly when some
stabilization of the matrix is elementary. -/
theorem mk_eq_one_iff {n : ℕ} {u : GL (Fin n) A} :
    mk A n u = 1 ↔
      ∃ k, ∃ h : n ≤ k, stabilizeGL A h u ∈ TauCeti.elementarySubgroup (Fin k) A := by
  rw [← StableGeneralLinearGroup.of_mem_elementarySubgroup_iff, ← ker_of, MonoidHom.mem_ker,
    mk, MonoidHom.comp_apply]

/-- Two invertible matrices of the same size have the same class in algebraic `K₁` exactly when
they agree modulo elementary matrices after some stabilization. -/
theorem mk_eq_mk_iff {n : ℕ} {u v : GL (Fin n) A} :
    mk A n u = mk A n v ↔
      ∃ k, ∃ h : n ≤ k, stabilizeGL A h (u⁻¹ * v) ∈ TauCeti.elementarySubgroup (Fin k) A := by
  rw [← mk_eq_one_iff, map_mul, map_inv, inv_mul_eq_one]

/-- Elementary matrices of size `n` lie in the kernel of `AlgebraicK1.mk A n`. -/
theorem elementarySubgroup_le_ker_mk (n : ℕ) :
    TauCeti.elementarySubgroup (Fin n) A ≤ (mk A n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, mk_eq_one_iff]
  exact ⟨n, le_rfl, by simpa using hu⟩

/-- The kernel of `AlgebraicK1.mk A n` is the preimage of the stable elementary subgroup `E_∞(A)`
along `StableGeneralLinearGroup.of A n`. -/
theorem ker_mk (n : ℕ) :
    (mk A n).ker =
      (StableGeneralLinearGroup.elementarySubgroup A).comap (StableGeneralLinearGroup.of A n) := by
  ext u
  rw [MonoidHom.mem_ker, mk_eq_one_iff, Subgroup.mem_comap,
    StableGeneralLinearGroup.of_mem_elementarySubgroup_iff]

/-- The kernel of `AlgebraicK1.mk A n` is the directed supremum of the preimages of the
finite-rank elementary subgroups under stabilization. -/
theorem ker_mk_eq_iSup (n : ℕ) :
    (mk A n).ker =
      ⨆ (k : ℕ) (h : n ≤ k), (TauCeti.elementarySubgroup (Fin k) A).comap (stabilizeGL A h) := by
  let f : {k : ℕ // n ≤ k} → Subgroup (GL (Fin n) A) :=
    fun p ↦ (TauCeti.elementarySubgroup (Fin p.val) A).comap (stabilizeGL A p.property)
  have hmono : Monotone f := by
    rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ (h₁₂ : k₁ ≤ k₂) u hu
    rw [Subgroup.mem_comap] at hu ⊢
    rw [← stabilizeGL_stabilizeGL hk₁ h₁₂]
    exact map_stabilizeGL_elementarySubgroup_le h₁₂ ⟨_, hu, rfl⟩
  have : Nonempty {k : ℕ // n ≤ k} := ⟨⟨n, le_rfl⟩⟩
  ext u
  have hsup : (⨆ (k : ℕ) (h : n ≤ k),
      (TauCeti.elementarySubgroup (Fin k) A).comap (stabilizeGL A h)) =
      ⨆ p : {k : ℕ // n ≤ k}, f p := iSup_subtype'
  rw [MonoidHom.mem_ker, mk_eq_one_iff, hsup, Subgroup.mem_iSup_of_directed hmono.directed_le]
  simp [f]

variable (A) in
/-- Algebraic `K₁` is the quotient of `GL_∞(A)` by the stable elementary subgroup. -/
def quotientElementarySubgroupEquiv :
    StableGeneralLinearGroup A ⧸ StableGeneralLinearGroup.elementarySubgroup A ≃* AlgebraicK1 A :=
  QuotientGroup.quotientMulEquivOfEq StableGeneralLinearGroup.elementarySubgroup_eq_commutator

/-- The identification of `GL_∞(A) / E_∞(A)` with algebraic `K₁` respects the projections. -/
@[simp]
theorem quotientElementarySubgroupEquiv_mk (x : StableGeneralLinearGroup A) :
    quotientElementarySubgroupEquiv A x = Group.Abelianization.of x :=
  (rfl)

/-- Homomorphisms out of algebraic `K₁` agree when they agree on the classes of invertible
matrices of each size. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {f g : AlgebraicK1 A →* G}
    (h : ∀ n, f.comp (mk A n) = g.comp (mk A n)) : f = g :=
  Group.Abelianization.hom_ext _ _ (StableGeneralLinearGroup.hom_ext h)

/-- The **universal property of algebraic `K₁`**: a family of homomorphisms from the groups
`GL (Fin n) A` to a commutative group which is compatible with stabilization induces a
homomorphism out of algebraic `K₁`. -/
def lift {G : Type*} [CommGroup G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) : AlgebraicK1 A →* G :=
  Group.Abelianization.lift (StableGeneralLinearGroup.lift f hf)

/-- The homomorphism induced by a compatible family sends the class of an invertible matrix to
its value under the family. -/
@[simp]
theorem lift_mk {G : Type*} [CommGroup G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) (n : ℕ) (u : GL (Fin n) A) :
    lift f hf (mk A n u) = f n u :=
  (Group.Abelianization.lift_apply_of _ _).trans (StableGeneralLinearGroup.lift_of f hf n u)

variable (A) in
/-- The class in algebraic `K₁` of an invertible `1 × 1` matrix: the homomorphism
`Aˣ →* K₁(A)`, `u ↦ [(u)]`. -/
def ofUnits : Aˣ →* AlgebraicK1 A :=
  (mk A 1).comp (GeneralLinearGroup.scalar (Fin 1))

/-- `ofUnits` sends a unit `u` to the class of the `1 × 1` matrix `(u)`. -/
theorem ofUnits_apply (u : Aˣ) : ofUnits A u = mk A 1 (GeneralLinearGroup.scalar (Fin 1) u) :=
  (rfl)

end AlgebraicK1

/-! ## Functoriality -/

section Map

variable {B C : Type*} [Ring B] [Ring C]

/-- Stabilization commutes with applying a ring homomorphism to the entries of an invertible
matrix. -/
theorem stabilizeGL_map {m n : ℕ} (h : m ≤ n) (f : A →+* B) (u : GL (Fin m) A) :
    stabilizeGL B h (Units.map (f.mapMatrix (m := Fin m)).toMonoidHom u) =
      Units.map (f.mapMatrix (m := Fin n)).toMonoidHom (stabilizeGL A h u) := by
  ext i j
  simp [coe_stabilizeGL_apply, apply_dite f, apply_ite f, Matrix.one_apply]

namespace StableGeneralLinearGroup

/-- The homomorphism of stable general linear groups induced by a ring homomorphism `f : A →+* B`,
applying `f` entrywise to invertible matrices. -/
def map (f : A →+* B) : StableGeneralLinearGroup A →* StableGeneralLinearGroup B :=
  lift (fun n ↦ (of B n).comp (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom))
    fun _ _ h u ↦ by simp only [MonoidHom.comp_apply, ← stabilizeGL_map, of_stabilizeGL]

/-- The induced homomorphism of `GL_∞` intertwines the stage maps `of`. -/
theorem map_comp_of (f : A →+* B) (n : ℕ) :
    (map f).comp (of A n) = (of B n).comp (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom) :=
  MonoidHom.ext fun _ ↦ lift_of ..

/-- The induced homomorphism of `GL_∞` acts entrywise on each finite matrix stage. -/
@[simp]
theorem map_of (f : A →+* B) (n : ℕ) (u : GL (Fin n) A) :
    map f (of A n u) = of B n (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom u) :=
  DFunLike.congr_fun (map_comp_of f n) u

/-- The identity ring homomorphism induces the identity of `GL_∞`. -/
@[simp]
theorem map_id : map (RingHom.id A) = MonoidHom.id (StableGeneralLinearGroup A) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp

/-- The stable general linear group is functorial in ring homomorphisms. -/
theorem map_comp (f : A →+* B) (g : B →+* C) :
    map (g.comp f) = (map g).comp (map f) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp only [MonoidHom.comp_apply, map_of]
  refine congrArg _ (Units.ext ?_)
  simp [Matrix.map_map]

/-- Applying the homomorphisms of `GL_∞` induced by `f` and then `g` is applying the one induced
by `g.comp f`. -/
@[simp]
theorem map_map (f : A →+* B) (g : B →+* C) (x : StableGeneralLinearGroup A) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- Ring homomorphisms map the stable elementary subgroup into the stable elementary subgroup. -/
theorem map_elementarySubgroup_le (f : A →+* B) :
    (elementarySubgroup A).map (map f) ≤ elementarySubgroup B := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hx
  rw [map_of]
  exact of_mem_elementarySubgroup (f.map_elementarySubgroup_le ⟨u, hu, rfl⟩)

/-- The homomorphism on stable elementary subgroups `E_∞(A) →* E_∞(B)` induced by a ring
homomorphism `f : A →+* B`. -/
def elementarySubgroupMap (f : A →+* B) : elementarySubgroup A →* elementarySubgroup B :=
  ((map f).comp (elementarySubgroup A).subtype).codRestrict (elementarySubgroup B)
    fun x ↦ map_elementarySubgroup_le f ⟨x, x.property, rfl⟩

/-- The stable elementary subgroup inclusion intertwines `elementarySubgroupMap` with
`StableGeneralLinearGroup.map`. -/
theorem subtype_comp_elementarySubgroupMap (f : A →+* B) :
    (elementarySubgroup B).subtype.comp (elementarySubgroupMap f) =
      (map f).comp (elementarySubgroup A).subtype :=
  (rfl)

/-- The induced homomorphism on `E_∞` agrees with `StableGeneralLinearGroup.map` on underlying
elements of `GL_∞`. -/
@[simp]
theorem coe_elementarySubgroupMap (f : A →+* B) (x : elementarySubgroup A) :
    (elementarySubgroupMap f x : StableGeneralLinearGroup B) = map f x :=
  DFunLike.congr_fun (subtype_comp_elementarySubgroupMap f) x

/-- The identity ring homomorphism induces the identity on `E_∞`. -/
@[simp]
theorem elementarySubgroupMap_id :
    elementarySubgroupMap (RingHom.id A) = MonoidHom.id (elementarySubgroup A) := by
  ext x
  simp

/-- The stable elementary subgroup is functorial in ring homomorphisms. -/
theorem elementarySubgroupMap_comp (f : A →+* B) (g : B →+* C) :
    elementarySubgroupMap (g.comp f) =
      (elementarySubgroupMap g).comp (elementarySubgroupMap f) := by
  ext x
  simp

/-- Applying the homomorphisms of `E_∞` induced by `f` and then `g` is applying the one induced
by `g.comp f`. -/
@[simp]
theorem elementarySubgroupMap_map (f : A →+* B) (g : B →+* C) (x : elementarySubgroup A) :
    elementarySubgroupMap g (elementarySubgroupMap f x) = elementarySubgroupMap (g.comp f) x := by
  rw [elementarySubgroupMap_comp, MonoidHom.comp_apply]

/-- A surjective ring homomorphism induces a surjective homomorphism of stable elementary
subgroups. -/
theorem elementarySubgroupMap_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (elementarySubgroupMap f) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hy
  obtain ⟨v, hv, huv⟩ := f.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hf hu
  refine ⟨⟨of A n v, of_mem_elementarySubgroup hv⟩, Subtype.ext ?_⟩
  rw [coe_elementarySubgroupMap, map_of, huv]

/-- Ring homomorphisms send stable transvections to stable transvections. -/
@[simp]
theorem map_stableTransvection (f : A →+* B) (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : A) :
    map f (stableTransvection p a) = stableTransvection p (f a) := by
  simp only [stableTransvection, map_of, RingHom.toMonoidHom_eq_coe,
    RingHom.unitsMap_mapMatrix_transvectionUnit]

end StableGeneralLinearGroup

namespace AlgebraicK1

/-- The homomorphism of algebraic `K₁` induced by a ring homomorphism `f : A →+* B`, applying `f`
to the entries of invertible matrices. -/
def map (f : A →+* B) : AlgebraicK1 A →* AlgebraicK1 B :=
  lift (fun n ↦ (mk B n).comp (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom))
    fun m n h u ↦ by simp only [MonoidHom.comp_apply, ← stabilizeGL_map, mk_stabilizeGL]

/-- The induced homomorphism of algebraic `K₁` sends the class of an invertible matrix to the
class of the matrix obtained by applying the ring homomorphism to its entries. -/
@[simp]
theorem map_mk (f : A →+* B) (n : ℕ) (u : GL (Fin n) A) :
    map f (mk A n u) = mk B n (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom u) :=
  lift_mk ..

/-- The identity ring homomorphism induces the identity of algebraic `K₁`. -/
@[simp]
theorem map_id : AlgebraicK1.map (RingHom.id A) = MonoidHom.id (AlgebraicK1 A) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp

/-- Algebraic `K₁` is functorial. -/
theorem map_comp (f : A →+* B) (g : B →+* C) :
    AlgebraicK1.map (g.comp f) = (AlgebraicK1.map g).comp (AlgebraicK1.map f) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp only [MonoidHom.comp_apply, map_mk]
  refine congrArg _ (Units.ext ?_)
  simp [Matrix.map_map]

/-- Applying the homomorphisms of algebraic `K₁` induced by `f` and then `g` is applying the one
induced by `g.comp f`. -/
@[simp]
theorem map_map (f : A →+* B) (g : B →+* C) (x : AlgebraicK1 A) :
    AlgebraicK1.map g (AlgebraicK1.map f x) = AlgebraicK1.map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- The homomorphism of algebraic `K₁` induced by a ring homomorphism sends the class of a unit
`u` to the class of `f u`. -/
@[simp]
theorem map_ofUnits (f : A →+* B) (u : Aˣ) :
    map f (ofUnits A u) = ofUnits B (Units.map (f : A →* B) u) := by
  rw [ofUnits_apply, ofUnits_apply, map_mk]
  congr 1
  ext
  simp [diagonal_apply, apply_ite f]

end AlgebraicK1

end Map

end TauCeti
