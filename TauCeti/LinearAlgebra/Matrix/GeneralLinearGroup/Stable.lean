/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
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
cohomology, factor through it.

## Main definitions

* `TauCeti.stabilizeGL`: the stabilization homomorphism `GL (Fin m) A →* GL (Fin n) A`,
  `u ↦ u ⊕ 1`, for `m ≤ n`.
* `TauCeti.StableGeneralLinearGroup`: the direct limit `GL_∞(A)` of the groups `GL (Fin n) A`.
* `TauCeti.StableGeneralLinearGroup.of`: the canonical homomorphism `GL (Fin n) A →* GL_∞(A)`.
* `TauCeti.StableGeneralLinearGroup.lift`: the universal property of `GL_∞(A)`, for families of
  homomorphisms compatible with stabilization.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup`: the stable elementary subgroup
  `E_∞(A)`.
* `TauCeti.AlgebraicK1`: algebraic `K₁(A)`, the abelianization of `GL_∞(A)`.
* `TauCeti.AlgebraicK1.mk`: the class in `K₁(A)` of an invertible matrix.
* `TauCeti.AlgebraicK1.lift`: the universal property of `K₁(A)`, for families of homomorphisms
  to a commutative group compatible with stabilization.
* `TauCeti.AlgebraicK1.quotientElementarySubgroupEquiv`: `GL_∞(A) / E_∞(A) ≃* K₁(A)`.

## Main results

* `TauCeti.coe_stabilizeGL_apply`: the entries of a stabilized matrix.
* `TauCeti.StableGeneralLinearGroup.mem_elementarySubgroup_iff`: an element of `GL_∞(A)` is
  stably elementary exactly when it is represented by an elementary matrix of some size.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup_normal`: `E_∞(A)` is normal.
* `TauCeti.StableGeneralLinearGroup.elementarySubgroup_eq_commutator`: `E_∞(A)` is the
  commutator subgroup of `GL_∞(A)`.
* `TauCeti.AlgebraicK1.mk_eq_one_iff`: an invertible matrix has trivial class in `K₁(A)` exactly
  when some stabilization of it is elementary.

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
    one_apply, e.apply_eq_iff_eq]
  rcases i with i | i <;> rcases j with j | j <;> simp [e, one_apply]

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
  simp only [coe_stabilizeGL_apply, one_apply, Fin.ext_iff]
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
    simp [coe_stabilizeGL_apply, one_apply, Fin.ext_iff] <;> omega

/-- Stabilization sends an elementary matrix to the elementary matrix with the same parameter at
the same pair of indices. -/
theorem stabilizeGL_transvectionUnit {m n : ℕ} (h : m ≤ n) {i j : Fin m} (hij : i ≠ j) (a : A) :
    stabilizeGL A h (transvectionUnit hij a) =
      transvectionUnit ((Fin.castLE_injective h).ne hij) a := by
  ext p q
  simp only [coe_stabilizeGL_apply, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
    one_apply, single_apply, Fin.ext_iff, Fin.val_castLE]
  split_ifs <;> first | rfl | omega | simp_all

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
def of (n : ℕ) : GL (Fin n) A →* StableGeneralLinearGroup A where
  toFun u := ⟦⟨n, u⟩⟧
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ stabilizeGL A h) n).symm
  map_mul' u v := (DirectLimit.mul_def (f := fun _ _ h ↦ stabilizeGL A h) n u v).symm

/-- The canonical homomorphism sends `u` to its class in the direct limit. -/
private theorem of_apply (n : ℕ) (u : GL (Fin n) A) : of A n u = ⟦⟨n, u⟩⟧ :=
  rfl

/-- The canonical homomorphisms are compatible with stabilization. -/
@[simp]
theorem of_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    of A n (stabilizeGL A h u) = of A m u := by
  rw [of_apply, of_apply, DirectLimit.mk_apply]

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
    (h : ∀ n, f.comp (of A n) = g.comp (of A n)) : f = g := by
  ext x
  obtain ⟨n, u, rfl⟩ := exists_of x
  exact DFunLike.congr_fun (h n) u

/-- The **universal property of `GL_∞(A)`**: a family of homomorphisms out of the groups
`GL (Fin n) A` which is compatible with stabilization induces a homomorphism out of the stable
general linear group. -/
def lift {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) :
    StableGeneralLinearGroup A →* G where
  toFun := DirectLimit.lift _ (fun n ↦ f n) fun m n h u ↦ (hf m n h u).symm
  map_one' := DirectLimit.lift_one _ _
  map_mul' := DirectLimit.lift_mul _ _

/-- The homomorphism induced by a compatible family restricts to the family. -/
@[simp]
theorem lift_of {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) (n : ℕ) (u : GL (Fin n) A) :
    lift f hf (of A n u) = f n u :=
  (rfl)

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

/-- **The stable elementary subgroup is the commutator subgroup** of `GL_∞(A)`: every commutator
is stably elementary, and every elementary matrix of size at least three is a commutator of
elementary matrices. -/
theorem elementarySubgroup_eq_commutator :
    elementarySubgroup A = commutator (StableGeneralLinearGroup A) := by
  refine le_antisymm ?_ commutator_le_elementarySubgroup
  intro x hx
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hx
  -- Stabilize to size `n + 3`, where elementary matrices are commutators.
  rw [← of_stabilizeGL (Nat.le_add_right n 3)]
  have h := elementarySubgroup_le_commutator (by simp)
    (map_stabilizeGL_elementarySubgroup_le (A := A) (Nat.le_add_right n 3) ⟨u, hu, rfl⟩)
  exact Subgroup.map_le_iff_le_comap.1 ((Subgroup.map_commutator _ _ _).trans_le
    (Subgroup.commutator_mono le_top le_top)) h

end StableGeneralLinearGroup

/-! ## Algebraic `K₁` -/

variable (A) in
/-- **Algebraic `K₁`** of a ring `A`: the quotient `GL_∞(A) / E_∞(A)` of the stable general
linear group by the stable elementary subgroup. Since `E_∞(A)` is the commutator subgroup
(`TauCeti.StableGeneralLinearGroup.elementarySubgroup_eq_commutator`), this is the
abelianization of `GL_∞(A)`, and it is defined as such. -/
abbrev AlgebraicK1 : Type _ :=
  Abelianization (StableGeneralLinearGroup A)

namespace AlgebraicK1

variable (A) in
/-- The class in algebraic `K₁` of an invertible matrix. -/
def mk (n : ℕ) : GL (Fin n) A →* AlgebraicK1 A :=
  Abelianization.of.comp (StableGeneralLinearGroup.of A n)

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
    (Abelianization.of : StableGeneralLinearGroup A →* AlgebraicK1 A).ker =
      StableGeneralLinearGroup.elementarySubgroup A := by
  rw [Abelianization.ker_of, StableGeneralLinearGroup.elementarySubgroup_eq_commutator]

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

variable (A) in
/-- Algebraic `K₁` is the quotient of `GL_∞(A)` by the stable elementary subgroup. -/
def quotientElementarySubgroupEquiv :
    StableGeneralLinearGroup A ⧸ StableGeneralLinearGroup.elementarySubgroup A ≃* AlgebraicK1 A :=
  QuotientGroup.quotientMulEquivOfEq StableGeneralLinearGroup.elementarySubgroup_eq_commutator

/-- The identification of `GL_∞(A) / E_∞(A)` with algebraic `K₁` respects the projections. -/
@[simp]
theorem quotientElementarySubgroupEquiv_mk (x : StableGeneralLinearGroup A) :
    quotientElementarySubgroupEquiv A x = Abelianization.of x :=
  (rfl)

/-- Homomorphisms out of algebraic `K₁` agree when they agree on the classes of invertible
matrices of each size. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {f g : AlgebraicK1 A →* G}
    (h : ∀ n, f.comp (mk A n) = g.comp (mk A n)) : f = g :=
  Abelianization.hom_ext _ _ (StableGeneralLinearGroup.hom_ext h)

/-- The **universal property of algebraic `K₁`**: a family of homomorphisms from the groups
`GL (Fin n) A` to a commutative group which is compatible with stabilization induces a
homomorphism out of algebraic `K₁`. -/
def lift {G : Type*} [CommGroup G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) : AlgebraicK1 A →* G :=
  Abelianization.lift (StableGeneralLinearGroup.lift f hf)

/-- The homomorphism induced by a compatible family sends the class of an invertible matrix to
its value under the family. -/
@[simp]
theorem lift_mk {G : Type*} [CommGroup G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u) (n : ℕ) (u : GL (Fin n) A) :
    lift f hf (mk A n u) = f n u :=
  (rfl)

end AlgebraicK1

end TauCeti
