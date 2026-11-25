/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Relative algebraic `K₁` of a ring and a two-sided ideal

Let `R` be a possibly noncommutative ring and `I` a two-sided ideal of `R`. The
**congruence subgroup** `GLₙ(R, I)` consists of the invertible matrices congruent to the identity
modulo `I`, the kernel of reduction `GLₙ(R) → GLₙ(R/I)`. The **relative elementary subgroup**
`Eₙ(R, I)` is the normal closure, inside the elementary subgroup `Eₙ(R)`, of the elementary
matrices `eᵢⱼ(x) = 1 + x Eᵢⱼ` with `x ∈ I`. In the limit over `n` these give subgroups
`GL_∞(R, I)` and `E_∞(R, I)` of the stable general linear group `GL_∞(R)`.

The **relative Whitehead lemma** says that for `g ∈ GLₙ(R, I)` the block diagonal matrix
`g ⊕ g⁻¹` lies in `E₂ₙ(R, I)`: it factors as
`U(g - 1) · L(1) U(g⁻¹ - 1) L(1)⁻¹ · L(1 - g)`, where `U(X)` and `L(Y)` are the block unipotent
matrices, whose off-diagonal blocks `g - 1`, `g⁻¹ - 1` and `1 - g` have entries in `I`, and the
middle factor is conjugated by the elementary matrix `L(1)`. Consequently, in the limit:

* `E_∞(R, I)` is a normal subgroup of `GL_∞(R)` contained in `GL_∞(R, I)`;
* the **relative commutator formula** `E_∞(R, I) = ⁅E_∞(R), E_∞(R, I)⁆ = ⁅GL_∞(R), GL_∞(R, I)⁆`
  holds; in particular `⁅GL_∞(R, I), GL_∞(R, I)⁆ ≤ E_∞(R, I)`.

Hence the **relative `K₁`**, `K₁(R, I) = GL_∞(R, I) / E_∞(R, I)`, is an abelian group. The
inclusion `GL_∞(R, I) → GL_∞(R)` induces a homomorphism `K₁(R, I) → K₁(R)`, and the sequence
`K₁(R, I) → K₁(R) → K₁(R/I)` is exact at `K₁(R)`: a class that dies in `K₁(R/I)` is represented
by a matrix whose reduction is elementary, and dividing by an elementary lift of that reduction,
which exists because `R → R/I` is surjective, gives a representative congruent to `1`.

The relative group `K₁(R, I)` is not defined as the kernel of `K₁(R) → K₁(R/I)`; the map
`K₁(R, I) → K₁(R)` need not be injective.

This relative `K₁` of a ring and an ideal is distinct from
`TauCeti.relativeAlgebraicK1`, the kernel of the augmentation `K₁(A⁺) → K₁(R)` of the forced
unitization of a nonunital algebra.

## Main definitions

* `TauCeti.congruenceSubgroupGL`: the congruence subgroup `GLₙ(R, I)` of `GL n R`.
* `TauCeti.relativeElementarySubgroup`: the relative elementary subgroup `Eₙ(R, I)` of `GL n R`.
* `TauCeti.StableGeneralLinearGroup.congruenceSubgroup`: the stable congruence subgroup
  `GL_∞(R, I)`.
* `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup`: the stable relative elementary
  subgroup `E_∞(R, I)`.
* `TauCeti.IdealAlgebraicK1`: the relative `K₁(R, I) = GL_∞(R, I) / E_∞(R, I)`, a commutative
  group.
* `TauCeti.IdealAlgebraicK1.toAlgebraicK1`: the homomorphism `K₁(R, I) → K₁(R)`.

## Main results

* `TauCeti.fromBlocksGL_inv_mem_relativeElementarySubgroup`: the relative Whitehead lemma,
  `g ⊕ g⁻¹ ∈ E₂ₙ(R, I)` for `g ∈ GLₙ(R, I)`.
* `TauCeti.fromBlocksGL_conj_mem_relativeElementarySubgroup`: `geg⁻¹ ⊕ 1 ∈ E₂ₙ(R, I)` for
  `g ∈ GLₙ(R)` and `e ∈ Eₙ(R, I)`.
* `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_eq_closure`: `E_∞(R, I)` is the
  normal closure in `E_∞(R)` of the stable elementary matrices with parameter in `I`.
* `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_normal`: `E_∞(R, I)` is normal in
  `GL_∞(R)`.
* `TauCeti.StableGeneralLinearGroup.commutator_elementarySubgroup_relativeElementarySubgroup`,
  `TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_eq_commutator`: the relative
  commutator formula.
* `TauCeti.IdealAlgebraicK1.range_toAlgebraicK1_eq_ker_map`: exactness of
  `K₁(R, I) → K₁(R) → K₁(R/I)` at `K₁(R)`.

## References

* C. A. Weibel, *The K-book*, Chapter III, §2: the Relative Whitehead Lemma 2.1, Definition 2.2
  and Proposition 2.3.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §4.
* H. Bass, *Algebraic K-Theory* (1968), Chapter V, §1.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Finite-size congruence and relative elementary subgroups -/

section Finite

variable {n m k : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  [DecidableEq k] [Fintype k] {R : Type*} [Ring R] {I : Ideal R}

variable (n I) in
/-- The **congruence subgroup** `GLₙ(R, I)` of `GL n R` for a two-sided ideal `I`: the kernel of
reduction modulo `I`, that is the invertible matrices congruent to the identity modulo `I`. -/
def congruenceSubgroupGL [I.IsTwoSided] : Subgroup (GL n R) :=
  (Units.map ((Ideal.Quotient.mk I).mapMatrix (m := n)).toMonoidHom).ker

/-- An invertible matrix lies in the congruence subgroup of `I` exactly when every entry of its
difference with the identity matrix lies in `I`. -/
theorem mem_congruenceSubgroupGL_iff [I.IsTwoSided] {u : GL n R} :
    u ∈ congruenceSubgroupGL n I ↔
      ∀ i j, (u : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  simp only [congruenceSubgroupGL, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
    Units.val_one, ← Matrix.ext_iff, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    RingHom.mapMatrix_apply, Matrix.map_apply, ← Ideal.Quotient.eq]
  refine forall₂_congr fun i j ↦ ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable (n I) in
/-- The **relative elementary subgroup** `Eₙ(R, I)` of `GL n R`: the subgroup generated by the
conjugates `e eᵢⱼ(x) e⁻¹` of the elementary matrices with parameter `x ∈ I` by elementary
matrices `e`, that is the normal closure in `Eₙ(R)` of the elementary matrices with parameter in
`I`. -/
def relativeElementarySubgroup : Subgroup (GL n R) :=
  Subgroup.closure {g | ∃ e ∈ elementarySubgroup n R, ∃ (i j : n) (hij : i ≠ j), ∃ x ∈ I,
    e * transvectionUnit hij x * e⁻¹ = g}

/-- The conjugate of an elementary matrix with parameter in `I` by an elementary matrix is
relatively elementary. -/
theorem mul_transvectionUnit_mul_inv_mem_relativeElementarySubgroup {e : GL n R}
    (he : e ∈ elementarySubgroup n R) {i j : n} (hij : i ≠ j) {x : R} (hx : x ∈ I) :
    e * transvectionUnit hij x * e⁻¹ ∈ relativeElementarySubgroup n I :=
  Subgroup.subset_closure ⟨e, he, i, j, hij, x, hx, rfl⟩

/-- An elementary matrix with parameter in `I` is relatively elementary. -/
theorem transvectionUnit_mem_relativeElementarySubgroup {i j : n} (hij : i ≠ j) {x : R}
    (hx : x ∈ I) : transvectionUnit hij x ∈ relativeElementarySubgroup n I := by
  simpa using mul_transvectionUnit_mul_inv_mem_relativeElementarySubgroup (one_mem _) hij hx

/-- The relative elementary subgroup is contained in a subgroup exactly when every conjugate of an
elementary matrix with parameter in `I` by an elementary matrix is. -/
theorem relativeElementarySubgroup_le_iff {H : Subgroup (GL n R)} :
    relativeElementarySubgroup n I ≤ H ↔
      ∀ e ∈ elementarySubgroup n R, ∀ (i j : n) (hij : i ≠ j), ∀ x ∈ I,
        e * transvectionUnit hij x * e⁻¹ ∈ H := by
  rw [relativeElementarySubgroup, Subgroup.closure_le]
  constructor
  · exact fun h e he i j hij x hx ↦ h ⟨e, he, i, j, hij, x, hx, rfl⟩
  · rintro h _ ⟨e, he, i, j, hij, x, hx, rfl⟩
    exact h e he i j hij x hx

/-- The relative elementary subgroup is normalized by the elementary subgroup. -/
theorem conj_mem_relativeElementarySubgroup {e g : GL n R} (he : e ∈ elementarySubgroup n R)
    (hg : g ∈ relativeElementarySubgroup n I) :
    e * g * e⁻¹ ∈ relativeElementarySubgroup n I := by
  have h : relativeElementarySubgroup n I ≤
      (relativeElementarySubgroup n I).comap (MulAut.conj e).toMonoidHom := by
    refine relativeElementarySubgroup_le_iff.2 fun f hf i j hij x hx ↦ ?_
    simpa [mul_assoc] using
      mul_transvectionUnit_mul_inv_mem_relativeElementarySubgroup (mul_mem he hf) hij hx
  simpa using h hg

/-- Relatively elementary matrices are elementary. -/
theorem relativeElementarySubgroup_le_elementarySubgroup :
    relativeElementarySubgroup n I ≤ elementarySubgroup n R :=
  relativeElementarySubgroup_le_iff.2 fun _ he _ _ hij x _ ↦
    mul_mem (mul_mem he (transvectionUnit_mem_elementarySubgroup hij x)) (inv_mem he)

/-- Relatively elementary matrices are congruent to the identity modulo `I`. -/
theorem relativeElementarySubgroup_le_congruenceSubgroupGL [I.IsTwoSided] :
    relativeElementarySubgroup n I ≤ congruenceSubgroupGL n I := by
  refine relativeElementarySubgroup_le_iff.2 fun e _ i j hij x hx ↦ ?_
  refine (MonoidHom.normal_ker _).conj_mem _ ?_ e
  rw [MonoidHom.mem_ker, RingHom.toMonoidHom_eq_coe, RingHom.unitsMap_mapMatrix_transvectionUnit,
    Ideal.Quotient.eq_zero_iff_mem.2 hx, transvectionUnit_zero]

/-- A homomorphism of general linear groups that maps elementary matrices to elementary matrices,
and elementary matrices with parameter in `I` to relatively elementary matrices, maps the
relative elementary subgroup into the relative elementary subgroup. -/
theorem map_relativeElementarySubgroup_le_of_map_elementarySubgroup_le {φ : GL n R →* GL m R}
    (hE : (elementarySubgroup n R).map φ ≤ elementarySubgroup m R)
    (ht : ∀ (i j : n) (hij : i ≠ j), ∀ x ∈ I,
      φ (transvectionUnit hij x) ∈ relativeElementarySubgroup m I) :
    (relativeElementarySubgroup n I).map φ ≤ relativeElementarySubgroup m I := by
  refine Subgroup.map_le_iff_le_comap.2 (relativeElementarySubgroup_le_iff.2 ?_)
  intro e he i j hij x hx
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact conj_mem_relativeElementarySubgroup (hE ⟨e, he, rfl⟩) (ht i j hij x hx)

/-- Placing a relatively elementary matrix in the upper left block, with the identity in the lower
right block, gives a relatively elementary matrix. -/
theorem map_relativeElementarySubgroup_le_relativeElementarySubgroup :
    (relativeElementarySubgroup m I).map (fromBlocksGL.comp (MonoidHom.inl (GL m R) (GL k R))) ≤
      relativeElementarySubgroup (m ⊕ k) I :=
  map_relativeElementarySubgroup_le_of_map_elementarySubgroup_le
    map_elementarySubgroup_le_elementarySubgroup fun i j hij x hx ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.inl_apply, fromBlocksGL_transvectionUnit_one]
      exact transvectionUnit_mem_relativeElementarySubgroup _ hx

end Finite

end TauCeti

namespace Equiv

open TauCeti

variable {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] {R : Type*}
  [Ring R] {I : Ideal R}

/-- Relabelling the indices along an equivalence maps the relative elementary subgroup into the
relative elementary subgroup. -/
theorem map_reindexGL_relativeElementarySubgroup_le (e : n ≃ m) :
    (relativeElementarySubgroup n I).map (e.reindexGL R).toMonoidHom ≤
      relativeElementarySubgroup m I :=
  map_relativeElementarySubgroup_le_of_map_elementarySubgroup_le
    (e.map_reindexGL_elementarySubgroup (A := R)).le fun i j hij x hx ↦ by
      rw [MulEquiv.coe_toMonoidHom, reindexGL_transvectionUnit]
      exact transvectionUnit_mem_relativeElementarySubgroup _ hx

end Equiv

namespace Matrix

open TauCeti

variable {m k : Type*} [DecidableEq m] [Fintype m] [DecidableEq k] [Fintype k] {R : Type*}
  [Ring R] {I : Ideal R}

/-- An upper block unipotent matrix whose off-diagonal block has entries in `I` is relatively
elementary: it is the product of the elementary matrices of its entries. -/
theorem upperBlockGL_mem_relativeElementarySubgroup {X : Matrix m k R} (hX : ∀ a b, X a b ∈ I) :
    upperBlockGL X ∈ relativeElementarySubgroup (m ⊕ k) I :=
  upperBlockGL_mem_of_forall_transvectionUnit_mem fun a b ↦
    transvectionUnit_mem_relativeElementarySubgroup _ (hX a b)

/-- A lower block unipotent matrix whose off-diagonal block has entries in `I` is relatively
elementary: it is the product of the elementary matrices of its entries. -/
theorem lowerBlockGL_mem_relativeElementarySubgroup {Y : Matrix k m R} (hY : ∀ b a, Y b a ∈ I) :
    lowerBlockGL Y ∈ relativeElementarySubgroup (m ⊕ k) I :=
  lowerBlockGL_mem_of_forall_transvectionUnit_mem fun b a ↦
    transvectionUnit_mem_relativeElementarySubgroup _ (hY b a)

end Matrix

namespace TauCeti

/-! ## The relative Whitehead lemma -/

section Whitehead

variable {m : Type*} [DecidableEq m] [Fintype m] {R : Type*} [Ring R] {I : Ideal R}

/-- **The relative Whitehead lemma.** For `g` congruent to the identity modulo `I`, the block
diagonal matrix `g ⊕ g⁻¹` is relatively elementary: it is
`U(g - 1) · L(1) U(g⁻¹ - 1) L(1)⁻¹ · L(1 - g)`, a product of block unipotent matrices with
off-diagonal blocks in `I` and of a conjugate of one by the elementary matrix `L(1)`. -/
theorem fromBlocksGL_inv_mem_relativeElementarySubgroup [I.IsTwoSided] {g : GL m R}
    (hg : g ∈ congruenceSubgroupGL m I) :
    fromBlocksGL (g, g⁻¹) ∈ relativeElementarySubgroup (m ⊕ m) I := by
  have h : fromBlocksGL (g, g⁻¹) =
      upperBlockGL ((g : Matrix m m R) - 1) *
        (lowerBlockGL 1 * upperBlockGL ((↑g⁻¹ : Matrix m m R) - 1) * (lowerBlockGL 1)⁻¹) *
          lowerBlockGL (1 - (g : Matrix m m R)) := by
    refine Units.ext ?_
    simp only [coe_fromBlocksGL, Units.val_mul, coe_upperBlockGL, coe_lowerBlockGL,
      lowerBlockGL_inv, fromBlocks_multiply]
    congr 1 <;> simp [sub_mul, mul_sub, mul_add, -Matrix.coe_units_inv] <;> abel
  have hg₁ := mem_congruenceSubgroupGL_iff.1 hg
  have hg₂ := mem_congruenceSubgroupGL_iff.1 (inv_mem hg)
  rw [h]
  refine mul_mem (mul_mem (upperBlockGL_mem_relativeElementarySubgroup fun a b ↦ ?_)
    (conj_mem_relativeElementarySubgroup (lowerBlockGL_mem_elementarySubgroup 1)
      (upperBlockGL_mem_relativeElementarySubgroup fun a b ↦ ?_)))
    (lowerBlockGL_mem_relativeElementarySubgroup fun a b ↦ ?_)
  · simpa using hg₁ a b
  · simpa using hg₂ a b
  · simpa using I.neg_mem (hg₁ a b)

/-- **The relative elementary subgroup is stably normal.** For `e` relatively elementary and `g`
invertible, the stabilized conjugate `g e g⁻¹ ⊕ 1` is relatively elementary, being the conjugate
of `e ⊕ 1` by the elementary matrix `g ⊕ g⁻¹`. -/
theorem fromBlocksGL_conj_mem_relativeElementarySubgroup (g : GL m R) {e : GL m R}
    (he : e ∈ relativeElementarySubgroup m I) :
    fromBlocksGL (g * e * g⁻¹, 1) ∈ relativeElementarySubgroup (m ⊕ m) I := by
  have h : fromBlocksGL (g * e * g⁻¹, 1) =
      fromBlocksGL (g, g⁻¹) * fromBlocksGL (e, 1) * (fromBlocksGL (g, g⁻¹))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    simp
  rw [h]
  exact conj_mem_relativeElementarySubgroup (fromBlocksGL_inv_mem_elementarySubgroup g)
    (map_relativeElementarySubgroup_le_relativeElementarySubgroup ⟨e, he, rfl⟩)

end Whitehead

/-! ## Stabilization -/

section Stabilization

variable {R : Type*} [Ring R] {I : Ideal R}

/-- A stabilization `u ⊕ 1` is congruent to the identity modulo `I` exactly when `u` is. -/
@[simp]
theorem stabilizeGL_mem_congruenceSubgroupGL_iff [I.IsTwoSided] {m n : ℕ} (h : m ≤ n)
    {u : GL (Fin m) R} :
    stabilizeGL R h u ∈ congruenceSubgroupGL (Fin n) I ↔ u ∈ congruenceSubgroupGL (Fin m) I := by
  simp only [congruenceSubgroupGL, MonoidHom.mem_ker, ← stabilizeGL_map,
    map_eq_one_iff _ (stabilizeGL_injective h)]

/-- Stabilization maps the relative elementary subgroup into the relative elementary subgroup. -/
theorem map_stabilizeGL_relativeElementarySubgroup_le {m n : ℕ} (h : m ≤ n) :
    (relativeElementarySubgroup (Fin m) I).map (stabilizeGL R h) ≤
      relativeElementarySubgroup (Fin n) I :=
  map_relativeElementarySubgroup_le_of_map_elementarySubgroup_le
    (map_stabilizeGL_elementarySubgroup_le h) fun i j hij x hx ↦ by
      rw [stabilizeGL_transvectionUnit]
      exact transvectionUnit_mem_relativeElementarySubgroup _ hx

end Stabilization

/-! ## The stable congruence and relative elementary subgroups -/

namespace StableGeneralLinearGroup

variable {R : Type*} [Ring R] (I : Ideal R)

section Congruence

variable [I.IsTwoSided]

/-- The **stable congruence subgroup** `GL_∞(R, I)` of `GL_∞(R)`: the union of the images of the
congruence subgroups `GLₙ(R, I)`, that is the elements represented by invertible matrices
congruent to the identity modulo `I`. -/
def congruenceSubgroup : Subgroup (StableGeneralLinearGroup R) :=
  ⨆ n, (congruenceSubgroupGL (Fin n) I).map (of R n)

/-- The images of the congruence subgroups increase with the size. -/
private theorem monotone_map_congruenceSubgroupGL :
    Monotone fun n ↦ (congruenceSubgroupGL (Fin n) I).map (of R n) := by
  intro m n h
  dsimp only
  rw [← of_comp_stabilizeGL h, ← Subgroup.map_map]
  exact Subgroup.map_mono fun _ ⟨u, hu, hv⟩ ↦
    hv ▸ (stabilizeGL_mem_congruenceSubgroupGL_iff h).2 hu

variable {I}

/-- An element of `GL_∞(R)` lies in the stable congruence subgroup exactly when it is represented
by an invertible matrix congruent to the identity modulo `I`. -/
theorem mem_congruenceSubgroup_iff {x : StableGeneralLinearGroup R} :
    x ∈ congruenceSubgroup I ↔ ∃ n, ∃ u ∈ congruenceSubgroupGL (Fin n) I, of R n u = x := by
  rw [congruenceSubgroup,
    Subgroup.mem_iSup_of_directed (monotone_map_congruenceSubgroupGL I).directed_le]
  simp only [Subgroup.mem_map]

/-- The image in `GL_∞(R)` of an invertible matrix lies in the stable congruence subgroup exactly
when the matrix is congruent to the identity modulo `I`. -/
@[simp]
theorem of_mem_congruenceSubgroup_iff {n : ℕ} {u : GL (Fin n) R} :
    of R n u ∈ congruenceSubgroup I ↔ u ∈ congruenceSubgroupGL (Fin n) I := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ mem_congruenceSubgroup_iff.2 ⟨n, u, hu, rfl⟩⟩
  obtain ⟨m, v, hv, hvu⟩ := mem_congruenceSubgroup_iff.1 hu
  obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
  rw [← of_stabilizeGL hmk, ← of_stabilizeGL hnk] at hvu
  rw [← stabilizeGL_mem_congruenceSubgroupGL_iff hnk, ← of_injective k hvu]
  exact (stabilizeGL_mem_congruenceSubgroupGL_iff hmk).2 hv

end Congruence

/-- The **stable relative elementary subgroup** `E_∞(R, I)` of `GL_∞(R)`: the union of the images
of the relative elementary subgroups `Eₙ(R, I)`. By
`TauCeti.StableGeneralLinearGroup.relativeElementarySubgroup_eq_closure` it is the normal closure
in `E_∞(R)` of the stable elementary matrices with parameter in `I`. -/
def relativeElementarySubgroup : Subgroup (StableGeneralLinearGroup R) :=
  ⨆ n, (TauCeti.relativeElementarySubgroup (Fin n) I).map (of R n)

/-- The images of the relative elementary subgroups increase with the size. -/
private theorem monotone_map_relativeElementarySubgroup :
    Monotone fun n ↦ (TauCeti.relativeElementarySubgroup (Fin n) I).map (of R n) := by
  intro m n h
  dsimp only
  rw [← of_comp_stabilizeGL h, ← Subgroup.map_map]
  exact Subgroup.map_mono (map_stabilizeGL_relativeElementarySubgroup_le h)

variable {I}

/-- An element of `GL_∞(R)` is stably relatively elementary exactly when it comes from a
relatively elementary matrix of some size. -/
theorem mem_relativeElementarySubgroup_iff {x : StableGeneralLinearGroup R} :
    x ∈ relativeElementarySubgroup I ↔
      ∃ n, ∃ u ∈ TauCeti.relativeElementarySubgroup (Fin n) I, of R n u = x := by
  rw [relativeElementarySubgroup,
    Subgroup.mem_iSup_of_directed (monotone_map_relativeElementarySubgroup I).directed_le]
  simp only [Subgroup.mem_map]

/-- Relatively elementary matrices are stably relatively elementary. -/
theorem of_mem_relativeElementarySubgroup {n : ℕ} {u : GL (Fin n) R}
    (hu : u ∈ TauCeti.relativeElementarySubgroup (Fin n) I) :
    of R n u ∈ relativeElementarySubgroup I :=
  mem_relativeElementarySubgroup_iff.2 ⟨n, u, hu, rfl⟩

/-- A stable elementary matrix with parameter in `I` is stably relatively elementary. -/
theorem stableTransvection_mem_relativeElementarySubgroup (p : {p : ℕ × ℕ // p.1 ≠ p.2})
    {x : R} (hx : x ∈ I) : stableTransvection p x ∈ relativeElementarySubgroup I := by
  rw [stableTransvection_eq_of p x (Nat.lt_succ_of_le (le_max_left _ _))
    (Nat.lt_succ_of_le (le_max_right _ _))]
  exact of_mem_relativeElementarySubgroup (transvectionUnit_mem_relativeElementarySubgroup _ hx)

/-- An invertible matrix `u` whose block diagonal stabilization `u ⊕ 1` of size `n + n` is
relatively elementary is stably relatively elementary. -/
private theorem of_mem_relativeElementarySubgroup_of_fromBlocksGL {n : ℕ} {u : GL (Fin n) R}
    (hu : fromBlocksGL (u, 1) ∈ TauCeti.relativeElementarySubgroup (Fin n ⊕ Fin n) I) :
    of R n u ∈ relativeElementarySubgroup I := by
  rw [← of_stabilizeGL (Nat.le_add_right n n), stabilizeGL_eq_reindexGL_fromBlocksGL]
  exact of_mem_relativeElementarySubgroup
    (finSumFinEquiv.map_reindexGL_relativeElementarySubgroup_le ⟨_, hu, rfl⟩)

/-- Stably relatively elementary elements are stably elementary. -/
theorem relativeElementarySubgroup_le_elementarySubgroup :
    relativeElementarySubgroup I ≤ elementarySubgroup R :=
  iSup_le fun _ ↦ Subgroup.map_le_iff_le_comap.2 fun _ hu ↦
    of_mem_elementarySubgroup (TauCeti.relativeElementarySubgroup_le_elementarySubgroup hu)

/-- Stably relatively elementary elements lie in the stable congruence subgroup. -/
theorem relativeElementarySubgroup_le_congruenceSubgroup [I.IsTwoSided] :
    relativeElementarySubgroup I ≤ congruenceSubgroup I :=
  iSup_le fun _ ↦ Subgroup.map_le_iff_le_comap.2 fun _ hu ↦
    of_mem_congruenceSubgroup_iff.2 (relativeElementarySubgroup_le_congruenceSubgroupGL hu)

/-- **The stable relative elementary subgroup is normal** in `GL_∞(R)`: a conjugate `g e g⁻¹`
of a relatively elementary matrix by any invertible matrix becomes relatively elementary after
stabilization. -/
instance relativeElementarySubgroup_normal : (relativeElementarySubgroup I).Normal where
  conj_mem x hx g := by
    obtain ⟨m, e, he, rfl⟩ := mem_relativeElementarySubgroup_iff.1 hx
    obtain ⟨n, g, rfl⟩ := exists_of g
    -- Move `g` and `e` to a common size `k`.
    obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    rw [← of_stabilizeGL hmk e, ← of_stabilizeGL hnk g, ← map_inv, ← map_mul, ← map_mul]
    exact of_mem_relativeElementarySubgroup_of_fromBlocksGL
      (fromBlocksGL_conj_mem_relativeElementarySubgroup _
        (map_stabilizeGL_relativeElementarySubgroup_le hmk ⟨e, he, rfl⟩))

/-- The stable relative elementary subgroup is the **normal closure in `E_∞(R)`** of the stable
elementary matrices with parameter in `I`: the subgroup generated by their conjugates by stably
elementary elements. -/
theorem relativeElementarySubgroup_eq_closure :
    relativeElementarySubgroup I =
      Subgroup.closure {g | ∃ e ∈ elementarySubgroup R, ∃ p : {p : ℕ × ℕ // p.1 ≠ p.2}, ∃ x ∈ I,
        e * stableTransvection p x * e⁻¹ = g} := by
  refine le_antisymm (iSup_le fun n ↦ Subgroup.map_le_iff_le_comap.2 ?_) ?_
  · refine relativeElementarySubgroup_le_iff.2 fun e he i j hij x hx ↦ ?_
    refine Subgroup.subset_closure ⟨of R n e, of_mem_elementarySubgroup he,
      ⟨((i : ℕ), (j : ℕ)), fun h ↦ hij (Fin.ext h)⟩, x, hx, ?_⟩
    rw [stableTransvection_eq_of _ x i.isLt j.isLt, map_mul, map_mul, map_inv]
  · rw [Subgroup.closure_le]
    rintro _ ⟨e, -, p, x, hx, rfl⟩
    exact (relativeElementarySubgroup_normal).conj_mem _
      (stableTransvection_mem_relativeElementarySubgroup p hx) e

/-- **The relative commutator formula, first half**: the commutators of invertible matrices with
matrices congruent to the identity modulo `I` are stably relatively elementary. -/
theorem commutator_top_congruenceSubgroup_le_relativeElementarySubgroup [I.IsTwoSided] :
    ⁅(⊤ : Subgroup (StableGeneralLinearGroup R)), congruenceSubgroup I⁆ ≤
      relativeElementarySubgroup I := by
  refine Subgroup.commutator_le.2 fun x _ y hy ↦ ?_
  obtain ⟨n, g, h, rfl, rfl⟩ := exists_of₂ x y
  rw [of_mem_congruenceSubgroup_iff] at hy
  -- Write `⁅g, h⁆ ⊕ 1` as `(g ⊕ 1) (h ⊕ h⁻¹) (g ⊕ 1)⁻¹ (h⁻¹ ⊕ h)` in size `n + n`.
  let s : GL (Fin n ⊕ Fin n) R →* StableGeneralLinearGroup R :=
    (of R (n + n)).comp (finSumFinEquiv.reindexGL R).toMonoidHom
  have hs : ∀ u : GL (Fin n) R, s (fromBlocksGL (u, 1)) = of R n u := fun u ↦ by
    simp [s, ← stabilizeGL_eq_reindexGL_fromBlocksGL]
  have hsE : ∀ w ∈ TauCeti.relativeElementarySubgroup (Fin n ⊕ Fin n) I,
      s w ∈ relativeElementarySubgroup I := fun w hw ↦
    of_mem_relativeElementarySubgroup
      (finSumFinEquiv.map_reindexGL_relativeElementarySubgroup_le ⟨w, hw, rfl⟩)
  have hfac : fromBlocksGL (⁅g, h⁆, (1 : GL (Fin n) R)) =
      fromBlocksGL (g, 1) * fromBlocksGL (h, h⁻¹) * (fromBlocksGL (g, 1))⁻¹ *
        fromBlocksGL (h⁻¹, h) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    ext : 1 <;> simp [commutatorElement_def, mul_assoc]
  rw [← map_commutatorElement, ← hs, hfac, map_mul, map_mul, map_mul, map_inv, hs]
  exact mul_mem ((relativeElementarySubgroup_normal).conj_mem _
    (hsE _ (fromBlocksGL_inv_mem_relativeElementarySubgroup hy)) _)
    (hsE _ (by simpa using fromBlocksGL_inv_mem_relativeElementarySubgroup (inv_mem hy)))

/-- **The relative commutator formula, second half**: `E_∞(R, I)` is its own commutator with
`E_∞(R)`, since `eᵢⱼ(x) = ⁅eᵢₖ(x), eₖⱼ(1)⁆` for a third index `k`. -/
theorem commutator_elementarySubgroup_relativeElementarySubgroup :
    ⁅elementarySubgroup R, relativeElementarySubgroup I⁆ = relativeElementarySubgroup I := by
  refine le_antisymm (Subgroup.commutator_le_right _ _) ?_
  rw [relativeElementarySubgroup_eq_closure, Subgroup.closure_le]
  rintro _ ⟨e, -, ⟨⟨i, j⟩, hij⟩, x, hx, rfl⟩
  have hik : i ≠ i + j + 1 := by omega
  have hkj : i + j + 1 ≠ j := by omega
  have ht : stableTransvection ⟨(i, j), hij⟩ x =
      ⁅stableTransvection ⟨(i, i + j + 1), hik⟩ x,
        stableTransvection (A := R) ⟨(i + j + 1, j), hkj⟩ 1⁆ := by
    rw [commutatorElement_stableTransvection hik hkj hij, mul_one]
  rw [ht, ← relativeElementarySubgroup_eq_closure]
  refine (Subgroup.commutator_normal _ _).conj_mem _ ?_ e
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator
    (stableTransvection_mem_relativeElementarySubgroup _ hx)
    (stableTransvection_mem_elementarySubgroup _ 1)

/-- **The relative commutator formula**: `E_∞(R, I)` is the commutator of `GL_∞(R)` with the
stable congruence subgroup `GL_∞(R, I)`. -/
theorem relativeElementarySubgroup_eq_commutator [I.IsTwoSided] :
    relativeElementarySubgroup I =
      ⁅(⊤ : Subgroup (StableGeneralLinearGroup R)), congruenceSubgroup I⁆ :=
  le_antisymm
    ((commutator_elementarySubgroup_relativeElementarySubgroup (I := I)).symm.trans_le
      (Subgroup.commutator_mono le_top relativeElementarySubgroup_le_congruenceSubgroup))
    commutator_top_congruenceSubgroup_le_relativeElementarySubgroup

/-- The commutator subgroup of the stable congruence subgroup is stably relatively elementary. -/
theorem commutator_congruenceSubgroup_le_relativeElementarySubgroup [I.IsTwoSided] :
    ⁅congruenceSubgroup I, congruenceSubgroup I⁆ ≤ relativeElementarySubgroup I :=
  (Subgroup.commutator_mono le_top le_rfl).trans
    commutator_top_congruenceSubgroup_le_relativeElementarySubgroup

end StableGeneralLinearGroup

/-! ## Relative `K₁` -/

open StableGeneralLinearGroup

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- The **relative `K₁`** of a ring `R` and a two-sided ideal `I`:
`K₁(R, I) = GL_∞(R, I) / E_∞(R, I)`, the quotient of the stable congruence subgroup by the stable
relative elementary subgroup. It is a commutative group by the relative commutator formula. -/
def IdealAlgebraicK1 : Type _ :=
  StableGeneralLinearGroup.congruenceSubgroup I ⧸
    (StableGeneralLinearGroup.relativeElementarySubgroup I).subgroupOf
      (StableGeneralLinearGroup.congruenceSubgroup I)

namespace IdealAlgebraicK1

/-- The quotient defining relative `K₁` is commutative, because the commutator subgroup of
`GL_∞(R, I)` is stably relatively elementary. -/
instance : IsMulCommutative
    (StableGeneralLinearGroup.congruenceSubgroup I ⧸
      (StableGeneralLinearGroup.relativeElementarySubgroup I).subgroupOf
        (StableGeneralLinearGroup.congruenceSubgroup I)) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 <|
    Subgroup.commutator_le.2 fun x _ y _ ↦ Subgroup.mem_subgroupOf.2 <| by
      have h := commutator_congruenceSubgroup_le_relativeElementarySubgroup
        (Subgroup.commutator_mem_commutator x.property y.property)
      rwa [← Subgroup.coe_subtype, ← map_commutatorElement] at h

open scoped IsMulCommutative in
instance : CommGroup (IdealAlgebraicK1 I) :=
  inferInstanceAs (CommGroup
    (StableGeneralLinearGroup.congruenceSubgroup I ⧸
      (StableGeneralLinearGroup.relativeElementarySubgroup I).subgroupOf
        (StableGeneralLinearGroup.congruenceSubgroup I)))

/-- The class in relative `K₁` of an element of the stable congruence subgroup. -/
def mk : congruenceSubgroup I →* IdealAlgebraicK1 I :=
  QuotientGroup.mk' _

variable {I}

/-- Every class in relative `K₁` is the class of an element of the stable congruence subgroup. -/
theorem mk_surjective : Function.Surjective (mk I) :=
  QuotientGroup.mk'_surjective _

/-- The class of an element of the stable congruence subgroup is trivial exactly when the element
is stably relatively elementary. -/
@[simp]
theorem mk_eq_one_iff {x : congruenceSubgroup I} :
    mk I x = 1 ↔
      (x : StableGeneralLinearGroup R) ∈ StableGeneralLinearGroup.relativeElementarySubgroup I :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

/-- Every class in relative `K₁` is the class of an invertible matrix of some size congruent to
the identity modulo `I`. -/
theorem exists_mk_of (y : IdealAlgebraicK1 I) :
    ∃ (n : ℕ) (u : GL (Fin n) R) (hu : u ∈ congruenceSubgroupGL (Fin n) I),
      mk I ⟨of R n u, of_mem_congruenceSubgroup_iff.2 hu⟩ = y := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := mk_surjective y
  obtain ⟨n, u, hu, rfl⟩ := mem_congruenceSubgroup_iff.1 hx
  exact ⟨n, u, hu, rfl⟩

/-- Homomorphisms out of relative `K₁` agree when they agree on the classes of elements of the
stable congruence subgroup. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {f g : IdealAlgebraicK1 I →* G}
    (h : f.comp (mk I) = g.comp (mk I)) : f = g :=
  QuotientGroup.monoidHom_ext _ h

variable (I) in
/-- The homomorphism `K₁(R, I) → K₁(R)` induced by the inclusion of the stable congruence subgroup
into `GL_∞(R)`. -/
def toAlgebraicK1 : IdealAlgebraicK1 I →* AlgebraicK1 R :=
  QuotientGroup.lift _ (Group.Abelianization.of.comp (congruenceSubgroup I).subtype) fun x hx ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, AlgebraicK1.ker_of]
    exact StableGeneralLinearGroup.relativeElementarySubgroup_le_elementarySubgroup
      (Subgroup.mem_subgroupOf.1 hx)

/-- The homomorphism `K₁(R, I) → K₁(R)` sends the class of an element of `GL_∞(R, I)` to its class
in `K₁(R)`. -/
@[simp]
theorem toAlgebraicK1_mk (x : congruenceSubgroup I) :
    toAlgebraicK1 I (mk I x) = Group.Abelianization.of (x : StableGeneralLinearGroup R) :=
  (rfl)

/-- **Exactness of `K₁(R, I) → K₁(R) → K₁(R/I)` at `K₁(R)`**: the image of relative `K₁` in
`K₁(R)` is the kernel of the homomorphism induced by the quotient map `R → R/I`. -/
theorem range_toAlgebraicK1_eq_ker_map :
    (toAlgebraicK1 I).range = (AlgebraicK1.map (Ideal.Quotient.mk I)).ker := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, u, hu, rfl⟩ := exists_mk_of y
    rw [MonoidHom.mem_ker, toAlgebraicK1_mk]
    rw [← AlgebraicK1.mk_apply, AlgebraicK1.map_mk, hu, map_one]
  · intro hz
    obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk z
    rw [MonoidHom.mem_ker, AlgebraicK1.map_mk, AlgebraicK1.mk_eq_one_iff] at hz
    obtain ⟨k, h, hk⟩ := hz
    -- The reduction of `u ⊕ 1` is elementary; divide `u ⊕ 1` by an elementary lift of it.
    rw [stabilizeGL_map] at hk
    obtain ⟨e, he, hee⟩ := (Ideal.Quotient.mk I).exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq
      Ideal.Quotient.mk_surjective hk
    have hg : stabilizeGL R h u * e⁻¹ ∈ congruenceSubgroupGL (Fin k) I := by
      rw [congruenceSubgroupGL, MonoidHom.mem_ker, map_mul, map_inv, hee, mul_inv_cancel]
    refine ⟨mk I ⟨of R k _, of_mem_congruenceSubgroup_iff.2 hg⟩, ?_⟩
    rw [toAlgebraicK1_mk, ← AlgebraicK1.mk_apply, map_mul, map_inv, AlgebraicK1.mk_stabilizeGL,
      AlgebraicK1.elementarySubgroup_le_ker_mk k he, inv_one, mul_one]

/-- The composite `K₁(R, I) → K₁(R) → K₁(R/I)` is trivial. -/
@[simp]
theorem map_toAlgebraicK1_eq_one (y : IdealAlgebraicK1 I) :
    AlgebraicK1.map (Ideal.Quotient.mk I) (toAlgebraicK1 I y) = 1 :=
  range_toAlgebraicK1_eq_ker_map.le ⟨y, rfl⟩

end IdealAlgebraicK1

end TauCeti
