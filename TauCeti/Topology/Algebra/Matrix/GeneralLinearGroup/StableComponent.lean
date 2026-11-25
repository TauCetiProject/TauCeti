/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.Topology.Algebra.Group.Connected
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Stable

/-!
# The stable component group and the comparison with algebraic `K₁`

Let `A` be a topological ring, for instance a unital complex Banach algebra. Each
`GL (Fin n) A` is a topological group, and its identity component `GLₙ(A)₀` is a closed normal
subgroup. Stabilization `u ↦ u ⊕ 1` is continuous, so it maps `GLₘ(A)₀` into `GLₙ(A)₀`. The
**stable identity component** `GL_∞(A)₀` is the union of the images of the `GLₙ(A)₀` in the
stable general linear group `GL_∞(A)`; it is a normal subgroup. The **stable component group**
`π₀GL_∞(A) = GL_∞(A) / GL_∞(A)₀` is the quotient by it. Its universal property
(`TauCeti.StableComponentGroup.lift`, `TauCeti.StableComponentGroup.hom_ext`) is that of the
colimit of the groups `GLₙ(A) / GLₙ(A)₀` along stabilization. It is functorial for continuous ring
homomorphisms; continuity is needed, since the construction depends on the topology.

When `A` is moreover connected, for instance a real or complex topological vector space, the
continuous map `c ↦ 1 + c Eᵢⱼ` sends `A` to a connected subset of `GLₙ(A)` containing `1` and the
elementary matrix `1 + a Eᵢⱼ`, so every elementary matrix lies in the identity component. Hence
the stable elementary subgroup `E_∞(A)`, which is the commutator subgroup of `GL_∞(A)`, lies in
`GL_∞(A)₀`: the stable component group is abelian, and the
projection `GL_∞(A) → π₀GL_∞(A)` factors through algebraic `K₁(A) = GL_∞(A) / E_∞(A)`. The
resulting comparison `K₁(A) → π₀GL_∞(A)` is a natural surjection whose kernel is the image of the
stable identity component. It is not injective in general: every `GLₙ(ℂ)` is connected, so the
stable component group of `ℂ` is trivial, while algebraic `K₁(ℂ) = ℂˣ`. That example is in
`TauCeti.Analysis.Matrix.GeneralLinearGroup.StableComponent`, which keeps the polar decomposition
of complex matrices out of this file.

## Main definitions

* `TauCeti.StableGeneralLinearGroup.identityComponent`: the stable identity component
  `GL_∞(A)₀`, the union of the images of the identity components of the `GL (Fin n) A`.
* `TauCeti.StableComponentGroup`: the stable component group `GL_∞(A) / GL_∞(A)₀`.
* `TauCeti.StableComponentGroup.mk`: the class of an invertible matrix.
* `TauCeti.StableComponentGroup.lift`: the universal property of the stable component group, for
  families of homomorphisms compatible with stabilization and trivial on identity components.
* `TauCeti.StableComponentGroup.map`: the homomorphism induced by a continuous ring
  homomorphism.
* `TauCeti.AlgebraicK1.toStableComponentGroup`: the comparison `K₁(A) → GL_∞(A) / GL_∞(A)₀`.

## Main results

* `TauCeti.elementarySubgroup_le_connectedComponentOfOne`: over a connected topological ring,
  elementary matrices lie in the identity component of `GLₙ`.
* `TauCeti.StableGeneralLinearGroup.identityComponent_normal`: the stable identity component is
  normal.
* `TauCeti.StableComponentGroup.mk_eq_one_iff`: an invertible matrix has trivial class exactly
  when some stabilization of it lies in the identity component.
* `TauCeti.StableComponentGroup.map_id`, `TauCeti.StableComponentGroup.map_comp`,
  `TauCeti.StableComponentGroup.map_map`: functoriality.
* `TauCeti.AlgebraicK1.toStableComponentGroup_surjective`,
  `TauCeti.AlgebraicK1.ker_toStableComponentGroup`: the comparison is surjective, with kernel the
  image of the stable identity component.
* `TauCeti.AlgebraicK1.toStableComponentGroup_map`: naturality of the comparison.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Corollary 1.5.1 and Example 1.5.2 (the comparison of
  algebraic `K₁` of a Banach algebra with the group of components of `GL(A)`).
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section Topology

variable {A : Type*} [Ring A] [TopologicalSpace A]

/-! ## Elementary paths -/

variable [IsTopologicalRing A]

section Elementary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Over a connected topological ring, every elementary matrix lies in the identity component of
`GLₙ`: the continuous map `c ↦ 1 + c Eᵢⱼ` sends the connected space `A` to a connected set
containing `1` and `1 + a Eᵢⱼ`. -/
theorem transvectionUnit_mem_connectedComponentOfOne [PreconnectedSpace A] {i j : n}
    (hij : i ≠ j) (a : A) :
    transvectionUnit hij a ∈ Subgroup.connectedComponentOfOne (GL n A) := by
  have hval : Continuous fun c : A ↦ (transvectionUnit hij c : Matrix n n A) := by
    simp only [coe_transvectionUnit_eq_one_add_single]
    refine continuous_const.add (continuous_matrix fun p q ↦ ?_)
    simp only [single_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have hcont : Continuous fun c : A ↦ transvectionUnit hij c := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    simpa only [transvectionUnit_inv, Function.comp_def] using hval.comp continuous_neg
  exact (isPreconnected_range hcont).subset_connectedComponent ⟨0, transvectionUnit_zero hij⟩
    ⟨a, rfl⟩

/-- Over a connected topological ring, the elementary subgroup `Eₙ(A)` is contained in the
identity component of `GLₙ(A)`. -/
theorem elementarySubgroup_le_connectedComponentOfOne [PreconnectedSpace A] :
    elementarySubgroup n A ≤ Subgroup.connectedComponentOfOne (GL n A) :=
  elementarySubgroup_le_iff.2 fun _ _ hij a ↦ transvectionUnit_mem_connectedComponentOfOne hij a

end Elementary

/-! ## The stable identity component -/

namespace StableGeneralLinearGroup

variable (A) in
/-- The **stable identity component** `GL_∞(A)₀` of the stable general linear group of a
topological ring: the union of the images of the identity components of the groups
`GL (Fin n) A`. -/
def identityComponent : Subgroup (StableGeneralLinearGroup A) :=
  ⨆ n, (Subgroup.connectedComponentOfOne (GL (Fin n) A)).map (of A n)

/-- The images of the identity components increase with the size. -/
private theorem monotone_map_connectedComponentOfOne :
    Monotone fun n ↦ (Subgroup.connectedComponentOfOne (GL (Fin n) A)).map (of A n) := by
  intro m n h
  dsimp only
  rw [← of_comp_stabilizeGL h, ← Subgroup.map_map]
  exact Subgroup.map_mono (Subgroup.map_connectedComponentOfOne_le (continuous_stabilizeGL h))

/-- An element of `GL_∞(A)` lies in the stable identity component exactly when it comes from
an element of the identity component of `GL (Fin n) A` for some `n`. -/
theorem mem_identityComponent_iff {x : StableGeneralLinearGroup A} :
    x ∈ identityComponent A ↔
      ∃ n, ∃ u ∈ Subgroup.connectedComponentOfOne (GL (Fin n) A), of A n u = x := by
  rw [identityComponent,
    Subgroup.mem_iSup_of_directed monotone_map_connectedComponentOfOne.directed_le]
  simp only [Subgroup.mem_map]

/-- Invertible matrices in the identity component lie in the stable identity component. -/
theorem of_mem_identityComponent {n : ℕ} {u : GL (Fin n) A}
    (hu : u ∈ Subgroup.connectedComponentOfOne (GL (Fin n) A)) :
    of A n u ∈ identityComponent A :=
  mem_identityComponent_iff.2 ⟨n, u, hu, rfl⟩

/-- An invertible matrix lies in the stable identity component exactly when some stabilization
of it lies in the identity component. -/
theorem of_mem_identityComponent_iff {n : ℕ} {u : GL (Fin n) A} :
    of A n u ∈ identityComponent A ↔
      ∃ k, ∃ h : n ≤ k,
        stabilizeGL A h u ∈ Subgroup.connectedComponentOfOne (GL (Fin k) A) := by
  refine ⟨fun hu ↦ ?_, fun ⟨k, h, hu⟩ ↦ of_stabilizeGL h u ▸ of_mem_identityComponent hu⟩
  obtain ⟨m, v, hv, hvu⟩ := mem_identityComponent_iff.1 hu
  obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
  rw [← of_stabilizeGL hmk, ← of_stabilizeGL hnk] at hvu
  exact ⟨k, hnk, of_injective k hvu ▸
    Subgroup.map_connectedComponentOfOne_le (continuous_stabilizeGL hmk) ⟨v, hv, rfl⟩⟩

/-- **The stable identity component is normal**, since each identity component is normal and
two elements of `GL_∞(A)` come from a common `GL (Fin k) A`. -/
instance identityComponent_normal : (identityComponent A).Normal where
  conj_mem x hx g := by
    obtain ⟨m, e, he, rfl⟩ := mem_identityComponent_iff.1 hx
    obtain ⟨n, g, rfl⟩ := exists_of g
    -- Move `g` and `e` to a common size `k`.
    obtain ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    rw [← of_stabilizeGL hmk e, ← of_stabilizeGL hnk g, ← map_inv, ← map_mul, ← map_mul]
    exact of_mem_identityComponent (Subgroup.normal_connectedComponentOfOne.conj_mem _
      (Subgroup.map_connectedComponentOfOne_le (continuous_stabilizeGL hmk) ⟨e, he, rfl⟩) _)

/-- Over a connected topological ring, the stable elementary subgroup is contained in the stable
identity component. -/
theorem elementarySubgroup_le_identityComponent [PreconnectedSpace A] :
    elementarySubgroup A ≤ identityComponent A := by
  intro x hx
  obtain ⟨n, u, hu, rfl⟩ := mem_elementarySubgroup_iff.1 hx
  exact of_mem_identityComponent (elementarySubgroup_le_connectedComponentOfOne hu)

/-- Over a connected topological ring, the commutator subgroup of `GL_∞(A)` is contained in the
stable identity component. -/
theorem commutator_le_identityComponent [PreconnectedSpace A] :
    commutator (StableGeneralLinearGroup A) ≤ identityComponent A :=
  elementarySubgroup_eq_commutator (A := A) ▸ elementarySubgroup_le_identityComponent

end StableGeneralLinearGroup

/-! ## The stable component group -/

variable (A) in
/-- The **stable component group** `GL_∞(A) / GL_∞(A)₀` of a topological ring `A`: the quotient
of the stable general linear group by its stable identity component. It is the colimit of the
groups `GLₙ(A) / GLₙ(A)₀` along stabilization, in the sense of
`TauCeti.StableComponentGroup.lift`. -/
abbrev StableComponentGroup : Type _ :=
  StableGeneralLinearGroup A ⧸ StableGeneralLinearGroup.identityComponent A

namespace StableComponentGroup

variable (A) in
/-- The class in the stable component group of an invertible matrix. -/
def mk (n : ℕ) : GL (Fin n) A →* StableComponentGroup A :=
  (QuotientGroup.mk' _).comp (StableGeneralLinearGroup.of A n)

/-- The class of an invertible matrix is its image in the quotient of `GL_∞(A)`. -/
theorem mk_apply (n : ℕ) (u : GL (Fin n) A) :
    mk A n u = (StableGeneralLinearGroup.of A n u : StableComponentGroup A) :=
  (rfl)

/-- The class of an invertible matrix is unchanged by stabilization. -/
@[simp]
theorem mk_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    mk A n (stabilizeGL A h u) = mk A m u := by
  simp [mk_apply]

/-- Every element of the stable component group is the class of an invertible matrix. -/
theorem exists_mk (x : StableComponentGroup A) : ∃ n u, mk A n u = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨n, u, rfl⟩ := StableGeneralLinearGroup.exists_of y
  exact ⟨n, u, rfl⟩

/-- The class of an invertible matrix is trivial exactly when some stabilization of it lies in
the identity component. -/
theorem mk_eq_one_iff {n : ℕ} {u : GL (Fin n) A} :
    mk A n u = 1 ↔
      ∃ k, ∃ h : n ≤ k,
        stabilizeGL A h u ∈ Subgroup.connectedComponentOfOne (GL (Fin k) A) := by
  rw [mk_apply, QuotientGroup.eq_one_iff,
    StableGeneralLinearGroup.of_mem_identityComponent_iff]

/-- Two invertible matrices of the same size have the same class exactly when they agree modulo
the identity component after some stabilization. -/
theorem mk_eq_mk_iff {n : ℕ} {u v : GL (Fin n) A} :
    mk A n u = mk A n v ↔
      ∃ k, ∃ h : n ≤ k,
        stabilizeGL A h (u⁻¹ * v) ∈ Subgroup.connectedComponentOfOne (GL (Fin k) A) := by
  rw [← mk_eq_one_iff, map_mul, map_inv, inv_mul_eq_one]

/-- Invertible matrices in the identity component have trivial class. -/
theorem mk_eq_one_of_mem_connectedComponentOfOne {n : ℕ} {u : GL (Fin n) A}
    (hu : u ∈ Subgroup.connectedComponentOfOne (GL (Fin n) A)) : mk A n u = 1 :=
  mk_eq_one_iff.2 ⟨n, le_rfl, by simpa using hu⟩

/-- Homomorphisms out of the stable component group agree when they agree on the classes of
invertible matrices of each size. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {f g : StableComponentGroup A →* G}
    (h : ∀ n, f.comp (mk A n) = g.comp (mk A n)) : f = g :=
  QuotientGroup.monoidHom_ext _ (StableGeneralLinearGroup.hom_ext h)

/-- The **universal property of the stable component group**: a family of homomorphisms out of
the groups `GL (Fin n) A` which is compatible with stabilization and trivial on each identity
component induces a homomorphism out of the stable component group. -/
def lift {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u)
    (hf₀ : ∀ n, Subgroup.connectedComponentOfOne (GL (Fin n) A) ≤ (f n).ker) :
    StableComponentGroup A →* G :=
  QuotientGroup.lift _ (StableGeneralLinearGroup.lift f hf) <| iSup_le fun n ↦
    Subgroup.map_le_iff_le_comap.2 <| by
      rw [MonoidHom.comap_ker]
      convert hf₀ n
      ext u
      exact StableGeneralLinearGroup.lift_of f hf n u

/-- The homomorphism induced by a compatible family sends the class of an invertible matrix to
its value under the family. -/
@[simp]
theorem lift_mk {G : Type*} [Monoid G] (f : ∀ n, GL (Fin n) A →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilizeGL A h u) = f m u)
    (hf₀ : ∀ n, Subgroup.connectedComponentOfOne (GL (Fin n) A) ≤ (f n).ker) (n : ℕ)
    (u : GL (Fin n) A) : lift f hf hf₀ (mk A n u) = f n u :=
  (QuotientGroup.lift_mk _ _ _).trans (StableGeneralLinearGroup.lift_of f hf n u)

/-- Over a connected topological ring, the stable component group is commutative, since the stable
identity component contains the commutator subgroup. -/
instance [PreconnectedSpace A] : IsMulCommutative (StableComponentGroup A) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2
    StableGeneralLinearGroup.commutator_le_identityComponent

open scoped IsMulCommutative in
/-- Over a connected topological ring, the stable component group is a commutative group. -/
instance [PreconnectedSpace A] : CommGroup (StableComponentGroup A) :=
  inferInstance

/-! ## Functoriality -/

section Map

variable {B C : Type*} [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [Ring C]
  [TopologicalSpace C] [IsTopologicalRing C]

/-- The homomorphism of stable component groups induced by a continuous ring homomorphism
`f : A →+* B`, applying `f` to the entries of invertible matrices. -/
def map (f : A →+* B) (hf : Continuous f) : StableComponentGroup A →* StableComponentGroup B :=
  lift (fun n ↦ (mk B n).comp (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom))
    (fun m n h u ↦ by simp only [MonoidHom.comp_apply, ← stabilizeGL_map, mk_stabilizeGL])
    fun n u hu ↦ mk_eq_one_of_mem_connectedComponentOfOne
      (Subgroup.map_connectedComponentOfOne_le (Units.continuous_map
        (continuous_id.matrix_map hf)) ⟨u, hu, rfl⟩)

/-- The induced homomorphism sends the class of an invertible matrix to the class of the matrix
obtained by applying the ring homomorphism to its entries. -/
@[simp]
theorem map_mk (f : A →+* B) (hf : Continuous f) (n : ℕ) (u : GL (Fin n) A) :
    map f hf (mk A n u) = mk B n (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom u) :=
  lift_mk ..

/-- The identity ring homomorphism induces the identity of the stable component group. -/
@[simp]
theorem map_id : map (RingHom.id A) continuous_id = MonoidHom.id (StableComponentGroup A) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp

/-- The stable component group is functorial for continuous ring homomorphisms. -/
theorem map_comp (f : A →+* B) (hf : Continuous f) (g : B →+* C) (hg : Continuous g) :
    map (g.comp f) (hg.comp hf) = (map g hg).comp (map f hf) := by
  refine hom_ext fun n ↦ MonoidHom.ext fun u ↦ ?_
  simp only [MonoidHom.comp_apply, map_mk]
  refine congrArg _ (Units.ext ?_)
  simp [Matrix.map_map]

/-- Applying the homomorphisms of stable component groups induced by `f` and then `g` is applying
the one induced by `g.comp f`. -/
@[simp]
theorem map_map (f : A →+* B) (hf : Continuous f) (g : B →+* C) (hg : Continuous g)
    (x : StableComponentGroup A) : map g hg (map f hf x) = map (g.comp f) (hg.comp hf) x := by
  rw [map_comp, MonoidHom.comp_apply]

end Map

end StableComponentGroup

/-! ## The comparison with algebraic `K₁` -/

namespace AlgebraicK1

variable [PreconnectedSpace A]

variable (A) in
/-- The **comparison of algebraic `K₁` with the stable component group** of a connected topological
ring: the projection `GL_∞(A) → GL_∞(A) / GL_∞(A)₀` factors through `K₁(A) = GL_∞(A) / E_∞(A)`
since `E_∞(A) ≤ GL_∞(A)₀`. -/
def toStableComponentGroup : AlgebraicK1 A →* StableComponentGroup A :=
  Group.Abelianization.lift (QuotientGroup.mk' _)

/-- The comparison sends the class in `K₁(A)` of an element of `GL_∞(A)` to its class in the
stable component group. -/
@[simp]
theorem toStableComponentGroup_of (x : StableGeneralLinearGroup A) :
    toStableComponentGroup A (Group.Abelianization.of x) = (x : StableComponentGroup A) :=
  Group.Abelianization.lift_apply_of _ _

/-- The comparison composed with the abelianization map `GL_∞(A) → K₁(A)` is the quotient map
`GL_∞(A) → GL_∞(A) / GL_∞(A)₀`. -/
theorem toStableComponentGroup_comp_of :
    (toStableComponentGroup A).comp Group.Abelianization.of = QuotientGroup.mk' _ :=
  MonoidHom.ext toStableComponentGroup_of

/-- The comparison sends the class in `K₁(A)` of an invertible matrix to its class in the stable
component group. -/
@[simp]
theorem toStableComponentGroup_mk (n : ℕ) (u : GL (Fin n) A) :
    toStableComponentGroup A (mk A n u) = StableComponentGroup.mk A n u := by
  rw [mk_apply, toStableComponentGroup_of, StableComponentGroup.mk_apply]

/-- The comparison of algebraic `K₁` with the stable component group is surjective. -/
theorem toStableComponentGroup_surjective : Function.Surjective (toStableComponentGroup A) := by
  intro x
  obtain ⟨n, u, rfl⟩ := StableComponentGroup.exists_mk x
  exact ⟨mk A n u, toStableComponentGroup_mk n u⟩

/-- The kernel of the comparison of algebraic `K₁` with the stable component group is the image
of the stable identity component. -/
theorem ker_toStableComponentGroup :
    (toStableComponentGroup A).ker =
      (StableGeneralLinearGroup.identityComponent A).map Group.Abelianization.of := by
  -- The abelianization map is surjective, so the kernel is the image of its preimage.
  rw [← Subgroup.map_comap_eq_self_of_surjective (Group.Abelianization.surjective_of _)
      (toStableComponentGroup A).ker,
    MonoidHom.comap_ker, toStableComponentGroup_comp_of, QuotientGroup.ker_mk']

/-- The comparison of algebraic `K₁` with the stable component group is natural for continuous
ring homomorphisms. -/
theorem toStableComponentGroup_map {B : Type*} [Ring B] [TopologicalSpace B]
    [IsTopologicalRing B] [PreconnectedSpace B] (f : A →+* B) (hf : Continuous f)
    (x : AlgebraicK1 A) :
    toStableComponentGroup B (map f x) =
      StableComponentGroup.map f hf (toStableComponentGroup A x) := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  simp

end AlgebraicK1

end Topology

end TauCeti
