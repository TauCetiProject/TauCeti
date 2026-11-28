/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic
public import TauCeti.Algebra.Group.Subgroup.Conjugates
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# Conjugacy classes of transitive permutation groups

The table of transitive groups of degree `n` lists one subgroup of `Equiv.Perm (Fin n)` for each
conjugacy class of transitive subgroups, conjugacy being taken in the full symmetric group. This
file defines the type of these classes and compares it with the labels of the reference family.

A subgroup of `Equiv.Perm α` is conjugated by `τ` as `G.map (MulAut.conj τ).toMonoidHom`, which is
the pointwise action of `ConjAct (Equiv.Perm α)` on `Subgroup (Equiv.Perm α)`. Transitivity is
invariant under conjugation (`Equiv.isPretransitive_map_conj_iff`), so an orbit of this action
that contains one transitive subgroup consists of transitive subgroups
(`TauCeti.TransitiveSubgroupClass.isPretransitive_of_mk_eq`).

An equivalence `α ≃ β` transports subgroups of `Equiv.Perm α` to subgroups of `Equiv.Perm β`, and
so identifies the conjugacy classes of transitive subgroups on both sides. Two equivalences
differ by a permutation of `β`, which acts trivially on conjugacy classes, so the identification
does not depend on the equivalence. In particular the classes of transitive subgroups of the
symmetric group on any `n`-element set are those of `Equiv.Perm (Fin n)`.

The labels of the reference family are compared with the classes through the class of each
reference subgroup: a subgroup carries the label `j` exactly when it lies in the class of the
reference subgroup of `j`. So the reference classes enumerate the classes without repetition
exactly when every transitive subgroup carries exactly one label. In degrees one to five this is
the native classification, and the classes number `1, 1, 2, 5, 5`. In degree zero there is one
class, that of the trivial group, which acts transitively on the empty set, but no label.

## Main definitions

* `TauCeti.TransitiveSubgroupClass α`: the conjugacy classes of transitive subgroups of
  `Equiv.Perm α`.
* `TauCeti.TransitiveSubgroupClass.mk`: the class of a transitive subgroup.
* `TauCeti.TransitiveSubgroupClass.congr`: the classes on `α` and on `β` are identified by an
  equivalence `α ≃ β`.
* `TauCeti.TransitiveSubgroupClass.reference`: the class of the reference subgroup of a label.

## Main results

* `TauCeti.TransitiveSubgroupClass.mk_eq_mk_iff`: two transitive subgroups have the same class
  exactly when they are conjugate.
* `TauCeti.TransitiveSubgroupClass.congr_eq_congr`: the identification along an equivalence does
  not depend on the equivalence.
* `TauCeti.TransitiveSubgroupClass.mk_eq_reference_iff`: a transitive subgroup lies in the class
  of the reference subgroup of `j` exactly when it carries the label `j`.
* `TauCeti.TransitiveSubgroupClass.reference_bijective_iff`: the reference classes enumerate the
  classes exactly when every transitive subgroup carries exactly one label, which in degrees one
  to five is `TauCeti.existsUnique_transitiveGroupLabel`
  (`TauCeti.TransitiveSubgroupClass.reference_bijective`).
* `TauCeti.natCard_transitiveSubgroupClass_fin`: in degrees one to five the number of classes is
  the number `1, 1, 2, 5, 5` of labels; `TauCeti.natCard_transitiveSubgroupClass_fin_zero`: in
  degree zero there is one class.

## References

* G. Butler and J. McKay, *The transitive groups of degree up to eleven*, Comm. Algebra 11
  (1983), 863–911.
* J. H. Conway, A. Hulpke and J. McKay, *On transitive permutation groups*, LMS J. Comput. Math.
  1 (1998), 1–8.
-/

public section

open Equiv MulAction
open scoped Pointwise

namespace TauCeti

variable {α β : Type*}

/-- The **conjugacy classes of transitive subgroups** of `Equiv.Perm α`: the orbits of
`ConjAct (Equiv.Perm α)`, acting on `Subgroup (Equiv.Perm α)` by conjugation, that contain a
subgroup acting transitively on `α`. Such an orbit consists of transitive subgroups
(`TauCeti.TransitiveSubgroupClass.isPretransitive_of_mk_eq`). For `α = Fin n` these are the classes
that the table of transitive groups of degree `n` lists. -/
@[ext]
structure TransitiveSubgroupClass (α : Type*) where
  /-- The class with a given orbit, which contains a transitive subgroup. -/
  ofOrbit ::
  /-- The orbit of conjugation underlying a class of transitive subgroups. -/
  orbit : orbitRel.Quotient (ConjAct (Perm α)) (Subgroup (Perm α))
  /-- The orbit contains a transitive subgroup. -/
  exists_isPretransitive : ∃ G : Subgroup (Perm α), Quotient.mk'' G = orbit ∧ IsPretransitive G α

namespace TransitiveSubgroupClass

/-- A class is determined by its orbit. -/
theorem orbit_injective :
    Function.Injective (orbit : TransitiveSubgroupClass α → _) :=
  fun _ _ ↦ TransitiveSubgroupClass.ext

/-- The conjugacy class of a transitive subgroup of `Equiv.Perm α`. -/
def mk (G : Subgroup (Perm α)) (hG : IsPretransitive G α) : TransitiveSubgroupClass α :=
  ⟨Quotient.mk'' G, G, rfl, hG⟩

@[simp]
theorem orbit_mk (G : Subgroup (Perm α)) (hG : IsPretransitive G α) :
    (mk G hG).orbit = Quotient.mk'' G :=
  (rfl)

/-- Every class is the class of a transitive subgroup. -/
theorem exists_mk_eq (c : TransitiveSubgroupClass α) :
    ∃ (G : Subgroup (Perm α)) (hG : IsPretransitive G α), mk G hG = c := by
  obtain ⟨c, G, rfl, hG⟩ := c
  exact ⟨G, hG, rfl⟩

/-- Induction on classes of transitive subgroups: a property holding for the class of every
transitive subgroup holds for every class. -/
@[elab_as_elim]
theorem ind {P : TransitiveSubgroupClass α → Prop}
    (h : ∀ (G : Subgroup (Perm α)) (hG : IsPretransitive G α), P (mk G hG))
    (c : TransitiveSubgroupClass α) : P c := by
  obtain ⟨G, hG, rfl⟩ := c.exists_mk_eq
  exact h G hG

/-- **Every subgroup in the orbit of a class is transitive**: transitivity is a conjugation
invariant, so an orbit containing one transitive subgroup consists of transitive subgroups. -/
theorem isPretransitive_of_mk_eq (c : TransitiveSubgroupClass α) {G : Subgroup (Perm α)}
    (hG : Quotient.mk'' G = c.orbit) : IsPretransitive G α := by
  obtain ⟨c, H, rfl, hH⟩ := c
  have hGH : G ∈ MulAction.orbit (ConjAct (Perm α)) H := orbitRel_apply.mp (Quotient.eq''.mp hG)
  obtain ⟨τ, rfl⟩ := mem_orbit_conjAct_iff.mp hGH
  exact (isPretransitive_map_conj_iff τ H).mpr hH

/-- Two transitive subgroups have the same class exactly when they are conjugate. -/
theorem mk_eq_mk_iff {G H : Subgroup (Perm α)} {hG : IsPretransitive G α}
    {hH : IsPretransitive H α} :
    mk G hG = mk H hH ↔ ∃ τ : Perm α, G.map (MulAut.conj τ).toMonoidHom = H := by
  rw [← orbit_injective.eq_iff, orbit_mk, orbit_mk, eq_comm, Quotient.eq'', orbitRel_apply,
    mem_orbit_conjAct_iff]
  simp only [MulEquiv.toMonoidHom_eq_coe]

/-- The class of a conjugate of a transitive subgroup is the class of the subgroup. -/
@[simp]
theorem mk_map_conj (τ : Perm α) (G : Subgroup (Perm α))
    (hG : IsPretransitive (G.map (MulAut.conj τ : Perm α →* Perm α)) α) :
    mk (G.map (MulAut.conj τ : Perm α →* Perm α)) hG =
      mk G ((isPretransitive_map_conj_iff τ G).mp hG) := by
  rw [eq_comm, mk_eq_mk_iff]
  exact ⟨τ, by rw [MulEquiv.toMonoidHom_eq_coe]⟩

instance [Finite α] : Finite (TransitiveSubgroupClass α) :=
  have : Finite (Subgroup (Perm α)) := Finite.of_injective _ SetLike.coe_injective
  Finite.of_injective _ orbit_injective

/-! ### Transport along an equivalence -/

/-- A class of transitive subgroups is an orbit containing a transitive subgroup. -/
private def equivSubtype : TransitiveSubgroupClass α ≃
    {c : orbitRel.Quotient (ConjAct (Perm α)) (Subgroup (Perm α)) //
      ∃ G : Subgroup (Perm α), Quotient.mk'' G = c ∧ IsPretransitive G α} where
  toFun c := ⟨c.orbit, c.exists_isPretransitive⟩
  invFun c := ofOrbit c.val c.property

/-- The conjugacy class of a subgroup contains a transitive subgroup exactly when the subgroup is
transitive. -/
theorem exists_isPretransitive_mk_iff (G : Subgroup (Perm α)) :
    (∃ H : Subgroup (Perm α), Quotient.mk'' H = (Quotient.mk'' G :
      orbitRel.Quotient (ConjAct (Perm α)) (Subgroup (Perm α))) ∧ IsPretransitive H α) ↔
      IsPretransitive G α :=
  ⟨fun hG ↦ isPretransitive_of_mk_eq (ofOrbit _ hG) rfl, fun hG ↦ ⟨G, rfl, hG⟩⟩

/-- Transport along an equivalence `e : α ≃ β` sends exactly the conjugacy classes of subgroups of
`Equiv.Perm α` that contain a transitive subgroup to those of `Equiv.Perm β` that contain one. -/
theorem exists_isPretransitive_orbitRelQuotientSubgroupEquiv_iff (e : α ≃ β)
    (c : orbitRel.Quotient (ConjAct (Perm α)) (Subgroup (Perm α))) :
    (∃ H : Subgroup (Perm β),
      Quotient.mk'' H = e.permCongrHom.orbitRelQuotientSubgroupEquiv c ∧ IsPretransitive H β) ↔
      ∃ G : Subgroup (Perm α), Quotient.mk'' G = c ∧ IsPretransitive G α := by
  induction c using Quotient.inductionOn' with
  | h G =>
    rw [MulEquiv.orbitRelQuotientSubgroupEquiv_mk, exists_isPretransitive_mk_iff,
      exists_isPretransitive_mk_iff, ← MulEquiv.toMonoidHom_eq_coe,
      isPretransitive_map_permCongrHom_iff]

/-- **Transport of classes along an equivalence.** An equivalence `e : α ≃ β` identifies the
conjugacy classes of transitive subgroups of `Equiv.Perm α` and of `Equiv.Perm β`, sending the
class of `G` to the class of its transport along `e`. By
`TauCeti.TransitiveSubgroupClass.congr_eq_congr` the identification does not depend on `e`. -/
def congr (e : α ≃ β) : TransitiveSubgroupClass α ≃ TransitiveSubgroupClass β :=
  equivSubtype.trans <| (e.permCongrHom.orbitRelQuotientSubgroupEquiv.subtypeEquiv fun c ↦
    (exists_isPretransitive_orbitRelQuotientSubgroupEquiv_iff e c).symm).trans equivSubtype.symm

/-- The orbit of the transport of a class is the transport of its orbit; this unfolds `congr`. -/
@[simp]
theorem orbit_congr (e : α ≃ β) (c : TransitiveSubgroupClass α) :
    (congr e c).orbit = e.permCongrHom.orbitRelQuotientSubgroupEquiv c.orbit :=
  (rfl)

/-- The transport of the class of `G` along `e` is the class of the transport of `G`. -/
@[simp]
theorem congr_mk (e : α ≃ β) (G : Subgroup (Perm α)) (hG : IsPretransitive G α) :
    congr e (mk G hG) = mk (G.map e.permCongrHom.toMonoidHom)
      ((isPretransitive_map_permCongrHom_iff e G).mpr hG) := by
  ext1
  rw [orbit_congr, orbit_mk, orbit_mk, MulEquiv.orbitRelQuotientSubgroupEquiv_mk,
    MulEquiv.toMonoidHom_eq_coe]

/-- The transport along the identity is the identity. -/
@[simp]
theorem congr_refl : congr (Equiv.refl α) = Equiv.refl _ := by
  refine Equiv.ext fun c ↦ ?_
  induction c using ind with
  | h G hG =>
    rw [congr_mk, Equiv.refl_apply, mk_eq_mk_iff]
    exact ⟨1, by ext; simp [← Perm.one_def]⟩

/-- Transporting along `e` and then along `f` is transporting along `e.trans f`. -/
@[simp]
theorem congr_trans {γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (congr e).trans (congr f) = congr (e.trans f) := by
  refine Equiv.ext fun c ↦ ?_
  induction c using ind with
  | h G hG =>
    ext1
    rw [Equiv.trans_apply, congr_mk, congr_mk, congr_mk, orbit_mk, orbit_mk, Subgroup.map_map]
    simp only [MulEquiv.toMonoidHom_eq_coe]
    rw [← MulEquiv.toMonoidHom_trans, Equiv.permCongrHom_trans]

/-- The inverse of the transport along `e` is the transport along `e.symm`. -/
@[simp]
theorem congr_symm (e : α ≃ β) : (congr e).symm = congr e.symm :=
  Equiv.symm_eq_iff_trans_eq_refl.mpr <| by rw [congr_trans, Equiv.self_trans_symm, congr_refl]

/-- **The transport of classes does not depend on the equivalence.** Two equivalences
`e e' : α ≃ β` differ by the permutation `e.symm.trans e'` of `β`, and conjugation by a
permutation fixes every conjugacy class. -/
theorem congr_eq_congr (e e' : α ≃ β) : congr e = congr e' := by
  refine Equiv.ext fun c ↦ ?_
  induction c using ind with
  | h G hG =>
    rw [congr_mk, congr_mk, mk_eq_mk_iff]
    exact ⟨e.symm.trans e', (map_permCongrHom_eq_map_conj e e' G).symm⟩

/-! ### Reference classes -/

/-- The class of the reference subgroup of the label `j`. -/
def reference (n : ℕ) (j : TransitiveGroupIndex n) : TransitiveSubgroupClass (Fin n) :=
  mk (referenceSubgroup n j) (isPretransitive_referenceSubgroup n j)

/-- **Labels are classes.** A transitive subgroup lies in the class of the reference subgroup of
`j` exactly when it carries the label `j`. -/
@[simp]
theorem mk_eq_reference_iff {n : ℕ} {j : TransitiveGroupIndex n} {G : Subgroup (Perm (Fin n))}
    {hG : IsPretransitive G (Fin n)} :
    mk G hG = reference n j ↔ TransitiveGroupLabel j G :=
  mk_eq_mk_iff.trans (transitiveGroupLabel_iff j G).symm

/-- **Enumeration of the classes by labels.** The reference classes enumerate the conjugacy
classes of transitive subgroups of `Equiv.Perm (Fin n)` without repetition exactly when every
transitive subgroup carries exactly one label. -/
theorem reference_bijective_iff {n : ℕ} :
    Function.Bijective (reference n) ↔
      ∀ G : Subgroup (Perm (Fin n)), IsPretransitive G (Fin n) →
        ∃! j, TransitiveGroupLabel j G := by
  constructor
  · rintro ⟨hinj, hsurj⟩ G hG
    obtain ⟨j, hj⟩ := hsurj (mk G hG)
    refine ⟨j, mk_eq_reference_iff.mp hj.symm, fun k hk ↦ hinj ?_⟩
    rw [hj, mk_eq_reference_iff.mpr hk]
  · intro h
    refine ⟨fun j k hjk ↦ ?_, fun c ↦ ?_⟩
    · have hj : TransitiveGroupLabel j (referenceSubgroup n j) := mk_eq_reference_iff.mp rfl
      have hk : TransitiveGroupLabel k (referenceSubgroup n j) := mk_eq_reference_iff.mp hjk
      exact (h _ (isPretransitive_referenceSubgroup n j)).unique hj hk
    · induction c using ind with
      | h G hG =>
        obtain ⟨j, hj, -⟩ := h G hG
        exact ⟨j, (mk_eq_reference_iff.mpr hj).symm⟩

/-- In degrees one to five the reference classes enumerate the conjugacy classes of transitive
subgroups without repetition. -/
theorem reference_bijective {n : ℕ} (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    Function.Bijective (reference n) :=
  reference_bijective_iff.mpr fun G _ ↦ existsUnique_transitiveGroupLabel h1 h5 G

end TransitiveSubgroupClass

open TransitiveSubgroupClass

/-- **The number of transitive groups in degrees one to five.** For `1 ≤ n ≤ 5` the symmetric group
on `n` points has `1, 1, 2, 5, 5` conjugacy classes of transitive subgroups, one for each label. -/
theorem natCard_transitiveSubgroupClass_fin {n : ℕ} (h1 : 1 ≤ n) (h5 : n ≤ 5) :
    Nat.card (TransitiveSubgroupClass (Fin n)) = numTransitiveGroups n := by
  rw [← Nat.card_eq_of_bijective _ (reference_bijective h1 h5), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- In degree zero there is one conjugacy class of transitive subgroups, that of the trivial
group, which acts transitively on the empty set; there is no label in degree zero. -/
theorem natCard_transitiveSubgroupClass_fin_zero :
    Nat.card (TransitiveSubgroupClass (Fin 0)) = 1 := by
  have hG : IsPretransitive (⊤ : Subgroup (Perm (Fin 0))) (Fin 0) := ⟨fun x ↦ x.elim0⟩
  have : Subsingleton (Subgroup (Perm (Fin 0))) := Subgroup.subsingleton_iff.mpr inferInstance
  refine Nat.card_eq_one_iff_exists.mpr ⟨mk ⊤ hG, fun c ↦ ?_⟩
  induction c using ind with
  | h G _ => exact mk_eq_mk_iff.mpr ⟨1, Subsingleton.elim _ _⟩

end TauCeti
