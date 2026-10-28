/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
public import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The canonical Clifford extension

For a representation `A` of a normal subgroup `N`, consider pairs `(t, U)` where `t` belongs
to the inertia group and `U` implements conjugation by `t` on the given `N`-action. The diagonal
pairs `(n, A n)` form a normal subgroup. Dividing by them gives the canonical Clifford extension
of the inertia quotient by the units of the actual equivariant endomorphism algebra.

This construction retains nonscalar endomorphisms and does not require algebraic closure,
simplicity, or a finite ambient group. It supplies the group in which the obstruction to
extending the specified `N`-action can be studied without choosing intertwining operators.

The implementing operators come from `TauCeti.mem_inertia_iff_exists_linearEquiv`. Kernel
identification uses Mathlib's `CategoryTheory.Aut.unitsEndEquivAut`; the quotient and its
universal property are Mathlib's `QuotientGroup`.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti.CliffordExtension

open CategoryTheory

universe u v

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [N.Normal]

section CommRing

variable [CommRing k] (A : FDRep k N)

/-- Pairs of inertia elements and operators implementing their conjugation on `N`. -/
def implementers : Subgroup (inertia A × (A ≃ₗ[k] A)) where
  carrier := {p | ∀ n x, p.2 (A.ρ n x) = A.ρ (MulAut.conjNormal (p.1 : G) n) (p.2 x)}
  one_mem' := by simp
  mul_mem' {p q} hp hq := by
    intro n x
    simpa [map_mul] using (congrArg p.2 (hq n x)).trans (hp _ (q.2 x))
  inv_mem' {p} hp := by
    intro n x
    apply p.2.injective
    simpa using (hp (MulAut.conjNormal (p.1 : G)⁻¹ n) (p.2.symm x)).symm

@[simp]
theorem mem_implementers_iff (p : inertia A × (A ≃ₗ[k] A)) :
    p ∈ implementers A ↔
      ∀ n x, p.2 (A.ρ n x) = A.ρ (MulAut.conjNormal (p.1 : G) n) (p.2 x) := Iff.rfl

/-- Projection of implementing pairs to the inertia group. -/
noncomputable def projection : implementers A →* inertia A :=
  (MonoidHom.fst _ _).comp (implementers A).subtype

@[simp]
theorem projection_apply (p : implementers A) : projection A p = p.1.1 := (rfl)

/-- The diagonal copy of `N`, pairing each element with its given action. -/
noncomputable def diagonal : N →* implementers A :=
  let r : N →* (A ≃ₗ[k] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp A.ρ.toHomUnits
  (Subgroup.inclusion (le_inertia A)).prod r |>.codRestrict (implementers A)
    (fun n => by
      intro m x
      exact Representation.apply_conjNormal_coe A.ρ n m x)

@[simp]
theorem diagonal_fst (n : N) : (diagonal A n).1.1 = Subgroup.inclusion (le_inertia A) n :=
  (rfl)

@[simp]
theorem diagonal_snd_apply (n : N) (x : A) : (diagonal A n).1.2 x = A.ρ n x := (rfl)

/-- The diagonal is faithful even if the original representation is not. -/
theorem diagonal_injective : Function.Injective (diagonal A) := by
  intro n m h
  apply Subtype.ext
  simpa using congrArg (fun p : implementers A => (p.1.1 : G)) h

/-- Conjugating a diagonal pair gives the diagonal pair for the conjugated element. -/
theorem mul_diagonal_mul_inv (p : implementers A) (n : N) :
    p * diagonal A n * p⁻¹ = diagonal A (MulAut.conjNormal (p.1.1 : G) n) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp [mul_assoc]
  · ext x
    simpa using p.2 n (p.1.2.symm x)

/-- The given `N`-action embeds as a normal subgroup of the implementing group. -/
instance diagonal_range_normal : (diagonal A).range.Normal where
  conj_mem n hn p := by
    obtain ⟨n, rfl⟩ := hn
    exact ⟨MulAut.conjNormal (p.1.1 : G) n, (mul_diagonal_mul_inv A p n).symm⟩

/-- The canonical Clifford group: implementing pairs modulo the diagonal `N`-action. -/
@[expose]
def Carrier := implementers A ⧸ (diagonal A).range

/-- The group structure on the canonical Clifford quotient. -/
noncomputable instance : Group (Carrier A) :=
  inferInstanceAs (Group (implementers A ⧸ (diagonal A).range))

/-- The quotient of the inertia group by the original normal subgroup. -/
abbrev Quotient := inertia A ⧸ N.subgroupOf (inertia A)

/-- Projection of the Clifford group to the inertia quotient. -/
noncomputable def rightHom : Carrier A →* Quotient A :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (projection A)) (by
    rintro _ ⟨n, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, projection_apply, diagonal_fst]
    exact (QuotientGroup.eq_one_iff _).mpr n.2)

@[simp]
theorem rightHom_mk (p : implementers A) :
    rightHom A (QuotientGroup.mk p) = QuotientGroup.mk p.1.1 := (rfl)

/-- An implementing pair is determined by its inertia element and its Clifford class. -/
theorem implementer_ext {p q : implementers A} (ht : projection A p = projection A q)
    (hc : (QuotientGroup.mk p : Carrier A) = QuotientGroup.mk q) : p = q := by
  obtain ⟨n, hn⟩ := QuotientGroup.eq.mp hc
  have hn1 : n = 1 := by
    apply Subtype.ext
    have hp : projection A (diagonal A n) = 1 := by
      rw [hn, map_mul, map_inv, ht, inv_mul_cancel]
    simpa only [projection_apply, diagonal_fst, Subgroup.coe_one, Subgroup.coe_inclusion] using
      congrArg Subtype.val hp
  have h : p⁻¹ * q = 1 := by simpa [hn1] using hn.symm
  exact inv_mul_eq_one.mp h

/-- Compatible inertia elements and Clifford classes have a unique implementing pair. -/
theorem existsUnique_implementer (t : inertia A) (c : Carrier A)
    (h : (QuotientGroup.mk t : Quotient A) = rightHom A c) :
    ∃! p : implementers A, projection A p = t ∧ QuotientGroup.mk p = c := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective c
  rw [rightHom_mk] at h
  have hn : (t / projection A p : inertia A) ∈ N.subgroupOf (inertia A) :=
    QuotientGroup.eq_iff_div_mem.mp (by simpa only [projection_apply] using h)
  let n : N := ⟨(t / projection A p : inertia A), Subgroup.mem_subgroupOf.mp hn⟩
  have ht : projection A (diagonal A n * p) = t := by
    apply Subtype.ext
    simp [n, div_eq_mul_inv]
  have hdiag : (QuotientGroup.mk (diagonal A n) : Carrier A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨n, rfl⟩
  have hc : (QuotientGroup.mk (diagonal A n * p) : Carrier A) = QuotientGroup.mk p := by
    rw [QuotientGroup.mk_mul, hdiag, one_mul]
  exact ⟨diagonal A n * p, ⟨ht, hc⟩, fun q hq => implementer_ext A (hq.1.trans ht.symm)
    (hq.2.trans hc.symm)⟩

/-- Equivariant automorphisms, inserted as implementing pairs over the identity. -/
noncomputable def kernelLift : (End A)ˣ →* implementers A where
  toFun d := ⟨(1, FDRep.isoToLinearEquiv (Aut.unitsEndEquivAut A d).asIso), by
    intro n x
    simp only [Subgroup.coe_one, map_one, MulAut.one_apply]
    exact LinearMap.congr_fun (FDRep.hom_hom_hom_comm d.val.asHom n) x⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext rfl
    ext x
    rfl
  map_mul' d e := by
    apply Subtype.ext
    refine Prod.ext (by simp) ?_
    ext x
    rfl

@[simp]
theorem kernelLift_fst (d : (End A)ˣ) : (kernelLift A d).1.1 = 1 := (rfl)

@[simp]
theorem kernelLift_snd_apply (d : (End A)ˣ) (x : A) :
    (kernelLift A d).1.2 x = d.val.asHom.hom.hom.hom x := (rfl)

/-- Invertible equivariant endomorphisms inject into the implementing group. -/
theorem kernelLift_injective : Function.Injective (kernelLift A) := by
  intro d e h
  apply Units.ext
  apply End.ext
  ext x
  exact congrArg (fun p : implementers A => p.1.2 x) h

/-- The kernel of projection consists exactly of equivariant automorphisms. -/
theorem range_kernelLift_eq_ker_projection : (kernelLift A).range = (projection A).ker := by
  ext p
  constructor
  · rintro ⟨d, rfl⟩
    exact kernelLift_fst A d
  · intro hp
    have ht : p.1.1 = 1 := hp
    have hU : ∀ n x, p.1.2 (A.ρ n x) = A.ρ n (p.1.2 x) := by
      intro n x
      simpa only [ht, Subgroup.coe_one, map_one, MulAut.one_apply] using p.2 n x
    let e : A ≅ A := Action.mkIso p.1.2.toFGModuleCatIso fun n =>
      FGModuleCat.hom_ext (by simpa using LinearMap.ext (hU n))
    refine ⟨(Aut.unitsEndEquivAut A).symm (Aut.of e), ?_⟩
    apply Subtype.ext
    apply Prod.ext ht.symm
    ext x
    rw [kernelLift_snd_apply]
    rfl

/-- Inclusion of endomorphism units in the canonical Clifford group. -/
noncomputable def inl : (End A)ˣ →* Carrier A :=
  (QuotientGroup.mk' _).comp (kernelLift A)

@[simp]
theorem inl_apply (d : (End A)ˣ) : inl A d = QuotientGroup.mk (kernelLift A d) := (rfl)

/-- No nonidentity equivariant automorphism is killed by dividing by diagonal pairs. -/
theorem inl_injective : Function.Injective (inl A) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro d hd
  obtain ⟨n, hn⟩ := (QuotientGroup.eq_one_iff (kernelLift A d)).mp hd
  have hn1 : n = 1 := by
    apply Subtype.ext
    simpa using congrArg (fun p : implementers A => (p.1.1 : G)) hn
  have hd1 : kernelLift A d = 1 := by simpa [hn1] using hn.symm
  exact (kernelLift_injective A (hd1.trans (map_one _).symm))

/-- Exactness of the Clifford group at its middle term. -/
theorem range_inl_eq_ker_rightHom : (inl A).range = (rightHom A).ker := by
  ext c
  refine QuotientGroup.induction_on c fun p => ?_
  constructor
  · rintro ⟨d, hd⟩
    rw [← hd]
    rw [MonoidHom.mem_ker, inl_apply, rightHom_mk, kernelLift_fst]
    exact map_one (QuotientGroup.mk' _)
  · intro hp
    have ht : (p.1.1 : G) ∈ N := (QuotientGroup.eq_one_iff p.1.1).mp hp
    let n : N := ⟨p.1.1, ht⟩
    have hk : p * (diagonal A n)⁻¹ ∈ (projection A).ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, projection_apply, diagonal_fst]
      exact mul_inv_eq_one.mpr (Subtype.ext rfl)
    obtain ⟨d, hd⟩ := (range_kernelLift_eq_ker_projection A).symm ▸ hk
    refine ⟨d, ?_⟩
    rw [inl_apply, hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hn : (QuotientGroup.mk (diagonal A n) : Carrier A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨n, rfl⟩
    simp only [hn, inv_one, mul_one]
    rfl

end CommRing

section Field

variable [Field k] (A : FDRep k N)

/-- Every inertia element has an implementing operator, over an arbitrary field. -/
theorem projection_surjective : Function.Surjective (projection A) := by
  intro t
  obtain ⟨U, hU⟩ := mem_inertia_iff_exists_linearEquiv.mp t.2
  exact ⟨⟨(t, U), hU⟩, rfl⟩

/-- The canonical Clifford group maps onto the inertia quotient. -/
theorem rightHom_surjective : Function.Surjective (rightHom A) :=
  QuotientGroup.lift_surjective_of_surjective _ ((QuotientGroup.mk' _).comp (projection A))
    ((QuotientGroup.mk'_surjective _).comp (projection_surjective A)) _

/-- The canonical Clifford extension of `T/N` by `End_N(A)ˣ`, where `T` is inertia.
The kernel need not be central; no scalar-Schur hypothesis is used. -/
noncomputable def groupExtension : GroupExtension (End A)ˣ (Carrier A) (Quotient A) where
  inl := inl A
  rightHom := rightHom A
  inl_injective := inl_injective A
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom A
  rightHom_surjective := rightHom_surjective A

@[simp]
theorem groupExtension_inl : (groupExtension A).inl = inl A := (rfl)

@[simp]
theorem groupExtension_rightHom : (groupExtension A).rightHom = rightHom A := (rfl)

end Field

end TauCeti.CliffordExtension
