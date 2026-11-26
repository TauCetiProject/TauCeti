/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.Algebra.DualNumber.Map

/-!
# Infinitesimal automorphisms and derivations

An automorphism of `A[ε]` over `R` that fixes `ε` and reduces to the identity modulo `ε`
is uniquely of the form `a + b ε ↦ a + (b + d a) ε`, for an `R`-derivation `d` of `A`.
Composition corresponds to addition of derivations. Fixing `ε` is essential: reduction to
identity alone would also allow changes of the infinitesimal parameter.

These are the affine infinitesimal automorphisms of the trivial first-order deformation.
The conditions for such automorphisms to commute with a morphism are the corresponding
compatibility conditions on derivations; in particular, fixing a target map or a marking
amounts to a vanishing condition on the derivation.

The automorphism `TauCeti.derivationLieAlgebra.toDualNumberAut` is built for derivations of a
not necessarily commutative algebra, using `DualNumber.lift` to extend `a ↦ a + (D a) ε` to the
dual numbers; `Derivation.toDualNumberAut` is its commutative case through
`TauCeti.derivationEquivDerivationLieAlgebra`.
The group isomorphism `TauCeti.derivationLieAlgebra.equivInfinitesimalDualNumberAut` identifies
derivations of a not necessarily commutative algebra, with addition written multiplicatively,
with the subgroup `TauCeti.infinitesimalDualNumberAut`; its inverse reads off the coefficient of
`ε` in the image of a constant. The commutative
`TauCeti.derivationEquivInfinitesimalDualNumberAut` is obtained from it through
`TauCeti.derivationEquivDerivationLieAlgebra`.

## References

* R. Hartshorne, *Deformation Theory*, Chapter 1, for infinitesimal automorphisms
  as derivations.
-/

public section

open TrivSqZeroExt DualNumber

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The algebra map `a ↦ a + (D a) ε` attached to a derivation; its multiplicativity is the
Leibniz rule. -/
private def toDualNumberAlgHom (D : derivationLieAlgebra R A) : A →ₐ[R] A[ε] where
  toFun a := inl a + inr ((D : Module.End R A) a)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_add_add_comm]
  commutes' r := by ext <;> simp [algebraMap_eq_inl']

private def dualNumberEnd (D : derivationLieAlgebra R A) : A[ε] →ₐ[R] A[ε] :=
  DualNumber.lift ⟨(toDualNumberAlgHom D, ε), eps_mul_eps, fun a ↦ by
    ext <;> simp [toDualNumberAlgHom]⟩

private theorem dualNumberEnd_fst (D : derivationLieAlgebra R A) (z : A[ε]) :
    (dualNumberEnd D z).fst = z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply, toDualNumberAlgHom]

private theorem dualNumberEnd_snd (D : derivationLieAlgebra R A) (z : A[ε]) :
    (dualNumberEnd D z).snd = z.snd + (D : Module.End R A) z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply, toDualNumberAlgHom, add_comm]

/-- The infinitesimal automorphism `a + b ε ↦ a + (b + D a) ε` attached to a derivation `D`.
Its inverse is the automorphism attached to `-D`. -/
def toDualNumberAut (D : derivationLieAlgebra R A) : A[ε] ≃ₐ[R] A[ε] :=
  AlgEquiv.ofAlgHom (dualNumberEnd D) (dualNumberEnd (-D))
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])

/-- An infinitesimal automorphism leaves the scalar part unchanged. -/
@[simp]
theorem toDualNumberAut_fst (D : derivationLieAlgebra R A) (z : A[ε]) :
    (toDualNumberAut D z).fst = z.fst :=
  dualNumberEnd_fst D z

/-- The infinitesimal part changes by the derivation of the scalar part. -/
@[simp]
theorem toDualNumberAut_snd (D : derivationLieAlgebra R A) (z : A[ε]) :
    (toDualNumberAut D z).snd = z.snd + (D : Module.End R A) z.fst :=
  dualNumberEnd_snd D z

/-- An infinitesimal automorphism fixes `ε`. -/
@[simp]
theorem toDualNumberAut_eps (D : derivationLieAlgebra R A) : toDualNumberAut D ε = ε := by
  ext <;> simp

@[simp]
theorem toDualNumberAut_zero : toDualNumberAut (0 : derivationLieAlgebra R A) = 1 := by
  ext z <;> simp

/-- Addition of derivations corresponds to composition of infinitesimal automorphisms. -/
@[simp]
theorem toDualNumberAut_add (D E : derivationLieAlgebra R A) :
    toDualNumberAut (D + E) = toDualNumberAut D * toDualNumberAut E := by
  ext z <;> simp [add_left_comm, add_comm]

@[simp]
theorem toDualNumberAut_neg (D : derivationLieAlgebra R A) :
    toDualNumberAut (-D) = (toDualNumberAut D)⁻¹ := by
  ext z <;> simp [toDualNumberAut, dualNumberEnd_fst, dualNumberEnd_snd]

end TauCeti.derivationLieAlgebra

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The infinitesimal automorphism `a + b ε ↦ a + (b + d a) ε` attached to a derivation: the
commutative case of `TauCeti.derivationLieAlgebra.toDualNumberAut`. -/
def toDualNumberAut (d : Derivation R A A) : A[ε] ≃ₐ[R] A[ε] :=
  TauCeti.derivationLieAlgebra.toDualNumberAut (TauCeti.derivationEquivDerivationLieAlgebra d)

/-- An infinitesimal automorphism leaves the scalar part unchanged. -/
@[simp]
theorem toDualNumberAut_fst (d : Derivation R A A) (z : A[ε]) :
    (d.toDualNumberAut z).fst = z.fst :=
  TauCeti.derivationLieAlgebra.toDualNumberAut_fst _ z

/-- The infinitesimal part changes by the derivation of the scalar part. -/
@[simp]
theorem toDualNumberAut_snd (d : Derivation R A A) (z : A[ε]) :
    (d.toDualNumberAut z).snd = z.snd + d z.fst := by
  simp [toDualNumberAut]

@[simp]
theorem toDualNumberAut_eps (d : Derivation R A A) : d.toDualNumberAut ε = ε :=
  TauCeti.derivationLieAlgebra.toDualNumberAut_eps _

@[simp]
theorem toDualNumberAut_zero : (0 : Derivation R A A).toDualNumberAut = 1 := by
  simp [toDualNumberAut]

/-- Addition of derivations corresponds to composition of infinitesimal automorphisms. -/
@[simp]
theorem toDualNumberAut_add (d e : Derivation R A A) :
    (d + e).toDualNumberAut = d.toDualNumberAut * e.toDualNumberAut := by
  simp [toDualNumberAut]

@[simp]
theorem toDualNumberAut_neg (d : Derivation R A A) :
    (-d).toDualNumberAut = d.toDualNumberAut⁻¹ := by
  simp [toDualNumberAut]

/-- Infinitesimal automorphisms commute with the coefficient map of `f` exactly when
their derivations are compatible with `f`. This is the affine compatibility criterion
for automorphisms of a morphism and for restriction to open charts. -/
theorem toDualNumberAut_comp_iff {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R A A) (e : Derivation R B B) (f : A →ₐ[R] B) :
    f.dualNumberMap.comp d.toDualNumberAut.toAlgHom =
      e.toDualNumberAut.toAlgHom.comp f.dualNumberMap ↔
        ∀ a, f (d a) = e (f a) := by
  constructor
  · intro h a
    have h' := congrArg (fun g : A[ε] →ₐ[R] B[ε] ↦ (g (inl a)).snd) h
    simpa using h'
  · intro h
    ext z <;> simp [h]

/-- The infinitesimal automorphism fixes a map from an undeformed target precisely when
the derivation vanishes on its image. -/
theorem toDualNumberAut_comp_dualNumberMap_eq_iff {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R A A) (f : B →ₐ[R] A) :
    d.toDualNumberAut.toAlgHom.comp f.dualNumberMap = f.dualNumberMap ↔
      ∀ b, d (f b) = 0 := by
  simpa [AlgEquiv.aut_one, eq_comm] using
    (toDualNumberAut_comp_iff (0 : Derivation R B B) d f)

/-- The infinitesimal automorphism preserves a marking precisely when the derivation
vanishes after evaluation at the marking. -/
theorem dualNumberMap_comp_toDualNumberAut_eq_iff {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R A A) (f : A →ₐ[R] B) :
    f.dualNumberMap.comp d.toDualNumberAut.toAlgHom = f.dualNumberMap ↔
      ∀ a, f (d a) = 0 := by
  simpa [AlgEquiv.aut_one] using
    (toDualNumberAut_comp_iff d (0 : Derivation R B B) f)

end Derivation

namespace TauCeti

section Subgroup

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- Automorphisms of `A[ε]` that fix the infinitesimal parameter and induce the identity
on `A` modulo `ε`. Equivalently these are automorphisms of the trivial first-order
deformation over the dual-number base, reducing to the identity. -/
def infinitesimalDualNumberAut : Subgroup (A[ε] ≃ₐ[R] A[ε]) where
  carrier := {e | (∀ z, (e z).fst = z.fst) ∧ e ε = ε}
  one_mem' := ⟨fun _ ↦ rfl, rfl⟩
  mul_mem' {e f} he hf := ⟨fun z ↦ (he.1 (f z)).trans (hf.1 z), by
    simpa only [AlgEquiv.mul_apply, hf.2] using he.2⟩
  inv_mem' := by
    intro e he
    constructor
    · intro z
      simpa using (he.1 (e.symm z)).symm
    · exact e.injective (by simpa using he.2.symm)

variable {R A}

/-- Membership in the infinitesimal automorphism subgroup is reduction to the identity
and preservation of `ε`. -/
@[simp]
theorem mem_infinitesimalDualNumberAut (e : A[ε] ≃ₐ[R] A[ε]) :
    e ∈ infinitesimalDualNumberAut R A ↔ (∀ z, (e z).fst = z.fst) ∧ e ε = ε :=
  Iff.rfl

end Subgroup

namespace derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The derivation `a ↦ (e a).snd` read off an infinitesimal automorphism `e`; multiplicativity
of `e` is its Leibniz rule. -/
private def ofInfinitesimalDualNumberAut (e : infinitesimalDualNumberAut R A) :
    derivationLieAlgebra R A :=
  ⟨{ toFun := fun a ↦ (e.val (inl a)).snd
     map_add' := fun a b ↦ by simp
     map_smul' := fun r a ↦ by simp [inl_smul] }, mem_derivationLieAlgebra.2 fun x y ↦ by
    have hfst (a : A) : (e.val (inl a)).fst = a := ((mem_infinitesimalDualNumberAut _).1 e.prop).1 _
    have h := congrArg snd (map_mul e.val (inl x) (inl y))
    rw [← inl_mul, DualNumber.snd_mul, hfst, hfst] at h
    simpa [add_comm] using h⟩

/-- **Infinitesimal automorphisms are derivations**: derivations of `A`, with addition written
multiplicatively, are the automorphisms of `A[ε]` over `R` that fix `ε` and reduce to the identity
modulo `ε`. The inverse reads off the coefficient of `ε` in the image of a constant. -/
def equivInfinitesimalDualNumberAut :
    Multiplicative (derivationLieAlgebra R A) ≃* infinitesimalDualNumberAut R A where
  toFun D := ⟨toDualNumberAut D.toAdd, by simp⟩
  invFun e := Multiplicative.ofAdd (ofInfinitesimalDualNumberAut e)
  left_inv D := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [ofInfinitesimalDualNumberAut]
  right_inv e := by
    obtain ⟨hfst, heps⟩ := (mem_infinitesimalDualNumberAut _).1 e.prop
    apply Subtype.ext
    ext z
    · simpa only [toDualNumberAut_fst] using (hfst z).symm
    · have h : e.val z = e.val (inl z.fst) + e.val (inl z.snd) * e.val ε :=
        AlgHom.apply_dualNumber e.val.toAlgHom z
      rw [heps] at h
      rw [h, toDualNumberAut_snd]
      simp [ofInfinitesimalDualNumberAut, hfst, add_comm]
  map_mul' D E := Subtype.ext (toDualNumberAut_add D.toAdd E.toAdd)

/-- The automorphism corresponding to a derivation is `toDualNumberAut`. -/
@[simp]
theorem equivInfinitesimalDualNumberAut_apply_coe
    (D : Multiplicative (derivationLieAlgebra R A)) :
    (equivInfinitesimalDualNumberAut D : A[ε] ≃ₐ[R] A[ε]) = toDualNumberAut D.toAdd :=
  (rfl)

/-- Recover a derivation by taking the infinitesimal part of the image of each constant. -/
@[simp]
theorem equivInfinitesimalDualNumberAut_symm_apply (e : infinitesimalDualNumberAut R A) (a : A) :
    ((equivInfinitesimalDualNumberAut.symm e).toAdd : Module.End R A) a = (e.val (inl a)).snd :=
  (rfl)

end derivationLieAlgebra

section Commutative

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Derivations, with addition written multiplicatively, are the infinitesimal
automorphisms of the dual numbers: the commutative case of
`TauCeti.derivationLieAlgebra.equivInfinitesimalDualNumberAut`. -/
def derivationEquivInfinitesimalDualNumberAut :
    Multiplicative (Derivation R A A) ≃* infinitesimalDualNumberAut R A :=
  (AddEquiv.toMultiplicative derivationEquivDerivationLieAlgebra.toLinearEquiv.toAddEquiv).trans
    derivationLieAlgebra.equivInfinitesimalDualNumberAut

/-- The automorphism corresponding to a derivation is `Derivation.toDualNumberAut`. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_apply_coe
    (d : Multiplicative (Derivation R A A)) :
    (derivationEquivInfinitesimalDualNumberAut d : A[ε] ≃ₐ[R] A[ε]) =
      d.toAdd.toDualNumberAut := by
  ext z <;> simp [derivationEquivInfinitesimalDualNumberAut]

/-- Recover a derivation by taking the infinitesimal part of the image of each constant. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_symm_apply
    (e : infinitesimalDualNumberAut R A) (a : A) :
    ((derivationEquivInfinitesimalDualNumberAut (R := R) (A := A)).symm e).toAdd a =
      (e.val (inl a)).snd :=
  -- the inverse of the composite is the inverse of `derivationEquivDerivationLieAlgebra`
  -- applied after that of `equivInfinitesimalDualNumberAut`
  (derivationEquivDerivationLieAlgebra_symm_apply _ a).trans
    (derivationLieAlgebra.equivInfinitesimalDualNumberAut_symm_apply e a)

end Commutative

end TauCeti
