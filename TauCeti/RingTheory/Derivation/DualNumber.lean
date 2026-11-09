/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.TrivSqZeroExt
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

The construction uses `TauCeti.derivationToTrivSqZeroExtEquivLift` for the correspondence
between derivations and lifts, and `DualNumber.lift` to extend a lift to the dual numbers.

## References

* R. Hartshorne, *Deformation Theory*, Chapter 1, for infinitesimal automorphisms
  as derivations.
-/

public section

open TrivSqZeroExt DualNumber

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private def dualNumberEnd (d : Derivation R A A) : A[ε] →ₐ[R] A[ε] :=
  DualNumber.lift ⟨((TauCeti.derivationToTrivSqZeroExtEquivLift R A A d).1, ε),
    eps_mul_eps, fun _ ↦ Commute.all _ _⟩

private theorem dualNumberEnd_fst (d : Derivation R A A) (z : A[ε]) :
    (dualNumberEnd d z).fst = z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply]

private theorem dualNumberEnd_snd (d : Derivation R A A) (z : A[ε]) :
    (dualNumberEnd d z).snd = z.snd + d z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply, add_comm]

/-- The infinitesimal automorphism `a + b ε ↦ a + (b + d a) ε` attached to a derivation.
Its inverse is the automorphism attached to `-d`. -/
def toDualNumberAut (d : Derivation R A A) : A[ε] ≃ₐ[R] A[ε] :=
  AlgEquiv.ofAlgHom (dualNumberEnd d) (dualNumberEnd (-d))
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])

/-- An infinitesimal automorphism leaves the scalar part unchanged. -/
@[simp]
theorem toDualNumberAut_fst (d : Derivation R A A) (z : A[ε]) :
    (d.toDualNumberAut z).fst = z.fst :=
  dualNumberEnd_fst d z

/-- The infinitesimal part changes by the derivation of the scalar part. -/
@[simp]
theorem toDualNumberAut_snd (d : Derivation R A A) (z : A[ε]) :
    (d.toDualNumberAut z).snd = z.snd + d z.fst :=
  dualNumberEnd_snd d z

@[simp]
theorem toDualNumberAut_eps (d : Derivation R A A) : d.toDualNumberAut ε = ε := by
  ext <;> simp

@[simp]
theorem toDualNumberAut_zero : (0 : Derivation R A A).toDualNumberAut = 1 := by
  ext z <;> simp

/-- Addition of derivations corresponds to composition of infinitesimal automorphisms. -/
@[simp]
theorem toDualNumberAut_add (d e : Derivation R A A) :
    (d + e).toDualNumberAut = d.toDualNumberAut * e.toDualNumberAut := by
  ext z <;> simp [add_left_comm, add_comm]

@[simp]
theorem toDualNumberAut_neg (d : Derivation R A A) :
    (-d).toDualNumberAut = d.toDualNumberAut⁻¹ := by
  ext z <;> simp [toDualNumberAut, dualNumberEnd_fst, dualNumberEnd_snd]

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

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Derivations, with addition written multiplicatively, are the infinitesimal
automorphisms of the dual numbers. The inverse reads off the coefficient of `ε`
in the image of a constant. -/
def derivationEquivInfinitesimalDualNumberAut :
    Multiplicative (Derivation R A A) ≃* infinitesimalDualNumberAut R A where
  toFun d := ⟨d.toAdd.toDualNumberAut, by simp⟩
  invFun e := Multiplicative.ofAdd <|
    (derivationToTrivSqZeroExtEquivLift R A A).symm
      ⟨e.val.toAlgHom.comp (inlAlgHom R A A), AlgHom.ext fun a ↦ e.prop.1 (inl a)⟩
  left_inv d := by
    apply Multiplicative.toAdd.injective
    ext a
    simp
  right_inv e := by
    apply Subtype.ext
    ext z
    · simpa only [Derivation.toDualNumberAut_fst] using (e.prop.1 z).symm
    · simp only [Derivation.toDualNumberAut_snd]
      have h : e.val z = e.val (inl z.fst) + e.val (inl z.snd) * e.val ε :=
        AlgHom.apply_dualNumber e.val.toAlgHom z
      rw [e.prop.2] at h
      rw [h]
      simp [e.prop.1, add_comm]
  map_mul' d e := by
    apply Subtype.ext
    exact Derivation.toDualNumberAut_add d.toAdd e.toAdd

/-- The automorphism corresponding to a derivation is `Derivation.toDualNumberAut`. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_apply_coe
    (d : Multiplicative (Derivation R A A)) :
    (derivationEquivInfinitesimalDualNumberAut d : A[ε] ≃ₐ[R] A[ε]) =
      d.toAdd.toDualNumberAut :=
  (rfl)

/-- Recover a derivation by taking the infinitesimal part of the image of each constant. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_symm_apply
    (e : infinitesimalDualNumberAut R A) (a : A) :
    ((derivationEquivInfinitesimalDualNumberAut (R := R) (A := A)).symm e).toAdd a =
      (e.val (inl a)).snd :=
  derivationToTrivSqZeroExtEquivLift_symm_apply _ _

end TauCeti
