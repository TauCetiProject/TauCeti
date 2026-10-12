/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Integral Galois lattices

An integral Galois lattice over a field is a finite free `ℤ`-module equipped with an action of
the absolute Galois group for which every vector has an open stabilizer. This is the continuity
criterion when the module carries the discrete topology.
These lattices encode the character and cocharacter groups of tori over arbitrary fields.

## Main declarations

* `TauCeti.galoisLatticeProperty`: integral representations that are finite free and have open
  stabilizers.
* `TauCeti.GaloisLatticeCat`: the corresponding full subcategory of integral representations.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The property of an integral representation of the absolute Galois group being a Galois
lattice: its module is finite free and every vector has an open stabilizer. -/
def galoisLatticeProperty (k : Type u) [Field k] :
    ObjectProperty (Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :=
  fun M ↦ (@Module.Free ℤ M _ _ M.hV2 ∧ @Module.Finite ℤ M _ _ M.hV2) ∧
    ∀ x : M, IsOpen {sigma | M.ρ sigma x = x}

/-- Membership in the Galois-lattice property. -/
@[simp]
theorem galoisLatticeProperty_iff (k : Type u) [Field k]
    (M : Rep.{u} ℤ (Field.absoluteGaloisGroup k)) :
    galoisLatticeProperty k M ↔
      (@Module.Free ℤ M _ _ M.hV2 ∧ @Module.Finite ℤ M _ _ M.hV2) ∧
        ∀ x : M, IsOpen {sigma | M.ρ sigma x = x} :=
  Iff.rfl

/-- A finitely generated free abelian group with open stabilizers gives an integral Galois
lattice via its induced representation on the additive carrier. -/
theorem galoisLatticeProperty_ofMulDistribMulAction (k : Type u) [Field k]
    (G : Type u) [CommGroup G] [MulDistribMulAction (Field.absoluteGaloisGroup k) G]
    [Module.Free ℤ (Additive G)] [Module.Finite ℤ (Additive G)]
    (hopen : ∀ x : G,
      IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
        Set (Field.absoluteGaloisGroup k))) :
    galoisLatticeProperty k
      (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G) := by
  rw [galoisLatticeProperty_iff]
  let e : Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G ≃ₗ[ℤ] Additive G :=
    Rep.toAdditive.toIntLinearEquiv
  refine ⟨⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩, ?_⟩
  -- Expose Mathlib's bundled carrier so the representation evaluation lemma applies.
  change ∀ x : Additive G, IsOpen {sigma |
    (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G).ρ sigma x = x}
  intro x
  have hstabilizer :
      {sigma | (Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) G).ρ sigma x = x} =
        (MulAction.stabilizer (Field.absoluteGaloisGroup k) x.toMul : Set _) :=
    Set.ext fun sigma ↦ by
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        Rep.ofMulDistribMulAction_ρ_apply_apply]
      exact Additive.ofMul.injective.eq_iff
  rw [hstabilizer]
  exact hopen x.toMul

/-- Being a Galois lattice is invariant under equivariant integral-linear isomorphisms. -/
instance (k : Type u) [Field k] :
    (galoisLatticeProperty k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [galoisLatticeProperty_iff] at hX ⊢
    let _ : Module.Free ℤ X := hX.1.1
    let _ : Module.Finite ℤ X := hX.1.2
    let f := Representation.equivOfIso e
    refine ⟨⟨Module.Free.of_equiv f.toLinearEquiv, Module.Finite.equiv f.toLinearEquiv⟩, ?_⟩
    intro y
    have hfixed (g : Field.absoluteGaloisGroup k) :
        Y.ρ g y = y ↔ X.ρ g (f.symm y) = f.symm y := by
      rw [← f.symm.toLinearEquiv.injective.eq_iff]
      simp only [Representation.Equiv.toLinearEquiv_apply,
        f.symm.toIntertwiningMap.isIntertwining, Representation.Equiv.coe_toIntertwiningMap]
    simpa only [hfixed] using hX.2 (f.symm y)

/-- The category of finite free integral representations of the absolute Galois group whose
vectors have open stabilizers. -/
abbrev GaloisLatticeCat (k : Type u) [Field k] : Type _ :=
  (galoisLatticeProperty k).FullSubcategory

namespace GaloisLatticeCat

/-- The integral module of a Galois lattice is free. -/
instance instModuleFree (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    Module.Free ℤ M.obj :=
  M.property.1.1

/-- The integral module of a Galois lattice is finite. -/
instance instModuleFinite (k : Type u) [Field k] (M : GaloisLatticeCat k) :
    Module.Finite ℤ M.obj :=
  M.property.1.2

/-- Every vector of a Galois lattice has an open stabilizer. -/
theorem isOpen_setOf_ρ_eq (k : Type u) [Field k] (M : GaloisLatticeCat k) (x : M.obj) :
    IsOpen {sigma | M.obj.ρ sigma x = x} :=
  M.property.2 x

end GaloisLatticeCat

end TauCeti
