/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Infinitesimal
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Smooth

/-!
# Group schemes that are not abelian schemes

An abelian scheme is a smooth proper group scheme with geometrically connected fibres. These
checks exhibit group schemes over a field that have all but one of these properties, and a
noncommutative group scheme.

* The constant group `(ℤ/2)_K` is proper and smooth but not geometrically connected.
* `μ_p = D(ℤ/p)` over `𝔽_p` is not smooth. Its only point over a field of characteristic `p` is
  the identity, but `1 + ε` is a nonidentity point over `𝔽_p[ε]/(ε²)`, so testing points only
  over fields misses part of the group.
* The constant group of the symmetric group on three letters is not commutative.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti
open scoped CategoryTheory.MonObj

universe u

namespace TauCeti.Examples.AbelianSchemeNonExamples

section Constant

variable (K : Type u) [Field K]

/-- The constant group `(ℤ/2)_K` is proper. -/
example : IsProper (ConstantGroup.groupScheme K (ULift.{u} (Multiplicative (ZMod 2)))).X.hom :=
  inferInstance

/-- The constant group `(ℤ/2)_K` is smooth. -/
example : Smooth (ConstantGroup.groupScheme K (ULift.{u} (Multiplicative (ZMod 2)))).X.hom :=
  inferInstance

/-- The constant group `(ℤ/2)_K` is not geometrically connected. -/
example :
    ¬ GeometricallyConnected
      (ConstantGroup.groupScheme K (ULift.{u} (Multiplicative (ZMod 2)))).X.hom :=
  ConstantGroup.not_geometricallyConnected_groupScheme _ K

/-- The constant group of the symmetric group on three letters is not commutative. -/
example : ¬ IsCommMonObj (ConstantGroup.groupScheme K (ULift.{u} (Equiv.Perm (Fin 3)))).X :=
  ConstantGroup.not_isCommMonObj_groupScheme _ K fun h ↦
    absurd (congr_arg ULift.down (h.is_comm.comm ⟨Equiv.swap 0 1⟩ ⟨Equiv.swap 1 2⟩)) (by decide)

end Constant

section RootsOfUnity

variable (p : ℕ)

/-- The character group `ℤ/p` of `μ_p`. -/
abbrev muCharacters [NeZero p] : FGCommGrpCat.{0} := FGCommGrpCat.of (Multiplicative (ZMod p))

/-- Every element of the character group `ℤ/p` of `μ_p` is killed by `p`. -/
private theorem muCharacters_pow_self (g : Multiplicative (ZMod p)) : g ^ p = 1 :=
  Multiplicative.toAdd.injective (by simp)

/-- The generator of the character group `ℤ/p` of `μ_p` is not the identity. -/
private theorem ofAdd_one_ne_one [Nontrivial (ZMod p)] :
    Multiplicative.ofAdd (1 : ZMod p) ≠ 1 := by
  simp

/-- `μ_p` over `𝔽_p` is not smooth. -/
example [Fact p.Prime] :
    ¬ Smooth (DiagonalizableGroup.groupScheme (ZMod p) (muCharacters p)).X.hom := by
  rw [DiagonalizableGroup.smooth_groupScheme_iff (ZMod p) p]
  exact fun h ↦ ofAdd_one_ne_one p (h _ (muCharacters_pow_self p _))

/-- Over a field of characteristic `p`, the only point of `μ_p` is the identity. -/
example [Fact p.Prime] (K : Type) [Field K] [CharP K p] [Algebra (ZMod p) K] :
    Subsingleton ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of (ZMod p))) ⟶
      (DiagonalizableGroup.groupScheme (ZMod p) (muCharacters p)).X) :=
  DiagonalizableGroup.subsingleton_schemePoints_of_isReduced p _ (muCharacters_pow_self p)

/-- The unit `1 + n ε` of `𝔽_p[ε]/(ε²)`. -/
def dualNumberUnit (n : ZMod p) : (DualNumber (ZMod p))ˣ where
  val := 1 + n • DualNumber.eps
  inv := 1 - n • DualNumber.eps
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- The character `ℤ/p → 𝔽_p[ε]ˣ`, `n ↦ 1 + n ε`. -/
def dualNumberCharacter : Multiplicative (ZMod p) →* (DualNumber (ZMod p))ˣ where
  toFun n := dualNumberUnit p n.toAdd
  map_one' := by ext <;> simp [dualNumberUnit]
  map_mul' m n := by ext <;> simp [dualNumberUnit, add_smul, add_comm]

/-- The point of `μ_p` over `𝔽_p[ε]/(ε²)` given by the character `n ↦ 1 + n ε`, which sends the
generator to `1 + ε`, is not the identity. -/
example [NeZero p] [Fact (1 < p)] :
    (DiagonalizableGroup.groupSchemePointsMulEquiv (R := ZMod p) (A := DualNumber (ZMod p))
      (muCharacters p)).symm (WithConv.toConv (DiagonalizableGroup.point (dualNumberCharacter p)))
      ≠ 1 := by
  rw [Ne, MulEquiv.symm_apply_eq, map_one]
  intro h
  -- Evaluate both points at the generator `1` of `ℤ/p` and take the `ε`-coefficient.
  let g : muCharacters p := Multiplicative.ofAdd (1 : ZMod p)
  have := congr_arg (fun x : WithConv (MonoidAlgebra (ZMod p) (muCharacters p) →ₐ[ZMod p]
    DualNumber (ZMod p)) ↦ TrivSqZeroExt.snd (x.ofConv (MonoidAlgebra.single g 1))) h
  dsimp only at this
  rw [WithConv.ofConv_toConv, DiagonalizableGroup.point_single, AlgHom.convOne_apply,
    MonoidAlgebra.counit_single] at this
  have hg : g = 1 := by simpa [dualNumberCharacter, dualNumberUnit] using this
  exact ofAdd_one_ne_one p hg

end RootsOfUnity

end TauCeti.Examples.AbelianSchemeNonExamples
