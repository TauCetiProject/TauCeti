/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Smooth
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic

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

/-- `μ_p` over `𝔽_p` is not smooth. -/
example [Fact p.Prime] : ¬ Smooth (RootsOfUnityGroup.groupScheme (ZMod p) p).X.hom :=
  RootsOfUnityGroup.groupScheme_not_smooth p

/-- Over a field of characteristic `p`, the only point of `μ_p` is the identity. -/
example [Fact p.Prime] (K : Type) [Field K] [CharP K p] [Algebra (ZMod p) K] :
    Subsingleton ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of (ZMod p))) ⟶
      (RootsOfUnityGroup.groupScheme (ZMod p) p).X) :=
  (RootsOfUnityGroup.schemePointsMulEquiv (R := ZMod p) (A := K) p).toEquiv.subsingleton_congr.mpr
    (by simpa using subsingleton_rootsOfUnity_prime_pow (R := K) p 1)

/-- The point of `μ_p` over `𝔽_p[ε]/(ε²)` given by the `p`th root of unity `1 + ε` is not the
identity. -/
example [Fact (1 < p)] :
    (RootsOfUnityGroup.schemePointsMulEquiv (R := ZMod p) (A := DualNumber (ZMod p)) p).symm
      ⟨dualNumberUnit 1, by rw [mem_rootsOfUnity, dualNumberUnit_pow]; ext <;> simp⟩ ≠ 1 := by
  simp [Ne, Subtype.ext_iff]

end RootsOfUnity

end TauCeti.Examples.AbelianSchemeNonExamples
