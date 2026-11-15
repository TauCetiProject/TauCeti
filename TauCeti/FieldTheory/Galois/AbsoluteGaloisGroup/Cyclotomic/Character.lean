/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The cyclotomic character of an absolute Galois group

The character `localCyclotomicCharacter p K` records the action of
`Field.absoluteGaloisGroup K` on roots of unity of `p`-power order in an algebraic closure.
It is Mathlib's cyclotomic character restricted from ring automorphisms to the Galois group.
The pointwise equation fixes this choice of character for later arithmetic comparisons.
Its bundled form `continuousLocalCyclotomicCharacter p K` is the continuous homomorphism that the
twisted coefficients `TauCeti.ZModTwist` and the prescription property
`TauCeti.HasPrescriptionProperty` take. It factors through the topological abelianization as
`abelianizedLocalCyclotomicCharacter p K`, which is how it is evaluated on Artin symbols.
The character is natural along field extensions (`localCyclotomicCharacter_mapOfAlgebra`,
`localCyclotomicCharacter_map`), so the image of `G_L` lies in that of `G_K` for every extension
`L/K` (`range_localCyclotomicCharacter_le_range`).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`. -/
noncomputable def localCyclotomicCharacter :
    Field.absoluteGaloisGroup K →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure K) p).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K))

/-- The local character is Mathlib's cyclotomic character evaluated on the underlying
ring automorphism. -/
@[simp]
theorem localCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    localCyclotomicCharacter p K σ =
      cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv :=
  (rfl)

/-- The cyclotomic character is continuous for the Krull topology on the absolute
Galois group and the `p`-adic topology on the units. -/
theorem localCyclotomicCharacter_continuous :
    Continuous (localCyclotomicCharacter p K) := by
  exact cyclotomicCharacter.continuous p K (AlgebraicClosure K)

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`, as a continuous
homomorphism. -/
noncomputable def continuousLocalCyclotomicCharacter :
    Field.absoluteGaloisGroup K →ₜ* ℤ_[p]ˣ :=
  ⟨localCyclotomicCharacter p K, localCyclotomicCharacter_continuous p K⟩

/-- The bundled continuous character takes the values of the cyclotomic character. -/
@[simp]
theorem continuousLocalCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    continuousLocalCyclotomicCharacter p K σ = localCyclotomicCharacter p K σ :=
  (rfl)

/-- The `p`-adic cyclotomic character on the topological abelianization of the absolute Galois
group of `K`, through which the cyclotomic character factors since `ℤ_[p]ˣ` is commutative. -/
noncomputable def abelianizedLocalCyclotomicCharacter :
    Field.absoluteGaloisGroupAbelianization K →ₜ* ℤ_[p]ˣ :=
  TopologicalAbelianization.lift (continuousLocalCyclotomicCharacter p K)

/-- On the class of `σ`, the abelianized cyclotomic character is the cyclotomic character
of `σ`. -/
@[simp]
theorem abelianizedLocalCyclotomicCharacter_mk (σ : Field.absoluteGaloisGroup K) :
    abelianizedLocalCyclotomicCharacter p K (σ : Field.absoluteGaloisGroupAbelianization K) =
      localCyclotomicCharacter p K σ :=
  TopologicalAbelianization.lift_mk _ σ

section Naturality

variable (L : Type*) [Field L] [Algebra K L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- **The cyclotomic character along a field extension.** The cyclotomic character of
`g ∈ G_L` is that of its image `Field.absoluteGaloisGroup.mapOfAlgebra K L g` in `G_K`. -/
theorem localCyclotomicCharacter_mapOfAlgebra (g : Field.absoluteGaloisGroup L) :
    localCyclotomicCharacter p K (Field.absoluteGaloisGroup.mapOfAlgebra K L g) =
      localCyclotomicCharacter p L g := by
  rw [localCyclotomicCharacter_apply, localCyclotomicCharacter_apply]
  exact (cyclotomicCharacter_eq_of_injective p
    (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)).injective
    (fun _ x _ ↦ (absoluteGaloisGroup_mapOfAlgebra_commutes K L g x).symm)
    fun H i ↦ let ⟨_, hζ⟩ := H i; hζ.exists_isPrimitiveRoot_of_isSepClosed K).symm

end Naturality

section Map

variable {K} {L : Type*} [Field L]

/-- **The cyclotomic character along a field embedding** `f : K →+* L`: the cyclotomic character
of `g ∈ G_L` is that of its image `Field.absoluteGaloisGroup.map f g` in `G_K`. -/
theorem localCyclotomicCharacter_map (f : K →+* L) (g : Field.absoluteGaloisGroup L) :
    localCyclotomicCharacter p K (Field.absoluteGaloisGroup.map f g) =
      localCyclotomicCharacter p L g :=
  letI := f.toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toAlgebra
  localCyclotomicCharacter_mapOfAlgebra p K L g

end Map

variable (L : Type*) [Field L] [Algebra K L]

/-- **The cyclotomic image of `G_L` lies in that of `G_K`** for any field extension `L/K`. -/
theorem range_localCyclotomicCharacter_le_range :
    (localCyclotomicCharacter p L).range ≤ (localCyclotomicCharacter p K).range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨Field.absoluteGaloisGroup.map (algebraMap K L) g,
    localCyclotomicCharacter_map p (algebraMap K L) g⟩

end TauCeti
