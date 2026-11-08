/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generators of a quadratic extension

Mathlib's `Algebra.IsQuadraticExtension K L` records that `L/K` has degree two but says nothing
about the elements realising that degree. This file first supplies a non-scalar element, then
shows how to *choose* and *change* a generator when the base is a field:

`Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap`: an element outside the image of
the base exists. Over a field base, the coordinate theorem below makes any such element a
generator.
`Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul`: every element is `b + aθ`
for a fixed generator `θ`, the coordinate presentation over the basis `1, θ` (used by the
quadratic field-norm computation).
`Algebra.IsQuadraticExtension.exists_ne_zero_eq_algebraMap_add_algebraMap_mul`: for a *second*
generator the `θ`-coefficient is nonzero, so any two generators differ by `θ' = b + aθ` with
`a ≠ 0` and a statement proved for one transfers to every other.
`TauCeti.linearIndependent_one_iff_notMem_range_algebraMap`, the linear-algebra step behind them,
characterises the elements `θ` making `1, θ` linearly independent as exactly the non-scalar ones.
`TauCeti.quadraticExtensionBasis` makes `(1, x)` a basis for any non-scalar `x` in a
degree-two algebra over a field, with evaluation lemmas for its two basis vectors.

None asks for a field on `L`: each theorem needs only a semiring, with the ring structure required
by linear independence obtained locally through `Algebra.semiringToRing`. Non-scalar existence is
stated over the commutative semirings admitted by Mathlib's `IsQuadraticExtension`; the strong rank
condition also forces the base to be nontrivial. The coordinate results require a field base:
over `ℤ`, the element `(0, 2)` lies outside the diagonal copy of `ℤ` in `ℤ × ℤ` but does not span
the algebra together with `1`. Over a field, the results cover split and non-reduced quadratic
algebras such as `K × K` and `K[X]/(X²)`.

These are used by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist/Basic.lean` and by the quadratic field-norm
computation in `TauCeti/NumberTheory/NumberField/Quadratic/Norm.lean`. The shared basis also
supplies explicit coordinates for quadratic-extension trace transfer.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/LinearAlgebra/Dimension/IsQuadraticExtension.lean` at commit
`bc2fe8ff7396`, FLT PR #1088, Apache 2.0). That file's own header reads
`Authors: Kevin Buzzard, Claude`; following this repository's convention for adapted material,
the upstream authorship is credited here rather than in the copyright header. Only the results
the twist consumes are ported; the rest of the source file — which restates
`Algebra.IsQuadraticExtension` itself, already in Mathlib — is not needed.
-/

public section

section GeneratorExistence

variable (K L : Type*) [CommSemiring K] [StrongRankCondition K]

/-- A quadratic algebra contains an element outside the image of the base ring. The base `K` is
any commutative semiring with the strong rank condition (Mathlib's setting for
`Algebra.IsQuadraticExtension`) and `L` any semiring. -/
theorem Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap [Semiring L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
  have h2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  by_contra! h
  have h1 : Module.finrank K L = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨FaithfulSMul.algebraMap_injective K L, h⟩
  omega

end GeneratorExistence

variable (K L : Type*) [Field K]

/-- `1` and an element `θ` are linearly independent over the base field exactly when `θ` lies
outside the base field. The ambient algebra `L` need only be a semiring. -/
theorem TauCeti.linearIndependent_one_iff_notMem_range_algebraMap [Semiring L] [Algebra K L]
    {θ : L} : LinearIndependent K ![(1 : L), θ] ↔ θ ∉ Set.range (algebraMap K L) := by
  let _ : Ring L := Algebra.semiringToRing K
  refine ⟨fun h ⟨a, ha⟩ ↦ (LinearIndependent.pair_iff' (h.ne_zero 0)).mp h a ?_, fun hθ ↦ ?_⟩
  · simp [← ha, Algebra.smul_def]
  have : Nontrivial L := nontrivial_of_ne θ (algebraMap K L 0) fun h ↦ hθ ⟨0, h.symm⟩
  exact (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦
    hθ ⟨a, by rwa [Algebra.algebraMap_eq_smul_one]⟩

namespace TauCeti

/-- The basis `(1, x)` of a degree-two algebra over a field for an element outside the base. -/
noncomputable def quadraticExtensionBasis [Semiring L] [Algebra K L] {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (hfin : Module.finrank K L = 2) :
    Module.Basis (Fin 2) K L := by
  let _ : Ring L := Algebra.semiringToRing K
  exact basisOfLinearIndependentOfCardEqFinrank (b := ![1, x])
    ((linearIndependent_one_iff_notMem_range_algebraMap K L).mpr hx) (by simp [hfin])

@[simp]
theorem quadraticExtensionBasis_zero [Semiring L] [Algebra K L] {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (hfin : Module.finrank K L = 2) :
    quadraticExtensionBasis K L hx hfin 0 = 1 := by
  simp [quadraticExtensionBasis]

@[simp]
theorem quadraticExtensionBasis_one [Semiring L] [Algebra K L] {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (hfin : Module.finrank K L = 2) :
    quadraticExtensionBasis K L hx hfin 1 = x := by
  simp [quadraticExtensionBasis]

end TauCeti

/-- **Every element of a quadratic extension is `b + aθ`** for a fixed generator `θ`: the basis
`1, θ` spans `L` over `K`. The `θ`-coefficient may vanish, exactly when the element lies in the
base field; `exists_ne_zero_eq_algebraMap_add_algebraMap_mul` records that it does not for a second
generator. The spanning is `K`-linear algebra, so this needs only a *semiring* on `L`. -/
theorem Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul [Semiring L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (x : L) :
    ∃ a b : K, x = algebraMap K L b + algebraMap K L a * θ := by
  let b := TauCeti.quadraticExtensionBasis K L hθ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  refine ⟨b.repr x 1, b.repr x 0, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp [b, Fin.sum_univ_two, Algebra.smul_def]

/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. So any
two generators differ by `θ' = b + aθ` with `a ≠ 0`. -/
theorem Algebra.IsQuadraticExtension.exists_ne_zero_eq_algebraMap_add_algebraMap_mul [Semiring L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  obtain ⟨a, b, hab⟩ :=
    Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul K L hθ θ'
  refine ⟨a, b, ?_, hab⟩
  rintro rfl
  exact hθ' ⟨b, by simp [hab]⟩

end
