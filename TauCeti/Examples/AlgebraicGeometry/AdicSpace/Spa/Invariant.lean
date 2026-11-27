/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Invariant

/-!
# Tests: the orbit space of the adic spectrum

For an action fixing every element of `A`, the induced action on `Spv A` is trivial, so the
orbits in `Spa(A, A⁺)` are points and restriction to the invariants is injective, hence a
homeomorphism `Spa(A, A⁺) ≅ Spa(Aᴳ, A^{+G})`. For an arbitrary action, two points in one orbit
have the same image in the orbit space and in `Spa(Aᴳ, A^{+G})`.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Examples.SpaInvariant

variable {A G : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [Group G] [Finite G] [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- For an action fixing every element, `G` acts trivially on `Spv A`. -/
example (h : ∀ (g : G) (a : A), g • a = a) (g : G) (v : Spv A) : g • v = v := by
  have hg : MulSemiringAction.toRingHom G A g⁻¹ = RingHom.id A := RingHom.ext (h g⁻¹)
  rw [smul_def, hg, comap_id, id]

/-- For an action fixing every element, restriction to the invariants is injective on
`Spa(A, A⁺)`: the orbits are points. -/
example (h : ∀ (g : G) (a : A), g • a = a) (P : Pair A) [IsInvariantSubring G P.plus] :
    Function.Injective (invariantPair.inclusion G P).spaComap := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := (invariantPair.spaComap_inclusion_eq_spaComap_inclusion_iff G P).mp hxy
  have hg : MulSemiringAction.toRingHom G A g⁻¹ = RingHom.id A := RingHom.ext (h g⁻¹)
  exact Subtype.ext (by rw [coe_smul, smul_def, hg, comap_id, id])

/-- Two points in one orbit have the same image in the orbit space and in `Spa(Aᴳ, A^{+G})`. -/
example (P : Pair A) [IsInvariantSubring G P.plus] (g : G) (x : spa P.plus) :
    invariantSpectrumHomeomorph G P (Quotient.mk _ (g • x)) =
      invariantSpectrumHomeomorph G P (Quotient.mk _ x) := by
  simp

end TauCeti.Examples.SpaInvariant
