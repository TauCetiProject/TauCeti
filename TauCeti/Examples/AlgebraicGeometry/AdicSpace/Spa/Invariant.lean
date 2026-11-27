/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Invariant.Quotient

/-!
# Tests: the orbit space of the adic spectrum

Throughout, a finite group `G` acts by continuous ring automorphisms on a Tate ring `A`, and in the
statements about `Spa(A, A⁺)` it preserves `A⁺`, so that it acts on `Spa(A, A⁺)`. If moreover the
action fixes every element of `A`, the induced action on `Spv A` is trivial, so the orbits in
`Spa(A, A⁺)` are points and restriction to the invariants is injective, hence a homeomorphism
`Spa(A, A⁺) ≅ Spa(Aᴳ, A^{+G})`. Without that extra hypothesis, two points in one orbit still have
the same image in the orbit space and in `Spa(Aᴳ, A^{+G})`.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Examples.SpaInvariant

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A]

/-- For an action fixing every element, `G` acts trivially on `Spv A`. -/
theorem smul_eq_self (h : ∀ (g : G) (a : A), g • a = a) (g : G) (v : Spv A) :
    g • v = v := by
  have hg : MulSemiringAction.toRingHom G A g⁻¹ = RingHom.id A := RingHom.ext (h g⁻¹)
  rw [smul_def, hg, comap_id, id]

variable [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [Finite G]
  [ContinuousConstSMul G A]

/-- For an action fixing every element, restriction to the invariants is injective on
`Spa(A, A⁺)`: the orbits are points. -/
example (h : ∀ (g : G) (a : A), g • a = a) (P : Pair A) [IsInvariantSubring G P.plus] :
    Function.Injective (invariantPair.inclusion G P).spaComap := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := (invariantPair.spaComap_inclusion_eq_spaComap_inclusion_iff G P).mp hxy
  exact Subtype.ext (by rw [val_smul, smul_eq_self h])

/-- Two points in one orbit have the same image in the orbit space and in `Spa(Aᴳ, A^{+G})`. -/
example (P : Pair A) [IsInvariantSubring G P.plus] (g : G) (x : spa P.plus) :
    invariantSpectrumHomeomorph G P (Quotient.mk _ (g • x)) =
      invariantSpectrumHomeomorph G P (Quotient.mk _ x) := by
  simp

end TauCeti.Examples.SpaInvariant
