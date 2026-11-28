/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Loop
public import Mathlib.Algebra.Lie.Weights.IsSimple
public import TauCeti.Algebra.Lie.Extension.Basic
-- Proof-only: general kernel criterion, H² classification on loops, and form
-- uniqueness.
import TauCeti.Algebra.Lie.Extension.Universal
import TauCeti.Algebra.Lie.Loop.Cocycle
import TauCeti.Algebra.Lie.Weights.IsSimple

/-!
# Kernel criteria for the residue central extension of a loop algebra

Specializing `LieAlgebra.ofTwoCocycle.lie_top_ker_eq_ker_of_surjective` via
`twoCocycle_eq_span_sup_range_d₁₂` and `LieSubalgebra.exists_eq_smul_killingForm_of_isSimple`
yields kernel criteria (`⁅⊤, f.ker⁆ = f.ker`) for surjections from perfect Lie algebras with a
central lift onto the residue central extension of `loopAlgebra K ℤ L`:
`TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle` and
`TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple`.
Both results establish conditional kernel equalities rather than the universal mapping property of
a central extension.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §7.4.
* C. Kassel, *Kähler differentials and coverings of complex simple Lie algebras extended over a
  commutative algebra*, J. Pure Appl. Algebra 34 (1984), 265–275.
-/

public section

noncomputable section

open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra _root_.LieModule.Cohomology
open _root_.LieAlgebra.ofTwoCocycle (centralElement)

namespace TauCeti.LieAlgebra.LoopAlgebra

/-- **Kernel criterion for the residue central extension**:
for a Lie algebra `L` with nondegenerate Killing form over a characteristic-zero field `K` whose
invariant bilinear forms are scalar multiples of a symmetric invariant form `Φ`, any surjective
`f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)` from a perfect Lie algebra `G`
lifting `centralElement` to a central element satisfies `⁅⊤, f.ker⁆ = f.ker`. This is a
conditional kernel criterion and does not establish the universal mapping property. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle
    {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsKilling K L] [LieRing G] [LieAlgebra K G]
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker :=
  ofTwoCocycle.lie_top_ker_eq_ker_of_surjective
    (by rw [twoCocycleOfBilinear_coe]; exact twoCocycle_eq_span_sup_range_d₁₂ hΦs hspan)
    hf hperf hcG_cent hcG_map

/-- **Kernel criterion for the residue central extension of a split simple Lie algebra**:
for any nonzero symmetric invariant bilinear form `Φ` on a split finite-dimensional simple Lie
algebra `L` over a characteristic-zero field `K` (without assuming algebraic closure), any
surjective homomorphism from a perfect Lie algebra `G` onto
`ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)` lifting the central element to a central
element satisfies `⁅⊤, f.ker⁆ = f.ker`. This is a conditional kernel criterion and does not
establish the universal mapping property. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple
    {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [IsSimple K L] [LieRing G] [LieAlgebra K G] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  refine lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle hΦ hΦs (fun Ψ hΨ ↦ ?_)
    hf hperf hcG_cent hcG_map
  obtain ⟨c, hc⟩ := H.exists_eq_smul_killingForm_of_isSimple hΦ
  obtain ⟨d, hd⟩ := H.exists_eq_smul_killingForm_of_isSimple hΨ
  have hc0 : c ≠ 0 := by rintro rfl; exact hΦ0 (by simpa using hc)
  exact ⟨d * c⁻¹, by rw [hd, hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩

end TauCeti.LieAlgebra.LoopAlgebra
