/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import TauCeti.FieldTheory.Galois.Basic
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.GroupTheory.GroupAction.CyclicFiber

/-!
# The prime fiber of a Frobenius cycle

In a Galois extension containing a quadratic subfield, the labels above an inert prime
and its conjugate form an orbit under the signed Frobenius. Requiring a label to be trivial
after level reduction replaces that generator by a power. This is the prime-fiber argument
of `New.Data.exists_orbit_of_mem_aPlaces` in lsernau/grh-lean, revision `72fead1`,
`grh/src/New/UpperBound/Divisibility/MarkOperator.lean`.
-/

public section

open scoped NumberField Pointwise

namespace Ideal

/-- Let `Q` be unramified in a Galois extension `L/F` and have residue degree two in the
quadratic subextension `M/F`. Among the automorphisms fixing `M` whose label under `f` is
trivial, the ones carrying a specified prime to `Q` or `c • Q` form a cycle, where `c` is an
involution nontrivial on `M` commuting with Frobenius. If `τ` carries the specified prime to `Q`,
the cycle starts at `τ` and its step is the signed Frobenius `c * σ` raised to the order of
its label under `f`. -/
theorem exists_zmod_cycle_of_inert_prime {F M L J : Type*}
    [Field F] [NumberField F] [Field M] [NumberField M] [Field L] [NumberField L]
    [Algebra F M] [Algebra M L] [Algebra F L] [IsScalarTower F M L]
    [Algebra.IsQuadraticExtension F M] [IsGalois F L] [Group J]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (hQ : (Q.under (𝓞 M)).inertiaDeg (𝓞 F) = 2)
    (f : (L ≃ₐ[F] L) →* J) {σ c τ : L ≃ₐ[F] L}
    (hσ : IsArithFrobAt (𝓞 F) σ Q) (hc : c ^ 2 = 1) (hcomm : Commute c σ)
    (hcM : c.restrictNormal M ≠ 1) (hτM : τ.restrictNormal M = 1) (hτf : f τ = 1) :
    let v := (c * σ) ^ orderOf (f (c * σ))
    ∃ t : ZMod (orderOf v) → (L ≃ₐ[F] L), Function.Injective t ∧ t 0 = τ ∧
      (∀ i, t (i + 1) = v * t i) ∧
      Set.range t = {y | y.restrictNormal M = 1 ∧ f y = 1 ∧
        (y • (τ⁻¹ • Q) = Q ∨ y • (τ⁻¹ • Q) = c • Q)} := by
  let P := Q.under (𝓞 M)
  have : Algebra.IsUnramifiedAt (𝓞 F) P := Algebra.IsUnramifiedAt.of_liesOver (𝓞 F) P Q
  have horder : orderOf (σ.restrictNormal M) = 2 :=
    (orderOf_eq_inertiaDeg_of_isArithFrobAt P (hσ.restrictNormal (M := M))).trans hQ
  have hσM : σ.restrictNormal M ≠ 1 := by
    intro h
    simp [h] at horder
  have hres : c.restrictNormal M = σ.restrictNormal M :=
    (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq F M hσM _).resolve_left hcM
  have hrestrict (y : L ≃ₐ[F] L) : AlgEquiv.restrictNormalHom M y = y.restrictNormal M := rfl
  simpa only [hrestrict, mul_smul] using
    MulAction.exists_zmod_cycle_fiber (AlgEquiv.restrictNormalHom M) f
      (zpowers_eq_stabilizer_of_isArithFrobAt Q hσ) hc hcomm hres hcM hτM hτf

end Ideal
