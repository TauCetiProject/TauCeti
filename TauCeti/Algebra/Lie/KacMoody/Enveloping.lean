/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Borel
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Triangular

/-!
# Triangular PBW decomposition for a Kac–Moody presentation

Multiplication gives linear equivalences
`U(𝔥) ⊗ U(n⁺) ≃ U(𝔟⁺)` and `U(n⁻) ⊗ (U(𝔥) ⊗ U(n⁺)) ≃ U(𝔤)`.
In particular the inverse triangular decomposition recovers the three tensor factors of an
ordered product. This separates the negative generators from the Borel relations in induced
highest-weight modules. The decompositions are linear: the factors need not commute.

We apply `LieSubalgebra.mulEquiv`, the relative PBW theorem for complementary subalgebras,
twice. There is no finite-dimensionality, finite-type, or characteristic-zero assumption.
The shared assembly in `TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Triangular`, extracted
from the finite-type construction in `TauCeti.Algebra.Lie.UniversalEnveloping.Triangular`,
provides the equivalences and their computation and extensionality rules.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.3 and §9.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.4 and §20.3.
-/

public section

namespace TauCeti.KacMoody

open scoped TensorProduct

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

local notation "U" => _root_.UniversalEnvelopingAlgebra K

/-- Multiplication factors the Borel enveloping algebra into its Cartan and positive factors. -/
noncomputable def borelMulEquiv :
    U (cartanSubalgebra R) ⊗[K] U (positiveSubalgebra R) ≃ₗ[K] U (borelSubalgebra R) :=
  LieSubalgebra.mulEquivOfLe (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R)

/-- The Borel PBW equivalence multiplies the images of the two tensor factors in order. -/
@[simp]
theorem borelMulEquiv_tmul (h : U (cartanSubalgebra R)) (e : U (positiveSubalgebra R)) :
    borelMulEquiv R (h ⊗ₜ e) =
      UniversalEnvelopingAlgebra.map K
          (LieSubalgebra.inclusion (cartanSubalgebra_le_borelSubalgebra R)) h *
        UniversalEnvelopingAlgebra.map K
          (LieSubalgebra.inclusion (positiveSubalgebra_le_borelSubalgebra R)) e :=
  LieSubalgebra.mulEquivOfLe_tmul (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R) h e

/-- The inverse Borel decomposition recovers the Cartan and positive factors of a product. -/
@[simp]
theorem borelMulEquiv_symm_mul (h : U (cartanSubalgebra R)) (e : U (positiveSubalgebra R)) :
    (borelMulEquiv R).symm
      (UniversalEnvelopingAlgebra.map K
          (LieSubalgebra.inclusion (cartanSubalgebra_le_borelSubalgebra R)) h *
        UniversalEnvelopingAlgebra.map K
          (LieSubalgebra.inclusion (positiveSubalgebra_le_borelSubalgebra R)) e) = h ⊗ₜ e :=
  LieSubalgebra.mulEquivOfLe_symm_mul (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R) h e

/-- The triangular PBW decomposition of the full presentation: multiplication in the order
`n⁻`, `𝔥`, `n⁺` is a linear equivalence, with no finiteness assumptions. -/
noncomputable def triangularMulEquiv :
    U (negativeSubalgebra R) ⊗[K]
      (U (cartanSubalgebra R) ⊗[K] U (positiveSubalgebra R)) ≃ₗ[K]
        U (PresentedLieAlgebra R) :=
  LieSubalgebra.triangularMulEquiv (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R)
    (negativeSubalgebra R) (isCompl_negativeSubalgebra_borelSubalgebra R)

/-- A pure tensor maps to the ordered product of its negative, Cartan, and positive factors. -/
@[simp]
theorem triangularMulEquiv_tmul (f : U (negativeSubalgebra R))
    (h : U (cartanSubalgebra R)) (e : U (positiveSubalgebra R)) :
    triangularMulEquiv R (f ⊗ₜ (h ⊗ₜ e)) =
      UniversalEnvelopingAlgebra.map K (negativeSubalgebra R).incl f *
        UniversalEnvelopingAlgebra.map K (cartanSubalgebra R).incl h *
          UniversalEnvelopingAlgebra.map K (positiveSubalgebra R).incl e :=
  LieSubalgebra.triangularMulEquiv_tmul (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R)
    (negativeSubalgebra R) (isCompl_negativeSubalgebra_borelSubalgebra R) f h e

/-- The inverse triangular decomposition recovers a tensor from an ordered product. -/
@[simp]
theorem triangularMulEquiv_symm_mul_mul (f : U (negativeSubalgebra R))
    (h : U (cartanSubalgebra R)) (e : U (positiveSubalgebra R)) :
    (triangularMulEquiv R).symm
      (UniversalEnvelopingAlgebra.map K (negativeSubalgebra R).incl f *
        UniversalEnvelopingAlgebra.map K (cartanSubalgebra R).incl h *
          UniversalEnvelopingAlgebra.map K (positiveSubalgebra R).incl e) = f ⊗ₜ (h ⊗ₜ e) :=
  LieSubalgebra.triangularMulEquiv_symm_mul_mul (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R)
    (negativeSubalgebra R) (isCompl_negativeSubalgebra_borelSubalgebra R) f h e

/-- Linear maps out of the full enveloping algebra are determined by ordered products. -/
theorem linearMap_ext_triangular {M : Type*} [AddCommMonoid M] [Module K M]
    {g g' : U (PresentedLieAlgebra R) →ₗ[K] M}
    (hg : ∀ (f : U (negativeSubalgebra R)) (h : U (cartanSubalgebra R))
      (e : U (positiveSubalgebra R)),
      g (UniversalEnvelopingAlgebra.map K (negativeSubalgebra R).incl f *
          UniversalEnvelopingAlgebra.map K (cartanSubalgebra R).incl h *
            UniversalEnvelopingAlgebra.map K (positiveSubalgebra R).incl e) =
        g' (UniversalEnvelopingAlgebra.map K (negativeSubalgebra R).incl f *
          UniversalEnvelopingAlgebra.map K (cartanSubalgebra R).incl h *
            UniversalEnvelopingAlgebra.map K (positiveSubalgebra R).incl e)) : g = g' :=
  LieSubalgebra.linearMap_ext_triangular (cartanSubalgebra_le_borelSubalgebra R)
    (positiveSubalgebra_le_borelSubalgebra R)
    (isCompl_cartanSubalgebra_positiveSubalgebra_ofLe R)
    (negativeSubalgebra R) (isCompl_negativeSubalgebra_borelSubalgebra R) hg

end TauCeti.KacMoody
