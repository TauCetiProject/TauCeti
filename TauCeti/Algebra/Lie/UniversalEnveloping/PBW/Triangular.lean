/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Decomposition

/-!
# PBW multiplication for nested complements

The relative PBW theorem gives `U(A) ⊗ U(B) ≃ U(L)` for complementary free subalgebras.
Here we transport it along inclusions to obtain `U(H) ⊗ U(P) ≃ U(B)` when `H` and `P`
complement each other inside `B`, and compose it with a complement `N` of `B` to obtain
`U(N) ⊗ (U(H) ⊗ U(P)) ≃ U(L)`. Computation, inverse and extensionality rules are shared
by the finite-type and Kac–Moody specializations.

These constructions extract the hypothesis-independent assembly from
`TauCeti.Algebra.Lie.UniversalEnveloping.Triangular`. They require only free factors over a
commutative ring, with no finite-dimensionality or characteristic assumption.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.4 and §20.3.
-/

public section

namespace LieSubalgebra

open TauCeti
open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R

section Nested

variable {H P B : LieSubalgebra R L} (hH : H ≤ B) (hP : P ≤ B)
  (hHP : IsCompl (H.ofLe hH).toSubmodule (P.ofLe hP).toSubmodule)
  [Module.Free R H] [Module.Free R P]

/-- Multiplication identifies the enveloping algebras of two complementary subalgebras of `B`
with `U(B)`, retaining their original carriers in the domain. -/
noncomputable def mulEquivOfLe : U H ⊗[R] U P ≃ₗ[R] U B :=
  letI := Module.Free.of_equiv (equivOfLe hH).toLinearEquiv
  letI := Module.Free.of_equiv (equivOfLe hP).toLinearEquiv
  (TensorProduct.congr
    (UniversalEnvelopingAlgebra.mapEquiv R (equivOfLe hH)).toLinearEquiv
    (UniversalEnvelopingAlgebra.mapEquiv R (equivOfLe hP)).toLinearEquiv).trans
    (mulEquiv _ _ hHP)

/-- The transported PBW equivalence multiplies the images under the two inclusions. -/
@[simp]
theorem mulEquivOfLe_tmul (h : U H) (p : U P) :
    mulEquivOfLe hH hP hHP (h ⊗ₜ p) =
      UniversalEnvelopingAlgebra.map R (inclusion hH) h *
        UniversalEnvelopingAlgebra.map R (inclusion hP) p := by
  simp only [mulEquivOfLe, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    mulEquiv_tmul, AlgEquiv.toLinearEquiv_apply,
    ← AlgEquiv.toAlgHom_apply, UniversalEnvelopingAlgebra.mapEquiv_toAlgHom,
    ← AlgHom.comp_apply, ← UniversalEnvelopingAlgebra.map_comp]
  -- Composing the inclusion with `equivOfLe` gives the original inclusion.
  rfl

/-- The inverse transported PBW equivalence recovers the two tensor factors. -/
@[simp]
theorem mulEquivOfLe_symm_mul (h : U H) (p : U P) :
    (mulEquivOfLe hH hP hHP).symm
      (UniversalEnvelopingAlgebra.map R (inclusion hH) h *
        UniversalEnvelopingAlgebra.map R (inclusion hP) p) = h ⊗ₜ p := by
  rw [← mulEquivOfLe_tmul hH hP hHP, LinearEquiv.symm_apply_apply]

variable (N : LieSubalgebra R L) (hNB : IsCompl N.toSubmodule B.toSubmodule)
  [Module.Free R N]

/-- Two successive PBW decompositions identify three ordered enveloping factors with `U(L)`.
Freeness of the intermediate subalgebra follows from its complementary free factors. -/
noncomputable def triangularMulEquiv : U N ⊗[R] (U H ⊗[R] U P) ≃ₗ[R] U L :=
  letI := Module.Free.of_equiv (equivOfLe hH).toLinearEquiv
  letI := Module.Free.of_equiv (equivOfLe hP).toLinearEquiv
  letI := Module.Free.of_equiv (Submodule.prodEquivOfIsCompl _ _ hHP)
  (TensorProduct.congr (LinearEquiv.refl R _) (mulEquivOfLe hH hP hHP)).trans
    (mulEquiv N B hNB)

/-- The triangular PBW equivalence sends a pure tensor to the ordered product of its images. -/
@[simp]
theorem triangularMulEquiv_tmul (n : U N) (h : U H) (p : U P) :
    triangularMulEquiv hH hP hHP N hNB (n ⊗ₜ (h ⊗ₜ p)) =
      UniversalEnvelopingAlgebra.map R N.incl n *
        UniversalEnvelopingAlgebra.map R H.incl h *
          UniversalEnvelopingAlgebra.map R P.incl p := by
  simp only [triangularMulEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, mulEquivOfLe_tmul, mulEquiv_tmul, map_mul,
    ← AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_incl_comp_map_inclusion, mul_assoc]

/-- The inverse triangular PBW equivalence recovers the three factors of an ordered product. -/
@[simp]
theorem triangularMulEquiv_symm_mul_mul (n : U N) (h : U H) (p : U P) :
    (triangularMulEquiv hH hP hHP N hNB).symm
      (UniversalEnvelopingAlgebra.map R N.incl n *
        UniversalEnvelopingAlgebra.map R H.incl h *
          UniversalEnvelopingAlgebra.map R P.incl p) = n ⊗ₜ (h ⊗ₜ p) := by
  rw [← triangularMulEquiv_tmul hH hP hHP N hNB, LinearEquiv.symm_apply_apply]

include hH hP hHP hNB in
/-- Linear maps out of the ambient enveloping algebra are determined on ordered products
of the three complementary factors. -/
theorem linearMap_ext_triangular {M : Type*} [AddCommMonoid M] [Module R M]
    {g g' : U L →ₗ[R] M}
    (hg : ∀ (n : U N) (h : U H) (p : U P),
      g (UniversalEnvelopingAlgebra.map R N.incl n *
          UniversalEnvelopingAlgebra.map R H.incl h *
            UniversalEnvelopingAlgebra.map R P.incl p) =
        g' (UniversalEnvelopingAlgebra.map R N.incl n *
          UniversalEnvelopingAlgebra.map R H.incl h *
            UniversalEnvelopingAlgebra.map R P.incl p)) : g = g' := by
  have hcomp : g ∘ₗ (triangularMulEquiv hH hP hHP N hNB).toLinearMap =
      g' ∘ₗ (triangularMulEquiv hH hP hHP N hNB).toLinearMap :=
    TensorProduct.ext_threefold' fun n h p => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, triangularMulEquiv_tmul] using hg n h p
  refine LinearMap.ext fun u => ?_
  obtain ⟨t, rfl⟩ := (triangularMulEquiv hH hP hHP N hNB).surjective u
  exact LinearMap.congr_fun hcomp t

end Nested

end LieSubalgebra
