/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Coinduced
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite character levels in coinduced representations

Let `φ : H →* G` and let `ρ` be a representation of `H` on `V`. A coinduced function satisfies
`f (φ h * g) = ρ h (f g)`. In the character weight space for a subgroup `K` it also satisfies
`f (g * k) = χ k • f g`. Thus its values at representatives of `φ(H) \ G / K` determine it.
Evaluation gives a linear injection into one copy of `V` for each double coset. When the class
set and the coefficient dimension are finite, so is this weight space, with dimension at most
the number of classes times the coefficient dimension.

No topology, finiteness of stabilizers, or injectivity of `φ` is required. In particular the
result applies before imposing smoothness on coinduced functions, and hence to spaces of smooth
algebraic modular forms of character level.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§4–6.
* [ShortProof]: grh-lean, https://github.com/lsernau/grh-lean, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`,
  `grh/src/Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean`
  (`New.finite_levelSpace_smoothFormRep`). The finiteness statement follows this source;
  the proof here uses Mathlib's coinduction and the existing character weight spaces.
-/

public section

namespace Representation

section Evaluation

variable {R H G V : Type*} [CommSemiring R] [Group H] [Group G]
  [AddCommMonoid V] [Module R V]
  (ρ : Representation R H V) (φ : H →* G) {K : Subgroup G} (χ : K →* R)
  (c : DoubleCoset.Quotient (φ.range : Set G) K → G)

/-- Evaluation of a coinduced function of character level at a family of double coset
representatives. This is injective when `c` represents every class. -/
def weightSpaceCoindEval :
    weightSpace ((coind φ ρ).comp K.subtype) χ →ₗ[R]
      (DoubleCoset.Quotient (φ.range : Set G) K → V) :=
  LinearMap.pi fun q ↦ (LinearMap.proj (c q)).comp
    ((coindV φ ρ).subtype.comp
      (weightSpace ((coind φ ρ).comp K.subtype) χ).subtype)

/-- Evaluation at `q` is the value of the underlying function at `c q`. -/
-- Evaluate before `MonoidHom.coe_range` normalizes the dependent double coset index type.
@[simp↓]
theorem weightSpaceCoindEval_apply
    (f : weightSpace ((coind φ ρ).comp K.subtype) χ)
    (q : DoubleCoset.Quotient (φ.range : Set G) K) :
    weightSpaceCoindEval ρ φ χ c f q = f.val.val (c q) := (rfl)

/-- Two coinduced functions of the same character level agree if they agree at representatives
of every double coset. -/
theorem weightSpace_coind_ext
    (hc : ∀ q, DoubleCoset.mk φ.range K (c q) = q)
    {f g : weightSpace ((coind φ ρ).comp K.subtype) χ}
    (hfg : ∀ q, f.val.val (c q) = g.val.val (c q)) : f = g := by
  have hf := mem_weightSpace_coind_comp_subtype_iff.mp f.property
  have hg := mem_weightSpace_coind_comp_subtype_iff.mp g.property
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨a, ⟨h, rfl⟩, k, hk, hx⟩ :=
    DoubleCoset.eq.mp (hc (DoubleCoset.mk φ.range K x))
  rw [hx, hf ⟨k, hk⟩, hg ⟨k, hk⟩]
  rw [f.val.property, g.val.property, hfg]

/-- Evaluation on double coset representatives is injective on the character level of a
coinduced representation. -/
theorem weightSpaceCoindEval_injective
    (hc : ∀ q, DoubleCoset.mk φ.range K (c q) = q) :
    Function.Injective (weightSpaceCoindEval ρ φ χ c) := by
  intro f g hfg
  exact weightSpace_coind_ext ρ φ χ c hc fun q ↦ congrFun hfg q

end Evaluation

section Dimension

variable {k H G V : Type*} [Field k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k H V) (φ : H →* G) (K : Subgroup G) (χ : K →* k)
  [Finite (DoubleCoset.Quotient (φ.range : Set G) K)] [FiniteDimensional k V]

/-- A character level in a coinduced representation is finite-dimensional if the double coset
class set and the coefficient dimension are finite. -/
instance finiteDimensional_weightSpace_coind :
    FiniteDimensional k (weightSpace ((coind φ ρ).comp K.subtype) χ) := by
  classical
  exact FiniteDimensional.of_injective
    (weightSpaceCoindEval ρ φ χ (fun q ↦ q.out))
    (weightSpaceCoindEval_injective ρ φ χ (fun q ↦ q.out) DoubleCoset.out_eq')

/-- The dimension of a character level is at most the number of double cosets times the
coefficient dimension. -/
theorem finrank_weightSpace_coind_le :
    Module.finrank k (weightSpace ((coind φ ρ).comp K.subtype) χ) ≤
      Nat.card (DoubleCoset.Quotient (φ.range : Set G) K) * Module.finrank k V := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (φ.range : Set G) K)
  have h := LinearMap.finrank_le_finrank_of_injective
    (weightSpaceCoindEval_injective ρ φ χ (fun q ↦ q.out) DoubleCoset.out_eq')
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card] using h

end Dimension

end Representation
