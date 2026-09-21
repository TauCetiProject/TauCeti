/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Lie.Killing.DualBasis
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

-- Non-public: the enveloping-algebra dictionary appears only inside proofs.
import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# The Casimir element of a universal enveloping algebra

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate.  Choosing a basis `x₁, …, xₙ` of `L` and the basis `y₁, …, yₙ` dual to it under `κ`,
the **Casimir element** is

`Ω = ∑ᵢ xᵢ yᵢ ∈ U(L)`,

a distinguished element of the universal enveloping algebra.  In the classical setting of a split
semisimple Lie algebra in characteristic zero it is the source of Weyl's complete reducibility
theorem: it is central, so it acts on any module by a module endomorphism, and on a highest weight
module by a scalar that separates the trivial module from the others.  Those extra hypotheses are
needed only for that application; centrality, the statement proved here, needs nothing beyond a
nondegenerate Killing form.

Two facts make `Ω` an invariant of `L` rather than of the chosen basis. They are developed in
`TauCeti.Algebra.Lie.Killing.DualBasis` and applied here.

* `Ω` does not depend on the basis.  The mechanism is `TauCeti.sum_apply_killingDualBasis_eq`:
  for *every* `K`-bilinear map `f` out of `L × L`, the value `∑ᵢ f xᵢ yᵢ` is the same for all
  bases, because expanding one basis in the other exchanges the two dual bases.  The Casimir
  element is the instance `f x y = x * y` in `U(L)`, so `TauCeti.casimirElement_eq_sum` computes
  it from any basis at all, and the chosen basis in the definition is immaterial.
* `Ω` is central (`TauCeti.casimirElement_mem_center`).  The same bilinear mechanism gives
  `TauCeti.sum_apply_lie_killingDualBasis_add_eq_zero`, the statement that the element
  `∑ᵢ xᵢ ⊗ yᵢ` is annihilated by the adjoint action of `L`; this is exactly the invariance
  `κ ⁅z, x⁆ y = -κ x ⁅z, y⁆` of the Killing form, summed.  Feeding it the commutator identity
  `ι z * ι x - ι x * ι z = ι ⁅z, x⁆` turns it into `ι z * Ω = Ω * ι z`, and the canonical Lie
  generators generate `U(L)` (`TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`), so `Ω`
  commutes with everything.

Only nondegeneracy, symmetry and invariance of the Killing form are used, so the argument below
would go through for any invariant nondegenerate symmetric form once the definitions and lemmas
are parameterised by such a form; as written they are stated for the Killing form, which is the
canonical choice this development needs and the one the roadmap pins.

## Main definitions

* `TauCeti.casimirElement`: the Casimir element of `U(L)`.

## Main results

* `TauCeti.sum_killingForm_killingDualBasis_eq_trace`: the sum `∑ᵢ κ (p xᵢ) yᵢ` is the trace of the
  endomorphism `p`.
* `TauCeti.sum_apply_killingDualBasis_of_isAdjointPair`: a pair of endomorphisms adjoint for the
  Killing form may be moved from the first slot of `f` to the second.
* `TauCeti.casimirElement_eq_sum`: the Casimir element is `∑ᵢ xᵢ yᵢ` for **any** basis `x` of `L`
  and its Killing-dual basis `y`, so the basis chosen in the definition does not matter.
* `TauCeti.representation_casimirElement_apply_eq_zero_of_isTrivial`: the Casimir element acts by
  zero on a module with trivial Lie action.
* `TauCeti.ι_mul_casimirElement`: the Casimir element commutes with every canonical Lie generator.
* `TauCeti.representation_casimirElement_lie`: the Casimir operator of a module commutes with the
  Lie action.
* `TauCeti.map_representation_casimirElement`: a homomorphism of Lie modules intertwines the
  Casimir operators.
* `TauCeti.casimirElement_mem_center`: **the Casimir element is central in `U(L)`.**

The remaining statement about `casimirElement`, that it acts on a highest weight module of weight
`λ` by the scalar `⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩`, is not proved here but in
`TauCeti/Algebra/Lie/HighestWeight/Casimir.lean`, which is where the highest weight vectors and the
invariant form on weights that it is phrased in are available.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*, Chapter I, §3, no. 7 ("Casimir
  element"), Proposition 11: given an invariant bilinear form whose restriction to an ideal `a` is
  nondegenerate, the element `c = Σᵢ eᵢ eᵢ'` built from a basis of `a` and the dual basis of `a`
  is independent of that basis and commutes with the whole Lie algebra.  Taking `a` to be all of
  `L` and the form to be the Killing form gives the two statements proved here; Bourbaki is
  strictly more general, since the form may be degenerate on `L` and the sum then runs over a basis
  of the proper ideal `a`, which is beyond the generality noted above.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §6.2, which builds
  the Casimir element of the trace form of a faithful representation of a semisimple Lie algebra;
  the Killing form is the case of the adjoint representation.
* [Highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 5, "The Casimir element".
-/

public section

open Finset LieAlgebra LieModule UniversalEnvelopingAlgebra

namespace TauCeti

universe u v

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

/-! ### The Casimir element -/

variable [FiniteDimensional K L]

variable (K L) in
/-- Multiplying two canonical Lie generators of `U(L)`, as a `K`-bilinear map.  This is the
bilinear map that turns the invariance of `∑ᵢ xᵢ ⊗ yᵢ` into the centrality of the Casimir
element. -/
private noncomputable def genMul :
    L →ₗ[K] L →ₗ[K] UniversalEnvelopingAlgebra K L :=
  LinearMap.mk₂ K (fun x y ↦ ι K x * ι K y)
    (fun _ _ _ ↦ by rw [map_add, add_mul]) (fun _ _ _ ↦ by rw [map_smul, smul_mul_assoc])
    (fun _ _ _ ↦ by rw [map_add, mul_add]) (fun _ _ _ ↦ by rw [map_smul, mul_smul_comm])

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem genMul_apply (x y : L) : genMul K L x y = ι K x * ι K y := (rfl)

variable (K L) in
/-- **The Casimir element** `Ω = ∑ᵢ xᵢ yᵢ ∈ U(L)` of a Lie algebra with nondegenerate Killing
form, built from a basis `x` of `L` and the basis `y` dual to it under the Killing form.

The definition names a particular basis, but the element does not depend on it:
`TauCeti.casimirElement_eq_sum` evaluates `Ω` against an arbitrary basis. -/
noncomputable def casimirElement : UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (Module.finBasis K L i) * ι K (killingDualBasis (Module.finBasis K L) i)

/-- **The Casimir element is `∑ᵢ xᵢ yᵢ` for every basis `x` of `L`** and its Killing-dual basis
`y`, so the basis chosen in the definition is immaterial. -/
theorem casimirElement_eq_sum {ι' : Type*} [DecidableEq ι'] [Fintype ι']
    (b : Module.Basis ι' K L) :
    casimirElement K L = ∑ i, ι K (b i) * ι K (killingDualBasis b i) := by
  simp only [casimirElement, ← genMul_apply]
  exact sum_apply_killingDualBasis_eq (genMul K L) (Module.finBasis K L) b

/-- **The Casimir element acts by zero on a module with trivial action.** Every summand
`xᵢ yᵢ` of `Ω` acts by a double bracket, and brackets vanish. -/
@[simp]
theorem representation_casimirElement_apply_eq_zero_of_isTrivial
    {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [LieModule.IsTrivial L M] (m : M) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m = 0 := by
  classical
  rw [casimirElement_eq_sum (Module.finBasis K L), map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_mul, Module.End.mul_apply, UniversalEnvelopingAlgebra.representation_ι,
    UniversalEnvelopingAlgebra.representation_ι]
  simp [trivial_lie_zero]

/-- **The Casimir element commutes with every canonical Lie generator.**  Expanding the commutator
of `ι z` with each summand `xᵢ yᵢ` by the Leibniz rule replaces the bracket by the adjoint action
on `∑ᵢ xᵢ ⊗ yᵢ`, which vanishes. -/
theorem ι_mul_casimirElement (z : L) :
    ι K z * casimirElement K L = casimirElement K L * ι K z := by
  classical
  set b := Module.finBasis K L with hb
  rw [← sub_eq_zero, casimirElement_eq_sum b, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  have hcomm : ∀ x y : L, ι K x * ι K y - ι K y * ι K x = ι K (⁅x, y⁆ : L) := fun x y ↦ by
    simpa using TauCeti.UniversalEnvelopingAlgebra.mul_sub_mul_eq_map_ι_lie
      (AlgHom.id K (UniversalEnvelopingAlgebra K L)) x y
  have step : ∀ i, ι K z * (ι K (b i) * ι K (killingDualBasis b i))
      - ι K (b i) * ι K (killingDualBasis b i) * ι K z
      = genMul K L ⁅z, b i⁆ (killingDualBasis b i)
        + genMul K L (b i) ⁅z, killingDualBasis b i⁆ := by
    intro i
    rw [genMul_apply, genMul_apply, ← hcomm z (b i), ← hcomm z (killingDualBasis b i)]
    noncomm_ring
  rw [sum_congr rfl fun i _ ↦ step i, Finset.sum_add_distrib]
  exact sum_apply_lie_killingDualBasis_add_eq_zero (genMul K L) b z

variable (K L) in
/-- **The Casimir element is central in `U(L)`.**  It commutes with the canonical Lie generators,
which generate `U(L)` as an algebra. -/
theorem casimirElement_mem_center :
    casimirElement K L ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L) := by
  refine Subalgebra.mem_center_iff.mpr fun u ↦ ?_
  induction u using TauCeti.UniversalEnvelopingAlgebra.induction_ι with
  | ι z => exact ι_mul_casimirElement (K := K) z
  | algebraMap r => exact Algebra.commutes r _
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

/-- **The Casimir element commutes with the Lie action.**  This is the centrality of the Casimir
element, read on a module: the Casimir operator of a module is a homomorphism of Lie modules. -/
@[simp]
theorem representation_casimirElement_lie
    {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (x : L) (m : M) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) ⁅x, m⁆ =
      ⁅x, UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m⁆ :=
  UniversalEnvelopingAlgebra.representation_lie_of_mem_center K L M
    (casimirElement_mem_center K L) x m

/-- **The Casimir operator is natural in the module.**  A homomorphism of Lie modules intertwines
the two Casimir operators, being equivariant for the whole enveloping algebra.  This is
`TauCeti.UniversalEnvelopingAlgebra.map_representation`, which carries the `simp` attribute, at the
Casimir element. -/
theorem map_representation_casimirElement
    {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    {N : Type*} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
    (f : M →ₗ⁅K,L⁆ N) (m : M) :
    f (UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m) =
      UniversalEnvelopingAlgebra.representation K L N (casimirElement K L) (f m) :=
  UniversalEnvelopingAlgebra.map_representation K L M N f (casimirElement K L) m

end TauCeti
