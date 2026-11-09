/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Teichmuller
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# The inverse-limit topology on perfection

The multiplicative perfection has the subspace topology from its coordinates. For an
`I`-adically complete ring whose topology is `I`-adic, reduction modulo `I` identifies its
multiplicative perfection homeomorphically with the perfection of the discrete quotient, provided
that quotient has characteristic `p`. The inverse is continuous because its zeroth coordinate,
the Teichmüller map, is determined modulo `I ^ (n + 1)` by the `n`-th coordinate.

This is the topological comparison used to identify integral tilts with inverse limits of
residue rings. The algebraic equivalence and its approximation estimate are Mathlib's
`Perfection.quotientMulEquiv` and `Perfection.teichmuller₀_sModEq`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2(i).
* P. Scholze, *Perfectoid spaces*, Lemma 3.4(i).
-/

public section

open Filter Topology

namespace Perfection

variable {M : Type*} {p : ℕ}

section Topology

variable [Pow M ℕ]

/-- The inverse-limit topology on multiplicative perfection. -/
instance instTopologicalSpace [TopologicalSpace M] : TopologicalSpace (Perfection M p) :=
  TopologicalSpace.induced Subtype.val inferInstance

/-- The coordinate sequence embeds the perfection in the product of its factors. -/
theorem isEmbedding_val [TopologicalSpace M] :
    Topology.IsEmbedding (Subtype.val : Perfection M p → ℕ → M) :=
  .subtypeVal

end Topology

section CommMonoid

variable [CommMonoid M] [TopologicalSpace M]

/-- Continuity into perfection is equivalent to continuity of every coordinate. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → Perfection M p} :
    Continuous f ↔ ∀ n, Continuous (fun x ↦ coeffMonoidHom M p n (f x)) :=
  isEmbedding_val.isInducing.continuous_iff.trans continuous_pi_iff

/-- Each coordinate of multiplicative perfection is continuous. -/
@[continuity, fun_prop]
theorem continuous_coeffMonoidHom (n : ℕ) : Continuous (coeffMonoidHom M p n) :=
  continuous_iff.mp continuous_id n

/-- Shifting the coordinate sequence is continuous. -/
@[continuity, fun_prop]
theorem continuous_pthRootMonoidHom : Continuous (pthRootMonoidHom M p) :=
  continuous_iff.mpr fun n ↦ continuous_coeffMonoidHom (n + 1)

end CommMonoid

section CommSemiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [Fact p.Prime] [CharP R p]

/-- Each ring coordinate of perfection is continuous. -/
@[continuity, fun_prop]
theorem continuous_coeff (n : ℕ) : Continuous (coeff R p n) :=
  continuous_coeffMonoidHom n

/-- The ring homomorphism shifting the root sequence is continuous. -/
@[continuity, fun_prop]
theorem continuous_pthRoot : Continuous (pthRoot R p) :=
  continuous_pthRootMonoidHom

end CommSemiring

/-- The coordinatewise ring operations on a characteristic-`p` perfection are continuous. -/
instance instIsTopologicalRing {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Fact p.Prime] [CharP R p] :
    IsTopologicalRing (Perfection R p) :=
  inferInstanceAs (IsTopologicalRing (subring R p))

section Adic

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Fact p.Prime] {I : Ideal R} [CharP (R ⧸ I) p] [IsAdicComplete I R]

/-- The Teichmüller map from the perfection of the discrete residue ring is continuous
for the adic topology on the target. -/
theorem continuous_teichmuller₀ (hI : IsAdic I) : Continuous (teichmuller₀ p I) := by
  have := hI.discreteTopology_quotient
  refine continuous_iff_continuousAt.mpr fun x ↦
    (hI.hasBasis_nhds _).tendsto_right_iff.mpr fun n _ ↦ ?_
  have he : ∀ᶠ y in 𝓝 x, coeff (R ⧸ I) p n y = coeff (R ⧸ I) p n x :=
    (continuous_coeff (R := R ⧸ I) (p := p) n).continuousAt
      ((isOpen_discrete ({coeff (R ⧸ I) p n x} : Set (R ⧸ I))).mem_nhds (by simp))
  filter_upwards [he] with y hy
  have hx := teichmuller₀_sModEq (p := p) (I := I)
    (Ideal.Quotient.mk_out (coeff (R ⧸ I) p n x))
  have hy' := teichmuller₀_sModEq (p := p) (I := I)
    ((Ideal.Quotient.mk_out (coeff (R ⧸ I) p n x)).trans hy.symm)
  refine ⟨teichmuller₀ p I y - teichmuller₀ p I x, ?_, by simp⟩
  exact SModEq.sub_mem.mp <|
    (hy'.trans hx.symm).mono (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- If the topology of `R` is `I`-adic, `R` is `I`-adically complete, and `R ⧸ I` has
characteristic `p`, reduction is a homeomorphism on multiplicative perfections.
The quotient topology on the factors is discrete; perfections carry the inverse-limit topology. -/
theorem isHomeomorph_quotientMulEquiv (hI : IsAdic I) :
    IsHomeomorph (quotientMulEquiv p I : Perfection R p → Perfection (R ⧸ I) p) := by
  have hmk : Continuous (Ideal.Quotient.mk I) := continuous_quot_mk
  have hf : Continuous (quotientMulEquiv p I : Perfection R p → Perfection (R ⧸ I) p) :=
    continuous_iff.mpr fun n ↦ hmk.comp (continuous_coeffMonoidHom n)
  have hg : Continuous ((quotientMulEquiv p I).symm : Perfection (R ⧸ I) p → Perfection R p) :=
    continuous_iff.mpr fun n ↦ by
      simpa only [coeffMonoidHom_symm_quotientMulEquiv, Function.comp_def] using
        (continuous_teichmuller₀ hI).comp (continuous_pthRootMonoidHom.iterate n)
  exact ((quotientMulEquiv p I).toEquiv.isHomeomorph_iff).mpr ⟨hf, hg⟩

end Adic

end Perfection
