/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Orbit.HighestWeight

/-!
# Extending the toral action on a highest-weight integral orbit

Let `b` be a rational Lie algebra basis and `φ` a Lie homomorphism into a possibly larger
Lie algebra. A highest-weight vector generates an integral orbit under the simple-generator
Kostant form of `b`. This file proves that adjoining binomial coefficients of additional toral
vectors does not enlarge that orbit, provided their highest weights and their weights on the
lowering generators are integers.

This allows a highest-weight lattice for the derived action to carry the full cocharacter
lattice, including central directions and toral vectors outside the integral coroot span.
No integral splitting of the center and derived algebra is required. The result concerns the
simple-generator form; its comparison with an all-root form is a separate question.

The main result `LieAlgebra.Basis.orbitOfRep_kostantForm_sumElim_eq` identifies the enlarged
orbit with the original one. Consequently `fg_orbitOfRep_kostantForm_sumElim` supplies
finite generation in a finite-dimensional representation. The weight formula and binomial
stability theorem also apply without finite dimensionality.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26.2, 27.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace LieAlgebra.Basis

open TauCeti.UniversalEnvelopingAlgebra

variable {ι D L : Type*} [Finite ι] [LieRing D] [LieAlgebra ℚ D]
  [LieRing L] [LieAlgebra ℚ L] {H : LieSubalgebra ℚ D}
  (b : LieAlgebra.Basis ι H) (φ : D →ₗ⁅ℚ⁆ L)
  {V : Type*} [AddCommGroup V] [Module ℚ V]
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  {κ : Type*} (t : κ → L) {α : ι → κ → ℤ} {wt : κ → ℤ} {v : V}

attribute [local instance] TauCeti.moduleNNRat

local notation "σ" => ρ.comp (TauCeti.UniversalEnvelopingAlgebra.map ℚ φ)

/-- A lowering monomial has integral weight for every additional toral direction, with shift
obtained by adding the weights of its letters with their multiplicities. The homomorphism `φ`
allows the toral vectors to lie outside the source Lie algebra. -/
theorem isCartanWeightVector_map_loweringMonomial
    (hα : ∀ i j, ⁅t j, φ (b.f i)⁆ = (α i j : ℚ) • φ (b.f i))
    (ht : IsCartanWeightVector t ρ wt v) (l : List (ι × ℕ)) :
    IsCartanWeightVector t ρ (wt + (l.map fun p => (p.2 + 1) • α p.1).sum)
      (σ (b.loweringMonomial l) v) := by
  induction l with
  | nil => simpa using ht
  | cons p l ih =>
    have h := IsCartanWeightVector.integralDividedPower
      (fun i => φ (b.f i)) (hα p.1) ih (p.2 + 1)
    have hw : wt + ((p.2 + 1) • α p.1 +
        (l.map fun p => (p.2 + 1) • α p.1).sum) =
        wt + (l.map fun p => (p.2 + 1) • α p.1).sum + (p.2 + 1) • α p.1 := by abel
    rw [List.map_cons, List.sum_cons, hw]
    simpa [loweringMonomial_cons, TauCeti.Associative.map_dividedPower,
      Module.End.smul_def, mul_apply_eq_comp] using h

/-- Binomial coefficients of an additional integral toral direction preserve the highest-weight
Kostant orbit. Only its weights on the lowering generators and on the highest vector are needed;
no commutativity or spanning hypothesis on the additional toral family is imposed. -/
theorem ringChoose_apply_mem_orbitOfRep_kostantForm
    {μ : ι → ℤ} (hv : IsCartanWeightVector b.h σ μ v)
    (he : ∀ i, σ (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0)
    (hα : ∀ i j, ⁅t j, φ (b.f i)⁆ = (α i j : ℚ) • φ (b.f i))
    (ht : IsCartanWeightVector t ρ wt v) (j : κ) (n : ℕ) {x : V}
    (hx : x ∈ Subring.orbitOfRep b.kostantForm σ {v}) :
    ρ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (t j)) n) x ∈
      Subring.orbitOfRep b.kostantForm σ {v} := by
  rw [b.orbitOfRep_kostantForm_eq_span_loweringMonomial hv he] at hx ⊢
  rw [Ring.map_choose]
  exact TauCeti.ringChoose_end_apply_mem_span_of_apply_eq_intCast_smul
    (fun l => (isCartanWeightVector_iff t ρ).1
      (b.isCartanWeightVector_map_loweringMonomial φ ρ t hα ht l) j) n hx

/-- Adjoining the binomial coefficients of integral toral directions leaves the highest-weight
integral orbit unchanged. The enlarged Cartan family retains the original coroot operators and
adds the specified vectors `t`; neither an integral coroot-span condition nor an integral
center/derived splitting is assumed. -/
theorem orbitOfRep_kostantForm_sumElim_eq
    {μ : ι → ℤ} (hv : IsCartanWeightVector b.h σ μ v)
    (he : ∀ i, σ (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0)
    (hα : ∀ i j, ⁅t j, φ (b.f i)⁆ = (α i j : ℚ) • φ (b.f i))
    (ht : IsCartanWeightVector t ρ wt v) :
    Subring.orbitOfRep
        (TauCeti.UniversalEnvelopingAlgebra.kostantForm
          (fun i => φ (rootGenerator b i)) (Sum.elim (fun i => φ (b.h i)) t))
        ρ {v} = Subring.orbitOfRep b.kostantForm σ {v} := by
  have hroot (i : ι ⊕ ι) (n : ℕ) :
      ρ (TauCeti.Associative.dividedPower n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (φ (rootGenerator b i)))) =
      σ (TauCeti.Associative.dividedPower n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator b i))) := by
    simp [TauCeti.Associative.map_dividedPower]
  have hcartan (i : ι) (n : ℕ) :
      ρ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (φ (b.h i))) n) =
      σ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.h i)) n) := by
    simp [Ring.map_choose]
  refine le_antisymm ?_ ?_
  · rw [Subring.orbitOfRep_le_iff]
    intro u hu x hx
    have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    refine kostantForm_apply_mem _ _ ρ _ (fun i n y hy => ?_) (fun j n y hy => ?_)
      u hu (Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v))
    · rw [hroot]
      exact Subring.apply_mem_orbitOfRep_of_mem _ _ _
        (b.dividedPower_mem_kostantForm i n) hy
    · cases j with
      | inl i =>
        rw [Sum.elim_inl, hcartan]
        exact Subring.apply_mem_orbitOfRep_of_mem _ _ _
          (b.ringChoose_mem_kostantForm i n) hy
      | inr j =>
        exact b.ringChoose_apply_mem_orbitOfRep_kostantForm φ ρ t hv he hα ht j n hy
  · have hmap : b.kostantForm ≤
        (TauCeti.UniversalEnvelopingAlgebra.kostantForm (fun i => φ (rootGenerator b i))
          (Sum.elim (fun i => φ (b.h i)) t)).comap
          (TauCeti.UniversalEnvelopingAlgebra.map ℚ φ).toRingHom := by
      rw [b.kostantForm_le_iff]
      constructor
      · intro i n
        simpa [TauCeti.Associative.map_dividedPower] using
          TauCeti.UniversalEnvelopingAlgebra.dividedPower_mem_kostantForm
            (fun i => φ (rootGenerator b i))
            (Sum.elim (fun i => φ (b.h i)) t) i n
      · intro i n
        simpa [Ring.map_choose] using
          TauCeti.UniversalEnvelopingAlgebra.ringChoose_mem_kostantForm
            (fun i => φ (rootGenerator b i))
            (Sum.elim (fun i => φ (b.h i)) t) (.inl i) n
    rw [Subring.orbitOfRep_le_iff]
    intro u hu x hx
    exact Subring.apply_mem_orbitOfRep _ ρ _ (hmap hu) hx

/-- In finite dimension, the highest-weight orbit remains finitely generated after adjoining
integral toral directions, including directions not in the integral coroot lattice. -/
theorem fg_orbitOfRep_kostantForm_sumElim [FiniteDimensional ℚ V]
    {μ : ι → ℤ} (hv : IsCartanWeightVector b.h σ μ v)
    (he : ∀ i, σ (_root_.UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0)
    (hα : ∀ i j, ⁅t j, φ (b.f i)⁆ = (α i j : ℚ) • φ (b.f i))
    (ht : IsCartanWeightVector t ρ wt v) :
    (Subring.orbitOfRep
      (TauCeti.UniversalEnvelopingAlgebra.kostantForm
        (fun i => φ (rootGenerator b i)) (Sum.elim (fun i => φ (b.h i)) t))
      ρ {v}).FG := by
  rw [b.orbitOfRep_kostantForm_sumElim_eq φ ρ t hv he hα ht]
  exact b.fg_orbitOfRep_kostantForm hv he

end LieAlgebra.Basis
