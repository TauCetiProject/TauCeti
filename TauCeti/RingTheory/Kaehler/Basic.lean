/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Basic induction and presentation descent for Kähler differentials

Mathlib constructs the module of Kähler differentials `Ω[S⁄R]` together with two structural tools:
`KaehlerDifferential.span_range_derivation` (showing that exact differentials `D R S s` generate
`Ω[S⁄R]` over `S`) and `KaehlerDifferential.quotKerTotalEquiv` (identifying `Ω[S⁄R]` with the
quotient of the free `S`-module `S →₀ S` by `KaehlerDifferential.kerTotal R S`).

This file packages those two facts for downstream constructions of non-`S`-linear operators on
`Ω[S⁄R]` (such as the degree-one exterior differential `s • D t ↦ D s ∧ D t` and Lie derivatives
along derivations of `S`):

* `KaehlerDifferential.inductionOn`: `S`-linear span induction on `Ω[S⁄R]` with cases `0`,
  `D R S s`, `s • ω`, and `ω₁ + ω₂`.
* `TauCeti.KaehlerDifferential.liftOfKerTotal`: descends any `k`-linear map `(S →₀ S) →ₗ[k] M`
  vanishing on `KaehlerDifferential.kerTotal R S` to a `k`-linear map `Ω[S⁄R] →ₗ[k] M`, over an
  arbitrary commutative base ring `k` with `[Algebra k S]`.
-/

public section

namespace KaehlerDifferential

/-- **Span induction on Kähler differentials**: to prove a predicate on `ω : Ω[S⁄R]`, it suffices to
verify it on `0` and exact differentials `D R S s`, and show closure under `S`-scalar multiplication
and addition. -/
@[elab_as_elim]
theorem inductionOn {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {motive : Ω[S⁄R] → Prop} (ω : Ω[S⁄R])
    (zero : motive 0)
    (D : ∀ s : S, motive (KaehlerDifferential.D R S s))
    (smul : ∀ (s : S) (ω : Ω[S⁄R]), motive ω → motive (s • ω))
    (add : ∀ ω₁ ω₂ : Ω[S⁄R], motive ω₁ → motive ω₂ → motive (ω₁ + ω₂)) :
    motive ω := by
  refine Submodule.span_induction ?_ zero (fun _ _ _ _ ↦ add _ _) (fun s _ _ ↦ smul s _)
    (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
      ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)))
  rintro _ ⟨s, rfl⟩
  exact D s

end KaehlerDifferential

namespace TauCeti.KaehlerDifferential

variable {k S M : Type*} (R : Type*) [CommRing k] [CommRing R] [CommRing S]
  [Algebra k S] [Algebra R S] [AddCommGroup M] [Module k M]

/-- **Presentation descent for `Ω[S⁄R]`**: any `k`-linear map `f : (S →₀ S) →ₗ[k] M` that vanishes
on `KaehlerDifferential.kerTotal R S` descends along `Finsupp.linearCombination S (D R S)` to a
`k`-linear map `Ω[S⁄R] →ₗ[k] M`. -/
noncomputable def liftOfKerTotal (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) : Ω[S⁄R] →ₗ[k] M :=
  (((_root_.KaehlerDifferential.kerTotal R S).restrictScalars k).liftQ f
    fun v hv ↦ hf v ((Submodule.restrictScalars_mem k _ v).mp hv)).comp
    ((Submodule.Quotient.restrictScalarsEquiv k
        (_root_.KaehlerDifferential.kerTotal R S)).symm.toLinearMap.comp
      ((_root_.KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.restrictScalars k))

variable {R}

/-- Evaluating `liftOfKerTotal` on a formal `S`-linear combination of exact differentials recovers
`f`. -/
@[simp]
theorem liftOfKerTotal_linearCombination (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) (w : S →₀ S) :
    liftOfKerTotal R f hf
        (Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) w) = f w := by
  have hw : (_root_.KaehlerDifferential.quotKerTotalEquiv R S).symm
      (Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) w) =
      Submodule.Quotient.mk w := by
    rw [_root_.KaehlerDifferential.quotKerTotalEquiv_symm_apply]
    exact congr($(_root_.KaehlerDifferential.derivationQuotKerTotal_lift_comp_linearCombination R S)
      w)
  simp only [liftOfKerTotal, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, hw, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.liftQ_apply _ _ w

/-- Evaluating `liftOfKerTotal` on `D R S s` gives `f (Finsupp.single s 1)`. -/
@[simp]
theorem liftOfKerTotal_D (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0) (s : S) :
    liftOfKerTotal R f hf (_root_.KaehlerDifferential.D R S s) = f (Finsupp.single s 1) := by
  rw [← one_smul S (_root_.KaehlerDifferential.D R S s), ← Finsupp.linearCombination_single,
    liftOfKerTotal_linearCombination]

/-- `liftOfKerTotal R f hf` is uniquely determined by its values on
`Finsupp.linearCombination S (D R S) w`. -/
theorem liftOfKerTotal_unique (f : (S →₀ S) →ₗ[k] M)
    (hf : ∀ v ∈ _root_.KaehlerDifferential.kerTotal R S, f v = 0)
    {g : Ω[S⁄R] →ₗ[k] M}
    (hg : ∀ w : S →₀ S,
      g (Finsupp.linearCombination S (_root_.KaehlerDifferential.D R S) w) = f w) :
    g = liftOfKerTotal R f hf := by
  refine LinearMap.ext fun ω ↦ ?_
  obtain ⟨w, rfl⟩ := _root_.KaehlerDifferential.linearCombination_surjective R S ω
  rw [hg, liftOfKerTotal_linearCombination]

end TauCeti.KaehlerDifferential
