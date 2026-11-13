/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Projective.Presentation
import TauCeti.RingTheory.Almost.ValuationRing

/-!
# Almost finite presentation from finite free factorizations

Importing checks for arbitrary basic setups and caller module structures, including zero-rank
free modules, the basic ideal, and an infinite free module in the zero setup. The kernel estimate
also allows a cokernel annihilator that is not contained in the basic ideal.
-/

open TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] (S : BasicSetup V)
  {M : Type*} [AddCommGroup M] [Module V M]

example (h : S.IsAlmostFiniteProjective M) : S.AlmostFP M :=
  h.almostFP

example (h : ∀ ε ∈ S.ideal,
    ∃ (n : ℕ) (u : M →ₗ[V] Fin n → V) (v : (Fin n → V) →ₗ[V] M),
      v ∘ₗ u = ε • LinearMap.id) : S.AlmostFP M :=
  (isAlmostFiniteProjective_iff.mpr h).almostFP

example (h : S.IsAlmostFiniteProjective M) {J K : Ideal V} (hJ : J.FG)
    (hK : K ≤ S.ideal) (hKfg : K.FG)
    {P : Type*} [AddCommGroup P] [Module V P] [Module.Finite V P] (φ : P →ₗ[V] M)
    (hφ : J • (⊤ : Submodule V M) ≤ LinearMap.range φ) :
    ∃ L ≤ LinearMap.ker φ, L.FG ∧ (J * K) • LinearMap.ker φ ≤ L :=
  h.exists_fg_smul_ker_le hJ hK hKfg φ hφ

example (n : ℕ) : S.AlmostFP (Fin n → V) :=
  (isAlmostFiniteProjective_of_finite_of_projective S).almostFP

example : S.AlmostFP (Fin 0 → V) :=
  (isAlmostFiniteProjective_of_finite_of_projective S).almostFP

-- The ideal need not be finitely generated, but its almost module is finitely presented.
example : S.AlmostFP S.ideal :=
  (S.isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective S)).almostFP

example : S.AlmostFP (V ⧸ S.ideal) :=
  S.isAlmostZero_quotient.isAlmostFiniteProjective.almostFP

example : (zero ℤ).AlmostFP (ℕ →₀ ℤ) :=
  (isAlmostFiniteProjective_zero (N := ℕ →₀ ℤ)).almostFP

section ValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
  (h : ¬ (IsLocalRing.maximalIdeal O).FG)

example : (ofValuationRing h).AlmostFP (ofValuationRing h).ideal :=
  ((ofValuationRing h).isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective _)).almostFP

example : ¬ Module.Finite O (ofValuationRing h).ideal := by
  rwa [Module.Finite.iff_fg, ofValuationRing_ideal]

end ValuationRing
