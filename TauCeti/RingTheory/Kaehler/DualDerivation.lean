/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Derivations dual to a basis of Kähler differentials

Let `A` be a commutative `R`-algebra. A derivation of `A` into an `A`-module is determined by its
values on any family `s` whose differentials `ds_i` span `Ω[A⁄R]`
(`Derivation.ext_of_span_kaehlerD_eq_top`), just as it is determined by its values on generators
of `A` as an algebra (`Derivation.ext_of_adjoin_eq_top`). The second criterion does not apply to
étale coordinates: for the coordinate `x` on `𝔽_p(x)` over `𝔽_p`, the differential `dx` spans
`Ω`, but `x` does not generate `𝔽_p(x)` as an algebra.

For a basis `b` of `Ω[A⁄R]`, the derivation dual to `b i` is the `i`-th coordinate of the
universal differential, `∂_i = b.dualDerivation i`. When the basis consists of exact
differentials `b i = ds_i`, the `∂_i` are the partial derivatives in the coordinates `s_i`:
`∂_i s_j = δ_ij`, they commute pairwise, and every derivation `D` of `A` is the finite
combination `D = ∑ i, D (s i) • ∂_i` when the coordinates are finite in number.

## Main declarations

* `Derivation.ext_of_span_kaehlerD_eq_top`: derivations agreeing on a family whose differentials
  span `Ω[A⁄R]` are equal.
* `Module.Basis.dualDerivation`: the derivation dual to an element of a basis of `Ω[A⁄R]`.
* `Module.Basis.lie_dualDerivation_eq_zero`: the derivations dual to a basis of exact
  differentials commute.
* `Module.Basis.sum_dualDerivation_smul`, `Module.Basis.sum_smul_dualDerivation`: a derivation
  is the combination of the dual derivations with coefficients its values on the coordinates.

## References

* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175--232, (5.4.3)--(5.4.4).
-/

public section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

namespace Derivation

/-- A derivation is determined by its values on a set whose differentials span `Ω[A⁄R]`. -/
theorem ext_of_span_kaehlerD_eq_top {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] {D₁ D₂ : Derivation R A M} (s : Set A)
    (hs : Submodule.span A (KaehlerDifferential.D R A '' s) = ⊤) (h : Set.EqOn D₁ D₂ s) :
    D₁ = D₂ := by
  have hlift : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [liftKaehlerDifferential_comp_D, liftKaehlerDifferential_comp_D, h ha]
  rw [← D₁.liftKaehlerDifferential_comp, ← D₂.liftKaehlerDifferential_comp, hlift]

end Derivation

namespace Module.Basis

variable {ι : Type*}

/-- The derivation dual to the `i`-th element of a basis `b` of `Ω[A⁄R]`: the `i`-th coordinate,
with respect to `b`, of the universal differential. -/
noncomputable def dualDerivation (b : Basis ι A Ω[A⁄R]) (i : ι) : Derivation R A A :=
  (b.coord i).compDer (KaehlerDifferential.D R A)

/-- The derivation dual to `b i` sends `a` to the `i`-th coordinate of `da`. -/
@[simp]
theorem dualDerivation_apply (b : Basis ι A Ω[A⁄R]) (i : ι) (a : A) :
    b.dualDerivation i a = b.repr (KaehlerDifferential.D R A a) i := by
  simp [dualDerivation]

variable {b : Basis ι A Ω[A⁄R]} {s : ι → A}

/-- If `b` is the basis `ds_i` of exact differentials, `∂_i s_j = δ_ij`. -/
theorem dualDerivation_apply_of_kaehlerD_eq [DecidableEq ι]
    (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i) (i j : ι) :
    b.dualDerivation i (s j) = if j = i then 1 else 0 := by
  simp [hs, Finsupp.single_apply]

/-- If `b` is the basis `ds_i` of exact differentials, a derivation `∂_i` dual to `b` kills the
value at `s_k` of any derivation `∂_j` dual to `b`, which is `0` or `1`. -/
theorem dualDerivation_apply_dualDerivation_apply_of_kaehlerD_eq
    (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i) (i j k : ι) :
    b.dualDerivation i (b.dualDerivation j (s k)) = 0 := by
  classical
  rw [dualDerivation_apply_of_kaehlerD_eq hs]
  split_ifs <;> simp

/-- If `b` is the basis `ds_i` of exact differentials, a derivation into an `A`-module is
determined by its values on the `s_i`. -/
theorem _root_.Derivation.ext_of_kaehlerD_eq_basis {M : Type*} [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i)
    {D₁ D₂ : Derivation R A M} (h : ∀ i, D₁ (s i) = D₂ (s i)) : D₁ = D₂ := by
  refine Derivation.ext_of_span_kaehlerD_eq_top (Set.range s) ?_ ?_
  · rw [← Set.range_comp, Function.comp_def]
    simp only [hs]
    exact b.span_eq
  · rintro _ ⟨i, rfl⟩
    exact h i

/-- **Coordinate derivations commute.** If `b` is the basis `ds_i` of exact differentials, the
dual derivations `∂_i` commute pairwise: `⁅∂_i, ∂_j⁆ = 0`. -/
theorem lie_dualDerivation_eq_zero (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i) (i j : ι) :
    ⁅b.dualDerivation i, b.dualDerivation j⁆ = 0 :=
  Derivation.ext_of_kaehlerD_eq_basis hs fun k ↦ by
    simp only [Derivation.commutator_apply,
      dualDerivation_apply_dualDerivation_apply_of_kaehlerD_eq hs, sub_self,
      zero_apply]

/-- **A derivation in coordinates.** If `b` is a finite basis `ds_i` of exact differentials,
every derivation `D` of `A` into an `A`-module satisfies `D a = ∑ i, ∂_i a • D (s i)`. -/
theorem sum_dualDerivation_smul [Fintype ι] {M : Type*} [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i)
    (D : Derivation R A M) (a : A) : ∑ i, b.dualDerivation i a • D (s i) = D a := by
  have h := congrArg D.liftKaehlerDifferential (b.sum_repr (KaehlerDifferential.D R A a))
  simpa [map_sum, ← hs] using h

/-- **A derivation in coordinates.** If `b` is a finite basis `ds_i` of exact differentials,
every derivation `D` of `A` is the combination `∑ i, D (s i) • ∂_i` of the dual derivations. -/
theorem sum_smul_dualDerivation [Fintype ι] (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i)
    (D : Derivation R A A) : ∑ i, D (s i) • b.dualDerivation i = D := by
  ext a
  simp [← sum_dualDerivation_smul hs D a, mul_comm]

end Module.Basis
