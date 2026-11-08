/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# The discriminant of a number field from an integral basis

If `b` is (the image in `K` of) a `ℤ`-basis of the ring of integers `𝒪_K` — an *integral
basis* — then its rational trace-form discriminant is exactly the field discriminant,

`disc b = d_K` (over `ℚ`).

More usefully, this holds for any `ℚ`-basis `b` of `K` consisting of algebraic integers whose
`ℤ`-span inside `𝒪_K` is everything: exhibiting such a spanning integral basis and evaluating
its discriminant computes `d_K` on the nose. This is the exact-attainment half of the effective
discriminant bound `|d_K| ≤ |disc b|`
(`NumberField.abs_discr_le_of_basis_isIntegral`), which is strict exactly when the span
has index `m > 1` (then `disc b = m² · d_K`). It also drives concrete discriminant computations,
e.g. `{1, i}` is a `ℤ`-basis of the Gaussian integers and `disc {1, i} = -4` gives `d_{ℚ(i)} = -4`.

## Main results

* `NumberField.discr_eq_of_integralBasis`: for a `ℤ`-basis `c` of `𝒪_K`, the rational
  discriminant of its image in `K` equals `d_K`.
* `NumberField.discr_eq_of_basis_isIntegral_of_span_eq_top`: the same, phrased for a
  `ℚ`-basis `b` of algebraic integers whose `ℤ`-span (inside `𝒪_K`) is everything.
* `NumberField.abs_discr_eq_of_basis_isIntegral_of_span_eq_top`: the matching
  `|d_K| = |disc b|`, the equality companion of `abs_discr_le_of_basis_isIntegral`.
* `NumberField.discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int`: the consumer
  form that turns an evaluated integer basis discriminant into `d_K` exactly, with
  `NumberField.natAbs_discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int` its
  `natAbs` corollary.

## Provenance

No formal code is vendored. The equality is assembled from Mathlib's
`Algebra.discr_localizationLocalization` and `NumberField.discr_eq_discr`; the `ℚ`-basis form
constructs the `ℤ`-basis of `𝒪_K` from the spanning hypothesis. It is the exact-attainment
companion of the bound `NumberField.abs_discr_le_of_basis_isIntegral`,
whose source attribution (kim-em/erdos-unit-distance) is in
`TauCeti/NumberTheory/EffectiveBounds/Discriminant/Basic.lean`.
-/

public section

open Module
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **An integral basis attains the discriminant bound.** For a `ℤ`-basis `c` of the ring of
integers `𝒪_K`, the rational discriminant of the induced `ℚ`-basis of `K` is exactly the field
discriminant `d_K`. -/
theorem discr_eq_of_integralBasis (c : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℚ (fun i => algebraMap (𝓞 K) K (c i)) = (NumberField.discr K : ℚ) := by
  rw [← discr_eq_discr K c, ← eq_intCast (algebraMap ℤ ℚ),
    ← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K]
  congr 1
  ext i
  simp

/-- **The discriminant bound is an equality for a spanning integral basis.** If `b` is a
`ℚ`-basis of `K` consisting of algebraic integers whose `ℤ`-span inside `𝒪_K` is all of `𝒪_K`,
then `disc b = d_K` exactly (over `ℚ`). -/
theorem discr_eq_of_basis_isIntegral_of_span_eq_top (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤) :
    Algebra.discr ℚ (b : ι → K) = (NumberField.discr K : ℚ) := by
  -- `algebraMap (𝓞 K) K ⟨x, hx⟩ = x` holds by `rfl` (`RingOfIntegers.map_mk`), so the image in
  -- `K` of the `𝓞 K`-valued family is `b` itself, which is `ℤ`-linearly independent.
  have hli : LinearIndependent ℤ fun i => (⟨b i, hb i⟩ : 𝓞 K) :=
    .of_comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap
      (b.linearIndependent.restrict_scalars' ℤ)
  -- Package it as a `ℤ`-basis of `𝒪_K`, whose image in `K` is `b`.
  convert discr_eq_of_integralBasis (Basis.mk hli hspan.ge) using 3 with i
  exact ((congrArg (algebraMap (𝓞 K) K) (Basis.mk_apply hli hspan.ge i)).trans
    (RingOfIntegers.map_mk (b i) (hb i))).symm

/-- **The equality companion of the effective discriminant bound.** For a `ℚ`-basis of algebraic
integers that generates `𝒪_K`, the effective bound `|d_K| ≤ |disc b|` is an equality. -/
theorem abs_discr_eq_of_basis_isIntegral_of_span_eq_top
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤) :
    |(NumberField.discr K : ℚ)| = |Algebra.discr ℚ (b : ι → K)| := by
  rw [discr_eq_of_basis_isIntegral_of_span_eq_top b hb hspan]

/-- **Evaluating the discriminant through a spanning integral basis.** If the discriminant of a
generating basis of algebraic integers computes to an integer `d`, then `d_K = d` exactly. This is
the consumer form used to read off `d_K` from a concrete trace-form computation, as in the
`ℚ(i)` example (`disc {1, i} = -4`, whence `d_{ℚ(i)} = -4`). -/
theorem discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤)
    {d : ℤ} (hd : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    NumberField.discr K = d :=
  Int.cast_injective (α := ℚ) <|
    (discr_eq_of_basis_isIntegral_of_span_eq_top b hb hspan).symm.trans hd

/-- **The absolute value of the discriminant from a spanning integral basis.** The `natAbs`
corollary of `discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int`, reading off `|d_K|`
from an evaluated integer basis discriminant (in the `ℚ(i)` example, `(d_{ℚ(i)}).natAbs = 4`). -/
theorem natAbs_discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤)
    {d : ℤ} (hd : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    (NumberField.discr K).natAbs = d.natAbs := by
  rw [discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int b hb hspan hd]

end NumberField
