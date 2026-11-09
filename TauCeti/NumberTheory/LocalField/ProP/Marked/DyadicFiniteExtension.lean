/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.MaximalProPExtension
public import TauCeti.NumberTheory.LocalField.ProP.Marked.Basic

/-!
# The dyadic marked presentations along finite extensions

Let `L/K` be a finite extension, embedded in a separable closure `Kˢ` by `σ`, where `L` is a
finite extension of `ℚ₂` with `q(L) = 2`. The marked theorems of
`TauCeti.NumberTheory.LocalField.ProP.Marked.Basic` present `G_L(2)` by one of Labute's dyadic
relators on `[L : ℚ₂] + 2` generators,

`x₁² x₂⁴ (x₂, x₃) (x₄, x₅) ⋯ (x_{N+1}, x_{N+2})`  if `[L : ℚ₂]` is odd,

`x₁^{2 + α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{N+1}, x_{N+2})`  if `[L : ℚ₂]` is even,

and record the values of the cyclotomic orientation on the marked generators. This file carries
that marking along `L/K`: for any presentation `m_K : G_K(2) ≃ₜ* P` of the maximal pro-`2` Galois
group of `K`, the map `G_L(2) → G_K(2)` induced by `σ` is read off as a continuous homomorphism `φ`
from the presented group of `L` to `P`, its image is open of index dividing `[L : K]`, and the
cyclotomic orientation of `G_K(2)` takes on the images under `φ` of the marked generators the values
recorded for `L`.

The presentation `m_K` is arbitrary, and no local-field structure on `K` is assumed, so the
extension may change the arithmetic branch and the number of generators: for instance `[K : ℚ₂]`
may be odd while `[L : ℚ₂]` is even. The map `φ` need not be injective, and the images of the
marked generators of `L` need not generate `P`. When `σ(L)` lies in the maximal pro-`2` extension
of `K`, `TauCeti.exists_continuousMulEquiv_of_le_range_absoluteGaloisGroupExtend` identifies the
presented group of `L` with an open subgroup of `P` of index `[L : K]`.

Each statement is the marked theorem for `L` composed with
`TauCeti.exists_continuousMonoidHom_absoluteGaloisGroupExtend`, the compatibility of arbitrary
presentations with finite extensions, which rests on the naturality of the cyclotomic orientation
(`TauCeti.cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend`).

## Main results

* `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd_finiteExtension`: the odd-degree
  marked presentation of `G_L(2)` along `L/K`.
* `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_plusMinus_finiteExtension`,
  `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_principal_finiteExtension`: the
  even-degree marked presentations of `G_L(2)` along `L/K`, according as the cyclotomic image of
  `L` is `{±1} × U^(f)` or `U^[k]`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132, §5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11) and
  (7.5.12).
-/

public section

namespace TauCeti

variable (K : Type*) (L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra ℚ_[2] L] [ValuativeExtension ℚ_[2] L]
  {P : Type*} [Group P] [TopologicalSpace P]

/-- **The odd-degree marked presentation of `G_L(2)` along a finite extension.** Let `L/K` be a
finite extension embedded in `Kˢ` by `σ`, where `K` contains a primitive square root of unity and
`L` is a finite extension of `ℚ₂` of odd degree `N`, and let `m_K : G_K(2) ≃ₜ* P` be any
presentation of `G_K(2)`. Then the marked presentation `e` of `G_L(2)` by
`⟨x₁, …, x_{N+2} ∣ x₁² x₂⁴ (x₂, x₃) (x₄, x₅) ⋯ (x_{N+1}, x_{N+2})⟩` maps to `P` by the continuous
homomorphism `φ` that `e` and `m_K` read off from `G_L(2) → G_K(2)`, the image of `φ` is open of
index dividing `[L : K]`, and the cyclotomic orientation of `G_K(2)`, read on `P` through `m_K`,
takes the value `-1` on `φ(x₁)`, the value `(1 - 4)⁻¹` on `φ(x₃)`, and the value `1` on the image
of every other marked generator. -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_odd_finiteExtension
    (σ : L →ₐ[K] SeparableClosure K) (hmuK : ∃ ζ : K, IsPrimitiveRoot ζ 2)
    (hodd : Odd (Module.finrank ℚ_[2] L)) (mK : absoluteGaloisGroupProP 2 K ≃ₜ* P) :
    ∃ e : absoluteGaloisGroupProP 2 L ≃ₜ*
        presentedProP 2 (Fin (Module.finrank ℚ_[2] L + 2))
          {demushkinWordTwoOdd 2 (Module.finrank ℚ_[2] L + 2)
            (freeProPGen 2 (Module.finrank ℚ_[2] L + 2))},
      ∃ φ : _ →ₜ* P,
        (∀ x, φ (e x) = mK (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x)) ∧
        IsOpen (φ.toMonoidHom.range : Set P) ∧ φ.toMonoidHom.range.index ∣ Module.finrank K L ∧
        cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 0))) = -1 ∧
        ((cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 2))) : ℤ_[2]) *
          (1 - 2 ^ 2) = 1) ∧
        ∀ i : ℕ, i ≠ 0 → i ≠ 2 → i < Module.finrank ℚ_[2] L + 2 →
          cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ i))) = 1 := by
  obtain ⟨e, h₀, h₂, h⟩ := absoluteGaloisGroupProP_two_marked_of_degree_odd L
    (hmuK.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩) hodd
  obtain ⟨φ, hsq, hopen, hdvd, hχ⟩ :=
    exists_continuousMonoidHom_absoluteGaloisGroupExtend 2 K L σ hmuK mK e
  refine ⟨e, φ, hsq, hopen, hdvd, ?_, ?_, fun i hi₀ hi₂ hi ↦ ?_⟩
  · rw [hχ]
    exact h₀
  · rw [hχ]
    exact h₂
  · rw [hχ]
    exact h i hi₀ hi₂ hi

/-- **The even-degree marked presentation of `G_L(2)` along a finite extension, image
`{±1} × U^(f)`.** Let `L/K` be a finite extension embedded in `Kˢ` by `σ`, where `K` contains a
primitive square root of unity and `L` is a finite extension of `ℚ₂` of even degree `N` whose
cyclotomic character has image `{±1} × U^(f)`, with `f ≥ 2`, and let `m_K : G_K(2) ≃ₜ* P` be any
presentation of `G_K(2)`. Then for every natural exponent `α` divisible by `2^f`, the marked
presentation `e` of `G_L(2)` by
`⟨x₁, …, x_{N+2} ∣ x₁^{2 + α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{N+1}, x_{N+2})⟩` maps to `P` by the
continuous homomorphism `φ` that `e` and `m_K` read off from `G_L(2) → G_K(2)`, the image of `φ`
is open of index dividing `[L : K]`, and the cyclotomic orientation of `G_K(2)`, read on `P`
through `m_K`, takes the value `-(1 + α)⁻¹` on `φ(x₂)`, the value `(1 - 2^f)⁻¹` on `φ(x₄)`, and the
value `1` on the image of every other marked generator. -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_even_plusMinus_finiteExtension
    [FiniteDimensional ℚ_[2] L] (σ : L →ₐ[K] SeparableClosure K)
    (hmuK : ∃ ζ : K, IsPrimitiveRoot ζ 2) (heven : Even (Module.finrank ℚ_[2] L)) {a f : ℕ}
    (hf : 2 ≤ f) (ha : 2 ^ f ∣ a)
    (hrange : (localCyclotomicCharacter 2 L).range = unitsPlusMinus f)
    (mK : absoluteGaloisGroupProP 2 K ≃ₜ* P) :
    ∃ e : absoluteGaloisGroupProP 2 L ≃ₜ*
        presentedProP 2 (Fin (Module.finrank ℚ_[2] L + 2))
          {demushkinWordTwoEven a f (Module.finrank ℚ_[2] L + 2)
            (freeProPGen 2 (Module.finrank ℚ_[2] L + 2))},
      ∃ φ : _ →ₜ* P,
        (∀ x, φ (e x) = mK (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x)) ∧
        IsOpen (φ.toMonoidHom.range : Set P) ∧ φ.toMonoidHom.range.index ∣ Module.finrank K L ∧
        ((cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 1))) : ℤ_[2]) *
          (1 + (a : ℤ_[2])) = -1) ∧
        ((cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 3))) : ℤ_[2]) *
          (1 - 2 ^ f) = 1) ∧
        ∀ i : ℕ, i ≠ 1 → i ≠ 3 → i < Module.finrank ℚ_[2] L + 2 →
          cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ i))) = 1 := by
  obtain ⟨e, h₁, h₃, h⟩ := absoluteGaloisGroupProP_two_marked_of_degree_even_plusMinus L
    (hmuK.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩) heven hf ha
    hrange
  obtain ⟨φ, hsq, hopen, hdvd, hχ⟩ :=
    exists_continuousMonoidHom_absoluteGaloisGroupExtend 2 K L σ hmuK mK e
  refine ⟨e, φ, hsq, hopen, hdvd, ?_, ?_, fun i hi₁ hi₃ hi ↦ ?_⟩
  · rw [hχ]
    exact h₁
  · rw [hχ]
    exact h₃
  · rw [hχ]
    exact h i hi₁ hi₃ hi

/-- **The even-degree marked presentation of `G_L(2)` along a finite extension, image `U^[k]`.**
Let `L/K` be a finite extension embedded in `Kˢ` by `σ`, where `K` contains a primitive square
root of unity and `L` is a finite extension of `ℚ₂` of even degree `N` whose cyclotomic character
has image the twisted subgroup `U^[k]`, topologically generated by `-1 + 2^k`, with `k ≥ 2`, and
let `m_K : G_K(2) ≃ₜ* P` be any presentation of `G_K(2)`. Then for every natural exponent `α` with
`v₂(α) = k` and every level `f > k`, the marked presentation `e` of `G_L(2)` by
`⟨x₁, …, x_{N+2} ∣ x₁^{2 + α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{N+1}, x_{N+2})⟩` maps to `P` by the
continuous homomorphism `φ` that `e` and `m_K` read off from `G_L(2) → G_K(2)`, the image of `φ`
is open of index dividing `[L : K]`, and the cyclotomic orientation of `G_K(2)`, read on `P`
through `m_K`, takes the value `-(1 + α)⁻¹` on `φ(x₂)`, the value `(1 - 2^f)⁻¹` on `φ(x₄)`, and the
value `1` on the image of every other marked generator. -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_even_principal_finiteExtension
    [FiniteDimensional ℚ_[2] L] (σ : L →ₐ[K] SeparableClosure K)
    (hmuK : ∃ ζ : K, IsPrimitiveRoot ζ 2) (heven : Even (Module.finrank ℚ_[2] L)) {a k f : ℕ}
    (hk : 2 ≤ k) (hak : 2 ^ k ∣ a) (hak' : ¬ 2 ^ (k + 1) ∣ a) (hkf : k < f) {u : ℤ_[2]ˣ}
    (hu : (u : ℤ_[2]) = -1 + 2 ^ k)
    (hrange : (localCyclotomicCharacter 2 L).range = (Subgroup.zpowers u).topologicalClosure)
    (mK : absoluteGaloisGroupProP 2 K ≃ₜ* P) :
    ∃ e : absoluteGaloisGroupProP 2 L ≃ₜ*
        presentedProP 2 (Fin (Module.finrank ℚ_[2] L + 2))
          {demushkinWordTwoEven a f (Module.finrank ℚ_[2] L + 2)
            (freeProPGen 2 (Module.finrank ℚ_[2] L + 2))},
      ∃ φ : _ →ₜ* P,
        (∀ x, φ (e x) = mK (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x)) ∧
        IsOpen (φ.toMonoidHom.range : Set P) ∧ φ.toMonoidHom.range.index ∣ Module.finrank K L ∧
        ((cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 1))) : ℤ_[2]) *
          (1 + (a : ℤ_[2])) = -1) ∧
        ((cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ 3))) : ℤ_[2]) *
          (1 - 2 ^ f) = 1) ∧
        ∀ i : ℕ, i ≠ 1 → i ≠ 3 → i < Module.finrank ℚ_[2] L + 2 →
          cyclotomicOrientation 2 K hmuK
            (mK.symm (φ (presentedProPGen 2 (Module.finrank ℚ_[2] L + 2) _ i))) = 1 := by
  obtain ⟨e, h₁, h₃, h⟩ := absoluteGaloisGroupProP_two_marked_of_degree_even_principal L
    (hmuK.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩) heven hk hak hak'
    hkf hu hrange
  obtain ⟨φ, hsq, hopen, hdvd, hχ⟩ :=
    exists_continuousMonoidHom_absoluteGaloisGroupExtend 2 K L σ hmuK mK e
  refine ⟨e, φ, hsq, hopen, hdvd, ?_, ?_, fun i hi₁ hi₃ hi ↦ ?_⟩
  · rw [hχ]
    exact h₁
  · rw [hχ]
    exact h₃
  · rw [hχ]
    exact h i hi₁ hi₃ hi

end TauCeti
