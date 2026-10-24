/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Marked.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.MaximalProPExtension

/-!
# Marked local presentations along finite extensions

For a finite extension `L/K`, the induced map `G_L(p) → G_K(p)` can be read in any
presentation of `G_K(p)`. When `q(L) ≠ 2`, the marked normal form for `G_L(p)` gives a
homomorphism from its one-relator presentation to that of `G_K(p)`, with the same cyclotomic
values on the images of its marked generators. The image is open and its index divides
`[L : K]`.

The target presentation is arbitrary: the extension may change the arithmetic branch and the
number of generators. In general this homomorphism is not injective. In particular, the images
of the source generators need not be a generating family of the target.

## Main results

* `TauCeti.absoluteGaloisGroupProP_marked_of_q_ne_two_finiteExtension`: the nonexceptional
  marked presentation of `G_L(p)`, together with its map to any presentation of `G_K(p)`, the
  commuting square with the Galois map, and the orientation values on the mapped generators.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132,
  Theorem 7.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L]
  [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra ℚ_[p] L] [ValuativeExtension ℚ_[p] L]
  {P : Type*} [Group P] [TopologicalSpace P]

/-- **Finite-extension compatibility of the nonexceptional marked presentation.** For `L/K`
finite with `μ_p ⊆ K` and `q(L) ≠ 2`, choose the marked normal form `e` of `G_L(p)` so that its
map `φ` to any presentation `mK` of `G_K(p)` commutes with the map induced by the embedding
`σ : L →ₐ[K] Kˢ`. The image of `φ` is open of index dividing `[L : K]`, and the orientation
read through `mK` takes the prescribed values on the images of the marked generators.
No containment of `L` in the maximal pro-`p` extension of `K` is required. -/
theorem absoluteGaloisGroupProP_marked_of_q_ne_two_finiteExtension
    (σ : L →ₐ[K] SeparableClosure K) (hmuK : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hq : localRootOfUnityOrder p L
      (finite_pPowerRootsOfUnity
        (hmuK.elim fun _ hζ ↦ (hζ.map_of_injective (algebraMap K L).injective).neZero'.out)) ≠ 2)
    (mK : absoluteGaloisGroupProP p K ≃ₜ* P) :
    ∃ e : absoluteGaloisGroupProP p L ≃ₜ*
        presentedProP p (Fin (Module.finrank ℚ_[p] L + 2))
          {demushkinWordNeTwo
            (localRootOfUnityOrder p L
              (finite_pPowerRootsOfUnity
                (hmuK.elim fun _ hζ ↦
                  (hζ.map_of_injective (algebraMap K L).injective).neZero'.out)))
            (Module.finrank ℚ_[p] L + 2)
            (freeProPGen p (Module.finrank ℚ_[p] L + 2))},
      ∃ φ : _ →ₜ* P,
        (∀ x, φ (e x) = mK (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x)) ∧
        IsOpen (φ.toMonoidHom.range : Set P) ∧
        φ.toMonoidHom.range.index ∣ Module.finrank K L ∧
        ((cyclotomicOrientation p K hmuK
            (mK.symm (φ (presentedProPGen p (Module.finrank ℚ_[p] L + 2) _ 1))) : ℤ_[p]) *
          (1 - (localRootOfUnityOrder p L
            (finite_pPowerRootsOfUnity
              (hmuK.elim fun _ hζ ↦
                (hζ.map_of_injective (algebraMap K L).injective).neZero'.out)) : ℤ_[p])) = 1) ∧
        ∀ i : ℕ, i ≠ 1 → i < Module.finrank ℚ_[p] L + 2 →
          cyclotomicOrientation p K hmuK
            (mK.symm (φ (presentedProPGen p (Module.finrank ℚ_[p] L + 2) _ i))) = 1 := by
  let hmuL : ∃ ζ : L, IsPrimitiveRoot ζ p :=
    hmuK.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩
  obtain ⟨e, hsecond, hother⟩ := absoluteGaloisGroupProP_marked_of_q_ne_two p L hmuL hq
  let ι := maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
    (continuous_absoluteGaloisGroupExtend K L σ)
  let φ : _ →ₜ* P :=
    ⟨(mK.toMulEquiv.toMonoidHom.comp ι).comp e.symm.toMulEquiv.toMonoidHom,
      mK.continuous.comp ((maximalProPQuotient.continuous_map _ _).comp e.symm.continuous)⟩
  have hφ (y) : mK.symm (φ y) = ι (e.symm y) := mK.symm_apply_apply _
  have hχ (y) : cyclotomicOrientation p K hmuK (mK.symm (φ y)) =
      cyclotomicOrientation p L hmuL (e.symm y) := by
    rw [hφ]
    exact cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend
      p K L σ hmuK (e.symm y)
  have hrange : φ.toMonoidHom.range = ι.range.comap mK.symm.toMonoidHom := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.symm.surjective, Subgroup.map_top,
      MonoidHom.range_comp]
    exact Subgroup.map_equiv_eq_comap_symm' mK.toMulEquiv ι.range
  refine ⟨e, φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun y ↦ mK (ι y)) (e.symm_apply_apply x)
  · rw [hrange, Subgroup.coe_comap]
    exact (isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend p K L σ).preimage
      mK.symm.continuous
  · rw [hrange, Subgroup.index_comap_of_surjective _ mK.symm.surjective]
    exact index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend_dvd p K L σ
  · simpa only [hχ] using hsecond
  · intro i hi hlt
    rw [hχ]
    exact hother i hi hlt

end TauCeti
