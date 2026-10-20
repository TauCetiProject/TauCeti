/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.MaximalProPExtension

/-!
# Compatibility of the marked presentations of `G_K(p)` with finite extensions

The marked theorems of `TauCeti.NumberTheory.LocalField.ProP.Marked.Basic` present `G_K(p)`, for
`K` a finite extension of `ℚ_p` containing a primitive `p`th root of unity, by an isomorphism
`m_K : G_K(p) ≃ₜ* P` onto a one-relator pro-`p` group `P`, and record the values of the
cyclotomic orientation `χ_K` on the generators of `P`. This file relates the marked presentations of
`K` and of a finite extension `L` of `K`.

Let `σ : L →ₐ[K] Kˢ` embed `L` in a separable closure of `K`, and suppose that `σ(L)` lies in the
maximal pro-`p` extension of `K`; for `L/K` normal this says that `Gal(L/K)` is a `p`-group
(`TauCeti.proPKernel_le_range_absoluteGaloisGroupExtend_iff`). Then for marked presentations
`m_K : G_K(p) ≃ₜ* P` and `m_L : G_L(p) ≃ₜ* Q`, the group `Q` presenting `G_L(p)` is identified with
an open subgroup `U` of index `[L : K]` of the group `P` presenting `G_K(p)`:

```text
Q ≃ₜ* U ≤ P,   [P : U] = [L : K],
```

by the map that `m_K` and `m_L` read off from the map `G_L(p) → G_K(p)` induced by `σ`, and the
orientation `χ_K ∘ m_K⁻¹` of `P` restricts on `U` to the orientation `χ_L ∘ m_L⁻¹` of `Q`. So the
marked presentation of `G_L(p)` is the marked presentation of `G_K(p)` restricted to an open
subgroup, with its orientation.

Two inputs combine. The map `G_L(p) → G_K(p)` is injective with image of index `[L : K]`
(`TauCeti.injective_maximalProPQuotient_map_absoluteGaloisGroupExtend`,
`TauCeti.index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend`), and the cyclotomic
orientation is natural along it
(`TauCeti.cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend`). The statement
is uniform in the marked presentations and so applies to every branch of the marked
classification; no hypothesis on the presented groups is used.

## Main results

* `TauCeti.exists_continuousMulEquiv_marked_of_le_range_absoluteGaloisGroupExtend`: for `σ(L)`
  inside the maximal pro-`p` extension of `K`, the group presenting `G_L(p)` is an open subgroup of
  index `[L : K]` of the group presenting `G_K(p)`, compatibly with the cyclotomic orientations.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11) and
  (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
  {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

/-- **Compatibility of the marked presentations with finite extensions.** Let `L/K` be a finite
extension embedded by `σ` in the maximal pro-`p` extension of `K`, where `K` contains a primitive
`p`th root of unity, and let `m_K : G_K(p) ≃ₜ* P` and `m_L : G_L(p) ≃ₜ* Q` be presentations of the
maximal pro-`p` Galois groups. Then `Q` is isomorphic to an open subgroup `U` of index `[L : K]` of
`P`, by the isomorphism `e` that the markings read off from the map `G_L(p) → G_K(p)` induced by
`σ`, and `e` carries the cyclotomic orientation of `G_L(p)`, read on `Q` through `m_L`, to that of
`G_K(p)`, read on `P` through `m_K`. -/
theorem exists_continuousMulEquiv_marked_of_le_range_absoluteGaloisGroupExtend
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hle : proPKernel p (Field.absoluteGaloisGroup K) ≤ (absoluteGaloisGroupExtend K L σ).range)
    (mK : absoluteGaloisGroupProP p K ≃ₜ* P) (mL : absoluteGaloisGroupProP p L ≃ₜ* Q) :
    ∃ U : Subgroup P, IsOpen (U : Set P) ∧ U.index = Module.finrank K L ∧ ∃ e : Q ≃ₜ* U,
      (∀ y, mK.symm (e y) = maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) (mL.symm y)) ∧
      ∀ y, cyclotomicOrientation p K hmu (mK.symm (e y)) =
        cyclotomicOrientation p L
          (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩)
          (mL.symm y) := by
  set ι := maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
    (continuous_absoluteGaloisGroupExtend K L σ)
  -- The map `Q → P` read off through the markings from `ι : G_L(p) → G_K(p)`.
  let φ : Q →ₜ* P :=
    ⟨(mK.toMulEquiv.toMonoidHom.comp ι).comp mL.symm.toMulEquiv.toMonoidHom,
      mK.continuous.comp ((maximalProPQuotient.continuous_map _ _).comp mL.symm.continuous)⟩
  have hφ : ∀ y, mK.symm (φ y) = ι (mL.symm y) := fun y ↦ mK.symm_apply_apply _
  have hrange : (φ : Q →* P).range = ι.range.comap (mK.symm : P ≃* _).toMonoidHom := by
    ext x
    refine ⟨?_, fun ⟨z, hz⟩ ↦ ⟨mL z, mK.symm.injective ?_⟩⟩
    · rintro ⟨y, rfl⟩
      exact ⟨mL.symm y, (hφ y).symm⟩
    · refine (hφ (mL z)).trans ?_
      rw [ContinuousMulEquiv.symm_apply_apply]
      exact hz
  -- `φ` is a continuous injection from a compact group to a Hausdorff one, hence an embedding.
  have : CompactSpace Q := mL.toHomeomorph.compactSpace
  have : T2Space P := mK.symm.toHomeomorph.isEmbedding.t2Space
  have hinj : Function.Injective φ := mK.injective.comp <|
    (injective_maximalProPQuotient_map_absoluteGaloisGroupExtend p K L σ hle).comp
      mL.symm.injective
  have hemb : Topology.IsEmbedding φ := (φ.continuous.isClosedEmbedding hinj).isEmbedding
  refine ⟨(φ : Q →* P).range, ?_, ?_, φ.equivRangeOfIsEmbedding hemb, fun y ↦ ?_, fun y ↦ ?_⟩
  · rw [hrange, Subgroup.coe_comap]
    exact (isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend p K L σ).preimage
      mK.symm.continuous
  · rw [hrange, Subgroup.index_comap_of_surjective _ mK.symm.surjective]
    exact index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend p K L σ hle
  · rw [ContinuousMonoidHom.equivRangeOfIsEmbedding_apply]
    exact hφ y
  · rw [ContinuousMonoidHom.equivRangeOfIsEmbedding_apply]
    simp only [hφ, ι, cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend]

end TauCeti
