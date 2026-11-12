/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.MaximalProPExtension

/-!
# Presentations of maximal pro-`p` Galois groups along finite extensions

Let `L/K` be a finite extension, embedded by `σ` in the maximal pro-`p` extension `K(p)` of `K`, so
that the map `G_L(p) → G_K(p)` induced by `absoluteGaloisGroupExtend K L σ` is injective with image
of index `[L : K]` (`TauCeti.injective_maximalProPQuotient_map_absoluteGaloisGroupExtend`).
Combined with the naturality of the cyclotomic orientation
(`TauCeti.cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend`), this gives the
compatibility of presentations of maximal pro-`p` Galois groups with such finite extensions: for
any isomorphisms `m_K : G_K(p) ≃ₜ* P` and `m_L : G_L(p) ≃ₜ* Q` onto topological groups, `Q` is
identified with an open subgroup `U` of index `[L : K]` of `P`,

```text
Q ≃ₜ* U ≤ P,   [P : U] = [L : K],
```

by the map that `m_K` and `m_L` read off from `G_L(p) → G_K(p)`, and when `K` contains a primitive
`p`th root of unity the orientation `χ_K ∘ m_K⁻¹` of `P` restricts on `U` to the orientation
`χ_L ∘ m_L⁻¹` of `Q`. The statement is uniform in `P`, `Q`, `m_K` and `m_L`, so it applies in
particular to the marked presentations of `TauCeti.NumberTheory.LocalField.ProP.Marked.Basic`,
whatever their branch; only the presented groups and their orientations are related, and no marking
data (generators, relator, values of the orientation on the generators) is transported.

Without the assumption that `σ(L)` lies in `K(p)`, the map `G_L(p) → G_K(p)` need not be injective,
but it is still read off through `m_K` and `m_L` as a continuous homomorphism `φ : Q → P` with open
image of index dividing `[L : K]`, and `φ` still carries the orientation of `Q` to that of `P`. The
values of the orientation of `G_K(p)` on the images under `φ` of the marked generators of a marked
presentation of `G_L(p)` are therefore the values recorded for `L`.

## Main results

* `TauCeti.exists_continuousMulEquiv_of_le_range_absoluteGaloisGroupExtend`: when `G_L` contains
  the pro-`p` kernel of `G_K`, any presentation of `G_L(p)` is an open subgroup of index `[L : K]`
  of any presentation of `G_K(p)`, compatibly with the cyclotomic orientations.
* `TauCeti.exists_continuousMonoidHom_absoluteGaloisGroupExtend`: for an arbitrary finite
  extension, any presentation of `G_L(p)` maps to any presentation of `G_K(p)` with open image of
  index dividing `[L : K]`, compatibly with the cyclotomic orientations.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11) and
  (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K) [Fact p.Prime]
  {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

/-- **Presentations of `G_L(p)` as open subgroups of presentations of `G_K(p)`.** Let `L/K` be a
finite extension embedded by `σ` in the maximal pro-`p` extension of `K`, where `K` contains a
primitive `p`th root of unity, and let `m_K : G_K(p) ≃ₜ* P` and `m_L : G_L(p) ≃ₜ* Q` be
presentations of the maximal pro-`p` Galois groups. Then `Q` is isomorphic to an open subgroup `U`
of index `[L : K]` of `P`, by the isomorphism `e` that `m_K` and `m_L` read off from the map
`G_L(p) → G_K(p)` induced by `σ`, and `e` carries the cyclotomic orientation of `G_L(p)`, read on
`Q` through `m_L`, to that of `G_K(p)`, read on `P` through `m_K`. No generators or orientation
values are transported, so this applies to the marked presentations of every branch of the marked
classification. -/
theorem exists_continuousMulEquiv_of_le_range_absoluteGaloisGroupExtend
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
  -- The map `Q → P` read off through `mK` and `mL` from `ι : G_L(p) → G_K(p)`.
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

/-- **Presentations of maximal pro-`p` Galois groups along an arbitrary finite extension.** Let
`L/K` be a finite extension embedded in `Kˢ` by `σ`, where `K` contains a primitive `p`th root of
unity, and let `m_K : G_K(p) ≃ₜ* P` and `m_L : G_L(p) ≃ₜ* Q` be presentations of the maximal
pro-`p` Galois groups. Then the map `G_L(p) → G_K(p)` induced by `σ` is read off through `m_K` and
`m_L` as a continuous homomorphism `φ : Q →ₜ* P`, whose image is open of index dividing `[L : K]`,
and the cyclotomic orientation of `G_K(p)`, read on `P` through `m_K`, restricts along `φ` to that
of `G_L(p)`, read on `Q` through `m_L`. Unlike
`TauCeti.exists_continuousMulEquiv_of_le_range_absoluteGaloisGroupExtend`, no containment of `σ(L)`
in the maximal pro-`p` extension of `K` is assumed, and `φ` need not be injective. -/
theorem exists_continuousMonoidHom_absoluteGaloisGroupExtend
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (mK : absoluteGaloisGroupProP p K ≃ₜ* P) (mL : absoluteGaloisGroupProP p L ≃ₜ* Q) :
    ∃ φ : Q →ₜ* P,
      (∀ x, φ (mL x) = mK (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x)) ∧
      IsOpen (φ.toMonoidHom.range : Set P) ∧ φ.toMonoidHom.range.index ∣ Module.finrank K L ∧
      ∀ y, cyclotomicOrientation p K hmu (mK.symm (φ y)) =
        cyclotomicOrientation p L
          (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩)
          (mL.symm y) := by
  set ι := maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
    (continuous_absoluteGaloisGroupExtend K L σ)
  -- The map `Q → P` read off through `mK` and `mL` from `ι : G_L(p) → G_K(p)`.
  let φ : Q →ₜ* P :=
    ⟨(mK.toMulEquiv.toMonoidHom.comp ι).comp mL.symm.toMulEquiv.toMonoidHom,
      mK.continuous.comp ((maximalProPQuotient.continuous_map _ _).comp mL.symm.continuous)⟩
  have hφ : ∀ y, mK.symm (φ y) = ι (mL.symm y) := fun y ↦ mK.symm_apply_apply _
  have hrange : φ.toMonoidHom.range = ι.range.comap (mK.symm : P ≃* _).toMonoidHom := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ mL.symm.surjective, Subgroup.map_top,
      MonoidHom.range_comp]
    exact Subgroup.map_equiv_eq_comap_symm' mK.toMulEquiv ι.range
  refine ⟨φ, fun x ↦ ?_, ?_, ?_, fun y ↦ ?_⟩
  · exact congrArg (fun y ↦ mK (ι y)) (mL.symm_apply_apply x)
  · rw [hrange, Subgroup.coe_comap]
    exact (isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend p K L σ).preimage
      mK.symm.continuous
  · rw [hrange, Subgroup.index_comap_of_surjective _ mK.symm.surjective]
    exact index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend_dvd p K L σ
  · simp only [hφ, ι, cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend]

end TauCeti
