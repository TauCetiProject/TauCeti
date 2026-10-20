/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.KernelSubgroup

/-!
# Finite extensions inside the maximal pro-`p` extension

Let `L/K` be a finite extension, embedded in a separable closure `Kˢ` by `σ`, so that
`absoluteGaloisGroupExtend K L σ` identifies `G_L` with the open subgroup of `G_K` of index
`[L : K]` fixing `σ(L)`. It induces a continuous homomorphism

```text
maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ) _ : G_L(p) → G_K(p)
```

of maximal pro-`p` Galois groups. Its image, the image of `G_L` in `G_K(p)`, is always open, of
index dividing `[L : K]`. In general the map is neither injective nor of image of index `[L : K]`:
for an extension of degree prime to `p`, the index of the image is a power of `p` dividing
`[L : K]`, hence `1`.

When `σ(L)` lies in the maximal pro-`p` extension `K(p)` of `K`, which is to say that `G_L`
contains the pro-`p` kernel of `G_K`, the map is injective with image of index exactly `[L : K]`
(`TauCeti.proPKernel_eq_comap_of_le_range`): the maximal pro-`p` Galois group of `L` is the open
subgroup of that of `K` fixing `L`. For a finite normal extension the condition says exactly that
`Gal(L/K)` is a `p`-group.

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

## Main results

* `TauCeti.proPKernel_le_range_absoluteGaloisGroupExtend_iff`: for `L/K` finite and normal, `G_L`
  contains the pro-`p` kernel of `G_K` exactly when `Gal(L/K)` is a `p`-group.
* `TauCeti.isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend`,
  `TauCeti.index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend_dvd`: the image of
  `G_L(p)` in `G_K(p)` is open, of index dividing `[L : K]`.
* `TauCeti.injective_maximalProPQuotient_map_absoluteGaloisGroupExtend`,
  `TauCeti.index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend`: when `G_L` contains the
  pro-`p` kernel of `G_K`, the map `G_L(p) → G_K(p)` is injective, with image of index `[L : K]`.
* `TauCeti.exists_continuousMulEquiv_of_le_range_absoluteGaloisGroupExtend`: in that case any
  presentation of `G_L(p)` is an open subgroup of index `[L : K]` of any presentation of `G_K(p)`,
  compatibly with the cyclotomic orientations.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11) and
  (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- **The image of `G_L(p)` in `G_K(p)` is open.** -/
theorem isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend :
    IsOpen ((maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
      (continuous_absoluteGaloisGroupExtend K L σ)).range : Set (absoluteGaloisGroupProP p K)) :=
  maximalProPQuotient.isOpen_range_map _ _ (isOpen_range_absoluteGaloisGroupExtend K L σ)

/-- **The image of `G_L(p)` in `G_K(p)` has index dividing `[L : K]`.** -/
theorem index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend_dvd :
    (maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
      (continuous_absoluteGaloisGroupExtend K L σ)).range.index ∣ Module.finrank K L :=
  index_range_absoluteGaloisGroupExtend K L σ ▸ maximalProPQuotient.index_range_map_dvd _ _

/-- **`G_L(p)` is a subgroup of `G_K(p)` when `L` lies in the maximal pro-`p` extension of
`K`.** If `G_L` contains the pro-`p` kernel of `G_K`, the map `G_L(p) → G_K(p)` induced by the
inclusion `absoluteGaloisGroupExtend K L σ` is injective. -/
theorem injective_maximalProPQuotient_map_absoluteGaloisGroupExtend
    (hle : proPKernel p (Field.absoluteGaloisGroup K) ≤ (absoluteGaloisGroupExtend K L σ).range) :
    Function.Injective (maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
      (continuous_absoluteGaloisGroupExtend K L σ)) :=
  haveI : T2Space (Field.absoluteGaloisGroup K) := krullTopology_t2
  maximalProPQuotient.map_injective_of_le_range _
    ((continuous_absoluteGaloisGroupExtend K L σ).isClosedEmbedding
      (injective_absoluteGaloisGroupExtend K L σ)).isEmbedding hle

/-- **The index of `G_L(p)` in `G_K(p)` is `[L : K]` when `L` lies in the maximal pro-`p` extension
of `K`.** If `G_L` contains the pro-`p` kernel of `G_K`, the image of `G_L(p) → G_K(p)` has index
`[L : K]`. -/
theorem index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend
    (hle : proPKernel p (Field.absoluteGaloisGroup K) ≤ (absoluteGaloisGroupExtend K L σ).range) :
    (maximalProPQuotient.map (p := p) (absoluteGaloisGroupExtend K L σ)
      (continuous_absoluteGaloisGroupExtend K L σ)).range.index = Module.finrank K L := by
  rw [maximalProPQuotient.index_range_map_of_le_range _ _ hle,
    index_range_absoluteGaloisGroupExtend]

/-- **A finite normal extension lies in the maximal pro-`p` extension exactly when its Galois group
is a `p`-group.** For `L/K` finite and normal, embedded in `Kˢ` by `σ`, the image of `G_L` in
`G_K` contains the pro-`p` kernel of `G_K` if and only if `Gal(L/K)` is a `p`-group. -/
theorem proPKernel_le_range_absoluteGaloisGroupExtend_iff [Normal K L] :
    proPKernel p (Field.absoluteGaloisGroup K) ≤ (absoluteGaloisGroupExtend K L σ).range ↔
      IsPGroup p Gal(L/K) := by
  have hcomap : (absoluteGaloisGroupExtend K L σ).range =
      (galoisSubgroup K L σ).toSubgroup.comap
        (absoluteGaloisGroupRestrictEquiv K).toMulEquiv.toMonoidHom :=
    Subgroup.ext fun _ ↦ mem_range_absoluteGaloisGroupExtend_iff K L σ
  -- The image of `G_L` is an open normal subgroup `W` of `G_K` with quotient `Gal(L/K)`.
  let W : OpenNormalSubgroup (Field.absoluteGaloisGroup K) :=
    { toSubgroup := (absoluteGaloisGroupExtend K L σ).range
      isOpen' := isOpen_range_absoluteGaloisGroupExtend K L σ
      isNormal' := hcomap ▸ (normal_galoisSubgroup K L σ).comap _ }
  have : W.toSubgroup.Normal := W.isNormal'
  let e : Field.absoluteGaloisGroup K ⧸ W.toSubgroup ≃* Gal(L/K) :=
    absoluteGaloisGroupExtendQuotientEquiv K L σ (U := W.toSubgroup) rfl
  exact (proPKernel_le_iff_isPGroup_quotient (U := W)).trans
    ⟨fun h ↦ h.of_equiv e, fun h ↦ h.of_equiv e.symm⟩

section Presentation

variable [Fact p.Prime] {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

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

end Presentation

end TauCeti
