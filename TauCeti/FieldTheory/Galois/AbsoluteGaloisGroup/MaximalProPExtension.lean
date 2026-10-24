/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

The compatibility of presentations of maximal pro-`p` Galois groups with such finite extensions,
which also uses the cyclotomic orientation, is in
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.MaximalProPExtension`.

## Main results

* `TauCeti.proPKernel_le_range_absoluteGaloisGroupExtend_iff`: for `L/K` finite and normal, `G_L`
  contains the pro-`p` kernel of `G_K` exactly when `Gal(L/K)` is a `p`-group.
* `TauCeti.isOpen_range_maximalProPQuotient_map_absoluteGaloisGroupExtend`,
  `TauCeti.index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend_dvd`: the image of
  `G_L(p)` in `G_K(p)` is open, of index dividing `[L : K]`.
* `TauCeti.injective_maximalProPQuotient_map_absoluteGaloisGroupExtend`,
  `TauCeti.index_range_maximalProPQuotient_map_absoluteGaloisGroupExtend`: when `G_L` contains the
  pro-`p` kernel of `G_K`, the map `G_L(p) → G_K(p)` is injective, with image of index `[L : K]`.

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

end TauCeti
