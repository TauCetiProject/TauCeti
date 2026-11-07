/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.AlgebraicGeometry.Fibers.Dimension
import TauCeti.Topology.KrullDimension.Basic

/-!
# The dimension formula for generalizing morphisms

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes whose underlying map is generalizing,
for instance a flat morphism, and let `x` be a point of `X`. The codimension of `x` in `X` is the
codimension of `f x` in `Y` plus the codimension of `x` in its fibre `f ⁻¹' {f x}`. Codimensions
are coheights for the specialization order, so by `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`
this is the scheme form of the dimension formula `dim 𝒪_{X,x} = dim 𝒪_{Y,f x} + dim 𝒪_{X_{f x},x}`
for local homomorphisms satisfying going down, such as flat ones. It expresses the dimension of a
fibre as a difference of dimensions, as in the computation of the dimension of an orbit from that
of its stabilizer.

The proof passes to compatible affine charts `Spec S → X` and `Spec R → Y` and applies Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`: the chart map `Spec S → Spec R` is
generalizing, which is going down for `R → S`. The codimension of a point of `Spec S` in its
fibre over `Spec R` is its height in `S ⧸ q S` by
`TauCeti.AlgebraicGeometry.coheight_fiber_eq_height_map`, and the chart identifies that fibre
with an open part of the fibre of `f`, along which coheights agree by
`Topology.IsOpenEmbedding.coheight_subtype_eq`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.coheight_eq_coheight_add_coheight_preimage`: for a generalizing
  morphism, such as a flat one, the codimension of a point is that of its image plus that in its
  fibre.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON), the algebraic dimension
  formula for going-down extensions.
* H. Matsumura, *Commutative Ring Theory*, Theorem 15.1.
-/

public section

open CategoryTheory Order Topology TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Dimension formula for generalizing morphisms.** For a morphism `f : X ⟶ Y` of locally
Noetherian schemes whose underlying map is generalizing, the codimension of a point `x` is the
codimension of `f x` plus the codimension of `x` in the fibre `f ⁻¹' {f x}`, the latter for the
specialization order induced from `X`. A flat morphism is generalizing by
`AlgebraicGeometry.Flat.generalizingMap`. -/
theorem Scheme.Hom.coheight_eq_coheight_add_coheight_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : GeneralizingMap f) (x : X) :
    coheight x = coheight (f x) + coheight (⟨x, rfl⟩ : f ⁻¹' {f x}) := by
  -- Choose an affine chart `Spec S` around `x` mapping into an affine chart `Spec R` of `Y`.
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (U := ⊤) (x := f x) (by simp)
  obtain ⟨V, hV, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := f ⁻¹ᵁ U) (x := x) hxU
  have hU : IsAffineOpen U := hU
  have hV : IsAffineOpen V := hV
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let φ : R ⟶ S := f.appLE U V hVU
  have hcomm : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU
  have hcomm_apply (v : Spec S) : hU.fromSpec (Spec.map φ v) = f (hV.fromSpec v) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  obtain ⟨x', hx'⟩ : x ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hxV
  have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let _ : Algebra R S := φ.hom.toAlgebra
  have : Algebra.HasGoingDown R S := by
    have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
      (topologically GeneralizingMap)
    have hf : topologically GeneralizingMap f := hf
    rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)] at hf
    exact Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mpr (hf ⟨U, hU⟩ ⟨V, hV⟩ hVU)
  let Q : Ideal S := x'.asIdeal
  let q : Ideal R := (Spec.map φ x').asIdeal
  have : Q.IsPrime := x'.isPrime
  have : q.IsPrime := (Spec.map φ x').isPrime
  have : Q.LiesOver q := ⟨rfl⟩
  let I : Ideal S := q.map (algebraMap R S)
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q
  rw [idealHeight_eq_coheight, idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion
    hV.fromSpec, hx', ← coheight_eq_of_isOpenImmersion hU.fromSpec, hcomm_apply, hx'] at hheight
  rw [hheight]
  congr 1
  refine (TauCeti.AlgebraicGeometry.coheight_fiber_eq_height_map φ x').symm.trans ?_
  -- The chart identifies the fibre of `Spec S → Spec R` with an open part of the fibre of `f`.
  have hTF (v : Spec S) : v ∈ {v : Spec S | Spec.map φ v = Spec.map φ x'} ↔
      hV.fromSpec v ∈ f ⁻¹' {f x} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, ← hx', ← hcomm_apply,
      ← hcomm_apply, hU.fromSpec.isOpenEmbedding.injective.eq_iff]
  subst hx'
  exact hV.fromSpec.isOpenEmbedding.coheight_subtype_eq hTF rfl

end AlgebraicGeometry
