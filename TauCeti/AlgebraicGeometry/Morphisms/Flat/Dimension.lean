/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.AlgebraicGeometry.Fibers.Dimension
import TauCeti.Topology.KrullDimension.Basic

/-!
# The dimension formula for flat morphisms

Let `f : X ⟶ Y` be a flat morphism of locally Noetherian schemes, and let `x` be a point of `X`.
The codimension of `x` in `X` is the codimension of `f x` in `Y` plus the codimension of `x` in
its fibre `f ⁻¹' {f x}`. Codimensions are coheights for the specialization order, so by
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` this is the scheme form of the dimension formula
`dim 𝒪_{X,x} = dim 𝒪_{Y,f x} + dim 𝒪_{X_{f x},x}` for flat local homomorphisms. It expresses
the dimension of a fibre as a difference of dimensions, as in the computation of the dimension of
an orbit from that of its stabilizer.

The proof passes to compatible affine charts `Spec S → X` and `Spec R → Y` and applies Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`: flat algebras satisfy going down. The
generizations of a point of `Spec S` lying over a prime `q` of `R` are exactly its generizations
in the closed subset `V(q S)`, and the codimension of a point of `Spec A` inside a closed subset
`V(I)` is its height in `A ⧸ I`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.coheight_eq_coheight_add_coheight_preimage`: for a flat morphism,
  the codimension of a point is that of its image plus that in its fibre.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_of_flat_of_surjective`: a flat,
  surjective morphism of schemes cannot increase dimension.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_flat_of_surjective`: a flat,
  surjective, locally quasi-finite morphism of schemes preserves dimension.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_opens_eq_of_flat_of_surjective`: the
  condition that every nonempty open has a prescribed dimension descends along such a morphism.

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

/-- **Dimension formula for flat morphisms.** For a flat morphism `f : X ⟶ Y` of locally
Noetherian schemes, the codimension of a point `x` is the codimension of `f x` plus the codimension
of `x` in the fibre `f ⁻¹' {f x}`, the latter for the specialization order induced from `X`. -/
theorem Scheme.Hom.coheight_eq_coheight_add_coheight_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (x : X) :
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
  have : Module.Flat R S := HasRingHomProperty.appLE @Flat f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
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

/-- The target of a flat, surjective morphism of schemes has Krull dimension at most that of
the source. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  (Flat.generalizingMap f).topologicalKrullDim_le_of_surjective f.continuous f.surjective

/-- A flat, surjective, locally quasi-finite morphism of schemes preserves Krull dimension.
In particular, this applies to finite faithfully flat covers. -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyQuasiFinite f] :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm f.topologicalKrullDim_le f.topologicalKrullDim_le_of_flat_of_surjective

/-- If every nonempty open of the source of a flat, surjective, locally quasi-finite morphism
has dimension `d`, the same holds for every nonempty open of its target. This is the dimension
condition used together with descent of regularity along finite faithfully flat covers. -/
theorem Scheme.Hom.topologicalKrullDim_opens_eq_of_flat_of_surjective (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyQuasiFinite f] {d : WithBot ℕ∞}
    (hd : ∀ U : X.Opens, Nonempty U → topologicalKrullDim U = d)
    (U : Y.Opens) [Nonempty U] : topologicalKrullDim U = d := by
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Surjective f› U
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨x, -⟩ := (f ∣_ U).surjective (Classical.choice ‹Nonempty U›)
    exact ⟨x⟩
  rw [← (f ∣_ U).topologicalKrullDim_eq_of_flat_of_surjective]
  exact hd (f ⁻¹ᵁ U) inferInstance

end AlgebraicGeometry
