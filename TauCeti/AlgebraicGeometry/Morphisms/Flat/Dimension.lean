/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

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

* `TauCeti.AlgebraicGeometry.coheight_zeroLocus_eq_height_map`: the codimension of a point of
  `Spec A` inside `V(I)` is the height of its image in `A ⧸ I`.
* `AlgebraicGeometry.Scheme.Hom.coheight_eq_coheight_add_coheight_preimage`: for a flat morphism,
  the codimension of a point is that of its image plus that in its fibre.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON), the algebraic dimension
  formula for going-down extensions.
* H. Matsumura, *Commutative Ring Theory*, Theorem 15.1.
-/

public section

open CategoryTheory Order Topology TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- In `Spec A`, the codimension of a point `x` of the closed subset `V(I)`, written as
`{y | I ≤ y.asIdeal}`, inside `V(I)` is the height of the image of `x` in `A ⧸ I`. -/
theorem coheight_zeroLocus_eq_height_map {A : CommRingCat.{u}} (I : Ideal A) (x : Spec A)
    (hx : I ≤ x.asIdeal) :
    coheight (⟨x, hx⟩ : {y : Spec A | I ≤ y.asIdeal}) =
      (x.asIdeal.map (Ideal.Quotient.mk I)).height := by
  let π := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hπ : IsInducing π := (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isInducing
  -- The closed immersion `π` is an embedding for the specialization orders.
  have hlt {a b : Spec (.of (A ⧸ I))} : π a < π b ↔ a < b :=
    and_congr hπ.specializes_iff (not_congr hπ.specializes_iff)
  have hrange (y : Spec A) : y ∈ Set.range π ↔ I ≤ y.asIdeal := by
    have h := Set.ext_iff.mp
      (range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I))) y
    rw [Ideal.mk_ker] at h
    exact h.trans SetLike.coe_subset_coe
  have := x.isPrime
  let z : Spec (.of (A ⧸ I)) := ⟨x.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
  have hπz : π z = x := PrimeSpectrum.ext (Ideal.comap_map_of_surjective' _
    Ideal.Quotient.mk_surjective _ |>.trans (by rw [Ideal.mk_ker, sup_eq_left.mpr hx]))
  let F : Spec (.of (A ⧸ I)) → {y : Spec A | I ≤ y.asIdeal} :=
    fun w ↦ ⟨π w, (hrange _).mp ⟨w, rfl⟩⟩
  refine (idealHeight_eq_coheight _ z).symm ▸ ?_
  have hxz : (⟨x, hx⟩ : {y : Spec A | I ≤ y.asIdeal}) = F z := Subtype.ext hπz.symm
  rw [hxz]
  refine (coheight_eq_of_strictMono F
    (fun _ _ h ↦ Subtype.coe_lt_coe.mp (hlt.mpr h))
    (fun w b h ↦ ?_) z).symm
  obtain ⟨w', hw'⟩ := (hrange b).mpr b.2
  exact ⟨w', hlt.mp (by rw [hw']; exact h), Subtype.ext hw'⟩

end TauCeti.AlgebraicGeometry

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
  -- The fibre of `Spec S → Spec R` over `q` lies in `V(I)` and contains its generizations there.
  let T : Set (Spec S) := {v | Spec.map φ v = Spec.map φ x'}
  have hT {v : Spec S} (hv : v ∈ T) : Spec.map φ v = Spec.map φ x' := hv
  have hTI {v : Spec S} (hv : v ∈ T) : I ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (congrArg PrimeSpectrum.asIdeal hv).ge
  have hTup {v v' : Spec S} (hv : v ∈ T) (hvv' : v ≤ v') (hv' : I ≤ v'.asIdeal) :
      v' ∈ T := by
    have hle : v'.asIdeal ≤ v.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hvv'
    refine PrimeSpectrum.ext (le_antisymm ?_ (Ideal.map_le_iff_le_comap.mp hv'))
    rw [← hT hv]
    exact Ideal.comap_mono hle
  have hx'T : x' ∈ T := rfl
  refine (TauCeti.AlgebraicGeometry.coheight_zeroLocus_eq_height_map I x' (hTI rfl)).symm.trans ?_
  refine (coheight_eq_of_strictMono
    (fun v : T ↦ (⟨v, hTI v.2⟩ : {v : Spec S | I ≤ v.asIdeal})) (fun _ _ h ↦ h)
    (fun v b h ↦ ⟨⟨b, hTup v.2 h.le b.2⟩, h, rfl⟩) ⟨x', hx'T⟩).symm.trans ?_
  -- The chart identifies the fibre of `Spec S → Spec R` with an open part of the fibre of `f`,
  -- containing all generizations of its points.
  let F : T → f ⁻¹' {f x} := fun v ↦ ⟨hV.fromSpec v, by
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← hcomm_apply, hT v.2, hcomm_apply, hx']⟩
  have hι : IsInducing hV.fromSpec := hV.fromSpec.isOpenEmbedding.isInducing
  have hlt {a b : Spec S} : hV.fromSpec a < hV.fromSpec b ↔ a < b :=
    and_congr hι.specializes_iff (not_congr hι.specializes_iff)
  have hxF : (⟨x, rfl⟩ : f ⁻¹' {f x}) = F ⟨x', hx'T⟩ := Subtype.ext hx'.symm
  rw [hxF]
  refine coheight_eq_of_strictMono F
    (fun _ _ h ↦ Subtype.coe_lt_coe.mp (hlt.mpr h)) (fun v b h ↦ ?_) _
  obtain ⟨v', hv'⟩ : (b : X) ∈ Set.range hV.fromSpec :=
    h.le.mem_open hV.fromSpec.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
  have hv'T : v' ∈ T := hU.fromSpec.isOpenEmbedding.injective <| by
    rw [hcomm_apply, hcomm_apply, hv', hx']
    exact b.2
  exact ⟨⟨v', hv'T⟩, hlt.mp (by rw [hv']; exact h), Subtype.ext hv'⟩

end AlgebraicGeometry
