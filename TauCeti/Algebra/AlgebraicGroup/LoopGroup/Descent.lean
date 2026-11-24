/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.RingTheory.HahnSeries.Map
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# The fpqc sheaf condition for formal loop groups

Let `H` be a Hopf algebra over a commutative ring `k`, not necessarily commutative. For a
commutative `k`-algebra `R`, the loops of `H` over `R` form the convolution group
`LG(R) = WithConv (H →ₐ[k] R⸨X⸩)`. Here `R⸨X⸩` carries the coefficientwise `k`-algebra structure
`HahnSeries.instAlgebra`, and a `k`-algebra map `R → S` acts on loops through the coefficients
(`HahnSeries.mapAlgHom`). When `H` is moreover commutative, `LG(R) = G(R⸨X⸩)` is the formal loop
group of the affine group scheme `G = Spec H`. This file proves that `R ↦ LG(R)` is a sheaf for
the fpqc topology on commutative `k`-algebras, in the affine form consisting of the two conditions
below; nonreduced `R` are included and no field or characteristic hypothesis is used.

* **Faithfully flat descent.** For a faithfully flat `R`-algebra `S`, base change identifies
  `LG(R)` with the subgroup of `LG(S)` of loops whose two images in `LG(S ⊗[R] S)` agree
  (`HopfAlgebra.loopFaithfullyFlatDescentMulEquiv`). The overlap is `(S ⊗[R] S)⸨X⸩`, with the two
  maps `s ↦ s ⊗ₜ 1` and `s ↦ 1 ⊗ₜ s` applied to every coefficient; it is not the tensor product
  `S⸨X⸩ ⊗[R⸨X⸩] S⸨X⸩`, so this is not the descent of points along `R⸨X⸩ → S⸨X⸩`. The input is the
  exactness of `R → S ⇉ S ⊗[R] S` (`Algebra.IsEffective.of_faithfullyFlat`), which holds
  coefficientwise (`HahnSeries.eqLocusS_mapRingHom`) because a Laurent series is determined by
  its coefficients and the coefficients of a descended series have the same support.
* **Finite products.** For a finite family of commutative `k`-algebras `A i`, the loops valued in
  `∀ i, A i` are the families of loops valued in the factors (`HopfAlgebra.loopPiMulEquiv`); for
  the empty family, `LG` of the zero ring is trivial. This needs only a bialgebra `H`, for which
  it is an isomorphism of convolution monoids.

For a finite fpqc covering `{R → R_i}` the sheaf condition reduces to these two: `S = ∀ i, R_i` is
faithfully flat over `R`, and `S ⊗[R] S` is the finite product of the `R_i ⊗[R] R_j`. Zariski
coverings of an affine scheme by finitely many basic opens are such coverings. This is the
reduction of the fpqc sheaf condition to finite products and single faithfully flat coverings of
affine schemes, which Mathlib records for presheaves on schemes as
`AlgebraicGeometry.isSheaf_type_propQCTopology_iff` (Stacks, Tag 022H).

The statements hold for Hahn series `R⟦Γ⟧` over any ordered cancellative exponent monoid `Γ`;
the formal loop group is the case `Γ = ℤ`, where `R⟦ℤ⟧ = R⸨X⸩`. For `Γ = ℤ` instance search
finds a second `k`-algebra structure on `R⸨X⸩`, inherited from `R⟦X⟧` through
`HahnSeries.powerSeriesAlgebra`; it agrees with the coefficientwise one only propositionally, and
files applying these results to `R⸨X⸩` should select the coefficientwise one with
`attribute [local instance 1100] HahnSeries.instAlgebra`.

## Main declarations

* `TauCeti.HopfAlgebra.loopDescentSubgroup`: the loops over `S` satisfying the descent condition
  over `S ⊗[R] S`, with `mem_loopDescentSubgroup_iff` stating it coefficient by coefficient.
* `TauCeti.HopfAlgebra.loopFaithfullyFlatDescentMulEquiv`: loops over `R` are the loops over a
  faithfully flat `S` satisfying the descent condition.
* `TauCeti.HopfAlgebra.loopPiMulEquiv`: loops over a finite product are families of loops.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, §1.3.1: the loop group `G((t))` as a
  functor of the coefficient algebra.
* V. Drinfeld, *Infinite-dimensional vector bundles in algebraic geometry: an introduction*,
  Theorem 3.11: the corresponding coefficient-ring descent for finite projective `R((t))`-modules,
  whose overlap is likewise `(S ⊗[R] S)((t))`.
* [The Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H): a presheaf is an fpqc
  sheaf when it is a Zariski sheaf and satisfies the sheaf condition for faithfully flat maps of
  affine schemes.
-/

public section

open Algebra.TensorProduct WithConv
open scoped HahnSeries TensorProduct

namespace TauCeti

namespace HopfAlgebra

variable (k : Type*) {H : Type*} [CommSemiring k] [Semiring H]
variable (Γ : Type*) [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]

section DescentSubgroup

variable [_root_.HopfAlgebra k H] (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra k R]
  [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- The coefficientwise map `S⟦Γ⟧ → (S ⊗[R] S)⟦Γ⟧` of `s ↦ s ⊗ₜ 1`. -/
private noncomputable def descentLeft : S⟦Γ⟧ →ₐ[k] (S ⊗[R] S)⟦Γ⟧ :=
  HahnSeries.mapAlgHom ((includeLeft : S →ₐ[R] S ⊗[R] S).restrictScalars k)

/-- The coefficientwise map `S⟦Γ⟧ → (S ⊗[R] S)⟦Γ⟧` of `s ↦ 1 ⊗ₜ s`. -/
private noncomputable def descentRight : S⟦Γ⟧ →ₐ[k] (S ⊗[R] S)⟦Γ⟧ :=
  HahnSeries.mapAlgHom ((includeRight : S →ₐ[R] S ⊗[R] S).restrictScalars k)

variable (H) in
/-- **The descent condition for loops.** For an `R`-algebra `S`, the subgroup of loops
`g : H →ₐ[k] S⟦Γ⟧` whose two images in the loops over `S ⊗[R] S`, through `s ↦ s ⊗ₜ 1` and
`s ↦ 1 ⊗ₜ s` on every coefficient, agree. For `Γ = ℤ` it is the equalizer of
`LG(S) ⇉ LG(S ⊗[R] S)`. -/
noncomputable def loopDescentSubgroup : Subgroup (WithConv (H →ₐ[k] S⟦Γ⟧)) :=
  MonoidHom.eqLocus (AlgHom.mapValue (H := H) (descentLeft k Γ R S))
    (AlgHom.mapValue (H := H) (descentRight k Γ R S))

/-- A loop satisfies the descent condition exactly when every coefficient of every value does:
`c ⊗ₜ 1 = 1 ⊗ₜ c` in `S ⊗[R] S`. -/
@[simp]
theorem mem_loopDescentSubgroup_iff (g : WithConv (H →ₐ[k] S⟦Γ⟧)) :
    g ∈ loopDescentSubgroup k H Γ R S ↔
      ∀ h n, (g.ofConv h).coeff n ⊗ₜ[R] (1 : S) = 1 ⊗ₜ[R] (g.ofConv h).coeff n := by
  -- Mathlib has no membership lemma for the subgroup `MonoidHom.eqLocus`, only `mem_eqLocusM`
  -- for the submonoid it extends, so membership is unfolded definitionally.
  change AlgHom.mapValue _ g = AlgHom.mapValue _ g ↔ _
  rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, WithConv.toConv_injective.eq_iff,
    AlgHom.ext_iff]
  refine forall_congr' fun h ↦ ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, descentLeft, descentRight, HahnSeries.ext_iff,
    funext_iff]
  simp only [HahnSeries.coeff_mapAlgHom, AlgHom.coe_restrictScalars', includeLeft_apply,
    includeRight_apply]

/-- Base change of loops along `R → S`, landing in the descent subgroup. -/
private noncomputable def loopDescentHom :
    WithConv (H →ₐ[k] R⟦Γ⟧) →* loopDescentSubgroup k H Γ R S :=
  (AlgHom.mapValue (H := H)
      (HahnSeries.mapAlgHom (Γ := Γ) (IsScalarTower.toAlgHom k R S))).codRestrict _ fun f ↦ by
      rw [mem_loopDescentSubgroup_iff]
      intro h n
      simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
        HahnSeries.coeff_mapAlgHom]
      rw [IsScalarTower.coe_toAlgHom', Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]

private theorem coe_loopDescentHom_apply (f : WithConv (H →ₐ[k] R⟦Γ⟧)) :
    (loopDescentHom k Γ R S f : WithConv (H →ₐ[k] S⟦Γ⟧)) =
      AlgHom.mapValue (H := H)
        (HahnSeries.mapAlgHom (Γ := Γ) (IsScalarTower.toAlgHom k R S)) f :=
  rfl

end DescentSubgroup

section Descent

variable [_root_.HopfAlgebra k H] (R S : Type*) [CommRing R] [CommRing S] [Algebra k R]
  [Algebra k S] [Algebra R S] [IsScalarTower k R S] [Module.FaithfullyFlat R S]

/-- The loops over `S` satisfying the descent condition are those coming from loops over `R`:
the coefficientwise image of `R⟦Γ⟧` is the equalizer of the two maps to `(S ⊗[R] S)⟦Γ⟧`. -/
private theorem loopDescentHom_bijective :
    Function.Bijective (loopDescentHom (H := H) k Γ R S) := by
  have hinj :
      Function.Injective (HahnSeries.mapAlgHom (Γ := Γ) (IsScalarTower.toAlgHom k R S)) :=
    HahnSeries.mapAlgHom_injective (FaithfulSMul.algebraMap_injective R S)
  refine ⟨fun f g hfg ↦ AlgHom.mapValue_injective hinj ?_, fun g ↦ ?_⟩
  · simpa only [coe_loopDescentHom_apply] using congr_arg Subtype.val hfg
  have heq : {x | descentLeft k Γ R S x = descentRight k Γ R S x} =
      Set.range (HahnSeries.mapAlgHom (Γ := Γ) (IsScalarTower.toAlgHom k R S)) := by
    have hS : (includeLeftRingHom.eqLocusS (includeRight.toRingHom : S →+* S ⊗[R] S)) =
        (algebraMap R S).rangeS :=
      SetLike.coe_injective <|
        (Algebra.IsEffective.of_faithfullyFlat R S).eqLocus_includeLeft_includeRight
    ext x
    have hx := SetLike.ext_iff.mp (HahnSeries.eqLocusS_mapRingHom (Γ := Γ) hS) x
    simp only [RingHom.mem_eqLocusS, RingHom.mem_rangeS, HahnSeries.mapRingHom_apply] at hx
    simp only [Set.mem_ofPred_eq, Set.mem_range, descentLeft, descentRight,
      HahnSeries.mapAlgHom_apply]
    exact hx
  obtain ⟨f, hf⟩ :=
    (AlgHom.mem_mrange_mapValue_iff_mapValue_eq_mapValue hinj heq).mpr g.property
  exact ⟨f, Subtype.ext hf⟩

/-- **Faithfully flat descent for formal loops.** For a faithfully flat `R`-algebra `S`, base
change along `R → S` identifies the loops `H →ₐ[k] R⟦Γ⟧` with the loops over `S` whose two images
in the loops over `S ⊗[R] S` agree. For `Γ = ℤ` this is the sheaf condition
`LG(R) = eq(LG(S) ⇉ LG(S ⊗[R] S))` of the formal loop group for the faithfully flat covering
`Spec S → Spec R`. -/
noncomputable def loopFaithfullyFlatDescentMulEquiv :
    WithConv (H →ₐ[k] R⟦Γ⟧) ≃* loopDescentSubgroup k H Γ R S :=
  MulEquiv.ofBijective (loopDescentHom k Γ R S) (loopDescentHom_bijective k Γ R S)

/-- The faithfully flat descent equivalence for loops is base change of the coefficients. -/
@[simp]
theorem loopFaithfullyFlatDescentMulEquiv_apply (f : WithConv (H →ₐ[k] R⟦Γ⟧)) (h : H) :
    (loopFaithfullyFlatDescentMulEquiv k Γ R S f : WithConv (H →ₐ[k] S⟦Γ⟧)).ofConv h =
      HahnSeries.mapRingHom (algebraMap R S) (f.ofConv h) := by
  rw [loopFaithfullyFlatDescentMulEquiv, MulEquiv.ofBijective_apply, coe_loopDescentHom_apply,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, HahnSeries.mapAlgHom_apply,
    HahnSeries.mapRingHom_apply]
  rfl

end Descent

section Pi

variable [_root_.Bialgebra k H] {ι : Type*} [Finite ι] (A : ι → Type*) [∀ i, CommSemiring (A i)]
  [∀ i, Algebra k (A i)]

/-- **Formal loops over a finite product.** A loop valued in Hahn series over a finite product
`∀ i, A i` is the family of its coefficientwise projections, as an isomorphism of convolution
monoids; for a Hopf algebra `H` it is an isomorphism of groups. For `Γ = ℤ` this is
`LG(∏ i, A i) ≃* ∏ i, LG(A i)`; for the empty family it says that `LG` of the zero ring is
trivial. -/
noncomputable def loopPiMulEquiv :
    WithConv (H →ₐ[k] (∀ i, A i)⟦Γ⟧) ≃* ∀ i, WithConv (H →ₐ[k] (A i)⟦Γ⟧) :=
  (HahnSeries.piAlgEquiv k).mapValueMulEquiv.trans AlgHom.piValueMulEquiv

/-- The `i`-th component of a loop over a product is its coefficientwise projection. -/
@[simp]
theorem loopPiMulEquiv_apply (g : WithConv (H →ₐ[k] (∀ i, A i)⟦Γ⟧)) (i : ι) (h : H) :
    (loopPiMulEquiv k Γ A g i).ofConv h =
      HahnSeries.mapRingHom (Pi.evalRingHom A i) (g.ofConv h) := by
  rw [loopPiMulEquiv, MulEquiv.trans_apply, AlgHom.piValueMulEquiv_apply,
    AlgEquiv.mapValueMulEquiv_apply, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, HahnSeries.piAlgEquiv_apply]

/-- A family of loops over the factors assembles to the loop over the product whose coefficients
are the families of coefficients. -/
@[simp]
theorem coeff_loopPiMulEquiv_symm_apply (g : ∀ i, WithConv (H →ₐ[k] (A i)⟦Γ⟧)) (h : H) (n : Γ)
    (i : ι) : (((loopPiMulEquiv k Γ A).symm g).ofConv h).coeff n i = ((g i).ofConv h).coeff n := by
  rw [loopPiMulEquiv, MulEquiv.symm_trans_apply, AlgEquiv.mapValueMulEquiv_symm_apply,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    HahnSeries.coeff_piAlgEquiv_symm_apply]
  exact congr_arg (fun x : (A i)⟦Γ⟧ ↦ x.coeff n) (AlgHom.piValueMulEquiv_symm_apply g h i)

end Pi

end HopfAlgebra

end TauCeti
