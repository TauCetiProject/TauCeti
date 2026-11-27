/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Linearity
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic

/-!
# Conjugation on a normal closed subgroup

Let `H` be a commutative Hopf algebra over a commutative ring `R`, the coordinate ring of an
affine group `G`, and let `I` be a normal Hopf ideal, cutting out the normal closed subgroup `N`
with coordinate ring `H ⧸ I`. For every commutative `R`-algebra `A`, the points `g ∈ G(A)` act
on the points `N(A)` by conjugation `n ↦ g * n * g⁻¹`
(`TauCeti.HopfIdeal.IsNormal.conjPoints`). This is a group homomorphism from `G(A)` to the
automorphisms of `N(A)`, natural in `A` (`TauCeti.HopfIdeal.IsNormal.mapValue_conjPoints`), and it
is characterized by its composite with the inclusion `N(A) → G(A)`
(`TauCeti.HopfIdeal.IsNormal.mapDomain_conjPoints`).

When `N` is a vector group, that is when `H ⧸ I` is identified with a symmetric algebra
`SymmetricAlgebra R M` as a bialgebra, the points of `N` are the linear maps `M →ₗ[R] A`. Over a
`ℚ`-algebra, conjugation then acts on them by `A`-linear automorphisms
(`TauCeti.HopfIdeal.IsNormal.conjLinearAut`): a natural action on a vector group by group
automorphisms is linear in characteristic zero (`TauCeti.AdditiveGroup.linearAutOfNaturality`).
This is how a group acts linearly on a normal vector subgroup, for instance on the centre of its
unipotent radical.

## Main declarations

* `TauCeti.HopfIdeal.IsNormal.conjPoints`: the conjugation action of the points of the ambient
  group on the points of a normal closed subgroup.
* `TauCeti.HopfIdeal.IsNormal.mapDomain_conjPoints`: in the ambient group it is `n ↦ g * n * g⁻¹`.
* `TauCeti.HopfIdeal.IsNormal.mapValue_conjPoints`: it is natural in the value algebra.
* `TauCeti.HopfIdeal.IsNormal.conjLinearAut`: over a `ℚ`-algebra, conjugation on a normal vector
  subgroup, as `A`-linear automorphisms of its points.
* `TauCeti.HopfIdeal.IsNormal.conjLinearAut_apply`: these automorphisms are conjugation.
* `TauCeti.HopfIdeal.IsNormal.conjLinearAut_mapValue`: they are natural in the value algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), the proof of Theorem 16.33, where a group acts linearly
  on a normal vector subgroup by conjugation.
-/

public section

open WithConv

namespace TauCeti.HopfIdeal

universe u v w x

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
  {I : HopfIdeal R H}

section Conjugation

/-- Restriction of points along the quotient map `H → H ⧸ I` is injective. -/
private theorem mapDomain_mkBialgHom_injective {A : Type w} [CommRing A] [Algebra R A] :
    Function.Injective
      (BialgHom.mapDomain (A := A) (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal)) :=
  BialgHom.mapDomain_injective_of_surjective _ Ideal.Quotient.mk_surjective

/-- `CommHopfAlgCat.quotientPointsSubgroup_normal`, stated for the image of restriction along
`H → H ⧸ I`, the form in which `MulAut.conjNormal` finds the instance. -/
private theorem IsNormal.range_mapDomain_mkBialgHom_normal (hI : I.IsNormal) (A : Type w)
    [CommRing A] [Algebra R A] :
    (BialgHom.mapDomain (A := A)
      (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal)).range.Normal :=
  CommHopfAlgCat.quotientPointsSubgroup_normal (_root_.CommHopfAlgCat.of R H) I hI
    (CommAlgCat.of R A)

/-- **Conjugation on a normal closed subgroup.** For a normal Hopf ideal `I`, the points
`g ∈ G(A)` of the ambient group act on the points of the normal closed subgroup `N` cut out by
`I`, the algebra maps `H ⧸ I →ₐ[R] A`, by conjugation `n ↦ g * n * g⁻¹`
(`TauCeti.HopfIdeal.IsNormal.mapDomain_conjPoints`). It is Mathlib's `MulAut.conjNormal` on the
image of `N(A)` in `G(A)`, the normal subgroup `CommHopfAlgCat.quotientPointsSubgroup`,
transported back to `N(A)` along the injective restriction map. -/
noncomputable def IsNormal.conjPoints (hI : I.IsNormal) (A : Type w) [CommRing A] [Algebra R A] :
    WithConv (H →ₐ[R] A) →* MulAut (WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :=
  haveI := hI.range_mapDomain_mkBialgHom_normal A
  (MulAut.congr (MonoidHom.ofInjective (mapDomain_mkBialgHom_injective (I := I) (A := A))).symm
    ).toMonoidHom.comp MulAut.conjNormal

/-- The conjugation action on a normal closed subgroup is conjugation `n ↦ g * n * g⁻¹` in the
ambient group. Since restriction along `H → H ⧸ I` is injective on points, this characterizes
`TauCeti.HopfIdeal.IsNormal.conjPoints`. -/
-- Not `@[simp]`: `BialgHom.mapDomain_apply` rewrites the left-hand side first.
theorem IsNormal.mapDomain_conjPoints (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) (hI.conjPoints A g n) =
      g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹ := by
  have := hI.range_mapDomain_mkBialgHom_normal A
  simp only [conjPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.symm_symm, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

/-- Pointwise form of `TauCeti.HopfIdeal.IsNormal.mapDomain_conjPoints`: the conjugate point
takes at the class of `x` the value of `g * n * g⁻¹` at `x`. -/
@[simp]
theorem IsNormal.conjPoints_apply_mk (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) (x : H) :
    (hI.conjPoints A g n).ofConv (Ideal.Quotient.mk I.toIdeal x) =
      (g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹).ofConv x := by
  rw [← hI.mapDomain_conjPoints g n, BialgHom.mapDomain_apply_apply,
    Bialgebra.Quotient.mkBialgHom_apply]

/-- **Conjugation on a normal closed subgroup is natural in the value algebra.** -/
theorem IsNormal.mapValue_conjPoints (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] {B : Type x} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A))
    (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    AlgHom.mapValue φ (hI.conjPoints A g n) =
      hI.conjPoints B (AlgHom.mapValue φ g) (AlgHom.mapValue φ n) := by
  apply mapDomain_mkBialgHom_injective
  rw [BialgHom.mapDomain_mapValue_apply, hI.mapDomain_conjPoints, hI.mapDomain_conjPoints,
    BialgHom.mapDomain_mapValue_apply, map_mul, map_mul, map_inv]

end Conjugation

section VectorGroup

variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- Conjugation on a normal closed subgroup, transported along an identification `e` of the
subgroup with the vector group `V(M)` to the points of `V(M)`. -/
private noncomputable def vectorConjPoints (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A : Type x) [CommRing A] [Algebra R A] :
    WithConv (H →ₐ[R] A) →* MulAut (WithConv (SymmetricAlgebra R M →ₐ[R] A)) :=
  (MulAut.congr (e.mapDomainMulEquiv (A := A))).toMonoidHom.comp (hI.conjPoints A)

private theorem vectorConjPoints_apply (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A : Type x) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    vectorConjPoints hI e A g P =
      e.mapDomainMulEquiv (hI.conjPoints A g (e.mapDomainMulEquiv.symm P)) :=
  (rfl)

private theorem vectorConjPoints_mapValue (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A B : Type x) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A))
    (P : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    AlgHom.mapValue φ (vectorConjPoints hI e A g P) =
      vectorConjPoints hI e B (AlgHom.mapValue φ g) (AlgHom.mapValue φ P) := by
  simp only [vectorConjPoints_apply, BialgEquiv.mapDomainMulEquiv_apply,
    BialgEquiv.mapDomainMulEquiv_symm_apply, ← BialgHom.mapDomain_mapValue_apply,
    hI.mapValue_conjPoints]

variable [Algebra ℚ R]

/-- **Conjugation on a normal vector subgroup is linear in characteristic zero.** Let the normal
closed subgroup `N` cut out by `I` be identified by `e` with the vector group `V(M)`, whose points
over `A` are the linear maps `M →ₗ[R] A`. Over a `ℚ`-algebra `R`, each point `g ∈ G(A)` acts on
them by an `A`-linear automorphism, the conjugation `n ↦ g * n * g⁻¹`
(`TauCeti.HopfIdeal.IsNormal.conjLinearAut_apply`), naturally in `A`
(`TauCeti.HopfIdeal.IsNormal.conjLinearAut_mapValue`). -/
noncomputable def IsNormal.conjLinearAut (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A : Type x) [CommRing A] [Algebra R A] :
    WithConv (H →ₐ[R] A) →* ((M →ₗ[R] A) ≃ₗ[A] (M →ₗ[R] A)) :=
  AdditiveGroup.linearAutOfNaturality (vectorConjPoints hI e) (vectorConjPoints_mapValue hI e) A

/-- The linear automorphism through which a point `g` acts sends the linear map
`m ↦ n (e (ι m))` of a point `n` of `N`, read in `V(M)`, to the linear map of its conjugate
`g * n * g⁻¹`. -/
-- Not `@[simp]`: `BialgHom.mapDomain_apply` rewrites the left-hand side first.
theorem IsNormal.conjLinearAut_apply (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A : Type x) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    hI.conjLinearAut e A g
        ((BialgHom.mapDomain (e : SymmetricAlgebra R M →ₐc[R] H ⧸ I.toIdeal) n).ofConv.toLinearMap
          ∘ₗ SymmetricAlgebra.ι R M) =
      (BialgHom.mapDomain (e : SymmetricAlgebra R M →ₐc[R] H ⧸ I.toIdeal)
        (hI.conjPoints A g n)).ofConv.toLinearMap ∘ₗ SymmetricAlgebra.ι R M := by
  have h := AdditiveGroup.linearAutOfNaturality_apply (vectorConjPoints hI e)
    (vectorConjPoints_mapValue hI e) A g (e.mapDomainMulEquiv n)
  rwa [vectorConjPoints_apply, MulEquiv.symm_apply_apply, BialgEquiv.mapDomainMulEquiv_apply,
    BialgEquiv.mapDomainMulEquiv_apply] at h

/-- The linear automorphisms through which the points act by conjugation on a normal vector
subgroup are natural in the value algebra. -/
theorem IsNormal.conjLinearAut_mapValue (hI : I.IsNormal)
    (e : SymmetricAlgebra R M ≃ₐc[R] H ⧸ I.toIdeal) (A B : Type x) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (f : M →ₗ[R] A) :
    φ.toLinearMap ∘ₗ hI.conjLinearAut e A g f =
      hI.conjLinearAut e B (AlgHom.mapValue φ g) (φ.toLinearMap ∘ₗ f) :=
  AdditiveGroup.linearAutOfNaturality_mapValue _ (vectorConjPoints_mapValue hI e) A B φ g f

end VectorGroup

end TauCeti.HopfIdeal
