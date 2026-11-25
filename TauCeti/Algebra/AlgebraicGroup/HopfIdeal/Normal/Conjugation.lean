/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Linearity
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
import Mathlib.Tactic.Group

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

/-- The conjugate `g * n * g⁻¹` of a point `n` of a normal closed subgroup, computed in the
ambient group, vanishes on the normal Hopf ideal `I` cutting out the subgroup. -/
theorem IsNormal.conj_mapDomain_apply_eq_zero (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) {x : H}
    (hx : x ∈ I) :
    (g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹).ofConv x = 0 := by
  rw [← HopfAlgebra.productMap_comp_conjugationAlgHom, AlgHom.comp_apply]
  -- The product of `g` with a point killing `I` kills the right tensor ideal `H ⊗ I`.
  have hker : Ideal.rightTensorIdeal (R := R) (A := H) I.toIdeal ≤
      RingHom.ker (Algebra.TensorProduct.productMap g.ofConv
        (BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n).ofConv).toRingHom := by
    rw [Ideal.rightTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  exact RingHom.mem_ker.mp (hker (hI.conjugation_mem hx))

/-- Restriction of points along the quotient map `H → H ⧸ I` is injective. -/
private theorem mapDomain_mkBialgHom_injective {A : Type w} [CommRing A] [Algebra R A] :
    Function.Injective
      (BialgHom.mapDomain (A := A) (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal)) :=
  BialgHom.mapDomain_injective_of_surjective _ Ideal.Quotient.mk_surjective

/-- The point of the normal closed subgroup whose image in the ambient group is the conjugate
`g * n * g⁻¹`. -/
private noncomputable def conjPointsFun (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    WithConv ((H ⧸ I.toIdeal) →ₐ[R] A) :=
  toConv (Ideal.Quotient.liftₐ I.toIdeal
    (g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹).ofConv
    fun _ hx ↦ hI.conj_mapDomain_apply_eq_zero g n (mem_toIdeal.mp hx))

private theorem mapDomain_conjPointsFun (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) (conjPointsFun hI g n) =
      g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹ := by
  apply WithConv.ofConv_injective
  ext x
  simp only [conjPointsFun, BialgHom.mapDomain_apply_apply]
  exact Ideal.Quotient.lift_mk _ _ _

/-- **Conjugation on a normal closed subgroup.** For a normal Hopf ideal `I`, the points
`g ∈ G(A)` of the ambient group act on the points of the normal closed subgroup `N` cut out by
`I`, the algebra maps `H ⧸ I →ₐ[R] A`, by conjugation `n ↦ g * n * g⁻¹`
(`TauCeti.HopfIdeal.IsNormal.mapDomain_conjPoints`). -/
noncomputable def IsNormal.conjPoints (hI : I.IsNormal) (A : Type w) [CommRing A] [Algebra R A] :
    WithConv (H →ₐ[R] A) →* MulAut (WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) where
  toFun g :=
    { toFun := conjPointsFun hI g
      invFun := conjPointsFun hI g⁻¹
      left_inv n := mapDomain_mkBialgHom_injective <| by
        rw [mapDomain_conjPointsFun, mapDomain_conjPointsFun]
        group
      right_inv n := mapDomain_mkBialgHom_injective <| by
        rw [mapDomain_conjPointsFun, mapDomain_conjPointsFun]
        group
      map_mul' n n' := mapDomain_mkBialgHom_injective <| by
        rw [map_mul, mapDomain_conjPointsFun, mapDomain_conjPointsFun, mapDomain_conjPointsFun,
          map_mul]
        group }
  map_one' := MulEquiv.ext fun n ↦ mapDomain_mkBialgHom_injective <| by
    rw [MulEquiv.coe_mk, Equiv.coe_fn_mk, mapDomain_conjPointsFun, MulAut.one_apply]
    group
  map_mul' g g' := MulEquiv.ext fun n ↦ mapDomain_mkBialgHom_injective <| by
    rw [MulEquiv.coe_mk, Equiv.coe_fn_mk, mapDomain_conjPointsFun, MulAut.mul_apply,
      MulEquiv.coe_mk, Equiv.coe_fn_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk, mapDomain_conjPointsFun,
      mapDomain_conjPointsFun]
    group

/-- The conjugation action on a normal closed subgroup is conjugation `n ↦ g * n * g⁻¹` in the
ambient group. Since restriction along `H → H ⧸ I` is injective on points, this characterizes
`TauCeti.HopfIdeal.IsNormal.conjPoints`. -/
-- Not `@[simp]`: `BialgHom.mapDomain_apply` rewrites the left-hand side first.
theorem IsNormal.mapDomain_conjPoints (hI : I.IsNormal) {A : Type w} [CommRing A]
    [Algebra R A] (g : WithConv (H →ₐ[R] A)) (n : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
    BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) (hI.conjPoints A g n) =
      g * BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) n * g⁻¹ :=
  mapDomain_conjPointsFun hI g n

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
  have key (m : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
      BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) (AlgHom.mapValue φ m) =
        AlgHom.mapValue φ (BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom I.toIdeal) m) :=
    DFunLike.congr_fun (BialgHom.mapValue_mapDomain _ φ) m
  apply mapDomain_mkBialgHom_injective
  rw [key, hI.mapDomain_conjPoints, hI.mapDomain_conjPoints, key, map_mul, map_mul, map_inv]

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
  have key₁ (m : WithConv ((H ⧸ I.toIdeal) →ₐ[R] A)) :
      BialgHom.mapDomain (e : SymmetricAlgebra R M →ₐc[R] H ⧸ I.toIdeal) (AlgHom.mapValue φ m) =
        AlgHom.mapValue φ (BialgHom.mapDomain (e : SymmetricAlgebra R M →ₐc[R] _) m) :=
    DFunLike.congr_fun (BialgHom.mapValue_mapDomain _ φ) m
  have key₂ (m : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
      BialgHom.mapDomain (e.symm : H ⧸ I.toIdeal →ₐc[R] SymmetricAlgebra R M)
          (AlgHom.mapValue φ m) =
        AlgHom.mapValue φ (BialgHom.mapDomain (e.symm : H ⧸ I.toIdeal →ₐc[R] _) m) :=
    DFunLike.congr_fun (BialgHom.mapValue_mapDomain _ φ) m
  rw [vectorConjPoints_apply, vectorConjPoints_apply, BialgEquiv.mapDomainMulEquiv_apply,
    BialgEquiv.mapDomainMulEquiv_apply, BialgEquiv.mapDomainMulEquiv_symm_apply,
    BialgEquiv.mapDomainMulEquiv_symm_apply, ← key₁, hI.mapValue_conjPoints, key₂]

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
