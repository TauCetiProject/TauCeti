/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# The group algebra of a product is the tensor product of group algebras

For two monoids `G` and `H`, the canonical map `single (g, h) 1 ↦ single g 1 ⊗ₜ
single h 1` is an isomorphism of `R`-bialgebras `R[G × H] ≃ₐc[R] R[G] ⊗[R] R[H]`. This file
constructs that isomorphism and records its consequence on the functor of points: the
diagonalizable group `D(G × H) = Spec R[G × H]`, for commutative groups `G` and `H`, is the
direct product `D(G) × D(H)` of the diagonalizable groups of the factors.

The bialgebra isomorphism is built from two mutually inverse algebra maps — the lift of the
group-like monoid hom `(g, h) ↦ single g 1 ⊗ₜ single h 1` one way, and the tensor-product
universal map of the two inclusions `R[G] → R[G × H]`, `R[H] → R[G × H]` (themselves
`MonoidAlgebra.mapDomainAlgHom` of `MonoidHom.inl`/`MonoidHom.inr`) the other way — and then
promoted to a bialgebra equivalence by checking compatibility with the counit and
comultiplication on the group-like generators `single (g, h) 1`.

On points this composes with `TauCeti.AffineGroup.Product.pointsMulEquiv`, the tensor-product
points calculation, through the equiv-version `AlgHom.mapDomainMulEquiv` of the contravariant
functoriality `AlgHom.mapDomain`. When `G` and `H` are commutative groups the group algebras
are Hopf algebras and these convolution monoids are the convolution groups of points
(`TauCeti.AlgHom.instGroup`), so the points equivalence is automatically an isomorphism of
groups: `D(G × H)(A) ≅ D(G)(A) × D(H)(A)`.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 4 "Diagonalizable groups" and the "Worked examples / products" theme, together with the
Layer 0 functor-of-points dictionary): a split torus `𝔾ₘⁿ` is the `n`-fold product of `𝔾ₘ`,
and this identifies its coordinate Hopf algebra `R[ℤⁿ]` with `R[ℤ]^{⊗ n}` and its points with
`(Aˣ)ⁿ`.

## Main definitions

* `TauCeti.MonoidAlgebra.prodTensorAlgEquiv`: the algebra isomorphism
  `R[G × H] ≃ₐ[R] R[G] ⊗[R] R[H]`.
* `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`: the same map as a bialgebra isomorphism.
* `TauCeti.DiagonalizableGroup.prodPointsMulEquiv`: on points,
  `D(G × H)(A) ≃* D(G)(A) × D(H)(A)`.

## References

The tensor-product bialgebra structure and `Algebra.TensorProduct.lift` are from Mathlib's
`Mathlib.RingTheory.Bialgebra.TensorProduct` and `Mathlib.RingTheory.TensorProduct.Maps`; the
group-algebra bialgebra structure and `MonoidAlgebra.mapDomainAlgHom` are from
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra` and `Mathlib.Algebra.MonoidAlgebra.Basic`. The
tensor-product points calculation `TauCeti.AffineGroup.Product.pointsMulEquiv` and the
contravariant functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's existing
functor-of-points infrastructure, built on the Mathlib convolution monoid of Yaël Dillies,
Michał Mrugała and Yunzhou Xie.
-/

open TensorProduct WithConv MonoidAlgebra

namespace TauCeti

universe u v w w'

namespace MonoidAlgebra

variable (R : Type u) [CommSemiring R]
variable {G : Type v} {H : Type w} [Monoid G] [Monoid H]

/-- The group-like monoid homomorphism `(g, h) ↦ single g 1 ⊗ₜ single h 1` from `G × H` into the
multiplicative monoid of `R[G] ⊗[R] R[H]`. -/
private noncomputable def prodGroupLike :
    G × H →* MonoidAlgebra R G ⊗[R] MonoidAlgebra R H where
  toFun p := single p.1 (1 : R) ⊗ₜ[R] single p.2 1
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, ← MonoidAlgebra.one_def,
      Algebra.TensorProduct.one_def]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Algebra.TensorProduct.tmul_mul_tmul,
      single_mul_single, mul_one]

@[simp]
private theorem prodGroupLike_apply (g : G) (h : H) :
    prodGroupLike R (g, h) = single g (1 : R) ⊗ₜ[R] single h 1 := rfl

/-- The forward algebra map `R[G × H] →ₐ[R] R[G] ⊗[R] R[H]`, sending `single (g, h) 1` to
`single g 1 ⊗ₜ single h 1`. -/
private noncomputable def prodTensorAlgHom :
    MonoidAlgebra R (G × H) →ₐ[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  lift R (MonoidAlgebra R G ⊗[R] MonoidAlgebra R H) (G × H) (prodGroupLike R)

@[simp]
private theorem prodTensorAlgHom_single (g : G) (h : H) :
    prodTensorAlgHom R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 := by
  simp only [prodTensorAlgHom, lift_single, one_smul, prodGroupLike_apply]

/-- The images of the two inclusions `R[G] → R[G × H]` and `R[H] → R[G × H]` commute: `single
(g, 1) a` and `single (1, h) b` multiply to `single (g, h) (a * b)` either way, since `R` is
commutative. This is the hypothesis needed to assemble the tensor-product universal map. -/
private theorem commute_mapDomainAlgHom_inl_inr (x : MonoidAlgebra R G) (y : MonoidAlgebra R H) :
    Commute (mapDomainAlgHom R R (MonoidHom.inl G H) x)
      (mapDomainAlgHom R R (MonoidHom.inr G H) y) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    induction y using MonoidAlgebra.induction_on with
    | hM h =>
      simp only [of_apply, mapDomainAlgHom_apply, mapDomain_single, MonoidHom.inl_apply,
        MonoidHom.inr_apply, commute_iff_eq, single_mul_single, Prod.mk_mul_mk, mul_one, one_mul]
    | hadd y₁ y₂ hy₁ hy₂ => rw [map_add]; exact hy₁.add_right hy₂
    | hsmul r y hy => rw [map_smul]; exact hy.smul_right r
  | hadd x₁ x₂ hx₁ hx₂ => rw [map_add]; exact hx₁.add_left hx₂
  | hsmul r x hx => rw [map_smul]; exact hx.smul_left r

/-- The inverse algebra map `R[G] ⊗[R] R[H] →ₐ[R] R[G × H]`, the tensor-product universal map of
the two inclusions `R[G] → R[G × H]` and `R[H] → R[G × H]`. -/
private noncomputable def tensorProdAlgHom :
    MonoidAlgebra R G ⊗[R] MonoidAlgebra R H →ₐ[R] MonoidAlgebra R (G × H) :=
  Algebra.TensorProduct.lift
    (mapDomainAlgHom R R (MonoidHom.inl G H) :
      MonoidAlgebra R G →ₐ[R] MonoidAlgebra R (G × H))
    (mapDomainAlgHom R R (MonoidHom.inr G H) :
      MonoidAlgebra R H →ₐ[R] MonoidAlgebra R (G × H))
    (commute_mapDomainAlgHom_inl_inr R)

@[simp]
private theorem tensorProdAlgHom_tmul_single (g : G) (h : H) :
    tensorProdAlgHom R (single g (1 : R) ⊗ₜ[R] single h 1) = single (g, h) 1 := by
  simp only [tensorProdAlgHom, Algebra.TensorProduct.lift_tmul, mapDomainAlgHom_apply,
    mapDomain_single, single_mul_single, MonoidHom.inl_apply, MonoidHom.inr_apply,
    Prod.mk_mul_mk, mul_one, one_mul]

/-- **The group algebra of a product is the tensor product of group algebras**, as an algebra
isomorphism. It sends `single (g, h) 1` to `single g 1 ⊗ₜ single h 1`. -/
noncomputable def prodTensorAlgEquiv :
    MonoidAlgebra R (G × H) ≃ₐ[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  AlgEquiv.ofAlgHom (prodTensorAlgHom R) (tensorProdAlgHom R)
    (by
      apply Algebra.TensorProduct.ext
      · apply MonoidAlgebra.algHom_ext
        intro g
        simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
        rw [show (1 : MonoidAlgebra R H) = single 1 1 from one_def,
          tensorProdAlgHom_tmul_single, prodTensorAlgHom_single]
      · apply MonoidAlgebra.algHom_ext
        intro h
        simp only [AlgHom.coe_restrictScalars', AlgHom.comp_apply, AlgHom.id_apply,
          Algebra.TensorProduct.includeRight_apply]
        rw [show (1 : MonoidAlgebra R G) = single 1 1 from one_def,
          tensorProdAlgHom_tmul_single, prodTensorAlgHom_single])
    (by
      apply MonoidAlgebra.algHom_ext
      rintro ⟨g, h⟩
      rw [AlgHom.comp_apply, prodTensorAlgHom_single, tensorProdAlgHom_tmul_single,
        AlgHom.id_apply])

@[simp]
theorem prodTensorAlgEquiv_single (g : G) (h : H) :
    prodTensorAlgEquiv R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 :=
  prodTensorAlgHom_single R g h

/-- **The group algebra of a product is the tensor product of group algebras**, as a bialgebra
isomorphism. -/
noncomputable def prodTensorBialgEquiv :
    MonoidAlgebra R (G × H) ≃ₐc[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  BialgEquiv.ofAlgEquiv (prodTensorAlgEquiv R)
    (by
      apply MonoidAlgebra.algHom_ext
      rintro ⟨g, h⟩
      simp)
    (by
      apply MonoidAlgebra.algHom_ext
      rintro ⟨g, h⟩
      simp)

@[simp]
theorem prodTensorBialgEquiv_single (g : G) (h : H) :
    prodTensorBialgEquiv R (single (g, h) (1 : R)) = single g 1 ⊗ₜ[R] single h 1 :=
  prodTensorAlgEquiv_single R g h

@[simp]
theorem prodTensorBialgEquiv_symm_tmul_single (g : G) (h : H) :
    (prodTensorBialgEquiv R).symm (single g (1 : R) ⊗ₜ[R] single h 1) = single (g, h) 1 := by
  rw [← prodTensorBialgEquiv_single R g h, BialgEquiv.symm_apply_apply]

end MonoidAlgebra

namespace DiagonalizableGroup

variable {R : Type u} [CommSemiring R]
variable {G : Type v} {H : Type w} [CommGroup G] [CommGroup H]
variable {A : Type w'} [CommSemiring A] [Algebra R A]

/-- **The diagonalizable group of a product is the product of diagonalizable groups, on points.**
For commutative groups `G` and `H` and every commutative `R`-algebra `A`, the convolution group
of `A`-points of `D(G × H)` is the product of the convolution groups of `A`-points of `D(G)` and
`D(H)`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (MonoidAlgebra R (G × H) →ₐ[R] A) ≃*
      WithConv (MonoidAlgebra R G →ₐ[R] A) × WithConv (MonoidAlgebra R H →ₐ[R] A) :=
  (AlgHom.mapDomainMulEquiv (A := A) (MonoidAlgebra.prodTensorBialgEquiv R)).symm.trans
    AffineGroup.Product.pointsMulEquiv

/-- The first component of `prodPointsMulEquiv` restricts an `A`-point of `D(G × H)` to the
factor `D(G)`: on the generator `single g 1` it evaluates the original point at `single (g, 1) 1`,
the image of `g` under `G → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_fst_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (g : G) :
    (prodPointsMulEquiv f).1.ofConv (single g (1 : R)) =
      f.ofConv (single (g, (1 : H)) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeLeft_apply, BialgEquiv.coe_toBialgHom]
  rw [show (1 : MonoidAlgebra R H) = single 1 1 from MonoidAlgebra.one_def,
    MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The second component of `prodPointsMulEquiv` restricts an `A`-point of `D(G × H)` to the
factor `D(H)`: on the generator `single h 1` it evaluates the original point at `single (1, h) 1`,
the image of `h` under `H → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_snd_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (h : H) :
    (prodPointsMulEquiv f).2.ofConv (single h (1 : R)) =
      f.ofConv (single ((1 : G), h) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeRight_apply, BialgEquiv.coe_toBialgHom]
  rw [show (1 : MonoidAlgebra R G) = single 1 1 from MonoidAlgebra.one_def,
    MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The inverse of `prodPointsMulEquiv` assembles an `A`-point of `D(G × H)` from a pair of
points of `D(G)` and `D(H)`: on the generator `single (g, h) 1` it multiplies the value of the
first point at `single g 1` and the value of the second at `single h 1`. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_single
    (f₁ : WithConv (MonoidAlgebra R G →ₐ[R] A)) (f₂ : WithConv (MonoidAlgebra R H →ₐ[R] A))
    (g : G) (h : H) :
    (prodPointsMulEquiv.symm (f₁, f₂)).ofConv (single (g, h) (1 : R)) =
      f₁.ofConv (single g 1) * f₂.ofConv (single h 1) := by
  rw [prodPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    AlgHom.mapDomainMulEquiv_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    BialgEquiv.coe_toBialgHom, MonoidAlgebra.prodTensorBialgEquiv_single,
    AffineGroup.Product.pointsMulEquiv_symm_apply, Algebra.TensorProduct.productMap_apply_tmul]

end DiagonalizableGroup

end TauCeti
