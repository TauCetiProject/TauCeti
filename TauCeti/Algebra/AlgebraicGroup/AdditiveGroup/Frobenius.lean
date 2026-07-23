/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# The Frobenius endomorphism of the additive group

Over a base commutative semiring `R` of exponential characteristic `p`, the additive group
`𝔾ₐ = Spec R[x]` (here `x = ι R R 1` in `SymmetricAlgebra R R`) carries the **Frobenius
endomorphism** `F : 𝔾ₐ → 𝔾ₐ`, which on every commutative `R`-algebra `A` raises a point to its
`p`-th power,
`a ↦ aᵖ`. This is a homomorphism of group functors precisely because of the freshman's dream:
raising to the `p`-th power is additive in exponential characteristic `p`. Contravariantly it is
induced by the bialgebra endomorphism of the coordinate Hopf algebra `R[x]` sending the primitive
generator `x` to `xᵖ` (again primitive, `Δ(xᵖ) = xᵖ ⊗ 1 + 1 ⊗ xᵖ`).

The exponential-characteristic hypothesis `[ExpChar R p]` covers both the interesting case of
prime characteristic `p` (where `F` is the genuine Frobenius) and the degenerate case `p = 1`
(characteristic zero, where `F` is the identity), so the API applies verbatim to the Frobenius
kernel group scheme `αₚ` of `TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic`,
where `R` has prime characteristic `p`.

## Main declarations

* `TauCeti.AdditiveGroup.comul_ι_pow`: in exponential characteristic `p` the Frobenius power `xᵖ`
  is primitive, `Δ(xᵖ) = xᵖ ⊗ 1 + 1 ⊗ xᵖ`.
* `TauCeti.AdditiveGroup.frobeniusBialgHom`: the Frobenius bialgebra endomorphism `x ↦ xᵖ` of the
  coordinate Hopf algebra `R[x]` of `𝔾ₐ`.
* `TauCeti.AdditiveGroup.frobeniusEnd`: the Frobenius endomorphism of `𝔾ₐ` on the functor of
  points, the contravariant image of `frobeniusBialgHom`.
* `TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd`: the Frobenius endomorphism acts as
  `a ↦ aᵖ` on points.
* `TauCeti.AdditiveGroup.mapValue_frobeniusEnd`: the Frobenius endomorphism is natural in the
  value algebra.

## References

The additive-group points dictionary `TauCeti.AdditiveGroup.gaPointsMulEquiv` and the
coordinate-Hopf-algebra functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's. The freshman's
dream `add_pow_expChar`, the symmetric-algebra bialgebra structure, and the bialgebra-hom
constructor `BialgHom.ofAlgHom` are Mathlib's.
-/

public section

open Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w

variable (R : Type u) [CommSemiring R] (p : ℕ)

/-- The coordinate `R`-algebra endomorphism of `R[x] = SymmetricAlgebra R R` sending the generator
`x = ι R R 1` to `xᵖ`. It underlies the Frobenius endomorphism of the additive group `𝔾ₐ`. -/
private noncomputable def frobeniusAlgHom :
    SymmetricAlgebra R R →ₐ[R] SymmetricAlgebra R R :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton R (SymmetricAlgebra R R) ((ι R R 1) ^ p))

private theorem frobeniusAlgHom_ι (r : R) :
    frobeniusAlgHom R p (ι R R r) = r • (ι R R 1) ^ p := by
  rw [frobeniusAlgHom, SymmetricAlgebra.lift_ι_apply, LinearMap.toSpanSingleton_apply]

private theorem frobeniusAlgHom_ι_one :
    frobeniusAlgHom R p (ι R R 1) = (ι R R 1) ^ p := by
  rw [frobeniusAlgHom_ι, one_smul]

variable [ExpChar R p]

/-- The tensor-square ring of the additive-group Hopf algebra has the same exponential
characteristic `p` as `R`: the structure map `R → R[x] ⊗ R[x]` is a section of the counit, hence
injective. -/
theorem expChar_tensorSquare :
    ExpChar (SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R) p :=
  expChar_of_injective_algebraMap
    (Function.LeftInverse.injective (g := Coalgebra.counit (R := R))
      fun r => Bialgebra.counit_algebraMap r) p

/-- **The Frobenius power `xᵖ` is primitive.** In exponential characteristic `p` the
comultiplication of `xᵖ` is `xᵖ ⊗ 1 + 1 ⊗ xᵖ`, by the freshman's dream applied to the primitive
generator `x`. -/
theorem comul_ι_pow :
    Coalgebra.comul (R := R) ((ι R R 1 : SymmetricAlgebra R R) ^ p) =
      ((ι R R 1 : SymmetricAlgebra R R) ^ p) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ((ι R R 1 : SymmetricAlgebra R R) ^ p) := by
  haveI := expChar_tensorSquare R p
  rw [Bialgebra.comul_pow, comul_ι, add_pow_expChar, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_pow, one_pow]

/-- **The Frobenius bialgebra endomorphism `x ↦ xᵖ` of the coordinate Hopf algebra of `𝔾ₐ`.** In
exponential characteristic `p` the generator `x` is primitive, hence so is `xᵖ`
(`Δ(xᵖ) = xᵖ ⊗ 1 + 1 ⊗ xᵖ` by the freshman's dream), and the counit still vanishes on `xᵖ`, so
the algebra endomorphism `x ↦ xᵖ` is a bialgebra endomorphism. It induces the Frobenius
endomorphism of `𝔾ₐ` on the functor of points. -/
noncomputable def frobeniusBialgHom :
    SymmetricAlgebra R R →ₐc[R] SymmetricAlgebra R R :=
  BialgHom.ofAlgHom (frobeniusAlgHom R p)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [frobeniusAlgHom_ι_one, algebraMapInv_ι, zero_pow (expChar_ne_zero R p)])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      simp [frobeniusAlgHom_ι_one, comul_ι_pow R p, comul_ι])

@[simp]
theorem frobeniusBialgHom_ι (r : R) :
    frobeniusBialgHom R p (ι R R r) = r • (ι R R 1) ^ p :=
  frobeniusAlgHom_ι R p r

theorem frobeniusBialgHom_ι_one :
    frobeniusBialgHom R p (ι R R 1) = (ι R R 1) ^ p :=
  frobeniusAlgHom_ι_one R p

variable {A : Type v} [CommSemiring A] [Algebra R A]

/-- **The Frobenius endomorphism of `𝔾ₐ`, on the functor of points.** For every commutative
`R`-algebra `A` it is the homomorphism of the convolution group of points induced (contravariantly)
by the Frobenius bialgebra endomorphism `x ↦ xᵖ`; on points it raises a point to its `p`-th power,
`a ↦ aᵖ`. -/
noncomputable def frobeniusEnd :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) →* WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
  AlgHom.mapDomain (frobeniusBialgHom R p)

/-- **The Frobenius endomorphism acts as `a ↦ aᵖ` on points.** Reading a `𝔾ₐ`-point off on the
generator `x = ι 1`, the Frobenius endomorphism raises the resulting element of `A` to its `p`-th
power.

This is not a `simp` lemma: the `@[simp]` lemma `toAdd_gaPointsMulEquiv` already rewrites the
left-hand side `Multiplicative.toAdd (gaPointsMulEquiv ..)`, so the statement is not in
simp-normal form. -/
theorem toAdd_gaPointsMulEquiv_frobeniusEnd (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv (frobeniusEnd R p F)) =
      Multiplicative.toAdd (gaPointsMulEquiv F) ^ p := by
  simp only [toAdd_gaPointsMulEquiv, frobeniusEnd, AlgHom.mapDomain_apply,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom, frobeniusBialgHom_ι_one, map_pow]

variable {B : Type w} [CommSemiring B] [Algebra R B]

/-- **Naturality in the value algebra.** The Frobenius endomorphism of `𝔾ₐ` commutes with the
value-algebra functoriality `AlgHom.mapValue`. -/
theorem mapValue_frobeniusEnd (χ : A →ₐ[R] B) :
    (frobeniusEnd R p (A := B)).comp (AlgHom.mapValue (H := SymmetricAlgebra R R) χ) =
      (AlgHom.mapValue (H := SymmetricAlgebra R R) χ).comp (frobeniusEnd R p (A := A)) :=
  AlgHom.mapValue_mapDomain (frobeniusBialgHom R p) χ

end AdditiveGroup

end TauCeti
