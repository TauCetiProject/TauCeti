/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic

/-!
# `αₚ` is the kernel of the Frobenius endomorphism of the additive group

Over a base ring `R` of prime characteristic `p`, the additive group `𝔾ₐ = Spec R[x]` (here
`x = ι R R 1` in `SymmetricAlgebra R R`) carries the **Frobenius endomorphism** `F : 𝔾ₐ → 𝔾ₐ`,
which on every commutative `R`-algebra `A` raises a point to its `p`-th power, `a ↦ aᵖ`. This is a
homomorphism of group functors precisely because of the freshman's dream: raising to the `p`-th
power is additive in characteristic `p`. Contravariantly it is induced by the bialgebra
endomorphism of the coordinate Hopf algebra `R[x]` sending the primitive generator `x` to `xᵖ`
(again primitive in characteristic `p`, `Δ(xᵖ) = xᵖ ⊗ 1 + 1 ⊗ xᵖ`).

`TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic` builds the Frobenius kernel group
scheme `αₚ = Spec R[x]/(xᵖ)` and identifies its functor of points with the `p`-nilpotent elements
of the additive group. This file makes the Frobenius endomorphism itself explicit on the functor
of points and proves that `αₚ` is exactly its kernel: as subgroups of the group of `𝔾ₐ`-points,
the image of the inclusion `αₚ ↪ 𝔾ₐ` equals the kernel of the Frobenius endomorphism. This
realizes `αₚ = ker(𝔾ₐ --a ↦ aᵖ--> 𝔾ₐ)` on the functor of points, the additive companion of the
identification of `μ_n` with the kernel of the `n`th power endomorphism of `𝔾ₘ`
(`TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Kernel`).

The mechanism is the worked-example points dictionary. A point of `𝔾ₐ = Spec R[x]` reads off the
element `F(x) : A` (`TauCeti.AdditiveGroup.gaPointsMulEquiv`); the Frobenius endomorphism raises
that element to the `p`-th power (`AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd`), while an
included `αₚ`-point reads off a `p`-nilpotent element (`aᵖ = 0`), whose `p`-th power vanishes.
Conversely a `𝔾ₐ`-point read off as an element `a` with `aᵖ = 0` is a `p`-nilpotent element,
hence the image of the `αₚ`-point attached to it (`TauCeti.AlphaP.mem_range_pointsHom_iff`).

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap): the standing hypotheses flag `αₚ` as one of the
non-smooth / non-reduced groups an affine group scheme of finite type must admit, described there
as "the kernel of the Frobenius endomorphism", and Layer 3 develops "Hopf ideals ↔ closed
subgroup schemes" with their kernels.

## Main declarations

* `TauCeti.AdditiveGroup.frobeniusBialgHom`: the Frobenius bialgebra endomorphism `x ↦ xᵖ` of the
  coordinate Hopf algebra `R[x]` of `𝔾ₐ`, in prime characteristic `p`.
* `TauCeti.AdditiveGroup.frobeniusEnd`: the Frobenius endomorphism of `𝔾ₐ` on the functor of
  points, the contravariant image of `frobeniusBialgHom`.
* `TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd`: the Frobenius endomorphism acts as
  `a ↦ aᵖ` on points.
* `TauCeti.AlphaP.inclusion`: the inclusion `αₚ ↪ 𝔾ₐ` on points, the contravariant image of the
  quotient map `R[x] ↠ R[x]/(xᵖ)`.
* `TauCeti.AlphaP.frobeniusEnd_comp_inclusion`: the Frobenius endomorphism annihilates `αₚ`.
* `TauCeti.AlphaP.mem_range_inclusion_iff`: a `𝔾ₐ`-point lies in the image of `αₚ` iff the
  Frobenius endomorphism kills it.
* `TauCeti.AlphaP.range_inclusion`: as subgroups of the `𝔾ₐ`-points, the image of `αₚ ↪ 𝔾ₐ` is
  the kernel of the Frobenius endomorphism of `𝔾ₐ`.

## References

The Frobenius kernel `αₚ` and its `p`-nilpotent functor of points are Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic`; the additive-group points
dictionary `TauCeti.AdditiveGroup.gaPointsMulEquiv` and the coordinate-Hopf-algebra functoriality
`TauCeti.AlgHom.mapDomain` are Tau Ceti's. The freshman's dream `add_pow_char`, the
symmetric-algebra bialgebra structure, and the bialgebra-hom constructor `BialgHom.ofAlgHom` are
Mathlib's. This realizes `αₚ = ker(Frobenius)` on the functor of points, the additive companion
of `TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Kernel`.
-/

public section

open Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

universe u v

namespace AdditiveGroup

/-! ### The Frobenius endomorphism of `𝔾ₐ` -/

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The coordinate `R`-algebra endomorphism of `R[x] = SymmetricAlgebra R R` sending the generator
`x = ι R R 1` to `xᵖ`. It underlies the Frobenius endomorphism of the additive group `𝔾ₐ`. -/
@[expose] noncomputable def frobeniusAlgHom :
    SymmetricAlgebra R R →ₐ[R] SymmetricAlgebra R R :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton R (SymmetricAlgebra R R) ((ι R R 1) ^ p))

omit [Fact p.Prime] [CharP R p] in
@[simp]
theorem frobeniusAlgHom_ι (r : R) :
    frobeniusAlgHom R p (ι R R r) = r • (ι R R 1) ^ p := by
  rw [frobeniusAlgHom, SymmetricAlgebra.lift_ι_apply, LinearMap.toSpanSingleton_apply]

omit [Fact p.Prime] [CharP R p] in
theorem frobeniusAlgHom_ι_one :
    frobeniusAlgHom R p (ι R R 1) = (ι R R 1) ^ p := by
  rw [frobeniusAlgHom_ι, one_smul]

omit [Fact p.Prime] in
/-- The tensor-square ring of the additive-group Hopf algebra has characteristic `p`: the
structure map `R → R[x] ⊗ R[x]` is a section of the counit, hence injective. -/
private theorem charP_tensorSquare :
    CharP (SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R) p :=
  charP_of_injective_algebraMap
    (Function.LeftInverse.injective (g := Coalgebra.counit (R := R))
      fun r => Bialgebra.counit_algebraMap r) p

/-- **The Frobenius power `xᵖ` is primitive.** In characteristic `p` the comultiplication of `xᵖ`
is `xᵖ ⊗ 1 + 1 ⊗ xᵖ`, by the freshman's dream applied to the primitive generator `x`. -/
private theorem comul_ι_pow :
    Coalgebra.comul (R := R) ((ι R R 1 : SymmetricAlgebra R R) ^ p) =
      ((ι R R 1 : SymmetricAlgebra R R) ^ p) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ((ι R R 1 : SymmetricAlgebra R R) ^ p) := by
  haveI := charP_tensorSquare R p
  rw [Bialgebra.comul_pow, comul_ι, add_pow_char, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_pow, one_pow]

/-- **The Frobenius bialgebra endomorphism `x ↦ xᵖ` of the coordinate Hopf algebra of `𝔾ₐ`.** In
prime characteristic `p` the generator `x` is primitive, hence so is `xᵖ`
(`Δ(xᵖ) = xᵖ ⊗ 1 + 1 ⊗ xᵖ` by the freshman's dream), and the counit still vanishes on `xᵖ`, so
the algebra endomorphism `x ↦ xᵖ` is a bialgebra endomorphism. It induces the Frobenius
endomorphism of `𝔾ₐ` on the functor of points. -/
@[expose] noncomputable def frobeniusBialgHom :
    SymmetricAlgebra R R →ₐc[R] SymmetricAlgebra R R :=
  BialgHom.ofAlgHom (frobeniusAlgHom R p)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      change Coalgebra.counit (R := R) (frobeniusAlgHom R p (ι R R 1)) =
          Coalgebra.counit (R := R) (ι R R 1)
      rw [frobeniusAlgHom_ι_one, Bialgebra.counit_pow, counit_ι,
        zero_pow (Fact.out (p := p.Prime)).ne_zero])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext_ring
      change (Algebra.TensorProduct.map (frobeniusAlgHom R p) (frobeniusAlgHom R p))
            (Coalgebra.comul (R := R) (ι R R 1)) =
          Coalgebra.comul (R := R) (frobeniusAlgHom R p (ι R R 1))
      rw [frobeniusAlgHom_ι_one, comul_ι_pow, comul_ι, map_add,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, frobeniusAlgHom_ι_one]
      simp only [map_one])

@[simp]
theorem frobeniusBialgHom_ι (r : R) :
    frobeniusBialgHom R p (ι R R r) = r • (ι R R 1) ^ p :=
  frobeniusAlgHom_ι R p r

theorem frobeniusBialgHom_ι_one :
    frobeniusBialgHom R p (ι R R 1) = (ι R R 1) ^ p :=
  frobeniusAlgHom_ι_one R p

variable {A : Type v} [CommRing A] [Algebra R A]

/-- **The Frobenius endomorphism of `𝔾ₐ`, on the functor of points.** For every commutative
`R`-algebra `A` it is the homomorphism of the convolution group of points induced (contravariantly)
by the Frobenius bialgebra endomorphism `x ↦ xᵖ`; on points it raises a point to its `p`-th power,
`a ↦ aᵖ`. -/
@[expose] noncomputable def frobeniusEnd :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) →* WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
  AlgHom.mapDomain (frobeniusBialgHom R p)

/-- **The Frobenius endomorphism acts as `a ↦ aᵖ` on points.** Reading a `𝔾ₐ`-point off on the
generator `x = ι 1`, the Frobenius endomorphism raises the resulting element of `A` to its `p`-th
power. -/
theorem toAdd_gaPointsMulEquiv_frobeniusEnd (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv (frobeniusEnd R p F)) =
      Multiplicative.toAdd (gaPointsMulEquiv F) ^ p := by
  rw [toAdd_gaPointsMulEquiv, frobeniusEnd, AlgHom.mapDomain_apply, ofConv_toConv,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom, frobeniusBialgHom_ι_one, map_pow,
    toAdd_gaPointsMulEquiv]

end AdditiveGroup

/-! ### `αₚ` as the kernel of the Frobenius endomorphism -/

namespace AlphaP

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
variable {A : Type v} [CommRing A] [Algebra R A]

/-- **The inclusion `αₚ ↪ 𝔾ₐ` on the functor of points.** It is the homomorphism of convolution
groups of points induced (contravariantly) by the quotient bialgebra map `R[x] ↠ R[x]/(xᵖ)`, i.e.
pre-composition of a point of `αₚ` with the quotient map. It agrees with the underlying-element map
`TauCeti.AlphaP.pointsHom` through `TauCeti.AdditiveGroup.gaPointsMulEquiv`. -/
@[expose] noncomputable def inclusion :
    WithConv (CoordinateRing (R := R) p →ₐ[R] A) →*
      WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
  AlgHom.mapDomain (Bialgebra.Quotient.mkBialgHom (hopfIdeal (R := R) p).toIdeal)

/-- Reading an included `αₚ`-point off as an element of the additive group is the underlying-element
map `TauCeti.AlphaP.pointsHom`. -/
theorem gaPointsMulEquiv_inclusion (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :
    AdditiveGroup.gaPointsMulEquiv (inclusion p F) = pointsHom p F :=
  rfl

/-- **The Frobenius endomorphism annihilates `αₚ`.** Composing the Frobenius endomorphism of `𝔾ₐ`
after the inclusion `αₚ ↪ 𝔾ₐ` is the trivial homomorphism of group functors: every `αₚ`-point maps
to a `p`-nilpotent element, whose `p`-th power is `0`. -/
theorem frobeniusEnd_comp_inclusion :
    (AdditiveGroup.frobeniusEnd R p (A := A)).comp (inclusion p) = 1 := by
  refine MonoidHom.ext fun F => ?_
  rw [MonoidHom.comp_apply, MonoidHom.one_apply]
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  apply Multiplicative.toAdd.injective
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd, gaPointsMulEquiv_inclusion, map_one,
    toAdd_one]
  exact (mem_range_pointsHom_iff p _).mp ⟨F, rfl⟩

/-- The Frobenius endomorphism annihilates every `αₚ`-point, in element form. -/
@[simp]
theorem frobeniusEnd_inclusion (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :
    AdditiveGroup.frobeniusEnd R p (inclusion p F) = 1 := by
  have := DFunLike.congr_fun (frobeniusEnd_comp_inclusion (R := R) (A := A) p) F
  simpa using this

/-- **Membership in the image of `αₚ ↪ 𝔾ₐ`.** A `𝔾ₐ`-point lies in the image of the `αₚ` inclusion
exactly when the Frobenius endomorphism kills it: `g` comes from `αₚ` iff `gᵖ = 0` in the additive
group of points. -/
theorem mem_range_inclusion_iff {g : WithConv (SymmetricAlgebra R R →ₐ[R] A)} :
    g ∈ MonoidHom.range (inclusion (R := R) (A := A) p) ↔
      AdditiveGroup.frobeniusEnd R p g = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨F, rfl⟩
    exact frobeniusEnd_inclusion p F
  · intro hg
    have hval : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ^ p = 0 := by
      have hpow := AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd (R := R) (A := A) p g
      rw [hg, map_one, toAdd_one] at hpow
      exact hpow.symm
    obtain ⟨F, hF⟩ :=
      (mem_range_pointsHom_iff (R := R) p (AdditiveGroup.gaPointsMulEquiv g)).mpr hval
    refine ⟨F, ?_⟩
    apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
    rw [gaPointsMulEquiv_inclusion, hF]

/-- **`αₚ` is the kernel of the Frobenius endomorphism of `𝔾ₐ`.** As subgroups of the group of
`𝔾ₐ`-points, the image of the inclusion `αₚ ↪ 𝔾ₐ` equals the kernel of the Frobenius endomorphism:
a `𝔾ₐ`-point comes from `αₚ` exactly when its `p`-th power is trivial. This realizes
`αₚ = ker(𝔾ₐ --a ↦ aᵖ--> 𝔾ₐ)` on the functor of points. -/
theorem range_inclusion :
    MonoidHom.range (inclusion (R := R) (A := A) p) =
      MonoidHom.ker (AdditiveGroup.frobeniusEnd R p (A := A)) := by
  ext g
  rw [MonoidHom.mem_ker, mem_range_inclusion_iff]

end AlphaP

end TauCeti
