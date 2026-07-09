/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroupFunctoriality
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity

/-!
# The inclusion `μ_n ↪ 𝔾ₘ` on points

The finite group scheme of `n`th roots of unity `μ_n = D(ℤ/n)` is a closed subgroup of the
multiplicative group `𝔾ₘ = D(ℤ)`. On the diagonalizable side the inclusion is
**contravariant** to the quotient homomorphism `ℤ ↠ ℤ/n`: writing that quotient
multiplicatively as `φ : Multiplicative ℤ →* Multiplicative (ZMod n)`, the diagonalizable
functor sends it to a homomorphism of group functors `D(φ) : D(ℤ/n) → D(ℤ)`, i.e.
`μ_n → 𝔾ₘ`, given on points by precomposition with the surjection `R[Multiplicative ℤ] ↠
R[Multiplicative (ZMod n)]` of coordinate Hopf algebras.

This file records that this points homomorphism is, under the two worked-example
identifications, exactly the inclusion of `n`th roots of unity into the unit group: reading
the image `μ_n(A) → 𝔾ₘ(A)` on the group-algebra generator `Multiplicative.ofAdd 1` of `𝔾ₘ`
returns the underlying unit of the root of unity. The same statement holds against the
canonical Laurent-polynomial `𝔾ₘ` of `TauCeti.MultiplicativeGroup`, and the inclusion is
injective (a monomorphism of functors) and natural in the value algebra.

## Main definitions

* `TauCeti.RootsOfUnityGroup.toMultZMod`: the quotient homomorphism `ℤ ↠ ℤ/n` written
  multiplicatively, `Multiplicative ℤ →* Multiplicative (ZMod n)`.
* `TauCeti.RootsOfUnityGroup.inclusion`: the inclusion `μ_n ↪ 𝔾ₘ` on points, the contravariant
  image of `toMultZMod n` under the diagonalizable functor.

## Main results

* `TauCeti.RootsOfUnityGroup.charOfPoint_inclusion`: reading the character of an included point
  is the `μ_n` character precomposed with the quotient `ℤ ↠ ℤ/n`.
* `TauCeti.RootsOfUnityGroup.charOfPoint_inclusion_ofAdd_one`: reading the included point on the
  `𝔾ₘ` generator `Multiplicative.ofAdd 1` returns the underlying unit of the root of unity.
* `TauCeti.RootsOfUnityGroup.multiplicativeGroup_pointEquiv_inclusion`: the same identification
  against the canonical Laurent-polynomial `𝔾ₘ` of `TauCeti.MultiplicativeGroup`.
* `TauCeti.RootsOfUnityGroup.inclusion_injective`: the inclusion is injective on points, so
  `μ_n → 𝔾ₘ` is a monomorphism of group functors.
* `TauCeti.RootsOfUnityGroup.mapValue_inclusion`: the inclusion is natural in the value algebra.

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 4: "`μ_n = D(ℤ/n)`", "`𝔾_m = D(ℤ)`",
and the diagonalizable anti-equivalence `M ↦ D(M)`), assembling the `μ_n` and `𝔾ₘ` worked
examples through the diagonalizable-group functoriality `DiagonalizableGroup.pointsMap`.

## References

The contravariant functoriality of the diagonalizable group is Tau Ceti's
`TauCeti.DiagonalizableGroup.pointsMap`; the `μ_n` and `𝔾ₘ` points calculations are
`TauCeti.RootsOfUnityGroup.pointsMulEquiv` and `TauCeti.MultiplicativeGroup.pointEquiv`. The
multiplicative quotient `ℤ ↠ ℤ/n` uses Mathlib's `AddMonoidHom.toMultiplicative` and
`Int.castAddHom`.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v w

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The quotient homomorphism `ℤ ↠ ℤ/n`, written multiplicatively as a homomorphism
`Multiplicative ℤ →* Multiplicative (ZMod n)`. Its diagonalizable image is the inclusion
`μ_n ↪ 𝔾ₘ`. -/
noncomputable def toMultZMod (n : ℕ) : Multiplicative ℤ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))

/-- The multiplicative quotient sends `ofAdd k` to `ofAdd (k : ℤ/n)`. -/
@[simp]
theorem toMultZMod_ofAdd (n : ℕ) (k : ℤ) :
    toMultZMod n (Multiplicative.ofAdd k) = Multiplicative.ofAdd (k : ZMod n) := by
  simp [toMultZMod]

/-- The multiplicative quotient sends the `𝔾ₘ` generator `Multiplicative.ofAdd 1` to the
`μ_n` generator `Multiplicative.ofAdd 1`. -/
@[simp]
theorem toMultZMod_ofAdd_one (n : ℕ) :
    toMultZMod n (Multiplicative.ofAdd 1) = generator n := by
  rw [toMultZMod_ofAdd, Int.cast_one]

/-- **The inclusion `μ_n ↪ 𝔾ₘ` on points.** It is the contravariant image of the quotient
`ℤ ↠ ℤ/n` under the diagonalizable functor: precomposition with the surjection
`R[Multiplicative ℤ] ↠ R[Multiplicative (ZMod n)]` of coordinate Hopf algebras carries a
point of `μ_n = D(ℤ/n)` to a point of `𝔾ₘ = D(ℤ)`. -/
@[expose] noncomputable def inclusion (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) →*
      WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :=
  DiagonalizableGroup.pointsMap (toMultZMod n)

/-- The inclusion acts by precomposition with the diagonalizable image of the quotient. -/
theorem inclusion_apply (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    inclusion n f = DiagonalizableGroup.pointsMap (toMultZMod n) f :=
  rfl

/-- **Reading the character of an included point.** The character of `inclusion n f`, a point of
`𝔾ₘ`, is the `μ_n` character of `f` precomposed with the quotient `ℤ ↠ ℤ/n`. -/
theorem charOfPoint_inclusion (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint (inclusion n f).ofConv =
      (DiagonalizableGroup.charOfPoint f.ofConv).comp (toMultZMod n) := by
  have h := DiagonalizableGroup.pointsMulEquiv_pointsMap (A := A) (toMultZMod n) f
  rwa [DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.pointsMulEquiv_apply,
    ← inclusion_apply] at h

/-- **The inclusion is the inclusion of roots of unity.** Reading the included point on the
`𝔾ₘ` group-algebra generator `Multiplicative.ofAdd 1` returns the underlying unit of the root
of unity `RootsOfUnityGroup.pointsMulEquiv n f`. -/
theorem charOfPoint_inclusion_ofAdd_one (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint (inclusion n f).ofConv (Multiplicative.ofAdd 1) =
      (RootsOfUnityGroup.pointsMulEquiv n f : Aˣ) := by
  apply Units.ext
  rw [charOfPoint_inclusion, MonoidHom.comp_apply, toMultZMod_ofAdd_one,
    DiagonalizableGroup.charOfPoint_apply_coe, pointsMulEquiv_apply]

/-- The same identification against the canonical Laurent-polynomial `𝔾ₘ` of
`TauCeti.MultiplicativeGroup`: pushing the included point along
`AddMonoidAlgebra.toMultiplicativeAlgEquiv` and reading it with `MultiplicativeGroup.pointEquiv`
returns the underlying unit of the root of unity. -/
theorem multiplicativeGroup_pointEquiv_inclusion (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    MultiplicativeGroup.pointEquiv
        ((inclusion n f).ofConv.comp
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv R ℤ).toAlgHom) =
      (RootsOfUnityGroup.pointsMulEquiv n f : Aˣ) := by
  rw [← DiagonalizableGroup.multiplicativeGroup_pointEquiv_apply,
    charOfPoint_inclusion_ofAdd_one]

/-- The multiplicative quotient `ℤ ↠ ℤ/n` is surjective. -/
theorem toMultZMod_surjective (n : ℕ) : Function.Surjective (toMultZMod n) := by
  intro y
  refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd y).cast, ?_⟩
  rw [toMultZMod_ofAdd, ZMod.intCast_zmod_cast, ofAdd_toAdd]

/-- **The inclusion is a monomorphism of functors.** The quotient `ℤ ↠ ℤ/n` is surjective, so
precomposing characters with it is injective; since a point is determined by its character, the
induced points homomorphism `μ_n(A) → 𝔾ₘ(A)` is injective. -/
theorem inclusion_injective (n : ℕ) :
    Function.Injective (inclusion (R := R) (A := A) n) := by
  intro f g hfg
  apply (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).injective
  rw [DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.pointsMulEquiv_apply]
  -- Precomposition with the surjection `toMultZMod n` is injective on characters.
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := toMultZMod_surjective n y
  have hchar : (DiagonalizableGroup.charOfPoint f.ofConv).comp (toMultZMod n) =
      (DiagonalizableGroup.charOfPoint g.ofConv).comp (toMultZMod n) := by
    rw [← charOfPoint_inclusion, ← charOfPoint_inclusion, hfg]
  exact DFunLike.congr_fun hchar x

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- **Naturality in the value algebra.** The inclusion `μ_n → 𝔾ₘ` commutes with the
value-algebra functoriality `AlgHom.mapValue`. -/
theorem mapValue_inclusion (n : ℕ) (φ : A →ₐ[R] B) :
    (inclusion (R := R) (A := B) n).comp
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ) =
      (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative ℤ)) φ).comp
        (inclusion (R := R) (A := A) n) :=
  DiagonalizableGroup.mapValue_pointsMap (toMultZMod n) φ

end RootsOfUnityGroup

end TauCeti
