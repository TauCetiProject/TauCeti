/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# Principal parts of finite adeles

Let `R` be a Dedekind domain with fraction field `K`. At a height one prime `v` of `R`, the
*principal part* of an element `x` of the completion `K_v` is its class in `K_v / 𝒪_v`, where
`𝒪_v` is the ring of local integers. A finite adele `a = (a_v)_v` is integral at all but finitely
many places, so all but finitely many of its principal parts vanish, and reading them off gives
an `R`-linear map

`principalParts : 𝔸ᶠ → ⨁_v K_v / 𝒪_v`

to the direct sum of the local quotients. Its kernel is the subalgebra `∏_v 𝒪_v` of integral
finite adeles, and it is surjective, since a finite family of principal parts is realized by a
sum of finite adeles supported at single places. This is the restricted-product condition read
modulo the integral finite adeles:

`𝔸ᶠ / ∏_v 𝒪_v ≃ ⨁_v K_v / 𝒪_v`.

Composed with the isomorphism `K / R ≃ 𝔸ᶠ / ∏_v 𝒪_v` given by strong approximation
(`IsDedekindDomain.FiniteAdeleRing.quotientEquivQuotientIntegralAdeles`), it gives the
decomposition of `K / R` into its local components

`K / R ≃ ⨁_v K_v / 𝒪_v`,

which sends the class of `x ∈ K` to the family of its principal parts at the finite places. For
`R = ℤ` this is the decomposition `ℚ / ℤ ≃ ⨁_p ℚ_p / ℤ_p`, and for `R = k[t]` it is the partial
fraction decomposition of a rational function modulo polynomials.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersSubmodule`: the local integers `𝒪_v`
  as an `R`-submodule of the completion `K_v`.
* `IsDedekindDomain.FiniteAdeleRing.principalParts`: the `R`-linear map
  `𝔸ᶠ → ⨁_v K_v / 𝒪_v` taking a finite adele to its principal parts.
* `IsDedekindDomain.FiniteAdeleRing.quotientIntegralAdelesEquivDirectSum`: the isomorphism
  `𝔸ᶠ / ∏_v 𝒪_v ≃ ⨁_v K_v / 𝒪_v`.
* `IsDedekindDomain.FiniteAdeleRing.quotientEquivDirectSum`: the isomorphism
  `K / R ≃ ⨁_v K_v / 𝒪_v`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.ker_principalParts`: the kernel of `principalParts` is the
  subalgebra of integral finite adeles.
* `IsDedekindDomain.FiniteAdeleRing.principalParts_single`: a finite adele supported at `v` has a
  single principal part, at `v`.
* `IsDedekindDomain.FiniteAdeleRing.principalParts_surjective`: every finitely supported family of
  principal parts comes from a finite adele.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5.
-/

public section

namespace IsDedekindDomain

open HeightOneSpectrum
open scoped DirectSum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace HeightOneSpectrum

/-- The local integers `𝒪_v` as an `R`-submodule of the completion `K_v` at a finite place `v`.
The quotient `K_v ⧸ 𝒪_v` is the module of principal parts at `v`. -/
noncomputable def adicCompletionIntegersSubmodule (v : HeightOneSpectrum R) :
    Submodule R (v.adicCompletion K) where
  carrier := v.adicCompletionIntegers K
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (coe_mem_adicCompletionIntegers v r) hx

/-- Membership in `adicCompletionIntegersSubmodule` is membership in the local integers. -/
@[simp]
theorem mem_adicCompletionIntegersSubmodule {v : HeightOneSpectrum R} {x : v.adicCompletion K} :
    x ∈ v.adicCompletionIntegersSubmodule K ↔ x ∈ v.adicCompletionIntegers K :=
  Iff.rfl

end HeightOneSpectrum

namespace FiniteAdeleRing

variable (R) in
/-- The **principal parts** of a finite adele `a`: the family of classes of its components `a v`
in `K_v ⧸ 𝒪_v`. All but finitely many of them vanish, because `a` is integral at all but finitely
many places, so this is an `R`-linear map to the direct sum of the local quotients. -/
noncomputable def principalParts :
    FiniteAdeleRing R K →ₗ[R]
      ⨁ v : HeightOneSpectrum R, v.adicCompletion K ⧸ v.adicCompletionIntegersSubmodule K where
  toFun a :=
    { toFun v := Submodule.Quotient.mk (a v)
      -- the principal part vanishes outside the finitely many non-integral places of `a`
      support' := Trunc.mk ⟨(finite_valued_one_lt a).toFinset.val, fun v ↦ by
        rw [or_iff_not_imp_left, Finset.mem_val, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
          not_lt]
        exact fun hv ↦ (Submodule.Quotient.mk_eq_zero _).mpr hv⟩ }
  map_add' a b := DirectSum.ext fun v ↦ by
    rw [DirectSum.add_apply]
    exact Submodule.Quotient.mk_add _
  map_smul' r a := DirectSum.ext fun v ↦ by
    rw [DirectSum.smul_apply, RingHom.id_apply]
    refine (congrArg Submodule.Quotient.mk ?_).trans (Submodule.Quotient.mk_smul _ r (a v))
    -- `R` acts on the finite adeles through `K`, hence place by place
    rw [Algebra.smul_def, Algebra.smul_def, mul_apply, IsScalarTower.algebraMap_apply R K,
      algebraMap_apply]
    rfl

/-- The principal part of a finite adele at `v` is the class of its `v`-component. -/
@[simp]
theorem principalParts_apply (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    principalParts R K a v = Submodule.Quotient.mk (a v) :=
  (rfl)

/-- A finite adele has no principal parts exactly when it is integral at every finite place. -/
@[simp]
theorem principalParts_eq_zero_iff {a : FiniteAdeleRing R K} :
    principalParts R K a = 0 ↔ a ∈ integralAdeles R K := by
  simp [DirectSum.ext_iff]

variable (R) in
/-- The kernel of `principalParts` is the subalgebra of integral finite adeles. -/
theorem ker_principalParts :
    LinearMap.ker (principalParts R K) = Subalgebra.toSubmodule (integralAdeles R K) := by
  ext a
  simp

/-- The finite adele supported at `v` with `v`-component `x` has a single principal part: the
class of `x` at `v`. -/
@[simp]
theorem principalParts_single [DecidableEq (HeightOneSpectrum R)] (v : HeightOneSpectrum R)
    (x : v.adicCompletion K) :
    principalParts R K (single K v x) = DirectSum.of _ v (Submodule.Quotient.mk x) := by
  ext w
  rcases eq_or_ne w v with rfl | hw
  · simp
  · simp [single_apply_of_ne hw, DirectSum.of_eq_of_ne _ _ _ hw]

variable (R) in
/-- Every finitely supported family of principal parts is the family of principal parts of a
finite adele, namely of a sum of finite adeles supported at single places. -/
theorem principalParts_surjective : Function.Surjective (principalParts R K) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro d -
  induction d using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of v x =>
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨single K v x, principalParts_single K v x⟩
  | add d e hd he => exact add_mem hd he

variable (R) in
/-- **The finite adeles modulo the integral finite adeles are the direct sum of the local
quotients**: `principalParts` induces an isomorphism of `R`-modules
`𝔸ᶠ / ∏_v 𝒪_v ≃ ⨁_v K_v / 𝒪_v`. -/
noncomputable def quotientIntegralAdelesEquivDirectSum :
    (FiniteAdeleRing R K ⧸ Subalgebra.toSubmodule (integralAdeles R K)) ≃ₗ[R]
      ⨁ v : HeightOneSpectrum R, v.adicCompletion K ⧸ v.adicCompletionIntegersSubmodule K :=
  (Submodule.quotEquivOfEq _ _ (ker_principalParts R K).symm).trans
    -- `quotKerEquivOfSurjective` asks for an additive group structure on the target, whereas the
    -- type of `principalParts` carries the additive monoid structure of the direct sum. Naming
    -- the target and elaborating without the expected type (`(e :)`) lets the two be unified
    -- once both are known; propagating the expected type first unfolds the quotients instead.
    (LinearMap.quotKerEquivOfSurjective
      (M₂ := ⨁ v : HeightOneSpectrum R, v.adicCompletion K ⧸ v.adicCompletionIntegersSubmodule K)
      (principalParts R K) (principalParts_surjective R K) :)

/-- The isomorphism `𝔸ᶠ / ∏_v 𝒪_v ≃ ⨁_v K_v / 𝒪_v` sends the class of a finite adele to its
principal parts. -/
@[simp]
theorem quotientIntegralAdelesEquivDirectSum_mk (a : FiniteAdeleRing R K) :
    quotientIntegralAdelesEquivDirectSum R K (Submodule.Quotient.mk a) = principalParts R K a := by
  simp only [quotientIntegralAdelesEquivDirectSum, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ a

variable (R) in
/-- **The decomposition of `K / R` into local components.** The class of `x ∈ K` modulo `R` is
determined by its principal parts at the finite places, and every finitely supported family of
local principal parts occurs: `K / R ≃ ⨁_v K_v / 𝒪_v` as `R`-modules. -/
noncomputable def quotientEquivDirectSum :
    (K ⧸ (1 : Submodule R K)) ≃ₗ[R]
      ⨁ v : HeightOneSpectrum R, v.adicCompletion K ⧸ v.adicCompletionIntegersSubmodule K :=
  (quotientEquivQuotientIntegralAdeles R K).trans (quotientIntegralAdelesEquivDirectSum R K)

/-- The isomorphism `K / R ≃ ⨁_v K_v / 𝒪_v` sends the class of `x` to the principal parts of its
diagonal image, so its component at `v` is the class of `x` in `K_v ⧸ 𝒪_v`. -/
@[simp]
theorem quotientEquivDirectSum_mk (x : K) :
    quotientEquivDirectSum R K (Submodule.Quotient.mk x) =
      principalParts R K (algebraMap K (FiniteAdeleRing R K) x) := by
  simp [quotientEquivDirectSum]

end FiniteAdeleRing

end IsDedekindDomain
