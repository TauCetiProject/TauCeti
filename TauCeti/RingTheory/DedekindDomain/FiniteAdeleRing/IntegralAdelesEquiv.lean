/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# The integral finite adeles are the product of the local integer rings

For a Dedekind domain `R` with fraction field `K`, the integral finite adeles
`IsDedekindDomain.FiniteAdeleRing.integralAdeles R K` are the finite adeles integral at every
finite place. This file records that, as a ring, they are the full product `∏_v 𝒪_v` of the
local integer rings (`IsDedekindDomain.FiniteAdeleRing.integralAdelesEquivPi`): an integral finite
adele is the family of its components, and every family of local integers is an integral finite
adele, through `IsDedekindDomain.FiniteAdeleRing.integralEmbedding`. This lets a statement about
`Ô = ∏_v 𝒪_v`, for instance about matrices over `Ô`, be proved place by place.
-/

public section

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (R K) in
/-- The integral finite adeles are the product of the local integer rings `𝒪_v`: an integral
finite adele corresponds to the family of its components. -/
noncomputable def integralAdelesEquivPi :
    integralAdeles R K ≃+* ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K where
  toFun a v := ⟨(a : FiniteAdeleRing R K) v, mem_integralAdeles.1 a.property v⟩
  invFun x := ⟨integralEmbedding x, mem_integralAdeles.2 fun v ↦ by
    rw [integralEmbedding_apply]
    exact (x v).property⟩
  left_inv a := Subtype.ext <| by
    ext v : 1
    exact integralEmbedding_apply (R := R) (K := K) _ v
  right_inv x := funext fun v ↦ Subtype.ext (integralEmbedding_apply x v)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The component at `v` of the family of an integral finite adele is its component at `v`. -/
@[simp]
theorem coe_integralAdelesEquivPi_apply (a : integralAdeles R K) (v : HeightOneSpectrum R) :
    (integralAdelesEquivPi R K a v : v.adicCompletion K) = (a : FiniteAdeleRing R K) v :=
  (rfl)

/-- The integral finite adele of a family of local integers is its image under the integral
embedding. -/
@[simp]
theorem coe_integralAdelesEquivPi_symm_apply
    (x : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) :
    ((integralAdelesEquivPi R K).symm x : FiniteAdeleRing R K) = integralEmbedding x :=
  (rfl)

end IsDedekindDomain.FiniteAdeleRing
