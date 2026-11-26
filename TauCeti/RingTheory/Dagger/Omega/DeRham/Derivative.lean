/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham
public import TauCeti.RingTheory.Dagger.Omega.Forms

/-!
# Degreewise properties and functoriality of the overconvergent exterior derivative

Complements `TauCeti.RingTheory.Dagger.Omega.DeRham` with additional properties of
`TauCeti.Dagger.Omega.extDeriv` and `TauCeti.Dagger.Omega.extDerivPow` needed for the
overconvergent de Rham complex: anticommutation with the grade involution, degree-zero
identification with `Omega.d`, scalar and graded Leibniz rules on `⋀^q`, vanishing on exact
wedges, and naturality along `formsMap` for morphisms of `K`-dagger algebras.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §3.1.
-/

public section
noncomputable section

namespace TauCeti.Dagger.Omega

section ExteriorDerivLemmas

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
  [Module.Finite A (Omega R A)]

/-- `extDeriv R A` anticommutes with the grade involution on `ExteriorAlgebra A (Omega R A)`. -/
theorem extDeriv_involute (x : ExteriorAlgebra A (Omega R A)) :
    extDeriv R A (CliffordAlgebra.involute (Q := (0 : QuadraticForm A (Omega R A))) x) =
      -CliffordAlgebra.involute (Q := (0 : QuadraticForm A (Omega R A))) (extDeriv R A x) := by
  induction x using exteriorAlgebra_inductionOn with
  | algebraMap a => simp
  | ι_d a => simp
  | mul x y ihx ihy =>
    rw [map_mul, extDeriv_mul, ihx, ihy, extDeriv_mul, map_add, map_mul, map_mul,
      neg_mul, mul_neg, neg_add]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy, map_add, map_add, neg_add]

/-- **Degree-zero identification (`simp` direction)**: under `zeroEquiv` and `oneEquiv`,
`Omega.extDerivPow R A 0` identifies with `Omega.d R A`, rewriting
`(zeroEquiv A (Omega R A)).symm a` to `(oneEquiv A (Omega R A)).symm (d R A a)`. See
`oneEquiv_extDerivPow_zero` for the forward-equivalence direction extracting `Omega.d R A`. -/
@[simp] theorem extDerivPow_zero_zeroEquiv_symm (a : A) :
    extDerivPow R A 0 ((exteriorPower.zeroEquiv A (Omega R A)).symm a) =
      (exteriorPower.oneEquiv A (Omega R A)).symm (d R A a) :=
  Subtype.ext <| by
    simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
      ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply, extDeriv_smul]

/-- **Degree-zero identification (forward-equivalence direction)**: under `zeroEquiv` and
`oneEquiv`, `Omega.extDerivPow R A 0` recovers `Omega.d R A` as
`oneEquiv A (Omega R A) (d ω) = d R A (zeroEquiv A (Omega R A) ω)`. See
`extDerivPow_zero_zeroEquiv_symm` for the `simp` direction. -/
theorem oneEquiv_extDerivPow_zero (ω : ⋀[A]^0 (Omega R A)) :
    exteriorPower.oneEquiv A (Omega R A) (extDerivPow R A 0 ω) =
      d R A (exteriorPower.zeroEquiv A (Omega R A) ω) := by
  conv_lhs =>
    rw [← (exteriorPower.zeroEquiv A (Omega R A)).symm_apply_apply ω,
      extDerivPow_zero_zeroEquiv_symm]
  exact LinearEquiv.apply_symm_apply _ _

/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` for an overconvergent `q`-form
`ω`, used for `simp` rewriting. -/
@[simp] theorem extDerivPow_extDerivPow_apply (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    extDerivPow R A (q + 1) (extDerivPow R A q ω) = 0 :=
  Subtype.ext <| by simp

/-- **Scalar Leibniz rule on overconvergent `q`-forms**: `d (a • ω) = d a ∧ ω + a • d ω`. -/
theorem extDerivPow_smul (q : ℕ) (a : A) (ω : ⋀[A]^q (Omega R A)) :
    extDerivPow R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (d R A a) q ω + a • extDerivPow R A q ω :=
  Subtype.ext <| by simp

/-- Every wedge product `d b₀ ∧ ⋯ ∧ d b_{q-1}` of exact differentials is closed (`d = 0`). -/
@[simp] theorem extDerivPow_ιMulti_comp_d {q : ℕ} (b : Fin q → A) :
    extDerivPow R A q (exteriorPower.ιMulti A q (d R A ∘ b)) = 0 :=
  Subtype.ext <| by
    rw [coe_extDerivPow_apply, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero]
    exact extDeriv_ιMulti_d b

/-- **Graded Leibniz rule for `exteriorPower.wedge`** of a `p`-form and a `q`-form, with sign
`(-1) ^ p` determined by the left factor's degree. -/
theorem extDerivPow_wedge (p q : ℕ) (ω : ⋀[A]^p (Omega R A)) (η : ⋀[A]^q (Omega R A)) :
    extDerivPow R A (p + q) (exteriorPower.wedge A (Omega R A) p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· (Omega R A)) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A (Omega R A) (p + 1) q (extDerivPow R A p ω) η) +
        (-1 : A) ^ p •
          exteriorPower.wedge A (Omega R A) p (q + 1) ω (extDerivPow R A q η) :=
  Subtype.ext <| by
    simpa using extDeriv_mul_of_mem_exteriorPower ω.property (η : ExteriorAlgebra A (Omega R A))

end ExteriorDerivLemmas

section Functoriality

variable {K A B : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [IsDaggerAlgebra K A] [IsDaggerAlgebra K B] [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Naturality of `extDeriv` along a homomorphism of dagger algebras.** -/
theorem mapSemilinear_extDeriv (f : A →ₐ[K] B) (x : ExteriorAlgebra A (Omega K A)) :
    ExteriorAlgebra.mapSemilinear (mapSemilinear f) (extDeriv K A x) =
      extDeriv K B (ExteriorAlgebra.mapSemilinear (mapSemilinear f) x) := by
  induction x using exteriorAlgebra_inductionOn with
  | algebraMap a =>
    rw [extDeriv_algebraMap, ExteriorAlgebra.mapSemilinear_ι, mapSemilinear_d,
      ExteriorAlgebra.mapSemilinear_algebraMap, extDeriv_algebraMap]
    rfl
  | ι_d a =>
    rw [extDeriv_ι_d, map_zero, ExteriorAlgebra.mapSemilinear_ι, mapSemilinear_d, extDeriv_ι_d]
  | mul x y ihx ihy =>
    rw [extDeriv_mul, map_add, map_mul, map_mul, ihx, ihy, ExteriorAlgebra.mapSemilinear_involute,
      map_mul, extDeriv_mul]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy, map_add, map_add]

/-- **Naturality of `extDerivPow` along a homomorphism of dagger algebras.** -/
theorem mapSemilinear_extDerivPow (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    exteriorPower.mapSemilinear (q + 1) (mapSemilinear f) (extDerivPow K A q ω) =
      extDerivPow K B q (exteriorPower.mapSemilinear q (mapSemilinear f) ω) :=
  Subtype.ext <| by
    simpa only [exteriorPower.coe_mapSemilinear_apply, coe_extDerivPow_apply] using
      mapSemilinear_extDeriv f ω.val

/-- Naturality of `extDerivPow` with respect to `formsMap`. -/
theorem extDerivPow_formsMap (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    extDerivPow K B q (formsMap f q ω) =
      formsMap f (q + 1) (extDerivPow K A q ω) := by
  simpa only [formsMap_apply] using (mapSemilinear_extDerivPow f q ω).symm

/-- Naturality of `extDerivPow` with respect to `formsMap` as a linear-map identity. -/
theorem extDerivPow_comp_formsMap (f : A →ₐ[K] B) (q : ℕ) :
    (extDerivPow K B q) ∘ₗ (formsMap f q) =
      (formsMap f (q + 1)) ∘ₗ (extDerivPow K A q) :=
  LinearMap.ext (extDerivPow_formsMap f q)

end Functoriality

end TauCeti.Dagger.Omega
