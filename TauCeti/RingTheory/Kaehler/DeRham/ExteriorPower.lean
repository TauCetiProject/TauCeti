/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.RingTheory.Derivation.ExteriorDerivative
public import TauCeti.RingTheory.Kaehler.DeRham.Basic

/-!
# Degreewise algebraic exterior derivative on Kähler exterior powers

Specializes `Derivation.exteriorPowerDeriv` to `KaehlerDifferential.D R A` on exterior powers
`⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]` (matching the restriction of
`TauCeti.KaehlerDeRham.extDeriv R A`), providing the degree-zero identification with
`KaehlerDifferential.D R A`, square-zero identities, scalar and graded Leibniz rules,
exact-differential formulas, and functoriality along `R`-algebra homomorphisms via
`KaehlerDifferential.mapSemilinear`.
-/

public section

namespace TauCeti.KaehlerDeRham

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- Identification of `TauCeti.KaehlerDeRham.extDeriv R A` with the generic
`Derivation.extDeriv` of `KaehlerDifferential.D R A`. -/
theorem extDeriv_eq_derivation_extDeriv :
    extDeriv R A = (KaehlerDifferential.D R A).extDeriv
      (KaehlerDifferential.D R A).derTwistedExt.liftKaehlerDifferential
      (KaehlerDifferential.span_range_derivation R A)
      (Derivation.liftKaehlerDifferential_comp_D _) :=
  Derivation.extDeriv_unique _ _ _ _ (extDeriv R A)
    (fun _ ↦ extDeriv_algebraMap _) (fun _ ↦ extDeriv_ι_D _) extDeriv_mul

/-- **The `q`-th algebraic exterior derivative** `⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]`,
specializing `Derivation.exteriorPowerDeriv` to `KaehlerDifferential.D R A`. -/
@[expose] noncomputable def exteriorPowerDeriv (q : ℕ) :
    ⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R] :=
  (KaehlerDifferential.D R A).exteriorPowerDeriv
    (KaehlerDifferential.D R A).derTwistedExt.liftKaehlerDifferential
    (KaehlerDifferential.span_range_derivation R A)
    (Derivation.liftKaehlerDifferential_comp_D _) q

variable {R A}

@[simp]
theorem coe_exteriorPowerDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (exteriorPowerDeriv R A q ω : ExteriorAlgebra A Ω[A⁄R]) = extDeriv R A ω.val := by
  rw [exteriorPowerDeriv, Derivation.coe_exteriorPowerDeriv_apply, extDeriv_eq_derivation_extDeriv]

/-- **Degree-zero identification (`simp` direction)**: under `zeroEquiv` and `oneEquiv`,
`TauCeti.KaehlerDeRham.exteriorPowerDeriv R A 0` identifies with `KaehlerDifferential.D R A`,
rewriting `(zeroEquiv A Ω[A⁄R]).symm a` to `(oneEquiv A Ω[A⁄R]).symm (KaehlerDifferential.D R A a)`.
See `oneEquiv_exteriorPowerDeriv_zero` for the unapplied equivalence direction extracting `D`. -/
@[simp]
theorem exteriorPowerDeriv_zero_zeroEquiv_symm (a : A) :
    exteriorPowerDeriv R A 0 ((exteriorPower.zeroEquiv A Ω[A⁄R]).symm a) =
      (exteriorPower.oneEquiv A Ω[A⁄R]).symm (KaehlerDifferential.D R A a) :=
  Derivation.exteriorPowerDeriv_zero_zeroEquiv_symm _ _ _ _ a

/-- **Degree-zero identification (forward-equivalence direction)**: under `zeroEquiv` and
`oneEquiv`, `TauCeti.KaehlerDeRham.exteriorPowerDeriv R A 0` recovers `KaehlerDifferential.D R A` as
`oneEquiv A Ω[A⁄R] (d ω) = KaehlerDifferential.D R A (zeroEquiv A Ω[A⁄R] ω)`. See
`exteriorPowerDeriv_zero_zeroEquiv_symm` for the `simp` direction. -/
theorem oneEquiv_exteriorPowerDeriv_zero (ω : ⋀[A]^0 Ω[A⁄R]) :
    exteriorPower.oneEquiv A Ω[A⁄R] (exteriorPowerDeriv R A 0 ω) =
      KaehlerDifferential.D R A (exteriorPower.zeroEquiv A Ω[A⁄R] ω) :=
  Derivation.oneEquiv_exteriorPowerDeriv_zero _ _ _ _ ω

/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` on Kähler `q`-forms, used for
`simp` rewriting. -/
@[simp]
theorem exteriorPowerDeriv_exteriorPowerDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPowerDeriv R A (q + 1) (exteriorPowerDeriv R A q ω) = 0 :=
  Derivation.exteriorPowerDeriv_exteriorPowerDeriv_apply _ _ _ _ q ω

/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on Kähler exterior
powers. -/
theorem exteriorPowerDeriv_comp_exteriorPowerDeriv (q : ℕ) :
    (exteriorPowerDeriv R A (q + 1)) ∘ₗ (exteriorPowerDeriv R A q) = 0 :=
  Derivation.exteriorPowerDeriv_comp_exteriorPowerDeriv _ _ _ _ q

/-- **Scalar Leibniz rule on Kähler `q`-forms**: `d (a • ω) = D a ∧ ω + a • d ω`. -/
theorem exteriorPowerDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPowerDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (KaehlerDifferential.D R A a) q ω +
        a • exteriorPowerDeriv R A q ω :=
  Derivation.exteriorPowerDeriv_smul _ _ _ _ q a ω

/-- Every wedge product `D b₀ ∧ ⋯ ∧ D b_{q-1}` of exact Kähler differentials is closed (`d = 0`). -/
@[simp]
theorem exteriorPowerDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    exteriorPowerDeriv R A q (exteriorPower.ιMulti A q (KaehlerDifferential.D R A ∘ b)) = 0 :=
  Derivation.exteriorPowerDeriv_ιMulti_comp_D _ _ _ _ b

/-- **Formula on scaled exact-differential wedges**: since `D b₀ ∧ ⋯ ∧ D b_{q-1}` is closed,
only its scalar coefficient `a` is differentiated:
`d (a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorPowerDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorPowerDeriv R A q
        (a • exteriorPower.ιMulti A q (KaehlerDifferential.D R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1)
        (Fin.cons (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A ∘ b)) :=
  Derivation.exteriorPowerDeriv_smul_ιMulti_comp_D _ _ _ _ a b

/-- **Graded Leibniz rule on `exteriorPower.wedge`** for Kähler forms. -/
theorem exteriorPowerDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p Ω[A⁄R]) (η : ⋀[A]^q Ω[A⁄R]) :
    exteriorPowerDeriv R A (p + q) (exteriorPower.wedge A Ω[A⁄R] p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· Ω[A⁄R]) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A Ω[A⁄R] (p + 1) q (exteriorPowerDeriv R A p ω) η) +
        (-1 : A) ^ p •
          exteriorPower.wedge A Ω[A⁄R] p (q + 1) ω (exteriorPowerDeriv R A q η) :=
  Derivation.exteriorPowerDeriv_wedge _ _ _ _ p q ω η

/-- An `R`-algebra homomorphism `f : A →ₐ[R] B` induces maps on Kähler `q`-forms via
`KaehlerDifferential.mapSemilinear f` that commute with
`TauCeti.KaehlerDeRham.exteriorPowerDeriv`. -/
theorem mapSemilinear_exteriorPowerDeriv {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1)
        (KaehlerDifferential.mapSemilinear f) (exteriorPowerDeriv R A q ω) =
      exteriorPowerDeriv R B q
        (exteriorPower.mapSemilinear q (KaehlerDifferential.mapSemilinear f) ω) :=
  Derivation.mapSemilinear_exteriorPowerDeriv _ _ _ _ _ _ _ _ f
    (KaehlerDifferential.mapSemilinear f) (KaehlerDifferential.mapSemilinear_D f) q ω

end TauCeti.KaehlerDeRham
