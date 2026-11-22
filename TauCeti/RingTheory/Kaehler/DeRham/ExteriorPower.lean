/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.RingTheory.Kaehler.DeRham.Basic

/-!
# Degreewise algebraic exterior derivative on Kähler exterior powers

Restricts the ambient algebraic exterior differential `TauCeti.KaehlerDeRham.extDeriv R A` to
exterior powers `⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]`, providing the degree-zero
identification with `KaehlerDifferential.D R A`, square-zero identities, scalar and graded Leibniz
rules, exact-differential formulas, and functoriality along `R`-algebra homomorphisms via
`TauCeti.KaehlerDeRham.map`.
-/

public section

namespace TauCeti.KaehlerDeRham

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- **The `q`-th algebraic exterior derivative** `⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R]`,
obtained by restricting `TauCeti.KaehlerDeRham.extDeriv R A` to the `q`-th exterior power. -/
noncomputable def exteriorDeriv (q : ℕ) : ⋀[A]^q Ω[A⁄R] →ₗ[R] ⋀[A]^(q + 1) Ω[A⁄R] where
  toFun ω := ⟨extDeriv R A ω.val, extDeriv_mem_exteriorPower ω.property⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (extDeriv R A) ω₁.val ω₂.val)
  map_smul' r ω := Subtype.ext ((extDeriv R A).map_smul r ω.val)

variable {R A}

@[simp]
theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (exteriorDeriv R A q ω : ExteriorAlgebra A Ω[A⁄R]) = extDeriv R A ω.val := (rfl)

/-- **Degree-zero identification (`simp` direction)**: under `zeroEquiv` and `oneEquiv`,
`TauCeti.KaehlerDeRham.exteriorDeriv R A 0` identifies with `KaehlerDifferential.D R A`,
rewriting `(zeroEquiv A Ω[A⁄R]).symm a` to `(oneEquiv A Ω[A⁄R]).symm (KaehlerDifferential.D R A a)`.
See `oneEquiv_exteriorDeriv_zero` for the unapplied equivalence direction extracting `D`. -/
@[simp]
theorem exteriorDeriv_zero_symm (a : A) :
    exteriorDeriv R A 0 ((exteriorPower.zeroEquiv A Ω[A⁄R]).symm a) =
      (exteriorPower.oneEquiv A Ω[A⁄R]).symm (KaehlerDifferential.D R A a) :=
  Subtype.ext <| by
    simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
      ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply]

/-- **Degree-zero identification (forward-equivalence direction)**: under `zeroEquiv` and
`oneEquiv`, `TauCeti.KaehlerDeRham.exteriorDeriv R A 0` recovers `KaehlerDifferential.D R A` as
`oneEquiv A Ω[A⁄R] (d ω) = KaehlerDifferential.D R A (zeroEquiv A Ω[A⁄R] ω)`. See
`exteriorDeriv_zero_symm` for the `simp` direction. -/
theorem oneEquiv_exteriorDeriv_zero (ω : ⋀[A]^0 Ω[A⁄R]) :
    exteriorPower.oneEquiv A Ω[A⁄R] (exteriorDeriv R A 0 ω) =
      KaehlerDifferential.D R A (exteriorPower.zeroEquiv A Ω[A⁄R] ω) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv A Ω[A⁄R]).symm_apply_apply ω, exteriorDeriv_zero_symm]
  exact LinearEquiv.apply_symm_apply _ _

/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` on Kähler `q`-forms, used for
`simp` rewriting. -/
@[simp]
theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A (q + 1) (exteriorDeriv R A q ω) = 0 :=
  Subtype.ext (extDeriv_extDeriv ω.val)

/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on Kähler exterior
powers. -/
theorem exteriorDeriv_comp_exteriorDeriv (q : ℕ) :
    (exteriorDeriv R A (q + 1)) ∘ₗ (exteriorDeriv R A q) = 0 :=
  LinearMap.ext (exteriorDeriv_exteriorDeriv_apply q)

/-- **Scalar Leibniz rule on Kähler `q`-forms**: `d (a • ω) = D a ∧ ω + a • d ω`. -/
theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (KaehlerDifferential.D R A a) q ω +
        a • exteriorDeriv R A q ω :=
  Subtype.ext <| by simp [extDeriv_smul a ω.val]

/-- Every wedge product `D b₀ ∧ ⋯ ∧ D b_{q-1}` of exact Kähler differentials is closed (`d = 0`). -/
@[simp]
theorem exteriorDeriv_ιMulti_comp_D {q : ℕ} (b : Fin q → A) :
    exteriorDeriv R A q (exteriorPower.ιMulti A q (KaehlerDifferential.D R A ∘ b)) = 0 := by
  apply Subtype.ext
  rw [coe_exteriorDeriv_apply, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero]
  induction q with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, Function.comp_apply, extDeriv_mul, extDeriv_ι_D,
      zero_mul, zero_add]
    exact (congrArg _ (ih (Matrix.vecTail b))).trans (mul_zero _)

/-- **Formula on scaled exact-differential wedges**: since `D b₀ ∧ ⋯ ∧ D b_{q-1}` is closed,
only its scalar coefficient `a` is differentiated:
`d (a • (D b₀ ∧ ⋯ ∧ D b_{q-1})) = D a ∧ D b₀ ∧ ⋯ ∧ D b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_D {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorDeriv R A q
        (a • exteriorPower.ιMulti A q (KaehlerDifferential.D R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1)
        (Fin.cons (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A ∘ b)) := by
  rw [exteriorDeriv_smul, exteriorDeriv_ιMulti_comp_D, smul_zero, add_zero,
    TauCeti.ExteriorAlgebra.wedgeLeft_ιMulti]

/-- **Graded Leibniz rule on `exteriorPower.wedge`** for Kähler forms. -/
theorem exteriorDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p Ω[A⁄R]) (η : ⋀[A]^q Ω[A⁄R]) :
    exteriorDeriv R A (p + q) (exteriorPower.wedge A Ω[A⁄R] p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· Ω[A⁄R]) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A Ω[A⁄R] (p + 1) q (exteriorDeriv R A p ω) η) +
        (-1 : A) ^ p •
          exteriorPower.wedge A Ω[A⁄R] p (q + 1) ω (exteriorDeriv R A q η) :=
  Subtype.ext <| by simpa using extDeriv_mul_of_mem_exteriorPower ω.property η.val

/-- On underlying rings, `TauCeti.KaehlerDeRham.map f` agrees with
`ExteriorAlgebra.mapSemilinear (KaehlerDifferential.mapSemilinear f)`. -/
theorem map_toRingHom_eq_mapSemilinear {B : Type*} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    ((map f : TauCeti.DGAlgHom (isDGAlgebra R A) (isDGAlgebra R B)).toAlgHom :
        ExteriorAlgebra A Ω[A⁄R] →+* ExteriorAlgebra B Ω[B⁄R]) =
      ExteriorAlgebra.mapSemilinear (KaehlerDifferential.mapSemilinear f) :=
  ExteriorAlgebra.ringHom_ext
    (fun a ↦ by
      change (map f : TauCeti.DGAlgHom _ _) (algebraMap A (ExteriorAlgebra A Ω[A⁄R]) a) = _
      rw [map_algebraMap, ExteriorAlgebra.mapSemilinear_algebraMap]; rfl)
    (fun ω ↦ by
      change (map f : TauCeti.DGAlgHom _ _) (ExteriorAlgebra.ι A ω) = _
      rw [map_ι, ExteriorAlgebra.mapSemilinear_ι])

/-- An `R`-algebra homomorphism `f : A →ₐ[R] B` induces maps on Kähler `q`-forms via
`KaehlerDifferential.mapSemilinear f` that commute with `TauCeti.KaehlerDeRham.exteriorDeriv`. -/
theorem mapSemilinear_exteriorDeriv {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.mapSemilinear (q + 1) (KaehlerDifferential.mapSemilinear f)
        (exteriorDeriv R A q ω) =
      exteriorDeriv R B q
        (exteriorPower.mapSemilinear q (KaehlerDifferential.mapSemilinear f) ω) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_mapSemilinear_apply, coe_exteriorDeriv_apply,
    ← map_toRingHom_eq_mapSemilinear f]
  exact ((map f).map_d ω.val).symm

end TauCeti.KaehlerDeRham
