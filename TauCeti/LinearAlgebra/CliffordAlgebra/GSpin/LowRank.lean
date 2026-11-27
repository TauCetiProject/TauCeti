/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.Scalar
public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.Torus
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer.Zero
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.One
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two
import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic

/-!
# The general spin group in ranks zero, one and two

This file computes the points of the general spin group `GSpin(Q)`
(`CliffordAlgebra.specialCliffordGroup`) and of `Spin(Q) = ker ν`
(`CliffordAlgebra.normOneSpinGroup`) in low rank, in every characteristic:

* in rank `0`, over any commutative ring `R`, `GSpin(Q)` is the group of central scalars `Rˣ`, and
  `Spin(Q)` is `μ₂(R)`, the units whose square is `1`; Mathlib's `spinGroup` is trivial in this
  rank;
* in rank `1`, over a field `K`, `GSpin(Q)` is again the group of central scalars `Kˣ` and
  `Spin(Q)` is `μ₂(K)`;
* in rank `2`, over a field `K`, for a hyperbolic pair `(e, f)` spanning the space, the torus
  `(c, t) ↦ c u(t)`, `u(t) = t e f + f e`, is an isomorphism `Kˣ × Kˣ ≃* GSpin(Q)`: the even
  Clifford algebra is spanned by `e f` and `f e`.

## Main declarations

* `CliffordAlgebra.specialCliffordGroupEquivUnitsOfSubsingleton`: `GSpin(Q) ≃* Rˣ` in rank `0`.
* `CliffordAlgebra.normOneSpinGroup_eq_map_rootsOfUnity_of_subsingleton`: `Spin(Q)` is `μ₂(R)` in
  rank `0`.
* `CliffordAlgebra.specialCliffordGroupEquivUnitsOfFinrankEqOne`: `GSpin(Q) ≃* Kˣ` in rank `1`.
* `CliffordAlgebra.normOneSpinGroup_eq_map_rootsOfUnity_of_finrank_eq_one`: `Spin(Q)` is `μ₂(K)`
  in rank `1`.
* `CliffordAlgebra.hyperbolicPlaneTorus`, `CliffordAlgebra.hyperbolicPlaneTorus_bijective`,
  `CliffordAlgebra.hyperbolicPlaneSpecialCliffordGroupEquiv`: `Kˣ × Kˣ ≃* GSpin(Q)` for a
  hyperbolic plane.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.4, for the Clifford and spin groups of a
  quadratic space over a ring.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

/-! ### Rank zero -/

section Zero

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
  [Subsingleton M]

/-- In rank `0` every Clifford unit lies in the general spin group. -/
@[simp]
theorem specialCliffordGroup_eq_top_of_subsingleton : specialCliffordGroup Q = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_specialCliffordGroup_iff, vectorNormalizer_eq_top_of_subsingleton,
    even_eq_top_of_subsingleton]
  exact ⟨Subgroup.mem_top x, Algebra.mem_top⟩

/-- In rank `0` the central scalars map bijectively onto the general spin group. -/
theorem scalarSpecialCliffordGroup_bijective_of_subsingleton :
    Function.Bijective (scalarSpecialCliffordGroup Q) := by
  refine ⟨scalarSpecialCliffordGroup_injective (algebraMap_injective_of_free Q), fun x => ?_⟩
  refine ⟨unitsEquivOfSubsingleton Q x, Subtype.ext (Units.ext ?_)⟩
  rw [coe_scalarSpecialCliffordGroup, coe_unitsEquivOfSubsingleton_apply,
    ← equivOfSubsingleton_symm_apply, AlgEquiv.symm_apply_apply]

/-- **`GSpin₀ = 𝔾_m`**: in rank `0` the general spin group is the group of central scalars. -/
noncomputable def specialCliffordGroupEquivUnitsOfSubsingleton :
    specialCliffordGroup Q ≃* Rˣ :=
  (MulEquiv.ofBijective _ (scalarSpecialCliffordGroup_bijective_of_subsingleton Q)).symm

/-- The rank-zero equivalence `Rˣ ≃* GSpin(Q)` is the central scalar map. -/
@[simp]
theorem specialCliffordGroupEquivUnitsOfSubsingleton_symm_apply (c : Rˣ) :
    (specialCliffordGroupEquivUnitsOfSubsingleton Q).symm c = scalarSpecialCliffordGroup Q c :=
  (rfl)

/-- The rank-zero equivalence `GSpin(Q) ≃* Rˣ` sends `g` to the scalar `g`. -/
@[simp]
theorem algebraMap_specialCliffordGroupEquivUnitsOfSubsingleton (g : specialCliffordGroup Q) :
    algebraMap R (CliffordAlgebra Q) (specialCliffordGroupEquivUnitsOfSubsingleton Q g : R) =
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  conv_rhs => rw [← (specialCliffordGroupEquivUnitsOfSubsingleton Q).symm_apply_apply g]
  rw [specialCliffordGroupEquivUnitsOfSubsingleton_symm_apply, coe_scalarSpecialCliffordGroup]

/-- **`Spin₀ = μ₂`**: in rank `0`, `Spin(Q)` consists of the scalars whose square is `1`.
Mathlib's `spinGroup` is trivial in this rank. -/
theorem normOneSpinGroup_eq_map_rootsOfUnity_of_subsingleton :
    normOneSpinGroup Q =
      (rootsOfUnity 2 R).map (Units.map (algebraMap R (CliffordAlgebra Q) : R →* _)) :=
  normOneSpinGroup_eq_map_rootsOfUnity (algebraMap_injective_of_free Q)
    (scalarSpecialCliffordGroup_bijective_of_subsingleton Q).2

end Zero

/-! ### Rank one -/

section One

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- In rank `1` the central scalars map bijectively onto the general spin group. -/
theorem scalarSpecialCliffordGroup_bijective_of_finrank_eq_one (hV : Module.finrank K V = 1) :
    Function.Bijective (scalarSpecialCliffordGroup Q) := by
  refine ⟨scalarSpecialCliffordGroup_injective (algebraMap_injective_of_free Q), fun x => ?_⟩
  obtain ⟨a, ha⟩ := exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one Q hV x
    (mem_specialCliffordGroup_iff.mp x.property).2
  refine ⟨a, Subtype.ext (Units.ext ?_)⟩
  rw [coe_scalarSpecialCliffordGroup, ha, Units.coe_map, MonoidHom.coe_ofClass]

/-- **`GSpin₁ = 𝔾_m`**: in rank `1`, over a field, the general spin group is the group of central
scalars. -/
noncomputable def specialCliffordGroupEquivUnitsOfFinrankEqOne (hV : Module.finrank K V = 1) :
    specialCliffordGroup Q ≃* Kˣ :=
  (MulEquiv.ofBijective _ (scalarSpecialCliffordGroup_bijective_of_finrank_eq_one Q hV)).symm

/-- The rank-one equivalence `Kˣ ≃* GSpin(Q)` is the central scalar map. -/
@[simp]
theorem specialCliffordGroupEquivUnitsOfFinrankEqOne_symm_apply (hV : Module.finrank K V = 1)
    (c : Kˣ) :
    (specialCliffordGroupEquivUnitsOfFinrankEqOne Q hV).symm c = scalarSpecialCliffordGroup Q c :=
  (rfl)

/-- The rank-one equivalence `GSpin(Q) ≃* Kˣ` sends `g` to the scalar `g`. -/
@[simp]
theorem algebraMap_specialCliffordGroupEquivUnitsOfFinrankEqOne (hV : Module.finrank K V = 1)
    (g : specialCliffordGroup Q) :
    algebraMap K (CliffordAlgebra Q) (specialCliffordGroupEquivUnitsOfFinrankEqOne Q hV g : K) =
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  conv_rhs => rw [← (specialCliffordGroupEquivUnitsOfFinrankEqOne Q hV).symm_apply_apply g]
  rw [specialCliffordGroupEquivUnitsOfFinrankEqOne_symm_apply, coe_scalarSpecialCliffordGroup]

/-- **`Spin₁ = μ₂`**: in rank `1`, over a field, `Spin(Q)` consists of the scalars whose square
is `1`. -/
theorem normOneSpinGroup_eq_map_rootsOfUnity_of_finrank_eq_one (hV : Module.finrank K V = 1) :
    normOneSpinGroup Q =
      (rootsOfUnity 2 K).map (Units.map (algebraMap K (CliffordAlgebra Q) : K →* _)) :=
  normOneSpinGroup_eq_map_rootsOfUnity (algebraMap_injective_of_free Q)
    (scalarSpecialCliffordGroup_bijective_of_finrank_eq_one Q hV).2

end One

/-! ### Rank two: the hyperbolic plane -/

section HyperbolicPlaneTorus

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
  {e f : M}

variable (Q) in
/-- **The torus of a hyperbolic plane** `(c, t) ↦ c u(t)`, `u(t) = t e f + f e`, as a
homomorphism `Rˣ × Rˣ →* GSpin(Q)`. -/
noncomputable def hyperbolicPlaneTorus (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Rˣ × Rˣ →* specialCliffordGroup Q :=
  MonoidHom.noncommCoprod (scalarSpecialCliffordGroup Q)
    ((hyperbolicPairUnitsHom he hef).codRestrict _
      (hyperbolicPairUnitsHom_mem_specialCliffordGroup he hf hef))
    fun c t => by
      refine (commute_iff_eq _ _).mpr (Subtype.ext (Units.ext ?_))
      simp only [Subgroup.coe_mul, Units.val_mul, coe_scalarSpecialCliffordGroup,
        MonoidHom.codRestrict_apply]
      exact Algebra.commutes _ _

/-- The torus of a hyperbolic plane sends `(c, t)` to `c (t e f + f e)`. -/
@[simp]
theorem coe_hyperbolicPlaneTorus (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    (x : Rˣ × Rˣ) :
    (((hyperbolicPlaneTorus Q he hf hef x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      algebraMap R _ x.1 * hyperbolicPairScaling Q e f x.2 := by
  rw [hyperbolicPlaneTorus, MonoidHom.noncommCoprod_apply, Subgroup.coe_mul, Units.val_mul,
    coe_scalarSpecialCliffordGroup, MonoidHom.codRestrict_apply, coe_hyperbolicPairUnitsHom]

/-- The torus element `c (t e f + f e)` in the coordinates `e f`, `f e`. -/
theorem coe_hyperbolicPlaneTorus_eq_smul_add_smul (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (x : Rˣ × Rˣ) :
    (((hyperbolicPlaneTorus Q he hf hef x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      ((x.1 : R) * x.2) • (ι Q e * ι Q f) + (x.1 : R) • (ι Q f * ι Q e) := by
  rw [coe_hyperbolicPlaneTorus, hyperbolicPairScaling_def, ← Algebra.smul_def, smul_add,
    smul_smul]

end HyperbolicPlaneTorus

section Two

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {e f : V}

/-- The torus of a hyperbolic pair in a vector space is injective, in every characteristic. -/
theorem hyperbolicPlaneTorus_injective (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Injective (hyperbolicPlaneTorus Q he hf hef) := by
  intro x y hxy
  have : Nontrivial (CliffordAlgebra Q) := (algebraMap_injective_of_free Q).nontrivial
  have h := congrArg (fun g : specialCliffordGroup Q =>
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) hxy
  simp only [coe_hyperbolicPlaneTorus_eq_smul_add_smul] at h
  have h1 := congrArg (· * (ι Q f * ι Q e)) h
  have h2 := congrArg (· * (ι Q e * ι Q f)) h
  simp only [smul_add_smul_mul_ι_mul_ι_swap_of_polar_eq_one he hef] at h1
  simp only [smul_add_smul_mul_ι_mul_ι_of_polar_eq_one he hef] at h2
  have hc : (x.1 : K) = y.1 :=
    smul_left_injective K (ι_mul_ι_swap_ne_zero_of_polar_eq_one hf hef) h1
  have hct : (x.1 : K) * x.2 = y.1 * y.2 :=
    smul_left_injective K (ι_mul_ι_ne_zero_of_polar_eq_one he hef) h2
  rw [hc] at hct
  exact Prod.ext (Units.ext hc) (Units.ext (mul_left_cancel₀ y.1.ne_zero hct))

/-- For a hyperbolic pair spanning a plane over a field, in every characteristic, every element
of the general spin group is a torus element `c (t e f + f e)`. -/
theorem hyperbolicPlaneTorus_surjective (hV : Module.finrank K V = 2) (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Surjective (hyperbolicPlaneTorus Q he hf hef) := by
  intro g
  have : Nontrivial (CliffordAlgebra Q) := (algebraMap_injective_of_free Q).nontrivial
  obtain ⟨a, b, hab⟩ := exists_eq_smul_add_smul_of_mem_even_of_polar_eq_one
    (QuadraticForm.span_pair_eq_top_of_polar_eq_one hV he hf hef) he hf hef
    (mem_specialCliffordGroup_iff.mp g.property).2
  set x : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hx
  have ha : a ≠ 0 := by
    rintro rfl
    apply ι_mul_ι_swap_ne_zero_of_polar_eq_one hf hef
    refine (Units.mul_right_eq_zero (g : (CliffordAlgebra Q)ˣ)).mp ?_
    rw [← hx, hab, smul_add_smul_mul_ι_mul_ι_swap_of_polar_eq_one he hef, zero_smul]
  have hb : b ≠ 0 := by
    rintro rfl
    apply ι_mul_ι_ne_zero_of_polar_eq_one he hef
    refine (Units.mul_right_eq_zero (g : (CliffordAlgebra Q)ˣ)).mp ?_
    rw [← hx, hab, smul_add_smul_mul_ι_mul_ι_of_polar_eq_one he hef, zero_smul]
  refine ⟨(Units.mk0 a ha, Units.mk0 b hb / Units.mk0 a ha), Subtype.ext (Units.ext ?_)⟩
  rw [coe_hyperbolicPlaneTorus_eq_smul_add_smul, ← hx, hab]
  simp only [Units.val_mk0, Units.val_div_eq_div_val]
  rw [mul_div_cancel₀ _ ha]

/-- **`GSpin₂ = 𝔾_m × 𝔾_m`**: for a hyperbolic pair spanning a plane over a field, in every
characteristic, the torus `(c, t) ↦ c (t e f + f e)` is a bijection onto the general spin group. -/
theorem hyperbolicPlaneTorus_bijective (hV : Module.finrank K V = 2) (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Bijective (hyperbolicPlaneTorus Q he hf hef) :=
  ⟨hyperbolicPlaneTorus_injective he hf hef, hyperbolicPlaneTorus_surjective hV he hf hef⟩

/-- **`GSpin₂ = 𝔾_m × 𝔾_m`** for a hyperbolic plane over a field, in every characteristic: the
torus `(c, t) ↦ c (t e f + f e)` is an isomorphism `Kˣ × Kˣ ≃* GSpin(Q)`. -/
noncomputable def hyperbolicPlaneSpecialCliffordGroupEquiv (hV : Module.finrank K V = 2)
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Kˣ × Kˣ ≃* specialCliffordGroup Q :=
  MulEquiv.ofBijective _ (hyperbolicPlaneTorus_bijective hV he hf hef)

/-- The isomorphism `Kˣ × Kˣ ≃* GSpin(Q)` of a hyperbolic plane is its torus. -/
@[simp]
theorem hyperbolicPlaneSpecialCliffordGroupEquiv_apply (hV : Module.finrank K V = 2)
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (x : Kˣ × Kˣ) :
    hyperbolicPlaneSpecialCliffordGroupEquiv hV he hf hef x = hyperbolicPlaneTorus Q he hf hef x :=
  (rfl)

end Two

end CliffordAlgebra
