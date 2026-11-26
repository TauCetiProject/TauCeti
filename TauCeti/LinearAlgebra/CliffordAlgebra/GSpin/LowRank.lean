/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.Torus
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer.Zero
public import Mathlib.RingTheory.RootsOfUnity.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.One
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two

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
  Clifford algebra is `K e f × K f e`.

These are the Checks `GSpin₀ = GSpin₁ = 𝔾_m`, `GSpin₂ = 𝔾_m × 𝔾_m` and `Spin₀ = Spin₁ = μ₂` of
ReductiveGroups §9B.7, on points.

## Main declarations

* `CliffordAlgebra.specialCliffordGroupEquivUnitsOfSubsingleton`: `GSpin(Q) ≃* Rˣ` in rank `0`.
* `CliffordAlgebra.map_normOneSpinGroup_unitsEquivOfSubsingleton`: `Spin(Q)` is `μ₂(R)` in rank
  `0`.
* `CliffordAlgebra.specialCliffordGroupEquivUnitsOfFinrankEqOne`: `GSpin(Q) ≃* Kˣ` in rank `1`.
* `CliffordAlgebra.normOneSpinGroup_eq_map_rootsOfUnity_of_finrank_eq_one`: `Spin(Q)` is `μ₂(K)`
  in rank `1`.
* `CliffordAlgebra.hyperbolicPlaneTorus`, `CliffordAlgebra.hyperbolicPlaneTorus_bijective`,
  `CliffordAlgebra.hyperbolicPlaneSpecialCliffordGroupEquiv`: `Kˣ × Kˣ ≃* GSpin(Q)` for a
  hyperbolic plane.
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
  refine ⟨fun a b h => Units.ext (algebraMap_injective_of_free Q ?_), fun x => ?_⟩
  · simpa using congrArg (fun x : specialCliffordGroup Q => ((x : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) h
  · refine ⟨unitsEquivOfSubsingleton Q x, Subtype.ext (Units.ext ?_)⟩
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

/-- **`Spin₀ = μ₂`**: in rank `0`, `Spin(Q)` is identified with the units of `R` whose square is
`1`. Mathlib's `spinGroup` is trivial in this rank. -/
theorem map_normOneSpinGroup_unitsEquivOfSubsingleton :
    (normOneSpinGroup Q).map (unitsEquivOfSubsingleton Q).toMonoidHom = rootsOfUnity 2 R := by
  ext c
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_rootsOfUnity]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := (mem_normOneSpinGroup_iff.mp hx).2
    rw [reverse_eq_self_of_subsingleton] at h
    apply (unitsEquivOfSubsingleton Q).symm.injective
    refine Units.ext ?_
    simp only [map_pow, MulEquiv.symm_apply_apply, map_one, Units.val_pow_eq_pow_val,
      Units.val_one]
    rw [pow_two, h]
  · intro hc
    refine ⟨(unitsEquivOfSubsingleton Q).symm c, ?_, by simp⟩
    have hmem := units_map_algebraMap_mem_normOneSpinGroup (Q := Q) (c := c)
      (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])
    convert hmem using 1
    refine Units.ext ?_
    rw [coe_unitsEquivOfSubsingleton_symm_apply, equivOfSubsingleton_symm_apply]
    rfl

end Zero

/-! ### Rank one -/

section One

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- In rank `1` the central scalars map bijectively onto the general spin group. -/
theorem scalarSpecialCliffordGroup_bijective_of_finrank_eq_one (hV : Module.finrank K V = 1) :
    Function.Bijective (scalarSpecialCliffordGroup Q) := by
  refine ⟨fun a b h => Units.ext (algebraMap_injective_of_free Q ?_), fun x => ?_⟩
  · simpa using congrArg (fun x : specialCliffordGroup Q => ((x : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) h
  · obtain ⟨a, ha⟩ := exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one Q hV x
      (mem_specialCliffordGroup_iff.mp x.property).2
    exact ⟨a, Subtype.ext (Units.ext (by rw [coe_scalarSpecialCliffordGroup, ha]; rfl))⟩

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

/-- **`Spin₁ = μ₂`**: in rank `1`, over a field, `Spin(Q)` consists of the scalars whose square
is `1`. -/
theorem normOneSpinGroup_eq_map_rootsOfUnity_of_finrank_eq_one (hV : Module.finrank K V = 1) :
    normOneSpinGroup Q =
      (rootsOfUnity 2 K).map (Units.map (algebraMap K (CliffordAlgebra Q) : K →* _)) := by
  ext x
  simp only [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one Q hV x
      (mem_specialCliffordGroup_iff.mp (mem_normOneSpinGroup_iff.mp hx).1).2
    refine ⟨a, Units.ext ?_, ha.symm⟩
    rw [ha] at hx
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (units_map_algebraMap_mem_normOneSpinGroup_iff (algebraMap_injective_of_free Q) a).mp hx
  · rintro ⟨a, ha, rfl⟩
    exact units_map_algebraMap_mem_normOneSpinGroup
      (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])

end One

/-! ### Rank two: the hyperbolic plane -/

section Two

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {e f : V}

/-- For a hyperbolic pair, `e f` is nonzero in the Clifford algebra of a vector space. -/
private theorem ι_mul_ι_ne_zero (he : Q e = 0) (hef : polar Q e f = 1) :
    ι Q e * ι Q f ≠ 0 := by
  intro h
  have hfe : ι Q e * ι Q f + ι Q f * ι Q e = 1 := ι_mul_ι_add_swap_of_polar_eq_one hef
  have h1 : ι Q e = ι Q e * (ι Q e * ι Q f + ι Q f * ι Q e) := by rw [hfe, mul_one]
  rw [mul_add, ← mul_assoc, ι_sq_scalar, he, map_zero, zero_mul, zero_add, ← mul_assoc, h,
    zero_mul] at h1
  have he0 : e = 0 := ι_injective_of_free Q (by rw [h1, map_zero])
  rw [he0, polar_zero_left] at hef
  exact zero_ne_one hef

/-- A hyperbolic pair spans a plane. -/
private theorem exists_eq_smul_add_smul (hV : Module.finrank K V = 2) (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) (w : V) : ∃ a b : K, a • e + b • f = w := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hli : LinearIndependent K ![e, f] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h1 := congrArg (fun v => polar Q v f) hst
    have h2 := congrArg (fun v => polar Q v e) hst
    simp only [polar_add_left, polar_smul_left, polar_self, he, hf, hef, hfe, smul_zero,
      polar_zero_left, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [hV, Fintype.card_fin])
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.pair_comm] at htop
  exact Submodule.mem_span_pair.mp (htop ▸ Submodule.mem_top)

/-- For a hyperbolic pair spanning a plane, every even Clifford element is `b e f + a f e`. -/
private theorem exists_eq_smul_add_smul_of_mem_even (hV : Module.finrank K V = 2) (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) {x : CliffordAlgebra Q} (hx : x ∈ even Q) :
    ∃ a b : K, x = b • (ι Q e * ι Q f) + a • (ι Q f * ι Q e) := by
  have hee : ι Q e * ι Q e = 0 := by rw [ι_sq_scalar, he, map_zero]
  have hff : ι Q f * ι Q f = 0 := by rw [ι_sq_scalar, hf, map_zero]
  obtain ⟨hEE, hFF, hEF, hFE⟩ := hyperbolic_relations he hef
  induction x, hx using even_induction with
  | algebraMap r =>
    refine ⟨r, r, ?_⟩
    rw [← smul_add, ι_mul_ι_add_swap_of_polar_eq_one hef, Algebra.algebraMap_eq_smul_one]
  | add x y _ _ ihx ihy =>
    obtain ⟨a, b, rfl⟩ := ihx
    obtain ⟨a', b', rfl⟩ := ihy
    exact ⟨a + a', b + b', by rw [add_smul, add_smul]; abel⟩
  | ι_mul_ι_mul m₁ m₂ y _ ih =>
    obtain ⟨a, b, rfl⟩ := ih
    obtain ⟨a₁, b₁, rfl⟩ := exists_eq_smul_add_smul hV he hf hef m₁
    obtain ⟨a₂, b₂, rfl⟩ := exists_eq_smul_add_smul hV he hf hef m₂
    have hm : ι Q (a₁ • e + b₁ • f) * ι Q (a₂ • e + b₂ • f) =
        (a₁ * b₂) • (ι Q e * ι Q f) + (b₁ * a₂) • (ι Q f * ι Q e) := by
      simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hee, hff,
        smul_zero, zero_add, add_zero, smul_smul]
      rw [add_comm, mul_comm a₂ b₁, mul_comm b₂ a₁]
    refine ⟨b₁ * a₂ * a, a₁ * b₂ * b, ?_⟩
    rw [hm]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hEE, hFF, hEF, hFE, smul_zero,
      add_zero, zero_add, smul_smul]
    rw [mul_comm b (a₁ * b₂), mul_comm a (b₁ * a₂)]

/-- For a hyperbolic pair, `f e` is nonzero in the Clifford algebra of a vector space. -/
private theorem ι_mul_ι_swap_ne_zero (hf : Q f = 0) (hef : polar Q e f = 1) :
    ι Q f * ι Q e ≠ 0 :=
  ι_mul_ι_ne_zero hf (by rw [polar_comm, hef])

variable (Q) in
/-- **The torus of a hyperbolic plane** `(c, t) ↦ c u(t)`, `u(t) = t e f + f e`, as a
homomorphism `Kˣ × Kˣ →* GSpin(Q)`. -/
noncomputable def hyperbolicPlaneTorus (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Kˣ × Kˣ →* specialCliffordGroup Q :=
  MonoidHom.noncommCoprod (scalarSpecialCliffordGroup Q)
    ((hyperbolicPairUnitsHom he hef).codRestrict _
      (hyperbolicPairUnitsHom_mem_specialCliffordGroup he hf hef))
    fun c t => by
      change _ * _ = _ * _
      refine Subtype.ext (Units.ext ?_)
      simp only [Subgroup.coe_mul, Units.val_mul, coe_scalarSpecialCliffordGroup,
        MonoidHom.codRestrict_apply]
      exact Algebra.commutes _ _

/-- The torus of a hyperbolic plane sends `(c, t)` to `c (t e f + f e)`. -/
theorem coe_hyperbolicPlaneTorus (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    (x : Kˣ × Kˣ) :
    (((hyperbolicPlaneTorus Q he hf hef x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      algebraMap K _ x.1 * hyperbolicPairScaling Q e f x.2 := by
  rw [hyperbolicPlaneTorus, MonoidHom.noncommCoprod_apply, Subgroup.coe_mul, Units.val_mul,
    coe_scalarSpecialCliffordGroup, MonoidHom.codRestrict_apply, coe_hyperbolicPairUnitsHom]

/-- The torus element `c (t e f + f e)` in the coordinates `e f`, `f e`. -/
theorem coe_hyperbolicPlaneTorus_eq_smul_add_smul (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (x : Kˣ × Kˣ) :
    (((hyperbolicPlaneTorus Q he hf hef x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      ((x.1 : K) * x.2) • (ι Q e * ι Q f) + (x.1 : K) • (ι Q f * ι Q e) := by
  rw [coe_hyperbolicPlaneTorus, hyperbolicPairScaling_def, ← Algebra.smul_def, smul_add,
    smul_smul]

/-- The torus of a hyperbolic pair in a vector space is injective, in every characteristic. -/
theorem hyperbolicPlaneTorus_injective (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Injective (hyperbolicPlaneTorus Q he hf hef) := by
  intro x y hxy
  obtain ⟨hEE, hFF, hEF, hFE⟩ := hyperbolic_relations he hef
  have h := congrArg (fun g : specialCliffordGroup Q =>
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) hxy
  simp only [coe_hyperbolicPlaneTorus_eq_smul_add_smul] at h
  have h1 := congrArg (· * (ι Q f * ι Q e)) h
  have h2 := congrArg (· * (ι Q e * ι Q f)) h
  simp only [add_mul, smul_mul_assoc, hEE, hFF, hEF, hFE, smul_zero, zero_add, add_zero]
    at h1 h2
  have hc : (x.1 : K) = y.1 := by
    rw [← sub_eq_zero]
    exact (smul_eq_zero.mp (by rw [sub_smul, h1, sub_self])).resolve_right
      (ι_mul_ι_swap_ne_zero hf hef)
  have hct : (x.1 : K) * x.2 = y.1 * y.2 := by
    rw [← sub_eq_zero]
    exact (smul_eq_zero.mp (by rw [sub_smul, h2, sub_self])).resolve_right
      (ι_mul_ι_ne_zero he hef)
  rw [hc] at hct
  exact Prod.ext (Units.ext hc) (Units.ext (mul_left_cancel₀ y.1.ne_zero hct))

/-- For a hyperbolic pair spanning a plane over a field, in every characteristic, every element
of the general spin group is a torus element `c (t e f + f e)`. -/
theorem hyperbolicPlaneTorus_surjective (hV : Module.finrank K V = 2) (he : Q e = 0)
    (hf : Q f = 0) (hef : polar Q e f = 1) :
    Function.Surjective (hyperbolicPlaneTorus Q he hf hef) := by
  intro g
  obtain ⟨-, -, hEF, hFE⟩ := hyperbolic_relations he hef
  obtain ⟨a, b, hab⟩ := exists_eq_smul_add_smul_of_mem_even hV he hf hef
    (mem_specialCliffordGroup_iff.mp g.property).2
  set x : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hx
  have hyx : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * x = 1 :=
    Units.inv_mul _
  have ha : a ≠ 0 := by
    rintro rfl
    apply ι_mul_ι_swap_ne_zero hf hef
    have : x * (ι Q f * ι Q e) = 0 := by
      rw [hab, zero_smul, add_zero, smul_mul_assoc, hEF, smul_zero]
    rw [← one_mul (ι Q f * ι Q e), ← hyx, mul_assoc, this, mul_zero]
  have hb : b ≠ 0 := by
    rintro rfl
    apply ι_mul_ι_ne_zero he hef
    have : x * (ι Q e * ι Q f) = 0 := by
      rw [hab, zero_smul, zero_add, smul_mul_assoc, hFE, smul_zero]
    rw [← one_mul (ι Q e * ι Q f), ← hyx, mul_assoc, this, mul_zero]
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
