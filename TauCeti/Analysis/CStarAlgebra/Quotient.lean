/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Subalgebra
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Quotient C⋆-algebras and closed range of `⋆`-homomorphisms

If `I` is a closed two-sided ideal of a (possibly nonunital) complex C⋆-algebra `A`, then the
quotient `A ⧸ I` equipped with the quotient norm `‖mk I a‖ = inf_{y ∈ I} ‖a + y‖` is a C⋆-algebra,
unital whenever `A` is unital. As an immediate consequence, every `⋆`-algebra homomorphism
`φ : A →⋆ₙₐ[ℂ] B` between C⋆-algebras factors through an isometric `⋆`-isomorphism
`A ⧸ ker φ ≃⋆ₐ[ℂ] φ.range` onto its range, so `φ.range` is automatically closed and every
dense-range `⋆`-homomorphism between C⋆-algebras is surjective.

To prove the C⋆-identity `‖x‖ ^ 2 ≤ ‖star x * x‖` on `A ⧸ I`, let `x = mk I a` and `z ∈ I`. Along
the increasing approximate unit `e` of `I.toNonUnitalStarSubalgebra`, ideal absorption gives
`mk I a = mk I (a - a * e)`, while in the unitization `A⁺¹` with `u = 1 - e` (`0 ≤ u ≤ 1`),
`star (a * u) * (a * u) = u * (star a * a + z) * u - u * (z - z * e)`,
giving `‖mk I a‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z * e - z‖ → ‖star a * a + z‖` and taking the infimum
over `z ∈ I` (see Gerard J. Murphy, *C*-Algebras and Operator Theory*, Theorem 3.1.4, or Kenneth R.
Davidson, *C*-Algebras by Example*, Theorem I.5.4 and Corollary I.5.5).

## Main declarations

* `TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`: C⋆-norm
  and C⋆-algebra instances on `A ⧸ I` for a closed two-sided ideal `I : TwoSidedIdeal A`.
* `TwoSidedIdeal.Quotient.mkStarAlgHom`, `TwoSidedIdeal.Quotient.liftStarAlgHom`,
  `TwoSidedIdeal.Quotient.factorStarAlgHom`, and `TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq`:
  universal `⋆`-homomorphisms and `⋆`-equivalences on C⋆-quotients, plus unital counterparts.
* `NonUnitalStarAlgHom.isClosed_range` and `StarAlgHom.isClosed_range`: the range of any
  `⋆`-algebra homomorphism between C⋆-algebras is closed.
* `NonUnitalStarAlgHom.quotientKerEquivRange`, `NonUnitalStarAlgHom.quotientKerEquivOfSurjective`,
  and `NonUnitalStarAlgHom.surjective_of_denseRange` (plus `StarAlgHom` counterparts): isometric
  first `⋆`-isomorphism theorem and surjectivity from dense range.
-/

public section

open Filter Topology Unitization
open scoped CStarAlgebra

namespace TwoSidedIdeal.Quotient

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

instance instStar : Star (A ⧸ I) where
  star := Quotient.map' star fun _ _ hab => by
    rw [quotientRel_def] at hab ⊢
    rw [← star_sub]
    exact I.star_mem_of_isClosed hab

@[simp]
theorem mk_star (a : A) : mk I (star a) = star (mk I a) := by
  rw [← quotientAddGroupMk_eq_mk, ← quotientAddGroupMk_eq_mk]
  rfl

instance instStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    rw [← mk_star, ← mk_star, star_star]
  star_mul x y := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    obtain ⟨b, rfl⟩ := mk_surjective I y
    rw [← map_mul, ← mk_star, star_mul, map_mul, mk_star, mk_star]
  star_add x y := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    obtain ⟨b, rfl⟩ := mk_surjective I y
    rw [← map_add, ← mk_star, star_add, map_add, mk_star, mk_star]

instance instModuleComplex : Module ℂ (A ⧸ I) :=
  inferInstanceAs <| Module ℂ (A ⧸ I.toSubmodule)

@[simp]
theorem submoduleQuotientMk_toSubmodule_eq_mk (a : A) :
    (Submodule.Quotient.mk (p := I.toSubmodule) a : A ⧸ I) = mk I a :=
  (Submodule.Quotient.quotientAddGroupMk_eq_mk a).symm.trans (quotientAddGroupMk_eq_mk I a)

@[simp]
theorem mk_smul_complex (c : ℂ) (a : A) : mk I (c • a) = c • mk I a := by
  rw [← submoduleQuotientMk_toSubmodule_eq_mk, ← submoduleQuotientMk_toSubmodule_eq_mk]
  exact Submodule.Quotient.mk_smul I.toSubmodule c a

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (A ⧸ I) :=
  Submodule.Quotient.normedSpace I.toSubmodule ℂ

instance instIsScalarTowerComplex : IsScalarTower ℂ (A ⧸ I) (A ⧸ I) where
  smul_assoc c x y := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    obtain ⟨b, rfl⟩ := mk_surjective I y
    simp only [smul_eq_mul]
    rw [← mk_smul_complex, ← map_mul, smul_mul_assoc, mk_smul_complex, map_mul]

instance instSMulCommClassComplex : SMulCommClass ℂ (A ⧸ I) (A ⧸ I) where
  smul_comm c x y := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    obtain ⟨b, rfl⟩ := mk_surjective I y
    simp only [smul_eq_mul]
    rw [← map_mul, ← mk_smul_complex, ← mul_smul_comm, map_mul, mk_smul_complex]

instance instStarModuleComplex : StarModule ℂ (A ⧸ I) where
  star_smul c x := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    rw [← mk_smul_complex, ← mk_star, star_smul, mk_smul_complex, mk_star]

instance instCStarRing : CStarRing (A ⧸ I) where
  norm_mul_self_le x := by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    rw [← mk_star, ← map_mul, ← sq, norm_mk_eq I (star a * a)]
    refine le_csInf ⟨‖star a * a + 0‖, 0, I.zero_mem, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    let _ : PartialOrder A := CStarAlgebra.spectralOrder A
    have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    -- Step 1: Use an increasing approximate unit `l` of `I` so that `z * e → z` in norm.
    let S := I.toNonUnitalStarSubalgebra
    let l : Filter S := CStarAlgebra.approximateUnit S
    have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit S
    have := hl.neBot
    let z' : S := ⟨z, I.mem_toNonUnitalStarSubalgebra.mpr hz⟩
    have hz_lim : Tendsto (fun e : S => ‖star a * a + z‖ + ‖(z' * e - z' : S)‖) l
        (𝓝 ‖star a * a + z‖) := by
      simpa only [add_zero] using tendsto_const_nhds.add
        (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_left z'))
    refine ge_of_tendsto hz_lim ?_
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
    -- Step 2: Bound `‖mk I a‖² ≤ ‖a - a * e‖²` and pass to `A⁺¹` with `u = 1 - e`.
    have heI : (e : A) ∈ I := I.mem_toNonUnitalStarSubalgebra.mp e.2
    have hmk_eq : mk I a = mk I (a - a * (e : A)) := by
      rw [map_sub, eq_zero_iff_mem.mpr (I.mul_mem_left a (e : A) heI), sub_zero]
    have hmk_sq : ‖mk I a‖ ^ 2 ≤ ‖a - a * (e : A)‖ ^ 2 := by
      rw [hmk_eq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_mk_le I _) 2
    have heA₀ : 0 ≤ (e : A) := he₀
    have heA₁ : ‖(e : A)‖ ≤ 1 := he₁
    have he_icc : ((e : A) : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
      CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨heA₀, heA₁⟩
    have h1_icc : 1 - ((e : A) : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
      Set.sub_mem_Icc_zero_iff_right.mpr he_icc
    obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
    have h1_star : star (1 - ((e : A) : A⁺¹)) = 1 - ((e : A) : A⁺¹) :=
      (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
    let u : A⁺¹ := 1 - ((e : A) : A⁺¹)
    let b : A⁺¹ := (a : A⁺¹) * u
    have hb_norm : ‖a - a * (e : A)‖ = ‖b‖ := by
      rw [← Unitization.norm_inr (𝕜 := ℂ), Unitization.inr_sub, Unitization.inr_mul]
      congr 1
      dsimp only [b, u]
      rw [mul_sub, mul_one]
    -- Step 3: Apply the C⋆-identity to `b = a * u` and use `‖u‖ ≤ 1` to bound by `‖a⋆ * a + z‖`.
    have hb_mul : star b * b =
        u * ((star a * a + z : A) : A⁺¹) * u - u * ((z - z * (e : A) : A) : A⁺¹) := by
      simp only [b, u, star_mul, h1_star, Unitization.inr_add, Unitization.inr_sub,
        Unitization.inr_mul, Unitization.inr_star]
      noncomm_ring
    calc
      ‖mk I a‖ ^ 2 ≤ ‖a - a * (e : A)‖ ^ 2 := hmk_sq
      _ = ‖b‖ ^ 2 := by rw [hb_norm]
      _ = ‖star b * b‖ := by rw [sq, ← CStarRing.norm_star_mul_self]
      _ = ‖u * ((star a * a + z : A) : A⁺¹) * u - u * ((z - z * (e : A) : A) : A⁺¹)‖ := by
          rw [hb_mul]
      _ ≤ ‖u * ((star a * a + z : A) : A⁺¹) * u‖ + ‖u * ((z - z * (e : A) : A) : A⁺¹)‖ :=
          norm_sub_le _ _
      _ ≤ ‖star a * a + z‖ + ‖(z' * e - z' : S)‖ := by
          refine add_le_add ?_ ?_
          · calc
              ‖u * ((star a * a + z : A) : A⁺¹) * u‖
                ≤ ‖u * ((star a * a + z : A) : A⁺¹)‖ * ‖u‖ := norm_mul_le _ _
              _ ≤ (‖u‖ * ‖((star a * a + z : A) : A⁺¹)‖) * 1 :=
                  mul_le_mul (norm_mul_le _ _) h1_norm (norm_nonneg _)
                    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              _ ≤ (1 * ‖star a * a + z‖) * 1 := by
                  rw [Unitization.norm_inr]
                  gcongr
              _ = ‖star a * a + z‖ := by ring
          · calc
              ‖u * ((z - z * (e : A) : A) : A⁺¹)‖
                ≤ ‖u‖ * ‖((z - z * (e : A) : A) : A⁺¹)‖ := norm_mul_le _ _
              _ ≤ 1 * ‖z - z * (e : A)‖ := by
                  rw [Unitization.norm_inr]
                  exact mul_le_mul_of_nonneg_right h1_norm (norm_nonneg _)
              _ = ‖(z' * e - z' : S)‖ := by
                  rw [one_mul, norm_sub_rev]
                  rfl

/-- The quotient of a nonunital C⋆-algebra by a closed two-sided ideal is a nonunital C⋆-algebra.
-/
noncomputable instance nonUnitalCStarAlgebra : NonUnitalCStarAlgebra (A ⧸ I) where
  smul_assoc := (instIsScalarTowerComplex I).smul_assoc
  smul_comm := (instSMulCommClassComplex I).smul_comm
  star_smul := (instStarModuleComplex I).star_smul

noncomputable instance nonUnitalCommCStarAlgebra {A : Type*}
    [NonUnitalCommCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    NonUnitalCommCStarAlgebra (A ⧸ I) :=
  { nonUnitalCStarAlgebra I, nonUnitalNormedCommRing I with }

/-- The canonical surjective `⋆`-algebra homomorphism `A →⋆ₙₐ[ℂ] A ⧸ I` onto a C⋆-quotient. -/
def mkStarAlgHom : A →⋆ₙₐ[ℂ] A ⧸ I where
  toFun := mk I
  map_smul' := mk_smul_complex I
  map_zero' := map_zero (mk I)
  map_add' := map_add (mk I)
  map_mul' := map_mul (mk I)
  map_star' := mk_star I

@[simp]
theorem coe_mkStarAlgHom : ⇑(mkStarAlgHom I) = mk I :=
  (rfl)

@[simp]
theorem mkStarAlgHom_apply (a : A) : mkStarAlgHom I a = mk I a :=
  (rfl)

theorem mkStarAlgHom_surjective : Function.Surjective (mkStarAlgHom I) :=
  mk_surjective I

@[simp]
theorem ker_mkStarAlgHom : TwoSidedIdeal.ker (mkStarAlgHom I) = I :=
  ker_mk I

/-- Two nonunital `⋆`-homomorphisms out of `A ⧸ I` agree when their compositions with
`mkStarAlgHom I` agree. -/
@[ext 1100]
theorem nonUnitalStarAlgHom_ext {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    ⦃f g : A ⧸ I →⋆ₙₐ[ℂ] B⦄ (h : f.comp (mkStarAlgHom I) = g.comp (mkStarAlgHom I)) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := mk_surjective I x
  exact DFunLike.congr_fun h a

/-- Descend a `⋆`-algebra homomorphism `f : A →⋆ₙₐ[ℂ] B` vanishing on `I` to `A ⧸ I →⋆ₙₐ[ℂ] B`. -/
def liftStarAlgHom (f : A →⋆ₙₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) : A ⧸ I →⋆ₙₐ[ℂ] B :=
  let hf' : ∀ y ∈ I, (f : A →ₙ+* B) y = 0 := hf
  { toFun := lift I (f : A →ₙ+* B) hf'
    map_smul' c x := by
      obtain ⟨a, rfl⟩ := mk_surjective I x
      rw [MonoidHom.id_apply, ← mk_smul_complex, lift_mk, lift_mk]
      exact map_smul f c a
    map_zero' := map_zero _
    map_add' := map_add _
    map_mul' := map_mul _
    map_star' x := by
      obtain ⟨a, rfl⟩ := mk_surjective I x
      rw [← mk_star, lift_mk, lift_mk]
      exact map_star f a }

@[simp]
theorem liftStarAlgHom_mk (f : A →⋆ₙₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) (a : A) :
    liftStarAlgHom I f hf (mk I a) = f a :=
  lift_mk I (f : A →ₙ+* B) hf a

@[simp]
theorem liftStarAlgHom_comp_mkStarAlgHom (f : A →⋆ₙₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) :
    (liftStarAlgHom I f hf).comp (mkStarAlgHom I) = f :=
  NonUnitalStarAlgHom.ext <| liftStarAlgHom_mk I f hf

theorem liftStarAlgHom_surjective_of_surjective {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    {f : A →⋆ₙₐ[ℂ] B} (hf : ∀ a ∈ I, f a = 0) (hsurj : Function.Surjective f) :
    Function.Surjective (liftStarAlgHom I f hf) :=
  lift_surjective_of_surjective (f := (f : A →ₙ+* B)) hf hsurj

theorem liftStarAlgHom_injective_of_ker_le {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    {f : A →⋆ₙₐ[ℂ] B} (hf : ∀ a ∈ I, f a = 0) (hker : TwoSidedIdeal.ker f ≤ I) :
    Function.Injective (liftStarAlgHom I f hf) :=
  lift_injective_of_ker_le (f := (f : A →ₙ+* B)) hf hker

/-- The canonical `⋆`-algebra homomorphism `A ⧸ I →⋆ₙₐ[ℂ] A ⧸ J` for closed ideals `I ≤ J`. -/
noncomputable def factorStarAlgHom {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I ≤ J) : A ⧸ I →⋆ₙₐ[ℂ] A ⧸ J :=
  liftStarAlgHom I (mkStarAlgHom J) fun _ hx => eq_zero_iff_mem.mpr (h hx)

@[simp]
theorem factorStarAlgHom_mk {I J : TwoSidedIdeal A} [IsClosed (I : Set A)] [IsClosed (J : Set A)]
    (h : I ≤ J) (a : A) : factorStarAlgHom h (mk I a) = mk J a :=
  liftStarAlgHom_mk I (mkStarAlgHom J) _ a

@[simp]
theorem factorStarAlgHom_comp_mkStarAlgHom {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I ≤ J) :
    (factorStarAlgHom h).comp (mkStarAlgHom I) = mkStarAlgHom J :=
  liftStarAlgHom_comp_mkStarAlgHom _ _ _

theorem factorStarAlgHom_surjective {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I ≤ J) : Function.Surjective (factorStarAlgHom h) :=
  liftStarAlgHom_surjective_of_surjective _ (mkStarAlgHom_surjective J)

/-- Isometric `⋆`-algebra equivalence between C⋆-quotients by equal closed two-sided ideals. -/
noncomputable def quotStarAlgEquivOfEq {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I = J) : A ⧸ I ≃⋆ₐ[ℂ] A ⧸ J where
  toFun := factorStarAlgHom h.le
  invFun := factorStarAlgHom h.ge
  left_inv x := by obtain ⟨a, rfl⟩ := mk_surjective I x; simp
  right_inv x := by obtain ⟨a, rfl⟩ := mk_surjective J x; simp
  map_mul' := map_mul _
  map_add' := map_add _
  map_star' := map_star _
  map_smul' := map_smul _

@[simp]
theorem quotStarAlgEquivOfEq_mk {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I = J) (a : A) :
    quotStarAlgEquivOfEq h (mk I a) = mk J a :=
  factorStarAlgHom_mk h.le a

@[simp]
theorem quotStarAlgEquivOfEq_symm {I J : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] (h : I = J) :
    (quotStarAlgEquivOfEq h).symm = quotStarAlgEquivOfEq h.symm := by
  ext x
  obtain ⟨a, rfl⟩ := mk_surjective J x
  exact (factorStarAlgHom_mk h.ge a).trans (quotStarAlgEquivOfEq_mk h.symm a).symm

end NonUnital

section Unital

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The quotient of a unital C⋆-algebra by a closed two-sided ideal is a unital C⋆-algebra. -/
noncomputable instance cstarAlgebra : CStarAlgebra (A ⧸ I) where
  star_smul := (instStarModuleComplex I).star_smul

noncomputable instance commCStarAlgebra {A : Type*} [CommCStarAlgebra A]
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)] : CommCStarAlgebra (A ⧸ I) :=
  { cstarAlgebra I, normedCommRing I with }

-- Verify that the unital C⋆-quotient structure agrees definitionally with the nonunital one.
example : (cstarAlgebra I).toNonUnitalCStarAlgebra = nonUnitalCStarAlgebra I :=
  rfl

/-- The canonical surjective unital `⋆`-algebra homomorphism `A →⋆ₐ[ℂ] A ⧸ I`. -/
def mkUnitalStarAlgHom : A →⋆ₐ[ℂ] A ⧸ I where
  toFun := mk I
  map_one' := mk_one I
  map_mul' := map_mul (mk I)
  map_zero' := map_zero (mk I)
  map_add' := map_add (mk I)
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, mk_smul_complex, mk_one, Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' := mk_star I

@[simp]
theorem coe_mkUnitalStarAlgHom : ⇑(mkUnitalStarAlgHom I) = mk I :=
  (rfl)

@[simp]
theorem mkUnitalStarAlgHom_apply (a : A) : mkUnitalStarAlgHom I a = mk I a :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_mkUnitalStarAlgHom :
    (mkUnitalStarAlgHom I).toNonUnitalStarAlgHom = mkStarAlgHom I := by
  ext a
  rfl

theorem mkUnitalStarAlgHom_surjective : Function.Surjective (mkUnitalStarAlgHom I) :=
  mk_surjective I

/-- Descend a unital `⋆`-algebra homomorphism `f : A →⋆ₐ[ℂ] B` vanishing on `I` to
`A ⧸ I →⋆ₐ[ℂ] B`. -/
noncomputable def liftUnitalStarAlgHom (f : A →⋆ₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) :
    A ⧸ I →⋆ₐ[ℂ] B :=
  let hf' : ∀ a ∈ I, f.toNonUnitalStarAlgHom a = 0 := hf
  { toFun := liftStarAlgHom I f.toNonUnitalStarAlgHom hf'
    map_one' := by
      rw [← mk_one I, liftStarAlgHom_mk]
      exact map_one f
    map_mul' := map_mul _
    map_zero' := map_zero _
    map_add' := map_add _
    commutes' c := by
      have hf1 : f.toNonUnitalStarAlgHom 1 = 1 := map_one f
      rw [Algebra.algebraMap_eq_smul_one, map_smul, ← mk_one I, liftStarAlgHom_mk, hf1,
        ← Algebra.algebraMap_eq_smul_one]
    map_star' := map_star _ }

@[simp]
theorem liftUnitalStarAlgHom_mk (f : A →⋆ₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) (a : A) :
    liftUnitalStarAlgHom I f hf (mk I a) = f a :=
  liftStarAlgHom_mk I f.toNonUnitalStarAlgHom hf a

@[simp]
theorem liftUnitalStarAlgHom_comp_mkUnitalStarAlgHom (f : A →⋆ₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) :
    (liftUnitalStarAlgHom I f hf).comp (mkUnitalStarAlgHom I) = f :=
  StarAlgHom.ext <| liftUnitalStarAlgHom_mk I f hf

@[simp]
theorem toNonUnitalStarAlgHom_liftUnitalStarAlgHom (f : A →⋆ₐ[ℂ] B) (hf : ∀ a ∈ I, f a = 0) :
    (liftUnitalStarAlgHom I f hf).toNonUnitalStarAlgHom =
      liftStarAlgHom I f.toNonUnitalStarAlgHom hf := by
  ext x
  rfl

end Unital

end TwoSidedIdeal.Quotient

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B)

/-- The injective `⋆`-homomorphism `A ⧸ ker φ →⋆ₙₐ[ℂ] B` factored from `φ : A →⋆ₙₐ[ℂ] B`. -/
def quotientKerHom : A ⧸ TwoSidedIdeal.ker φ →⋆ₙₐ[ℂ] B :=
  TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker φ) φ fun _ ha =>
    (TwoSidedIdeal.mem_ker φ).mp ha

@[simp]
theorem quotientKerHom_mk (a : A) :
    φ.quotientKerHom (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) = φ a :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_mk (TwoSidedIdeal.ker φ) φ _ a

@[simp]
theorem quotientKerHom_comp_mkStarAlgHom :
    φ.quotientKerHom.comp (TwoSidedIdeal.Quotient.mkStarAlgHom (TwoSidedIdeal.ker φ)) = φ :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_comp_mkStarAlgHom _ _ _

theorem quotientKerHom_injective : Function.Injective φ.quotientKerHom :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ le_rfl

theorem isometry_quotientKerHom : Isometry φ.quotientKerHom :=
  NonUnitalStarAlgHom.isometry φ.quotientKerHom φ.quotientKerHom_injective

@[simp]
theorem range_quotientKerHom : Set.range φ.quotientKerHom = Set.range φ := by
  ext b
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (TwoSidedIdeal.ker φ) x
    exact ⟨a, (φ.quotientKerHom_mk a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a, φ.quotientKerHom_mk a⟩

/-- Every `⋆`-algebra homomorphism between C⋆-algebras has closed range as a subset of `B`. -/
theorem isClosed_setRange : IsClosed (Set.range φ) := by
  rw [← φ.range_quotientKerHom]
  exact φ.isometry_quotientKerHom.isClosedEmbedding.isClosed_range

/-- The `⋆`-subalgebra range `φ.range` of any `⋆`-homomorphism between C⋆-algebras is closed, hence
a C⋆-subalgebra in its own right. -/
instance isClosed_range : IsClosed (φ.range : Set B) := by
  rw [NonUnitalStarAlgHom.coe_range]
  exact φ.isClosed_setRange

/-- Every `⋆`-homomorphism between C⋆-algebras with dense range is surjective. -/
theorem surjective_of_denseRange {φ : A →⋆ₙₐ[ℂ] B} (hφ : DenseRange φ) :
    Function.Surjective φ := by
  rw [← Set.range_eq_univ, ← φ.isClosed_setRange.closure_eq, hφ.closure_eq]

/-- First isometric `⋆`-isomorphism theorem for C⋆-algebras: `A ⧸ ker φ ≃⋆ₐ[ℂ] φ.range`. -/
noncomputable def quotientKerEquivRange : A ⧸ TwoSidedIdeal.ker φ ≃⋆ₐ[ℂ] φ.range :=
  StarAlgEquiv.ofBijective
    (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker φ) φ.rangeRestrict
      fun _ ha => Subtype.ext ((TwoSidedIdeal.mem_ker φ).mp ha))
    ⟨TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ φ.ker_rangeRestrict.le,
     TwoSidedIdeal.Quotient.liftStarAlgHom_surjective_of_surjective _ φ.rangeRestrict_surjective⟩

@[simp]
theorem quotientKerEquivRange_mk (a : A) :
    φ.quotientKerEquivRange (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) =
      φ.rangeRestrict a :=
  TwoSidedIdeal.Quotient.liftStarAlgHom_mk (TwoSidedIdeal.ker φ) φ.rangeRestrict _ a

theorem coe_quotientKerEquivRange_mk (a : A) :
    (φ.quotientKerEquivRange (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) : B) = φ a :=
  congrArg Subtype.val (φ.quotientKerEquivRange_mk a)

/-- Isometric `⋆`-isomorphism `A ⧸ ker φ ≃⋆ₐ[ℂ] B` induced by a surjective `⋆`-homomorphism of
C⋆-algebras. -/
noncomputable def quotientKerEquivOfSurjective {φ : A →⋆ₙₐ[ℂ] B} (hφ : Function.Surjective φ) :
    A ⧸ TwoSidedIdeal.ker φ ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective φ.quotientKerHom
    ⟨φ.quotientKerHom_injective,
     TwoSidedIdeal.Quotient.liftStarAlgHom_surjective_of_surjective _ hφ⟩

@[simp]
theorem quotientKerEquivOfSurjective_mk {φ : A →⋆ₙₐ[ℂ] B} (hφ : Function.Surjective φ) (a : A) :
    quotientKerEquivOfSurjective hφ (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) = φ a :=
  φ.quotientKerHom_mk a

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B)

/-- Every unital `⋆`-algebra homomorphism between C⋆-algebras has closed range as a subset of `B`.
-/
theorem isClosed_setRange : IsClosed (Set.range φ) :=
  NonUnitalStarAlgHom.isClosed_setRange φ.toNonUnitalStarAlgHom

/-- The unital `⋆`-subalgebra range `φ.range` of any unital `⋆`-homomorphism between C⋆-algebras is
closed, hence a unital C⋆-subalgebra in its own right. -/
instance isClosed_range : IsClosed (φ.range : Set B) := by
  have hcoe : (φ.range : Set B) = Set.range φ := φ.toAlgHom.coe_range
  rw [hcoe]
  exact φ.isClosed_setRange

/-- Every unital `⋆`-homomorphism between C⋆-algebras with dense range is surjective. -/
theorem surjective_of_denseRange {φ : A →⋆ₐ[ℂ] B} (hφ : DenseRange φ) : Function.Surjective φ :=
  NonUnitalStarAlgHom.surjective_of_denseRange (φ := φ.toNonUnitalStarAlgHom) hφ

/-- Isometric `⋆`-isomorphism `A ⧸ ker φ ≃⋆ₐ[ℂ] B` induced by a surjective unital `⋆`-homomorphism
of C⋆-algebras. -/
noncomputable def quotientKerEquivOfSurjective {φ : A →⋆ₐ[ℂ] B} (hφ : Function.Surjective φ) :
    A ⧸ TwoSidedIdeal.ker φ ≃⋆ₐ[ℂ] B :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective (φ := φ.toNonUnitalStarAlgHom) hφ

@[simp]
theorem quotientKerEquivOfSurjective_mk {φ : A →⋆ₐ[ℂ] B} (hφ : Function.Surjective φ) (a : A) :
    quotientKerEquivOfSurjective hφ (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) = φ a :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk (φ := φ.toNonUnitalStarAlgHom) hφ a

/-- First isometric `⋆`-isomorphism theorem for unital C⋆-algebras: `A ⧸ ker φ ≃⋆ₐ[ℂ] φ.range`. -/
noncomputable def quotientKerEquivRange : A ⧸ TwoSidedIdeal.ker φ ≃⋆ₐ[ℂ] φ.range :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq φ.ker_rangeRestrict.symm).trans
    (quotientKerEquivOfSurjective φ.rangeRestrict_surjective)

@[simp]
theorem quotientKerEquivRange_mk (a : A) :
    φ.quotientKerEquivRange (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) =
      φ.rangeRestrict a :=
  (congrArg (quotientKerEquivOfSurjective φ.rangeRestrict_surjective)
      (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_mk φ.ker_rangeRestrict.symm a)).trans
    (quotientKerEquivOfSurjective_mk φ.rangeRestrict_surjective a)

theorem coe_quotientKerEquivRange_mk (a : A) :
    (φ.quotientKerEquivRange (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a) : B) = φ a :=
  congrArg Subtype.val (φ.quotientKerEquivRange_mk a)

end StarAlgHom
