/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Lift
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TauCeti.Algebra.Star.Subalgebra

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
`star (a * u) * (a * u) = u * (star a * a + z) * u - u * (z - z * e)`
(`TauCeti.CStarAlgebra.norm_sub_mul_sq_le`),
giving `‖mk I a‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖ → ‖star a * a + z‖` and taking the infimum
over `z ∈ I` (see Gerard J. Murphy, *C*-Algebras and Operator Theory*, Theorem 3.1.4, or Kenneth R.
Davidson, *C*-Algebras by Example*, Theorem I.5.4 and Corollary I.5.5).

## Main declarations

* `TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`: C⋆-norm
  and C⋆-algebra instances on `A ⧸ I` for a closed two-sided ideal `I : TwoSidedIdeal A`.
* `TwoSidedIdeal.Quotient.mkStarAlgHom`, `TwoSidedIdeal.Quotient.liftStarAlgHom`,
  `TwoSidedIdeal.Quotient.factorStarAlgHom`, `TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq`, and
  `TwoSidedIdeal.Quotient.opStarAlgEquiv`: universal `⋆`-homomorphisms and `⋆`-equivalences on
  C⋆-quotients. `mkStarAlgHom` and `liftStarAlgHom` have unital counterparts
  `TwoSidedIdeal.Quotient.mkUnitalStarAlgHom` and `TwoSidedIdeal.Quotient.liftUnitalStarAlgHom`.
* `NonUnitalStarAlgHom.isClosed_range`, `StarAlgHom.isClosed_range`,
  `TwoSidedIdeal.isClosed_map_mk`, and `TwoSidedIdeal.isClosed_sup`: `⋆`-homomorphism ranges,
  images of closed ideals in quotients, and sums `I ⊔ J` of closed ideals are automatically closed.
* `TwoSidedIdeal.Quotient.exists_norm_mk_eq`: every class in a C⋆-quotient has a representative
  attaining the quotient norm.
* `NonUnitalStarAlgHom.norm_apply_le_norm_apply_of_ker_le`: a `⋆`-homomorphism killing the kernel
  of another is dominated by it in norm.
* `NonUnitalStarAlgHom.exists_mem_comap_norm_sub_lt`: the distance from `a` to the preimage of a
  closed ideal `J` under `φ` is at most `‖φ a - x‖` for every `x ∈ J`.
* `NonUnitalStarAlgHom.quotientKerEquivRange`, `NonUnitalStarAlgHom.quotientKerEquivOfSurjective`,
  `NonUnitalStarAlgHom.quotientEquivOfSurjective`, `NonUnitalStarAlgHom.liftOfSurjective`, and
  `NonUnitalStarAlgHom.surjective_of_denseRange` (plus `StarAlgHom` counterparts): isometric first
  `⋆`-isomorphism theorem, factorization through surjections, and surjectivity from dense range.
-/

public section

open Filter Topology Unitization
open scoped CStarAlgebra

namespace TwoSidedIdeal.Quotient

section NonUnital

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

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

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (A ⧸ I) where
  norm_smul_le := (Submodule.Quotient.normedSpace I.toSubmodule ℂ).norm_smul_le

-- Verify that the normed-space module agrees with `instModuleComplex` at instance transparency,
-- so that instance search finds the normed scalar classes on `A ⧸ I`.
example : (instNormedSpaceComplex I).toModule = instModuleComplex I := by
  with_reducible_and_instances rfl

example : NormSMulClass ℂ (A ⧸ I) := inferInstance

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
    have hz_lim : Tendsto (fun e : S => ‖star a * a + z‖ + ‖(z' - z' * e : S)‖) l
        (𝓝 ‖star a * a + z‖) := by
      simpa only [add_zero, norm_sub_rev] using tendsto_const_nhds.add
        (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_left z'))
    refine ge_of_tendsto hz_lim ?_
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
    -- Step 2: Ideal absorption gives `mk I a = mk I (a - a * e)`; then apply the C⋆-estimate
    -- `TauCeti.CStarAlgebra.norm_sub_mul_sq_le` for the positive contraction `e`.
    have hmk_eq : mk I a = mk I (a - a * (e : A)) := by
      rw [map_sub, eq_zero_iff_mem.mpr
        (I.mul_mem_left a (e : A) (I.mem_toNonUnitalStarSubalgebra.mp e.property)), sub_zero]
    calc
      ‖mk I a‖ ^ 2 ≤ ‖a - a * (e : A)‖ ^ 2 := by
        rw [hmk_eq]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_mk_le I _) 2
      _ ≤ ‖star a * a + z‖ + ‖z - z * (e : A)‖ :=
        TauCeti.CStarAlgebra.norm_sub_mul_sq_le (e := (e : A)) he₀ he₁ a z
      _ = ‖star a * a + z‖ + ‖(z' - z' * e : S)‖ := rfl

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

@[simp]
theorem factorStarAlgHom_refl {I : TwoSidedIdeal A} [IsClosed (I : Set A)] :
    factorStarAlgHom (le_refl I) = NonUnitalStarAlgHom.id ℂ (A ⧸ I) :=
  NonUnitalStarAlgHom.ext fun x => by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    simp

@[simp]
theorem factorStarAlgHom_comp {I J K : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] [IsClosed (K : Set A)] (h₁ : I ≤ J) (h₂ : J ≤ K) :
    (factorStarAlgHom h₂).comp (factorStarAlgHom h₁) = factorStarAlgHom (h₁.trans h₂) :=
  NonUnitalStarAlgHom.ext fun x => by
    obtain ⟨a, rfl⟩ := mk_surjective I x
    simp

@[simp]
theorem factorStarAlgHom_comp_apply {I J K : TwoSidedIdeal A} [IsClosed (I : Set A)]
    [IsClosed (J : Set A)] [IsClosed (K : Set A)] (h₁ : I ≤ J) (h₂ : J ≤ K) (x : A ⧸ I) :
    factorStarAlgHom h₂ (factorStarAlgHom h₁ x) = factorStarAlgHom (h₁.trans h₂) x :=
  DFunLike.congr_fun (factorStarAlgHom_comp h₁ h₂) x

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
    (quotStarAlgEquivOfEq h).symm = quotStarAlgEquivOfEq h.symm :=
  (rfl)

/-- Canonical isometric `⋆`-algebra isomorphism `(A ⧸ I)ᵐᵒᵖ ≃⋆ₐ[ℂ] Aᵐᵒᵖ ⧸ I.op` identifying the
opposite of a C⋆-quotient with the quotient of `Aᵐᵒᵖ` by `I.op`. -/
noncomputable def opStarAlgEquiv (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    (A ⧸ I)ᵐᵒᵖ ≃⋆ₐ[ℂ] Aᵐᵒᵖ ⧸ I.op where
  toFun := opEquiv I
  invFun := (opEquiv I).symm
  left_inv := (opEquiv I).left_inv
  right_inv := (opEquiv I).right_inv
  map_mul' := map_mul (opEquiv I)
  map_add' := map_add (opEquiv I)
  map_star' x := by
    obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
    obtain ⟨a, rfl⟩ := mk_surjective I x
    rw [← MulOpposite.op_star, ← mk_star, opEquiv_op_mk, opEquiv_op_mk,
      MulOpposite.op_star, mk_star]
  map_smul' c x := by
    obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
    obtain ⟨a, rfl⟩ := mk_surjective I x
    rw [← MulOpposite.op_smul, ← mk_smul_complex, opEquiv_op_mk, opEquiv_op_mk,
      MulOpposite.op_smul, mk_smul_complex]

@[simp]
theorem opStarAlgEquiv_op_mk (I : TwoSidedIdeal A) [IsClosed (I : Set A)] (a : A) :
    opStarAlgEquiv I (MulOpposite.op (mk I a)) = mk I.op (MulOpposite.op a) :=
  opEquiv_op_mk I a

@[simp]
theorem opStarAlgEquiv_symm_mk (I : TwoSidedIdeal A) [IsClosed (I : Set A)] (u : Aᵐᵒᵖ) :
    (opStarAlgEquiv I).symm (mk I.op u) = MulOpposite.op (mk I u.unop) :=
  opEquiv_symm_mk I u

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
    (mkUnitalStarAlgHom I).toNonUnitalStarAlgHom = mkStarAlgHom I :=
  (rfl)

theorem mkUnitalStarAlgHom_surjective : Function.Surjective (mkUnitalStarAlgHom I) :=
  mk_surjective I

@[simp]
theorem ker_mkUnitalStarAlgHom : TwoSidedIdeal.ker (mkUnitalStarAlgHom I) = I := by
  ext a
  simp [TwoSidedIdeal.mem_ker, eq_zero_iff_mem]

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
      liftStarAlgHom I f.toNonUnitalStarAlgHom hf :=
  (rfl)

end Unital

/-- In the quotient of a C⋆-algebra by a closed two-sided ideal, every class has a representative
whose norm equals the quotient norm: the infimum in `TwoSidedIdeal.Quotient.norm_mk_eq` is
attained. -/
theorem exists_norm_mk_eq {A : Type*} [NonUnitalCStarAlgebra A] {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (x : A ⧸ I) : ∃ a : A, mk I a = x ∧ ‖a‖ = ‖x‖ := by
  simpa only [mkStarAlgHom_apply] using
    NonUnitalStarAlgHom.exists_apply_eq_norm_eq (mkStarAlgHom I) (mkStarAlgHom_surjective I x)

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
  simpa only [Function.comp_def, φ.quotientKerHom_mk] using
    ((TwoSidedIdeal.Quotient.mk_surjective (TwoSidedIdeal.ker φ)).range_comp
      φ.quotientKerHom).symm

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

@[simp]
theorem quotientKerEquivOfSurjective_symm_apply {φ : A →⋆ₙₐ[ℂ] B}
    (hφ : Function.Surjective φ) (a : A) :
    (quotientKerEquivOfSurjective hφ).symm (φ a) =
      TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a :=
  (quotientKerEquivOfSurjective hφ).symm_apply_eq.mpr
    (quotientKerEquivOfSurjective_mk hφ a).symm

/-- Isometric `⋆`-isomorphism `A ⧸ I ≃⋆ₐ[ℂ] B` induced by a surjective `⋆`-homomorphism of
C⋆-algebras with kernel `I`. -/
noncomputable def quotientEquivOfSurjective {φ : A →⋆ₙₐ[ℂ] B} {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hφ : Function.Surjective φ) (hker : TwoSidedIdeal.ker φ = I) :
    A ⧸ I ≃⋆ₐ[ℂ] B :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq hker.symm).trans
    (quotientKerEquivOfSurjective hφ)

@[simp]
theorem quotientEquivOfSurjective_mk {φ : A →⋆ₙₐ[ℂ] B} {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hφ : Function.Surjective φ) (hker : TwoSidedIdeal.ker φ = I) (a : A) :
    quotientEquivOfSurjective hφ hker (TwoSidedIdeal.Quotient.mk I a) = φ a := by
  simp [quotientEquivOfSurjective]

@[simp]
theorem quotientEquivOfSurjective_symm_apply {φ : A →⋆ₙₐ[ℂ] B} {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hφ : Function.Surjective φ) (hker : TwoSidedIdeal.ker φ = I) (a : A) :
    (quotientEquivOfSurjective hφ hker).symm (φ a) = TwoSidedIdeal.Quotient.mk I a :=
  (quotientEquivOfSurjective hφ hker).symm_apply_eq.mpr
    (quotientEquivOfSurjective_mk hφ hker a).symm

@[simp]
theorem quotientEquivOfSurjective_comp_mkStarAlgHom {φ : A →⋆ₙₐ[ℂ] B} {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hφ : Function.Surjective φ) (hker : TwoSidedIdeal.ker φ = I) :
    (quotientEquivOfSurjective hφ hker).toNonUnitalStarAlgHom.comp
        (TwoSidedIdeal.Quotient.mkStarAlgHom I) = φ :=
  NonUnitalStarAlgHom.ext (quotientEquivOfSurjective_mk hφ hker)

@[simp]
theorem quotientEquivOfSurjective_symm_comp {φ : A →⋆ₙₐ[ℂ] B} {I : TwoSidedIdeal A}
    [IsClosed (I : Set A)] (hφ : Function.Surjective φ) (hker : TwoSidedIdeal.ker φ = I) :
    (quotientEquivOfSurjective hφ hker).symm.toNonUnitalStarAlgHom.comp φ =
      TwoSidedIdeal.Quotient.mkStarAlgHom I :=
  NonUnitalStarAlgHom.ext (quotientEquivOfSurjective_symm_apply hφ hker)

/-- Factor a `⋆`-homomorphism `ψ : A →⋆ₙₐ[ℂ] C` vanishing on `ker φ` through a surjective
`⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` of C⋆-algebras. -/
noncomputable def liftOfSurjective {C : Type*} [NonUnitalCStarAlgebra C]
    (hφ : Function.Surjective φ) (ψ : A →⋆ₙₐ[ℂ] C) (hψ : ∀ a, φ a = 0 → ψ a = 0) :
    B →⋆ₙₐ[ℂ] C :=
  (TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker φ) ψ
    fun a ha => hψ a ((TwoSidedIdeal.mem_ker φ).mp ha)).comp
    (quotientKerEquivOfSurjective hφ).symm.toNonUnitalStarAlgHom

@[simp]
theorem liftOfSurjective_apply {C : Type*} [NonUnitalCStarAlgebra C]
    (hφ : Function.Surjective φ) (ψ : A →⋆ₙₐ[ℂ] C) (hψ : ∀ a, φ a = 0 → ψ a = 0) (a : A) :
    φ.liftOfSurjective hφ ψ hψ (φ a) = ψ a := by
  simp [liftOfSurjective]

@[simp]
theorem liftOfSurjective_comp {C : Type*} [NonUnitalCStarAlgebra C]
    (hφ : Function.Surjective φ) (ψ : A →⋆ₙₐ[ℂ] C) (hψ : ∀ a, φ a = 0 → ψ a = 0) :
    (φ.liftOfSurjective hφ ψ hψ).comp φ = ψ :=
  NonUnitalStarAlgHom.ext (φ.liftOfSurjective_apply hφ ψ hψ)

/-- Uniqueness of factorization through a surjective `⋆`-homomorphism `φ`: `θ = φ.liftOfSurjective`
if and only if `θ.comp φ = ψ`. -/
theorem eq_liftOfSurjective_iff {C : Type*} [NonUnitalCStarAlgebra C]
    (hφ : Function.Surjective φ) (ψ : A →⋆ₙₐ[ℂ] C) (hψ : ∀ a, φ a = 0 → ψ a = 0)
    {θ : B →⋆ₙₐ[ℂ] C} :
    θ = φ.liftOfSurjective hφ ψ hψ ↔ θ.comp φ = ψ := by
  refine ⟨fun h => h ▸ φ.liftOfSurjective_comp hφ ψ hψ,
    fun hθ => NonUnitalStarAlgHom.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hφ b
  simpa using DFunLike.congr_fun hθ a

@[simp]
theorem liftOfSurjective_comp_self {C : Type*} [NonUnitalCStarAlgebra C]
    (hφ : Function.Surjective φ) (θ : B →⋆ₙₐ[ℂ] C) (hθ : ∀ a, φ a = 0 → (θ.comp φ) a = 0) :
    φ.liftOfSurjective hφ (θ.comp φ) hθ = θ :=
  ((φ.eq_liftOfSurjective_iff hφ (θ.comp φ) hθ).mpr rfl).symm

/-- The image of a closed two-sided ideal of a C⋆-algebra under any `⋆`-algebra homomorphism is
closed. -/
theorem isClosed_image_ideal (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    IsClosed (φ '' (I : Set A)) := by
  have hrange : φ '' (I : Set A) = Set.range (φ.comp I.starAlgHom) := by
    ext b
    simp [Set.mem_image, Set.mem_range]
  rw [hrange]
  exact (φ.comp I.starAlgHom).isClosed_setRange

end NonUnitalStarAlgHom

namespace NonUnitalStarAlgHom

variable {F G A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
  [FunLike G A C] [NonUnitalAlgHomClass G ℂ A C] [StarHomClass G A C]

/-- If every element killed by `φ` is killed by a `⋆`-homomorphism `ψ` between C⋆-algebras, then
`ψ` is dominated in norm by `φ`: `‖ψ a‖ ≤ ‖φ a‖`. -/
theorem norm_apply_le_norm_apply_of_ker_le {φ : F} {ψ : G}
    (h : TwoSidedIdeal.ker φ ≤ TwoSidedIdeal.ker ψ) (a : A) : ‖ψ a‖ ≤ ‖φ a‖ := by
  -- `ψ` factors contractively through `A ⧸ ker φ`, which `φ` embeds isometrically
  let φ' : A →⋆ₙₐ[ℂ] B := ofClass φ
  let q := TwoSidedIdeal.Quotient.liftStarAlgHom (TwoSidedIdeal.ker φ') (ofClass ψ) fun b hb =>
    (TwoSidedIdeal.mem_ker ψ).1 (h hb)
  -- `ofClass φ` and `ofClass ψ` agree with `φ` and `ψ` definitionally
  calc ‖ψ a‖ = ‖q (TwoSidedIdeal.Quotient.mk _ a)‖ :=
        congrArg norm (TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ (ofClass ψ) _ a).symm
    _ ≤ ‖TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ') a‖ :=
        NonUnitalStarAlgHom.norm_apply_le q _
    _ = ‖φ a‖ := (φ'.isometry_quotientKerHom.norm_map_of_map_zero (map_zero _) _).symm.trans
        (congrArg norm (φ'.quotientKerHom_mk a))

/-- **Distance to the preimage of an ideal.** If `x` lies in a closed two-sided ideal `J` of `B`,
then for every `a ∈ A` and `ε > 0` there is `b` in the preimage of `J` under `φ` with
`‖a - b‖ < ‖φ a - x‖ + ε`. -/
theorem exists_mem_comap_norm_sub_lt (φ : F) (J : TwoSidedIdeal B) [IsClosed (J : Set B)]
    {x : B} (hx : x ∈ J) (a : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ b ∈ J.comap φ, ‖a - b‖ < ‖φ a - x‖ + ε := by
  have : IsClosed (J.comap φ : Set A) := J.isClosed_comap (map_continuous φ) ‹_›
  let χ := (TwoSidedIdeal.Quotient.mkStarAlgHom J).comp (ofClass φ)
  let ψ := TwoSidedIdeal.Quotient.mkStarAlgHom (J.comap φ)
  have hker : TwoSidedIdeal.ker χ ≤ TwoSidedIdeal.ker ψ := fun c hc => by
    rw [TwoSidedIdeal.mem_ker] at hc ⊢
    simp only [χ, ψ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_ofClass,
      TwoSidedIdeal.Quotient.mkStarAlgHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem,
      TwoSidedIdeal.mem_comap] at hc ⊢
    exact hc
  -- `‖mk (J.comap φ) a‖ ≤ ‖mk J (φ a)‖ = ‖mk J (φ a - x)‖ ≤ ‖φ a - x‖`
  have hle : ‖ψ a‖ ≤ ‖φ a - x‖ := by
    refine (norm_apply_le_norm_apply_of_ker_le hker a).trans ?_
    have hχ : χ a = TwoSidedIdeal.Quotient.mk J (φ a - x) := by
      simp only [χ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_ofClass,
        TwoSidedIdeal.Quotient.mkStarAlgHom_apply, map_sub,
        TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 hx, sub_zero]
    rw [hχ]
    exact TwoSidedIdeal.Quotient.norm_mk_le J _
  obtain ⟨a', ha', hlt⟩ := TwoSidedIdeal.Quotient.exists_norm_mk_lt (ψ a) hε
  refine ⟨a - a', ?_, ?_⟩
  · have h0 : ψ (a - a') = 0 := by
      rw [map_sub, TwoSidedIdeal.Quotient.mkStarAlgHom_apply _ a', ha', sub_self]
    exact TwoSidedIdeal.Quotient.eq_zero_iff_mem.1 (by simpa [ψ] using h0)
  · rw [sub_sub_cancel]
    linarith

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

@[simp]
theorem quotientKerEquivOfSurjective_symm_apply {φ : A →⋆ₐ[ℂ] B}
    (hφ : Function.Surjective φ) (a : A) :
    (quotientKerEquivOfSurjective hφ).symm (φ a) =
      TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker φ) a :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective_symm_apply
    (φ := φ.toNonUnitalStarAlgHom) hφ a

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

namespace TwoSidedIdeal

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Under a surjective `⋆`-algebra homomorphism between C⋆-algebras, the pushforward of a closed
two-sided ideal is already closed without taking closure. -/
theorem isClosed_map_of_surjective {φ : A →⋆ₙₐ[ℂ] B} (hφ : Function.Surjective φ)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    IsClosed (TwoSidedIdeal.map φ I : Set B) := by
  rw [TwoSidedIdeal.coe_map_of_surjective hφ]
  exact φ.isClosed_image_ideal I

/-- The image of a closed two-sided ideal `I` in the C⋆-quotient `A ⧸ J` by a closed ideal `J` is
closed. -/
instance isClosed_map_mk (I J : TwoSidedIdeal A) [IsClosed (I : Set A)] [IsClosed (J : Set A)] :
    IsClosed (TwoSidedIdeal.map (Quotient.mk J) I : Set (A ⧸ J)) :=
  isClosed_map_of_surjective (φ := Quotient.mkStarAlgHom J) (Quotient.mkStarAlgHom_surjective J) I

/-- Normalizing `TwoSidedIdeal.map` along `Quotient.mkStarAlgHom J` to `Quotient.mk J`, so
`TwoSidedIdeal.isClosed_map_mk` applies uniformly. -/
@[simp]
theorem map_mkStarAlgHom (I J : TwoSidedIdeal A) [IsClosed (J : Set A)] :
    TwoSidedIdeal.map (Quotient.mkStarAlgHom J) I = TwoSidedIdeal.map (Quotient.mk J) I :=
  (rfl)

/-- The algebraic sum `I ⊔ J` of two closed two-sided ideals in a C⋆-algebra is automatically
closed. -/
instance isClosed_sup (I J : TwoSidedIdeal A) [IsClosed (I : Set A)] [IsClosed (J : Set A)] :
    IsClosed ((I ⊔ J : TwoSidedIdeal A) : Set A) := by
  rw [← TwoSidedIdeal.comap_map_mk I J]
  exact TwoSidedIdeal.isClosed_comap (Quotient.continuous_mk J) inferInstance

end TwoSidedIdeal
