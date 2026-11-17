/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.Normed.Algebra.DoubleCentralizer
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Closed two-sided ideals in C⋆-algebras and ideal multiplier homomorphisms

Every closed two-sided ring ideal `I : TwoSidedIdeal A` of a (possibly nonunital) complex
C⋆-algebra `A` is automatically closed under complex scalar multiplication and under the involution
`star`, hence forms a nonunital C⋆-subalgebra of `A` in its own right.

For scalar multiplication, `(c • e) * a = c • (e * a) → c • a` along an approximate unit `e` of `A`
while `(c • e) * a ∈ I` by left ideal absorption. For self-adjointness, the symmetric core
`S = {x ∈ I | star x ∈ I}` is already a closed nonunital ⋆-subalgebra of `A`, hence a nonunital
C⋆-algebra containing `star a * a` for every `a ∈ I`. Along the increasing approximate unit `e` of
`S`, right ideal absorption gives `(e : A) * star a ∈ I`, while the C⋆-identity in the unitization
`A⁺¹` yields
`‖star a - (e : A) * star a‖ ^ 2 ≤ ‖star a * a - (e : A) * (star a * a)‖ → 0`,
following the standard approximate-unit argument (see, e.g., Gerard J. Murphy, *C*-Algebras and
Operator Theory*, Theorem 3.1.3, or Kenneth R. Davidson, *C*-Algebras by Example*, Theorem I.5.3).

More generally, every two-sided star ideal `I : NonUnitalStarSubalgebra 𝕜 A` of a nonunital normed
star algebra `A` over `𝕜` acts on itself by left and right multiplication in `A` (with right
absorption deduced from left absorption via `StarMemClass.mul_mem_right_of_mul_mem_left`). This
yields a canonical contractive nonunital star-algebra homomorphism
`I.multiplierHom hmul : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` extending the inclusion of `I` into its multiplier
algebra. When `A` has a proper involution (in particular, when `A` is a C⋆-algebra), the kernel of
`I.multiplierHom hmul` is the left annihilator `{a : A | ∀ x ∈ I, a * x = 0}` of `I` in `A`, so
`I.multiplierHom hmul` is injective precisely when `I` is an essential ideal.

## Main declarations

* `TwoSidedIdeal.smul_mem_of_isClosed`: closed two-sided ideals in C⋆-algebras absorb complex
  scalars (specializing `TwoSidedIdeal.smul_mem_of_isApproximateUnit`).
* `TwoSidedIdeal.star_mem_of_isClosed` and `Ideal.star_mem_of_isClosed`: closed two-sided ideals in
  C⋆-algebras are closed under `star`.
* `TwoSidedIdeal.toSubmodule` and `TwoSidedIdeal.toNonUnitalStarSubalgebra`: bundle a closed
  two-sided ideal of a C⋆-algebra as a `Submodule ℂ A` and as a `NonUnitalStarSubalgebra ℂ A`.
* `TwoSidedIdeal.nonUnitalCStarAlgebra`: a closed two-sided ideal `I : TwoSidedIdeal A` is a
  `NonUnitalCStarAlgebra` on its subtype carrier, with canonical isometric `⋆`-monomorphism
  `TwoSidedIdeal.starAlgHom : I →⋆ₙₐ[ℂ] A` and `⋆`-isomorphism
  `TwoSidedIdeal.toNonUnitalStarSubalgebraEquiv : I ≃⋆ₐ[ℂ] I.toNonUnitalStarSubalgebra`.
* `NonUnitalStarSubalgebra.multiplierHom`: the canonical contractive star-algebra homomorphism
  `A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` attached to a star ideal `I` of `A`, with action formulas
  `multiplierHom_fst_apply` and `multiplierHom_snd_apply`, inclusion compatibility
  `multiplierHom_coe` and `multiplierHom_comp_subtype`, norm bound `norm_multiplierHom_le`, and
  proper-star annihilator characterizations `multiplierHom_eq_zero_iff` and
  `multiplierHom_injective_iff`.

## References

* Gerard J. Murphy, *C*-Algebras and Operator Theory*, Theorem 3.1.3.
* Kenneth R. Davidson, *C*-Algebras by Example*, Theorem I.5.3.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Section 2.3 and Proposition 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

open Filter Topology Unitization
open scoped CStarAlgebra

namespace TwoSidedIdeal

section CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

/-- Every closed two-sided ideal of a C⋆-algebra is closed under complex scalar multiplication. -/
theorem smul_mem_of_isClosed (c : ℂ) {a : A} (ha : a ∈ I) : c • a ∈ I := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  exact I.smul_mem_of_isApproximateUnit
    (CStarAlgebra.increasingApproximateUnit A).toIsApproximateUnit c ha

/-- Every closed two-sided ideal of a C⋆-algebra is self-adjoint (closed under `star`). -/
theorem star_mem_of_isClosed {a : A} (ha : a ∈ I) : star a ∈ I := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  -- Step 1: Form the closed self-adjoint core `S = I ∩ I⋆`, which is a C⋆-subalgebra of `A`.
  let S : NonUnitalStarSubalgebra ℂ A :=
    { carrier := {x : A | x ∈ I ∧ star x ∈ I}
      mul_mem' := fun {x y} hx hy =>
        ⟨I.mul_mem_left x y hy.1, by rw [star_mul]; exact I.mul_mem_left (star y) (star x) hx.2⟩
      add_mem' := fun {x y} hx hy =>
        ⟨I.add_mem hx.1 hy.1, by rw [star_add]; exact I.add_mem hx.2 hy.2⟩
      zero_mem' := ⟨I.zero_mem, by rw [star_zero]; exact I.zero_mem⟩
      smul_mem' := fun c {x} hx =>
        ⟨I.smul_mem_of_isClosed c hx.1,
          by rw [star_smul]; exact I.smul_mem_of_isClosed (star c) hx.2⟩
      star_mem' := fun {x} hx => ⟨hx.2, by rw [star_star]; exact hx.1⟩ }
  have hS_closed : IsClosed (S : Set A) := by
    have hS_set : (S : Set A) = (I : Set A) ∩ star ⁻¹' (I : Set A) := rfl
    rw [hS_set]
    exact hI.inter (hI.preimage continuous_star)
  let _ : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hS_closed)
  have _ : StarOrderedRing S := Subtype.starOrderedRing S (hs := hS_closed)
  -- Step 2: Notice `k = a⋆ * a` lies in `S`, and take an increasing approximate unit `l` of `S`.
  let k : S := ⟨star a * a, I.mul_mem_left (star a) a ha,
    by rw [star_mul, star_star]; exact I.mul_mem_left (star a) a ha⟩
  let l : Filter S := CStarAlgebra.approximateUnit S
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit S
  have := hl.neBot
  -- Step 3: Bound `‖e * a⋆ - a⋆‖² ≤ ‖e * k - k‖` in `A⁺¹` so `e * a⋆ → a⋆`.
  have hlim : Tendsto (fun e : S => (e : A) * star a) l (𝓝 (star a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ᶠ e : S in l,
        ‖(e : A) * star a - star a‖ ^ 2 ≤ ‖(e * k - k : S)‖ := by
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
      have h := TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le (A := A) (e := (e : A)) he₀ he₁ a
      rw [norm_sub_rev (star a * a)] at h
      exact h
    have hk_lim : Tendsto (fun e : S => ‖(e * k - k : S)‖) l (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_right k)
    have hsqrt : Tendsto (fun e : S => Real.sqrt ‖(e * k - k : S)‖) l (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using
        (Real.continuous_sqrt.tendsto 0).comp hk_lim
    refine squeeze_zero_norm' ?_ hsqrt
    filter_upwards [hsq] with e he
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact Real.le_sqrt_of_sq_le he
  exact hI.mem_of_tendsto hlim
    (Eventually.of_forall fun e => I.mul_mem_right (e : A) (star a) e.2.1)

@[simp]
theorem star_mem_iff_of_isClosed {a : A} : star a ∈ I ↔ a ∈ I :=
  ⟨fun h => star_star a ▸ I.star_mem_of_isClosed h, I.star_mem_of_isClosed⟩

/-- A closed two-sided ideal of a C⋆-algebra bundled as a complex submodule. -/
@[expose] def toSubmodule : Submodule ℂ A where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c _ ha := I.smul_mem_of_isClosed c ha

@[simp]
theorem coe_toSubmodule : (I.toSubmodule : Set A) = I :=
  (rfl)

@[simp]
theorem mem_toSubmodule {a : A} : a ∈ I.toSubmodule ↔ a ∈ I :=
  Iff.rfl

instance isClosed_toSubmodule : IsClosed (I.toSubmodule : Set A) :=
  hI

/-- A closed two-sided ideal of a C⋆-algebra bundled as a nonunital complex ⋆-subalgebra. -/
def toNonUnitalStarSubalgebra : NonUnitalStarSubalgebra ℂ A where
  __ := I.toSubmodule
  mul_mem' hx _ := I.mul_mem_right _ _ hx
  star_mem' hx := I.star_mem_of_isClosed hx

@[simp]
theorem coe_toNonUnitalStarSubalgebra : (I.toNonUnitalStarSubalgebra : Set A) = I :=
  (rfl)

@[simp]
theorem mem_toNonUnitalStarSubalgebra {a : A} : a ∈ I.toNonUnitalStarSubalgebra ↔ a ∈ I :=
  Iff.rfl

instance isClosed_toNonUnitalStarSubalgebra :
    IsClosed (I.toNonUnitalStarSubalgebra : Set A) :=
  hI

instance instStar : Star I where
  star x := ⟨star (x : A), I.star_mem_of_isClosed x.2⟩

@[simp, norm_cast]
theorem coe_star (x : I) : ((star x : I) : A) = star (x : A) :=
  (rfl)

instance instStarRing : StarRing I where
  star_involutive x := Subtype.ext (star_star (x : A))
  star_mul x y := Subtype.ext (star_mul (x : A) (y : A))
  star_add x y := Subtype.ext (star_add (x : A) (y : A))

instance instSMulComplex : SMul ℂ I where
  smul c x := ⟨c • (x : A), I.smul_mem_of_isClosed c x.2⟩

@[simp, norm_cast]
theorem coe_smul_complex (c : ℂ) (x : I) : ((c • x : I) : A) = c • (x : A) :=
  (rfl)

instance instModuleComplex : Module ℂ I :=
  Function.Injective.module ℂ I.coeAddMonoidHom Subtype.coe_injective I.coe_smul_complex

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ I where
  norm_smul_le c x := norm_smul_le c (x : A)

instance instIsScalarTowerComplex : IsScalarTower ℂ I I where
  smul_assoc c x y := Subtype.ext (smul_mul_assoc c (x : A) (y : A))

instance instSMulCommClassComplex : SMulCommClass ℂ I I where
  smul_comm c x y := Subtype.ext (mul_smul_comm c (x : A) (y : A)).symm

instance instStarModuleComplex : StarModule ℂ I where
  star_smul c x := Subtype.ext (star_smul c (x : A))

instance instCompleteSpace : CompleteSpace I :=
  hI.completeSpace_coe

instance instCStarRing : CStarRing I where
  norm_mul_self_le x := (CStarRing.norm_star_mul_self (x := (x : A))).symm.le

/-- Every closed two-sided ideal of a C⋆-algebra is a nonunital C⋆-algebra in its own right. -/
noncomputable instance nonUnitalCStarAlgebra : NonUnitalCStarAlgebra I where

noncomputable instance nonUnitalCommCStarAlgebra {A : Type*}
    [NonUnitalCommCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    NonUnitalCommCStarAlgebra I where
  mul_comm x y := Subtype.ext (mul_comm (x : A) (y : A))

/-- The canonical isometric ⋆-algebra monomorphism from a closed two-sided ideal `I` into `A`. -/
def starAlgHom : I →⋆ₙₐ[ℂ] A where
  toFun x := x
  map_smul' c x := by simp
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_starAlgHom : ⇑I.starAlgHom = ((↑) : I → A) :=
  (rfl)

@[simp]
theorem starAlgHom_apply (x : I) : I.starAlgHom x = (x : A) :=
  (rfl)

theorem starAlgHom_injective : Function.Injective I.starAlgHom :=
  Subtype.coe_injective

theorem isometry_starAlgHom : Isometry I.starAlgHom :=
  isometry_subtype_coe

@[simp]
theorem range_starAlgHom :
    NonUnitalStarAlgHom.range I.starAlgHom = I.toNonUnitalStarSubalgebra := by
  ext a
  simp [NonUnitalStarAlgHom.mem_range]

@[simp]
theorem ker_starAlgHom : TwoSidedIdeal.ker I.starAlgHom = ⊥ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, TwoSidedIdeal.mem_bot, starAlgHom_apply, Subtype.ext_iff]
  rfl

/-- The canonical `⋆`-algebra isomorphism between a closed two-sided ideal `I` and its associated
nonunital `⋆`-subalgebra `I.toNonUnitalStarSubalgebra`. -/
def toNonUnitalStarSubalgebraEquiv : I ≃⋆ₐ[ℂ] I.toNonUnitalStarSubalgebra :=
  { NonUnitalStarAlgHom.codRestrict I.starAlgHom I.toNonUnitalStarSubalgebra
      fun x => I.mem_toNonUnitalStarSubalgebra.mpr x.2 with
    invFun := fun x => ⟨x, I.mem_toNonUnitalStarSubalgebra.mp x.2⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }

@[simp]
theorem toNonUnitalStarSubalgebraEquiv_apply (x : I) :
    I.toNonUnitalStarSubalgebraEquiv x = ⟨x, I.mem_toNonUnitalStarSubalgebra.mpr x.2⟩ :=
  (rfl)

@[simp]
theorem toNonUnitalStarSubalgebraEquiv_symm_apply (x : I.toNonUnitalStarSubalgebra) :
    I.toNonUnitalStarSubalgebraEquiv.symm x = ⟨x, I.mem_toNonUnitalStarSubalgebra.mp x.2⟩ :=
  (rfl)

theorem coe_toNonUnitalStarSubalgebraEquiv_apply (x : I) :
    (I.toNonUnitalStarSubalgebraEquiv x : A) = x :=
  (rfl)

theorem coe_toNonUnitalStarSubalgebraEquiv_symm_apply (x : I.toNonUnitalStarSubalgebra) :
    (I.toNonUnitalStarSubalgebraEquiv.symm x : A) = x :=
  (rfl)

@[simp]
theorem subtype_comp_toNonUnitalStarSubalgebraEquiv :
    (NonUnitalStarSubalgebraClass.subtype I.toNonUnitalStarSubalgebra).comp
      I.toNonUnitalStarSubalgebraEquiv.toNonUnitalStarAlgHom = I.starAlgHom :=
  (rfl)

end CStarAlgebra

end TwoSidedIdeal

namespace Ideal

variable {A : Type*} [CStarAlgebra A] (I : Ideal A) [I.IsTwoSided] [hI : IsClosed (I : Set A)]

/-- Every closed two-sided `Ideal` of a unital C⋆-algebra is closed under `star`. -/
theorem star_mem_of_isClosed {a : A} (ha : a ∈ I) : star a ∈ I := by
  have : IsClosed (I.toTwoSided : Set A) := by simpa only [Ideal.coe_toTwoSided] using hI
  rw [← Ideal.mem_toTwoSided] at ha ⊢
  exact I.toTwoSided.star_mem_of_isClosed ha

@[simp]
theorem star_mem_iff_of_isClosed {a : A} : star a ∈ I ↔ a ∈ I :=
  ⟨fun h => star_star a ▸ I.star_mem_of_isClosed h, I.star_mem_of_isClosed⟩

/-- Bundle a closed two-sided `Ideal` of a unital C⋆-algebra as a `NonUnitalStarSubalgebra ℂ A`. -/
def toNonUnitalStarSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c a ha := algebraMap_smul A c a ▸ I.mul_mem_left (algebraMap ℂ A c) ha
  mul_mem' hx _ := I.mul_mem_right _ hx
  star_mem' hx := I.star_mem_of_isClosed hx

@[simp]
theorem coe_toNonUnitalStarSubalgebra : (I.toNonUnitalStarSubalgebra : Set A) = I :=
  (rfl)

@[simp]
theorem mem_toNonUnitalStarSubalgebra {a : A} : a ∈ I.toNonUnitalStarSubalgebra ↔ a ∈ I :=
  Iff.rfl

instance isClosed_toNonUnitalStarSubalgebra :
    IsClosed (I.toNonUnitalStarSubalgebra : Set A) :=
  hI

end Ideal

noncomputable section

open scoped MultiplierAlgebra

namespace NonUnitalStarSubalgebra

section NormedStarAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
  [StarRing A] (I : NonUnitalStarSubalgebra 𝕜 A)

omit [IsScalarTower 𝕜 A A] in
/-- Left multiplication by `a : A` as a continuous linear endomorphism of a star ideal `I`. -/
private def idealMulLeftCLM (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : I →L[𝕜] I :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨a * x, hmul a x x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a x y)
      map_smul' := fun c x => Subtype.ext (mul_smul_comm c a x) }
    ‖a‖ fun x => norm_mul_le a (x : A)

omit [SMulCommClass 𝕜 A A] in
/-- Right multiplication by `a : A` as a continuous linear endomorphism of a star ideal `I`. -/
private def idealMulRightCLM (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : I →L[𝕜] I :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2⟩
      map_add' := fun x y => Subtype.ext (add_mul (x : A) y a)
      map_smul' := fun c x => Subtype.ext (smul_mul_assoc c (x : A) a) }
    ‖a‖ fun x => (norm_mul_le (x : A) a).trans_eq (mul_comm ‖(x : A)‖ ‖a‖)

omit [IsScalarTower 𝕜 A A] in
@[simp]
private theorem coe_idealMulLeftCLM_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    ((I.idealMulLeftCLM hmul a x : I) : A) = a * x :=
  rfl

omit [SMulCommClass 𝕜 A A] in
@[simp]
private theorem coe_idealMulRightCLM_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    ((I.idealMulRightCLM hmul a x : I) : A) = x * a :=
  rfl

/-- The double centralizer on `I` given by left and right multiplication by `a : A`. -/
private def idealMultiplier (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) : 𝓜(𝕜, I) where
  fst := I.idealMulLeftCLM hmul a
  snd := I.idealMulRightCLM hmul a
  central x y := Subtype.ext (mul_assoc (x : A) a y)

variable [StarRing 𝕜] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The canonical nonunital star-algebra homomorphism `A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` induced by left and
right multiplication of `A` on a star ideal `I`. -/
def multiplierHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I) where
  toFun := I.idealMultiplier hmul
  map_smul' c a := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (smul_mul_assoc c a x))
    (fun x => Subtype.ext (mul_smul_comm c (x : A) a))
  map_zero' := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (zero_mul (x : A)))
    (fun x => Subtype.ext (mul_zero (x : A)))
  map_add' a b := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (add_mul a b x))
    (fun x => Subtype.ext (mul_add (x : A) a b))
  map_mul' a b := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (mul_assoc a b x))
    (fun x => Subtype.ext (mul_assoc (x : A) a b).symm)
  map_star' a := DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext <| by simp [idealMultiplier, DoubleCentralizer.star_fst])
    (fun x => Subtype.ext <| by simp [idealMultiplier, DoubleCentralizer.star_snd])

variable {I}

/-- The left centralizer of `I.multiplierHom hmul a` acts on `I` by left multiplication by `a`. -/
@[simp]
theorem multiplierHom_fst_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (I.multiplierHom hmul a).fst x = ⟨a * x, hmul a x x.2⟩ :=
  (rfl)

/-- The right centralizer of `I.multiplierHom hmul a` acts on `I` by right multiplication by `a`. -/
@[simp]
theorem multiplierHom_snd_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (I.multiplierHom hmul a).snd x =
      ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2⟩ :=
  (rfl)

/-- Coercing `(I.multiplierHom hmul a).fst x` to `A` gives `a * x`. -/
theorem coe_multiplierHom_fst_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (((I.multiplierHom hmul a).fst x : I) : A) = a * x :=
  (rfl)

/-- Coercing `(I.multiplierHom hmul a).snd x` to `A` gives `x * a`. -/
theorem coe_multiplierHom_snd_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    (((I.multiplierHom hmul a).snd x : I) : A) = x * a :=
  (rfl)

/-- On elements of `I`, `I.multiplierHom hmul` agrees with the canonical inclusion into
`𝓜(𝕜, I)`. -/
@[simp]
theorem multiplierHom_coe (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : I) :
    I.multiplierHom hmul (x : A) = (x : 𝓜(𝕜, I)) :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext rfl)

/-- Composing `I.multiplierHom hmul` with the subtype inclusion of `I` recovers
`DoubleCentralizer.coeHom`. -/
@[simp]
theorem multiplierHom_comp_subtype (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (I.multiplierHom hmul).comp (NonUnitalStarSubalgebraClass.subtype I) =
      DoubleCentralizer.coeHom :=
  NonUnitalStarAlgHom.ext (I.multiplierHom_coe hmul)

/-- The canonical map from `A` into the multiplier algebra of a star ideal is contractive. -/
theorem norm_multiplierHom_le (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) :
    ‖I.multiplierHom hmul a‖ ≤ ‖a‖ := by
  rw [DoubleCentralizer.norm_def, DoubleCentralizer.toProdHom_apply, Prod.norm_def]
  exact max_le
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => norm_mul_le a (x : A))
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x =>
      (norm_mul_le (x : A) a).trans_eq (mul_comm ‖(x : A)‖ ‖a‖))

/-- The canonical map `I.multiplierHom hmul : A →⋆ₙₐ[𝕜] 𝓜(𝕜, I)` is norm continuous. -/
@[fun_prop]
theorem continuous_multiplierHom (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    Continuous (I.multiplierHom hmul) :=
  AddMonoidHomClass.continuous_of_bound (I.multiplierHom hmul) 1 fun a => by
    simpa only [one_mul] using I.norm_multiplierHom_le hmul a

/-- When `A` has a proper involution, `I.multiplierHom hmul a = 0` precisely when `a`
left-annihilates `I`. -/
theorem multiplierHom_eq_zero_iff [IsProperStar A] (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {a : A} :
    I.multiplierHom hmul a = 0 ↔ ∀ x ∈ I, a * x = 0 := by
  refine ⟨fun h x hx => ?_, fun h => DoubleCentralizer.ext_fst_snd
    (fun x => Subtype.ext (h x x.2)) fun x => Subtype.ext ?_⟩
  · have := congrArg (fun m : 𝓜(𝕜, I) => ((m.fst ⟨x, hx⟩ : I) : A)) h
    simpa using this
  · -- Right annihilation `x * a = 0` follows from `(x * a) * star (x * a) = x * (a * _) = 0`.
    have hzero : (x : A) * a * star ((x : A) * a) = 0 := by
      rw [mul_assoc, h _ (star_mem (StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.2)),
        mul_zero]
    exact mul_star_self_eq_zero.mp hzero

/-- When `A` has a proper involution, `I.multiplierHom hmul` is injective if and only if `I` has
trivial left annihilator in `A`. -/
theorem multiplierHom_injective_iff [IsProperStar A] (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    Function.Injective (I.multiplierHom hmul) ↔ ∀ a : A, (∀ x ∈ I, a * x = 0) → a = 0 := by
  rw [injective_iff_map_eq_zero]
  exact forall_congr' fun _ => imp_congr_left (I.multiplierHom_eq_zero_iff hmul)

end NormedStarAlgebra

end NonUnitalStarSubalgebra

end
