/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import TauCeti.Algebra.Order.Group.OrdConnected
public import TauCeti.Analysis.Convex.Cone.Basic
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Algebra.Order.Star.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.Normed.Module.CohenFactorization.Bimodule
import TauCeti.Analysis.RCLike.Basic

/-!
# Hereditary C⋆-subalgebras, closed left ideals, and hereditary cones

In an ordered additive group, an additive subgroup contains every positive element dominated by one
of its members (`0 ≤ a ≤ b` and `b ∈ B` imply `a ∈ B`) if and only if its underlying set satisfies
`Set.OrdConnected` (`AddSubgroupClass.ordConnected_iff`), and the same equivalence holds for any
pointed subcone of the nonnegative cone (`ProperCone.ordConnected_iff_of_le_positive`). We therefore
express heredity in a (possibly nonunital) C⋆-algebra `A` directly through `Set.OrdConnected`.

This file develops the structure theory of hereditary C⋆-subalgebras:

* **Heredity of closed ideals**: if `0 ≤ a ≤ b` and `b` belongs to a closed star subalgebra `s`,
  then `(e : A) * a * (e : A) → a` along any increasing approximate unit of `s`
  (`Filter.IsIncreasingApproximateUnit.tendsto_mul_mul_of_nonneg_of_le`). Consequently, every closed
  complex left ideal (`Submodule.mem_of_nonneg_of_le`, `Submodule.ordConnected_of_isClosed`), every
  closed two-sided ideal (`TwoSidedIdeal.mem_of_nonneg_of_le`,
  `TwoSidedIdeal.ordConnected_of_isClosed`), and every closed left `Ideal` of a unital C⋆-algebra
  (`Ideal.mem_of_nonneg_of_le`, `Ideal.ordConnected_of_isClosed`) is hereditary.
* **Order-preserving correspondences**: closed hereditary C⋆-subalgebras `B`, closed complex left
  ideals `L`, and closed hereditary positive cones `C ≤ ProperCone.positive ℝ A` correspond
  bijectively and monotonically via `L ↦ L ∩ star ⁻¹' L` (`Submodule.starCore`),
  `B ↦ {x : A | star x * x ∈ B}` (`NonUnitalStarSubalgebra.hereditaryLeftIdeal`), and
  `B ↦ {a ∈ B | 0 ≤ a}` (`NonUnitalStarSubalgebra.positiveCone`), bundled as order isomorphisms
  `TauCeti.CStarAlgebra.hereditarySubalgebraLeftIdealOrderIso`,
  `TauCeti.CStarAlgebra.hereditarySubalgebraPositiveConeOrderIso`,
  `TauCeti.CStarAlgebra.closedLeftIdealPositiveConeOrderIso`, and (in the unital case)
  `TauCeti.CStarAlgebra.hereditarySubalgebraClosedIdealOrderIso`.
* **Algebraic sandwich characterizations and Cohen–Hewitt factorization**: every order-connected
  nonunital ⋆-subalgebra `B` satisfies `b₁ * a * b₂ ∈ B` (`NonUnitalStarSubalgebra.mul_mul_mem`),
  and a closed nonunital ⋆-subalgebra `B` is hereditary if and only if `b₁ * a * b₂ ∈ B` for all
  `b₁, b₂ ∈ B` and `a : A`, or equivalently `b * a * star b ∈ B` for all `b ∈ B` and `a : A`
  (`NonUnitalStarSubalgebra.ordConnected_iff_mul_mul_mem`,
  `NonUnitalStarSubalgebra.ordConnected_iff_mul_mul_star_mem`). Right-module Cohen–Hewitt
  factorization (`NonUnitalStarSubalgebra.exists_mul_eq_of_star_mul_self_mem`) identifies
  `{x : A | star x * x ∈ B}` with the set of products `A * B`
  (`NonUnitalStarSubalgebra.coe_hereditaryLeftIdeal_eq_range_mul`).
* **Closed ideal correspondence**: for an order-connected nonunital ⋆-subalgebra `B` generating the
  closed two-sided ideal `B.closedIdeal`, restriction `J ↦ J ∩ B` and extension
  `K ↦ (K.map (NonUnitalStarSubalgebraClass.subtype B)).topologicalClosure` form an order
  isomorphism `B.closedIdealOrderIso` between closed two-sided ideals of `A` contained in
  `B.closedIdeal` and closed two-sided ideals of `B`.
* **Generated hereditary subalgebras, full positive elements, and strictly positive elements**: for
  self-adjoint `a` (in particular for `0 ≤ a`), `TauCeti.CStarAlgebra.hereditarySubalgebra a` is the
  closure of `{a * x * a | x : A}` and is the smallest closed hereditary C⋆-subalgebra containing
  `a`. We define `TauCeti.CStarAlgebra.IsFullPositive` and
  `TauCeti.CStarAlgebra.IsStrictlyPositive`, prove that strict positivity implies full positivity,
  and show that in unital C⋆-algebras `TauCeti.CStarAlgebra.IsStrictlyPositive` agrees with
  `IsStrictlyPositive` (`TauCeti.CStarAlgebra.isStrictlyPositive_iff_of_unital`).

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.5.1.1(ii), II.5.3.1, II.5.3.2, II.5.3.5, and II.5.3.7.
* Gert K. Pedersen, *C*-Algebras and their Automorphism Groups*, §1.5, Theorem 1.5.2.
* Gerard J. Murphy, *C*-Algebras and Operator Theory*, §3.2, Theorem 3.2.2.
-/

public section

open Filter Topology Unitization Complex
open scoped CStarAlgebra NNReal ComplexStarModule

/-! ### Heredity of self-adjoint cores, closed left ideals, and closed two-sided ideals -/

namespace Submodule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The self-adjoint core of a closed complex left ideal is hereditary (`Set.OrdConnected`). -/
instance ordConnected_starCore (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    [IsClosed (L : Set A)] : (L.starCore hL : Set A).OrdConnected := by
  rw [AddSubgroupClass.ordConnected_iff]
  intro a b ha hab hb
  let S := L.starCore hL
  have hl : (CStarAlgebra.approximateUnit S).IsIncreasingApproximateUnit :=
    CStarAlgebra.increasingApproximateUnit S
  exact (L.isClosed_starCore hL).mem_of_tendsto (hl.tendsto_mul_mul_of_nonneg_of_le ha hab hb)
    (Eventually.of_forall fun e ↦ L.mul_mul_mem_starCore hL e.2 a e.2)

/-- The underlying set of a closed left-absorbing complex submodule in a C⋆-algebra is
order-connected. -/
theorem ordConnected_of_isClosed (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    [IsClosed (L : Set A)] : (L : Set A).OrdConnected := by
  rw [AddSubgroupClass.ordConnected_iff]
  intro a b ha hab hb
  have hb_core : b ∈ L.starCore hL :=
    (L.mem_starCore hL).mpr ⟨hb, by rwa [(ha.trans hab).isSelfAdjoint.star_eq]⟩
  exact ((L.mem_starCore hL).mp
    ((L.ordConnected_starCore hL).out (zero_mem _) hb_core ⟨ha, hab⟩)).1

/-- Every closed left-absorbing complex submodule of a C⋆-algebra is hereditary: if `0 ≤ a ≤ b` and
`b ∈ L`, then `a ∈ L`. -/
theorem mem_of_nonneg_of_le (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    [IsClosed (L : Set A)] {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ L) : a ∈ L :=
  (L.ordConnected_of_isClosed hL).out L.zero_mem hb ⟨ha, hab⟩

end Submodule

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The underlying set of a closed two-sided ideal in a C⋆-algebra is order-connected. -/
instance ordConnected_of_isClosed (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    (I : Set A).OrdConnected := by
  rw [← I.coe_toSubmodule]
  exact I.toSubmodule.ordConnected_of_isClosed fun a x hx ↦
    I.mem_toSubmodule.mpr (I.mul_mem_left a x (I.mem_toSubmodule.mp hx))

/-- Every closed two-sided ideal of a C⋆-algebra is hereditary: if `0 ≤ a ≤ b` and `b ∈ I`, then
`a ∈ I`. -/
theorem mem_of_nonneg_of_le (I : TwoSidedIdeal A) [IsClosed (I : Set A)] {a b : A}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ I) : a ∈ I :=
  I.ordConnected_of_isClosed.out I.zero_mem hb ⟨ha, hab⟩

end TwoSidedIdeal

namespace Ideal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The underlying set of a closed left ideal in a unital C⋆-algebra is order-connected. -/
instance ordConnected_of_isClosed (I : Ideal A) [hI : IsClosed (I : Set A)] :
    (I : Set A).OrdConnected := by
  have : IsClosed ((I.restrictScalars ℂ : Submodule ℂ A) : Set A) := by
    rwa [Submodule.coe_restrictScalars]
  rw [← Submodule.coe_restrictScalars (S := ℂ)]
  exact (I.restrictScalars ℂ).ordConnected_of_isClosed fun a x hx ↦
    (I.restrictScalars_mem ℂ _).mpr (I.mul_mem_left a ((I.restrictScalars_mem ℂ x).mp hx))

/-- Every closed left ideal of a unital C⋆-algebra is hereditary: if `0 ≤ a ≤ b` and `b ∈ I`, then
`a ∈ I`. -/
theorem mem_of_nonneg_of_le (I : Ideal A) [IsClosed (I : Set A)] {a b : A}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ I) : a ∈ I :=
  I.ordConnected_of_isClosed.out I.zero_mem hb ⟨ha, hab⟩

end Ideal

/-! ### Closed hereditary cones and their associated closed left ideals -/

namespace ProperCone

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private lemma mem_of_mul_self_mem_of_nonneg (C : ProperCone ℝ A) [hC : (C : Set A).OrdConnected]
    {a : A} (ha : 0 ≤ a) (ha2 : a * a ∈ C) : a ∈ C := by
  have ha_sa : IsSelfAdjoint a := ha.isSelfAdjoint
  let g : ℕ → ℝ → ℝ := fun n t ↦ max (t - ((n : ℝ) + 1)⁻¹) 0
  have hg_cont : ∀ n : ℕ, Continuous (g n) := fun n ↦ by fun_prop
  have hg_zero : ∀ n : ℕ, g n 0 = 0 := fun n ↦ max_eq_right (sub_nonpos.mpr (by positivity))
  refine C.isClosed.mem_of_tendsto (TauCeti.CStarAlgebra.tendsto_cfcₙ_max_sub_inv ha)
    (Eventually.of_forall fun n ↦ ?_)
  set ε : ℝ := ((n : ℝ) + 1)⁻¹
  have hε : 0 < ε := by positivity
  have hnonneg : 0 ≤ cfcₙ (g n) a := cfcₙ_nonneg fun _ _ ↦ le_max_right _ _
  have hbound : cfcₙ (g n) a ≤ ε⁻¹ • (a * a) := by
    have hrhs : ε⁻¹ • (a * a) = cfcₙ (fun t : ℝ ↦ ε⁻¹ • (t * t)) a := by
      symm
      rw [cfcₙ_smul ε⁻¹ (fun t : ℝ ↦ t * t) a (hf := (by fun_prop)) (h0 := mul_zero 0),
        cfcₙ_mul (fun t : ℝ ↦ t) (fun t : ℝ ↦ t) a
          (hf := continuousOn_id) (hf0 := rfl) (hg := continuousOn_id) (hg0 := rfl),
        cfcₙ_id' ℝ a]
    rw [hrhs]
    refine cfcₙ_mono (hf := (hg_cont n).continuousOn) (hf0 := hg_zero n)
      (hg := Continuous.continuousOn (by fun_prop)) (hg0 := by simp) fun t ht ↦ ?_
    have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg a ha t ht
    dsimp only [g, smul_eq_mul]
    rcases le_total t ε with hle | hge
    · rw [max_eq_right (sub_nonpos.mpr hle)]
      positivity
    · rw [max_eq_left (sub_nonneg.mpr hge), inv_mul_eq_div, le_div_iff₀ hε]
      nlinarith
  exact hC.out C.zero_mem (C.smul_mem ha2 (inv_nonneg.mpr hε.le)) ⟨hnonneg, hbound⟩

/-- For a nonnegative element `a` and an order-connected proper cone `C` in a C⋆-algebra,
`a * a ∈ C` if and only if `a ∈ C`. -/
theorem mul_self_mem_iff_of_nonneg (C : ProperCone ℝ A) [hC : (C : Set A).OrdConnected] {a : A}
    (ha : 0 ≤ a) : a * a ∈ C ↔ a ∈ C := by
  refine ⟨mem_of_mul_self_mem_of_nonneg C ha, fun haC ↦ ?_⟩
  let s : A := CFC.sqrt a
  have hs_star : star s = s := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hs_mul : s * s = a := CFC.sqrt_mul_sqrt_self a ha
  have hsq_eq : a * a = star s * a * s := by
    simp only [hs_star, ← hs_mul, mul_assoc]
  have hle : a * a ≤ ‖a‖ • a := by
    rw [hsq_eq]
    simpa only [hs_star, hs_mul] using
      CStarAlgebra.star_left_conjugate_le_norm_smul s a ha.isSelfAdjoint
  have ha2_nonneg : 0 ≤ a * a := by
    simpa only [ha.isSelfAdjoint.star_eq] using star_mul_self_nonneg a
  exact hC.out C.zero_mem (C.smul_mem haC (norm_nonneg a)) ⟨ha2_nonneg, hle⟩

/-- The closed complex left ideal `{x : A | star x * x ∈ C}` associated to an order-connected proper
cone `C` in a C⋆-algebra. -/
def hereditaryLeftIdeal (C : ProperCone ℝ A) [hC : (C : Set A).OrdConnected] : Submodule ℂ A where
  carrier := {x : A | star x * x ∈ C}
  zero_mem' := by
    simp only [Set.mem_ofPred, star_zero, zero_mul]
    exact C.zero_mem
  add_mem' {x y} hx hy :=
    hC.out C.zero_mem (two_nsmul (star x * x + star y * y) ▸
        C.add_mem (C.add_mem hx hy) (C.add_mem hx hy))
      ⟨star_mul_self_nonneg (x + y), TauCeti.star_add_mul_self_le x y⟩
  smul_mem' c {x} hx := by
    simp only [Set.mem_ofPred, TauCeti.star_smul_mul_self]
    exact C.smul_mem hx (sq_nonneg ‖c‖)

@[simp]
theorem mem_hereditaryLeftIdeal (C : ProperCone ℝ A) [(C : Set A).OrdConnected] {x : A} :
    x ∈ C.hereditaryLeftIdeal ↔ star x * x ∈ C :=
  Iff.rfl

@[simp]
theorem coe_hereditaryLeftIdeal (C : ProperCone ℝ A) [(C : Set A).OrdConnected] :
    (C.hereditaryLeftIdeal : Set A) = {x : A | star x * x ∈ C} :=
  (rfl)

/-- The left ideal associated to an order-connected proper cone is closed. -/
instance isClosed_hereditaryLeftIdeal (C : ProperCone ℝ A) [(C : Set A).OrdConnected] :
    IsClosed (C.hereditaryLeftIdeal : Set A) := by
  rw [coe_hereditaryLeftIdeal]
  exact C.isClosed.preimage (continuous_star.mul continuous_id)

/-- The complex subspace `C.hereditaryLeftIdeal` absorbs multiplication on the left by `A`. -/
theorem mul_mem_hereditaryLeftIdeal (C : ProperCone ℝ A) [hC : (C : Set A).OrdConnected] (a : A)
    {x : A} (hx : x ∈ C.hereditaryLeftIdeal) : a * x ∈ C.hereditaryLeftIdeal :=
  hC.out C.zero_mem (C.smul_mem hx (norm_nonneg _))
    ⟨star_mul_self_nonneg (a * x), TauCeti.CStarAlgebra.star_mul_mul_self_le a x⟩

/-- `ProperCone.hereditaryLeftIdeal` is monotone with respect to inclusion. -/
theorem hereditaryLeftIdeal_mono {C₁ C₂ : ProperCone ℝ A} [(C₁ : Set A).OrdConnected]
    [(C₂ : Set A).OrdConnected] (h : C₁ ≤ C₂) :
    C₁.hereditaryLeftIdeal ≤ C₂.hereditaryLeftIdeal :=
  fun _ hx ↦ h hx

end ProperCone

/-! ### Hereditary C⋆-subalgebras, sandwich characterizations, and Cohen–Hewitt factorization -/

namespace NonUnitalStarSubalgebra

section Hereditary

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive cone `{a ∈ B | 0 ≤ a}` of a closed nonunital ⋆-subalgebra `B` of `A`, bundled as a
`ProperCone ℝ A`. -/
def positiveCone (B : NonUnitalStarSubalgebra ℂ A) [hB : IsClosed (B : Set A)] :
    ProperCone ℝ A where
  carrier := {a : A | a ∈ B ∧ 0 ≤ a}
  add_mem' {_ _} hx hy := ⟨add_mem hx.1 hy.1, add_nonneg hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem B, le_rfl⟩
  smul_mem' c {_} hx :=
    ⟨(SMulMemClass.ofIsScalarTower _ ℝ ℂ A).smul_mem (c : ℝ) hx.1, smul_nonneg c.2 hx.2⟩
  isClosed' := hB.inter CStarAlgebra.isClosed_nonneg

@[simp]
theorem mem_positiveCone (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)] {a : A} :
    a ∈ B.positiveCone ↔ a ∈ B ∧ 0 ≤ a :=
  Iff.rfl

@[simp]
theorem coe_positiveCone (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)] :
    (B.positiveCone : Set A) = (B : Set A) ∩ Set.Ici 0 :=
  (rfl)

/-- The positive cone of a closed nonunital ⋆-subalgebra is contained in `ProperCone.positive ℝ A`.
-/
theorem positiveCone_le_positive (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)] :
    B.positiveCone ≤ ProperCone.positive ℝ A :=
  fun _ hx ↦ ProperCone.mem_positive.mpr hx.2

/-- `NonUnitalStarSubalgebra.positiveCone` is monotone with respect to inclusion. -/
theorem positiveCone_mono {B₁ B₂ : NonUnitalStarSubalgebra ℂ A} [IsClosed (B₁ : Set A)]
    [IsClosed (B₂ : Set A)] (h : B₁ ≤ B₂) :
    B₁.positiveCone ≤ B₂.positiveCone :=
  fun _ hx ↦ ⟨h hx.1, hx.2⟩

/-- If `B` is hereditary (`Set.OrdConnected`), then `B.positiveCone` is also order-connected. -/
instance ordConnected_positiveCone (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)]
    [(B : Set A).OrdConnected] : (B.positiveCone : Set A).OrdConnected := by
  rw [coe_positiveCone]
  infer_instance

/-- The complex left ideal `{x : A | star x * x ∈ B}` associated to an order-connected nonunital
⋆-subalgebra `B` of `A`. -/
def hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [hB : (B : Set A).OrdConnected] :
    Submodule ℂ A where
  carrier := {x : A | star x * x ∈ B}
  zero_mem' := by
    simp only [Set.mem_ofPred, star_zero, zero_mul]
    exact zero_mem B
  add_mem' {x y} hx hy :=
    hB.out (zero_mem B) (nsmul_mem (add_mem hx hy) 2)
      ⟨star_mul_self_nonneg (x + y), TauCeti.star_add_mul_self_le x y⟩
  smul_mem' c {x} hx := by
    simp only [Set.mem_ofPred, TauCeti.star_smul_mul_self]
    exact (SMulMemClass.ofIsScalarTower _ ℝ ℂ A).smul_mem (‖c‖ ^ 2) hx

@[simp]
theorem mem_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    {x : A} : x ∈ B.hereditaryLeftIdeal ↔ star x * x ∈ B :=
  Iff.rfl

@[simp]
theorem coe_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected] :
    (B.hereditaryLeftIdeal : Set A) = {x : A | star x * x ∈ B} :=
  (rfl)

@[simp]
theorem hereditaryLeftIdeal_positiveCone (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)]
    [(B : Set A).OrdConnected] :
    B.positiveCone.hereditaryLeftIdeal = B.hereditaryLeftIdeal := by
  ext x
  simp only [ProperCone.mem_hereditaryLeftIdeal, mem_positiveCone, mem_hereditaryLeftIdeal,
    and_iff_left (star_mul_self_nonneg x)]

/-- If `B` is closed in `A`, then `B.hereditaryLeftIdeal` is closed in `A`. -/
instance isClosed_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [hB : IsClosed (B : Set A)]
    [(B : Set A).OrdConnected] : IsClosed (B.hereditaryLeftIdeal : Set A) := by
  rw [coe_hereditaryLeftIdeal]
  exact hB.preimage (continuous_star.mul continuous_id)

/-- `B.hereditaryLeftIdeal` absorbs left multiplication by arbitrary elements of `A`. -/
theorem mul_mem_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A)
    [hB : (B : Set A).OrdConnected] (a : A) {x : A} (hx : x ∈ B.hereditaryLeftIdeal) :
    a * x ∈ B.hereditaryLeftIdeal :=
  hB.out (zero_mem B) ((SMulMemClass.ofIsScalarTower _ ℝ ℂ A).smul_mem ‖star a * a‖ hx)
    ⟨star_mul_self_nonneg (a * x), TauCeti.CStarAlgebra.star_mul_mul_self_le a x⟩

/-- Every element of `B` lies in `B.hereditaryLeftIdeal`. -/
theorem mem_hereditaryLeftIdeal_of_mem (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    {b : A} (hb : b ∈ B) : b ∈ B.hereditaryLeftIdeal :=
  B.mem_hereditaryLeftIdeal.mpr (mul_mem (star_mem hb) hb)

/-- The underlying set of `B` is contained in `B.hereditaryLeftIdeal`. -/
theorem subset_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected] :
    (B : Set A) ⊆ B.hereditaryLeftIdeal :=
  fun _ ↦ B.mem_hereditaryLeftIdeal_of_mem

/-- `NonUnitalStarSubalgebra.hereditaryLeftIdeal` is monotone with respect to inclusion. -/
theorem hereditaryLeftIdeal_mono {B₁ B₂ : NonUnitalStarSubalgebra ℂ A} [(B₁ : Set A).OrdConnected]
    [(B₂ : Set A).OrdConnected] (h : B₁ ≤ B₂) :
    B₁.hereditaryLeftIdeal ≤ B₂.hereditaryLeftIdeal :=
  fun _ hx ↦ h hx

/-- Polarization: if `x` and `y` belong to `B.hereditaryLeftIdeal`, then `star x * y ∈ B`. -/
theorem star_mul_mem_of_mem_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A)
    [(B : Set A).OrdConnected] {x y : A}
    (hx : x ∈ B.hereditaryLeftIdeal) (hy : y ∈ B.hereditaryLeftIdeal) :
    star x * y ∈ B := by
  have hpol : star x * y = (4 : ℂ)⁻¹ • (star (x + y) * (x + y) - star (x - y) * (x - y) -
      I • (star (x + I • y) * (x + I • y)) + I • (star (x - I • y) * (x - I • y))) := by
    simp only [star_add, star_sub, star_smul, star_def, conj_I, mul_add, add_mul, mul_sub, sub_mul,
      neg_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, neg_smul, smul_neg,
      smul_smul, I_mul_I]
    module
  rw [hpol]
  refine SMulMemClass.smul_mem (4 : ℂ)⁻¹ (add_mem (sub_mem (sub_mem ?_ ?_) ?_) ?_)
  · exact B.mem_hereditaryLeftIdeal.mp (B.hereditaryLeftIdeal.add_mem hx hy)
  · exact B.mem_hereditaryLeftIdeal.mp (B.hereditaryLeftIdeal.sub_mem hx hy)
  · exact SMulMemClass.smul_mem I (B.mem_hereditaryLeftIdeal.mp
      (B.hereditaryLeftIdeal.add_mem hx (B.hereditaryLeftIdeal.smul_mem I hy)))
  · exact SMulMemClass.smul_mem I (B.mem_hereditaryLeftIdeal.mp
      (B.hereditaryLeftIdeal.sub_mem hx (B.hereditaryLeftIdeal.smul_mem I hy)))

/-- Every order-connected nonunital ⋆-subalgebra `B` satisfies the sandwich property
`b₁ * a * b₂ ∈ B` for all `b₁, b₂ ∈ B` and `a : A`. -/
theorem mul_mul_mem (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected] {b₁ : A}
    (hb₁ : b₁ ∈ B) (a : A) {b₂ : A} (hb₂ : b₂ ∈ B) : b₁ * a * b₂ ∈ B := by
  have h1 : star b₁ ∈ B.hereditaryLeftIdeal := B.mem_hereditaryLeftIdeal_of_mem (star_mem hb₁)
  have h2 : a * b₂ ∈ B.hereditaryLeftIdeal :=
    B.mul_mem_hereditaryLeftIdeal a (B.mem_hereditaryLeftIdeal_of_mem hb₂)
  simpa only [star_star, mul_assoc] using B.star_mul_mem_of_mem_hereditaryLeftIdeal h1 h2

/-- If `a` is self-adjoint and `a * a` lies in a closed hereditary C⋆-subalgebra `B`, then `a ∈ B`.
-/
theorem mem_of_isSelfAdjoint_of_mul_self_mem (B : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [hB : (B : Set A).OrdConnected] {a : A} (ha : IsSelfAdjoint a)
    (ha2 : a * a ∈ B) : a ∈ B := by
  have hsq : a * a = a⁺ * a⁺ + a⁻ * a⁻ := by
    conv_lhs => rw [← CFC.posPart_sub_negPart a ha]
    simp only [sub_mul, mul_sub, CFC.posPart_mul_negPart, CFC.negPart_mul_posPart,
      sub_zero, zero_sub, sub_neg_eq_add]
  have hp_nonneg : 0 ≤ a⁺ * a⁺ := by
    simpa only [(CFC.posPart_nonneg a).isSelfAdjoint.star_eq] using star_mul_self_nonneg a⁺
  have hn_nonneg : 0 ≤ a⁻ * a⁻ := by
    simpa only [(CFC.negPart_nonneg a).isSelfAdjoint.star_eq] using star_mul_self_nonneg a⁻
  have hp_sq : a⁺ * a⁺ ∈ B :=
    hB.out (zero_mem B) ha2 ⟨hp_nonneg, hsq ▸ le_add_of_nonneg_right hn_nonneg⟩
  have hn_sq : a⁻ * a⁻ ∈ B :=
    hB.out (zero_mem B) ha2 ⟨hn_nonneg, hsq ▸ le_add_of_nonneg_left hp_nonneg⟩
  have hp : a⁺ ∈ B :=
    ((ProperCone.mul_self_mem_iff_of_nonneg B.positiveCone (CFC.posPart_nonneg a)).mp
      ⟨hp_sq, hp_nonneg⟩).1
  have hn : a⁻ ∈ B :=
    ((ProperCone.mul_self_mem_iff_of_nonneg B.positiveCone (CFC.negPart_nonneg a)).mp
      ⟨hn_sq, hn_nonneg⟩).1
  rw [← CFC.posPart_sub_negPart a ha]
  exact sub_mem hp hn

/-- Recovering a closed hereditary C⋆-subalgebra `B` as the self-adjoint core of
`B.hereditaryLeftIdeal`. -/
@[simp]
theorem starCore_hereditaryLeftIdeal (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)]
    [(B : Set A).OrdConnected] :
    B.hereditaryLeftIdeal.starCore B.mul_mem_hereditaryLeftIdeal = B := by
  ext x
  rw [Submodule.mem_starCore]
  refine ⟨fun ⟨hx1, hx2⟩ ↦ ?_, fun hx ↦ ⟨B.mem_hereditaryLeftIdeal_of_mem hx,
    B.mem_hereditaryLeftIdeal_of_mem (star_mem hx)⟩⟩
  have hu_mem : (ℜ x : A) ∈ B.hereditaryLeftIdeal := by
    rw [realPart_apply_coe]
    exact B.hereditaryLeftIdeal.smul_of_tower_mem (2 : ℝ)⁻¹
      (B.hereditaryLeftIdeal.add_mem hx1 hx2)
  have hv_mem : (ℑ x : A) ∈ B.hereditaryLeftIdeal := by
    rw [imaginaryPart_apply_coe]
    exact B.hereditaryLeftIdeal.smul_mem (-I)
      (B.hereditaryLeftIdeal.smul_of_tower_mem (2 : ℝ)⁻¹
        (B.hereditaryLeftIdeal.sub_mem hx1 hx2))
  have hu_sq : (ℜ x : A) * (ℜ x : A) ∈ B := by
    simpa only [(ℜ x).prop.star_eq] using B.mem_hereditaryLeftIdeal.mp hu_mem
  have hv_sq : (ℑ x : A) * (ℑ x : A) ∈ B := by
    simpa only [(ℑ x).prop.star_eq] using B.mem_hereditaryLeftIdeal.mp hv_mem
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem (B.mem_of_isSelfAdjoint_of_mul_self_mem (ℜ x).prop hu_sq)
    (SMulMemClass.smul_mem I (B.mem_of_isSelfAdjoint_of_mul_self_mem (ℑ x).prop hv_sq))

/-- Recovering a closed complex left ideal `L` as the hereditary left ideal of its self-adjoint
core `L.starCore hL`. -/
@[simp]
theorem hereditaryLeftIdeal_starCore (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    [IsClosed (L : Set A)] :
    (L.starCore hL).hereditaryLeftIdeal = L := by
  ext x
  simp only [mem_hereditaryLeftIdeal, L.star_mul_self_mem_starCore_iff hL]

/-- A closed nonunital ⋆-subalgebra `B` of a C⋆-algebra is hereditary if and only if
`b * a * star b ∈ B` for all `b ∈ B` and `a : A`. -/
theorem ordConnected_iff_mul_mul_star_mem (B : NonUnitalStarSubalgebra ℂ A)
    [hB : IsClosed (B : Set A)] :
    (B : Set A).OrdConnected ↔ ∀ ⦃b : A⦄, b ∈ B → ∀ a : A, b * a * star b ∈ B := by
  refine ⟨fun _ b hb a ↦ B.mul_mul_mem hb a (star_mem hb), fun h ↦ ?_⟩
  rw [AddSubgroupClass.ordConnected_iff]
  intro x y hx hxy hy
  let l : Filter B := CStarAlgebra.approximateUnit B
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit B
  refine hB.mem_of_tendsto (hl.tendsto_mul_mul_of_nonneg_of_le hx hxy hy) ?_
  filter_upwards [hl.eventually_star_eq] with e he_star
  have he_coe : star (e : A) = (e : A) := by
    simpa only [StarMemClass.coe_star] using congrArg ((↑) : B → A) he_star
  have hmem : (e : A) * x * star (e : A) ∈ B := h e.2 x
  rwa [he_coe] at hmem

/-- A closed nonunital ⋆-subalgebra `B` of a C⋆-algebra is hereditary if and only if
`b₁ * a * b₂ ∈ B` for all `b₁, b₂ ∈ B` and `a : A`. -/
theorem ordConnected_iff_mul_mul_mem (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)] :
    (B : Set A).OrdConnected ↔ ∀ ⦃b₁ : A⦄, b₁ ∈ B → ∀ (a : A) ⦃b₂ : A⦄, b₂ ∈ B → b₁ * a * b₂ ∈ B :=
  ⟨fun _ _ hb₁ a _ hb₂ ↦ B.mul_mul_mem hb₁ a hb₂,
    fun h ↦ B.ordConnected_iff_mul_mul_star_mem.mpr fun _ hb a ↦ h hb a (star_mem hb)⟩

/-! #### Cohen–Hewitt factorization for `{x : A | star x * x ∈ B}` -/

/-- By right-module Cohen–Hewitt factorization, if `B` is a closed nonunital ⋆-subalgebra of `A` and
`star x * x ∈ B`, then `x` factors as `y * b` with `b ∈ B`, `‖b‖ ≤ 1`, `y` in the closure of
`x · B`, and `‖y - x‖ < ε`. -/
theorem exists_mul_eq_of_star_mul_self_mem (B : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (B : Set A)] {x : A} (hx : star x * x ∈ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : A, ∃ b ∈ B, ‖b‖ ≤ 1 ∧ y ∈ closure (Set.range fun c : B ↦ x * (c : A)) ∧
      ‖y - x‖ < ε ∧ y * b = x := by
  let R : A →L[ℂ] B →L[ℂ] A :=
    ((ContinuousLinearMap.mul ℂ A).flip.comp (Submodule.ofClass B).subtypeL).flip
  have hR_apply (y : A) (b : B) : R y b = y * (b : A) := rfl
  have hR : ∀ y (b₁ b₂ : B), R (R y b₁) b₂ = R y (b₁ * b₂) := fun y b₁ b₂ ↦ by
    rw [hR_apply, hR_apply, hR_apply, MulMemClass.coe_mul, mul_assoc]
  let l : Filter B := CStarAlgebra.approximateUnit B
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit B
  have hx_mem :
      x ∈ (Submodule.span ℂ (Set.range fun p : A × B ↦ R p.1 p.2)).topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine mem_closure_of_tendsto (hl.tendsto_mul_left_of_star_mul_self_mem hx)
      (Eventually.of_forall fun e ↦ Submodule.subset_span ⟨(x, e), ?_⟩)
    exact hR_apply x e
  obtain ⟨b, y, hb_norm, hy_mem, hy_dist, hyb⟩ :=
    ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span_right R hR
      hl.eventually_norm hl.tendsto_mul_left hx_mem hε
  rw [AddSubgroupClass.coe_norm] at hb_norm
  simp_rw [hR_apply] at hy_mem hyb
  exact ⟨y, b, b.2, hb_norm, hy_mem, hy_dist, hyb⟩

/-- For a closed hereditary C⋆-subalgebra `B`, the associated closed complex left ideal
`{x : A | star x * x ∈ B}` coincides with the set of products `A * B`. -/
theorem coe_hereditaryLeftIdeal_eq_range_mul (B : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [(B : Set A).OrdConnected] :
    (B.hereditaryLeftIdeal : Set A) = Set.range fun p : A × B ↦ p.1 * (p.2 : A) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨y, b, hb, -, -, -, rfl⟩ :=
      B.exists_mul_eq_of_star_mul_self_mem (B.mem_hereditaryLeftIdeal.mp hx) zero_lt_one
    exact ⟨(y, ⟨b, hb⟩), rfl⟩
  · rintro ⟨⟨y, b⟩, rfl⟩
    exact B.mul_mem_hereditaryLeftIdeal y (B.mem_hereditaryLeftIdeal_of_mem b.2)

end Hereditary

end NonUnitalStarSubalgebra

namespace ProperCone

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Recovering an order-connected proper subcone `C ≤ ProperCone.positive ℝ A` as the positive cone
of the self-adjoint core of `C.hereditaryLeftIdeal`. -/
@[simp]
theorem positiveCone_starCore_hereditaryLeftIdeal (C : ProperCone ℝ A)
    (hC_pos : C ≤ ProperCone.positive ℝ A) [(C : Set A).OrdConnected] :
    (C.hereditaryLeftIdeal.starCore C.mul_mem_hereditaryLeftIdeal).positiveCone = C := by
  ext a
  simp only [NonUnitalStarSubalgebra.mem_positiveCone, Submodule.mem_starCore,
    ProperCone.mem_hereditaryLeftIdeal]
  refine ⟨fun ⟨⟨ha1, _⟩, ha_nonneg⟩ ↦ ?_, fun haC ↦ ?_⟩
  · rw [ha_nonneg.isSelfAdjoint.star_eq] at ha1
    exact (C.mul_self_mem_iff_of_nonneg ha_nonneg).mp ha1
  · have ha_nonneg : 0 ≤ a := ProperCone.mem_positive.mp (hC_pos haC)
    have ha2 : a * a ∈ C := (C.mul_self_mem_iff_of_nonneg ha_nonneg).mpr haC
    rw [star_star, ha_nonneg.isSelfAdjoint.star_eq]
    exact ⟨⟨ha2, ha2⟩, ha_nonneg⟩

end ProperCone

/-! ### Closed ideal correspondence for order-connected ⋆-subalgebras -/

namespace NonUnitalStarSubalgebra

section ClosedIdealCorrespondence

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private lemma exists_seq_mul_left_tendsto (B : NonUnitalStarSubalgebra ℂ A)
    [hB : (B : Set A).OrdConnected] (b : B) :
    ∃ u : ℕ → B, (∀ n, ‖(u n : A)‖ ≤ 1) ∧
      Tendsto (fun n ↦ (b : A) * (u n : A)) atTop (𝓝 (b : A)) := by
  let x : A := star (b : A) * (b : A)
  have hx₀ : 0 ≤ x := star_mul_self_nonneg (b : A)
  have hx_sa : IsSelfAdjoint x := hx₀.isSelfAdjoint
  let g : ℕ → ℝ → ℝ := fun n t ↦ min (((n : ℝ) + 1) * max t 0) 1
  have hg : ∀ n, Continuous (g n) := fun n ↦ by fun_prop
  have hu₀ : ∀ n, 0 ≤ cfcₙ (g n) x := fun n ↦
    cfcₙ_nonneg fun _ _ ↦ le_min (by positivity) zero_le_one
  have hu₁ : ∀ n, ‖cfcₙ (g n) x‖ ≤ 1 := fun n ↦ norm_cfcₙ_le fun _ _ ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) zero_le_one)]
    exact min_le_right _ _
  have huB : ∀ n, cfcₙ (g n) x ∈ B := fun n ↦ by
    have hrhs : ((n : ℝ) + 1) • x = cfcₙ (fun t : ℝ ↦ ((n : ℝ) + 1) • t) x := by
      symm
      rw [cfcₙ_smul ((n : ℝ) + 1) (fun t : ℝ ↦ t) x (hf := continuousOn_id) (h0 := rfl),
        cfcₙ_id' ℝ x]
    have hle : cfcₙ (g n) x ≤ ((n : ℝ) + 1) • x := by
      rw [hrhs]
      refine cfcₙ_mono (hf := (hg n).continuousOn) (hf0 := by simp [g])
        (hg := Continuous.continuousOn (by fun_prop)) (hg0 := smul_zero _) fun t ht ↦ ?_
      dsimp only [g, smul_eq_mul]
      rw [max_eq_left (quasispectrum_nonneg_of_nonneg x hx₀ t ht)]
      exact min_le_left _ _
    exact hB.out (zero_mem B)
      ((SMulMemClass.ofIsScalarTower _ ℝ ℂ A).smul_mem _ (mul_mem (star_mem b.2) b.2))
      ⟨hu₀ n, hle⟩
  refine ⟨fun n ↦ ⟨cfcₙ (g n) x, huB n⟩, hu₁, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, one_div, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_) hsqrt
  rw [Real.norm_of_nonneg (norm_nonneg _), ← norm_star ((b : A) * cfcₙ (g n) x - (b : A)),
    star_sub, star_mul, (hu₀ n).isSelfAdjoint.star_eq]
  exact Real.le_sqrt_of_sq_le
    ((TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le (hu₀ n) (hu₁ n) (b : A)).trans
      (TauCeti.CStarAlgebra.norm_sub_cfcₙ_min_mul_le hx₀ n))

private lemma exists_seq_mul_tendsto (B : NonUnitalStarSubalgebra ℂ A)
    [(B : Set A).OrdConnected] (b : B) :
    ∃ uL uR : ℕ → B, (∀ n, ‖(uL n : A)‖ ≤ 1) ∧ (∀ n, ‖(uR n : A)‖ ≤ 1) ∧
      Tendsto (fun n ↦ (uL n : A) * (b : A)) atTop (𝓝 (b : A)) ∧
      Tendsto (fun n ↦ (b : A) * (uR n : A)) atTop (𝓝 (b : A)) ∧
      Tendsto (fun n ↦ (uL n : A) * (b : A) * (uR n : A)) atTop (𝓝 (b : A)) := by
  obtain ⟨uR, huR₁, huR_lim⟩ := B.exists_seq_mul_left_tendsto b
  obtain ⟨v, hv₁, hv_lim⟩ := B.exists_seq_mul_left_tendsto (star b)
  let uL : ℕ → B := fun n ↦ star (v n)
  have huL₁ : ∀ n, ‖(uL n : A)‖ ≤ 1 := fun n ↦ by
    rw [StarMemClass.coe_star, norm_star]
    exact hv₁ n
  have huL_lim : Tendsto (fun n ↦ (uL n : A) * (b : A)) atTop (𝓝 (b : A)) := by
    have hv_coe : Tendsto (fun n ↦ star (b : A) * (v n : A)) atTop (𝓝 (star (b : A))) := by
      simpa only [StarMemClass.coe_star] using hv_lim
    simpa only [uL, StarMemClass.coe_star, star_mul, star_star, Function.comp_def] using
      (continuous_star.tendsto (star (b : A))).comp hv_coe
  exact ⟨uL, uR, huL₁, huR₁, huL_lim, huR_lim,
    TauCeti.tendsto_mul_mul_of_tendsto (Eventually.of_forall huL₁) (Eventually.of_forall huR₁)
      tendsto_const_nhds huL_lim huR_lim⟩

private lemma mul_mul_coe_mem_ideal (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    (K : TwoSidedIdeal B) [hK : IsClosed (K : Set B)] {k : B} (hk : k ∈ K)
    (b₁ b₂ : B) (a c : A) :
    (⟨(b₁ : A) * (a * (k : A) * c) * (b₂ : A), B.mul_mul_mem b₁.2 _ b₂.2⟩ : B) ∈ K := by
  obtain ⟨uL, uR, -, -, -, -, hlimA⟩ := B.exists_seq_mul_tendsto k
  let g : A → B := fun z ↦
    ⟨(b₁ : A) * (a * z * c) * (b₂ : A), B.mul_mul_mem b₁.2 (a * z * c) b₂.2⟩
  have hg : Continuous g := Continuous.subtype_mk (by fun_prop) _
  refine hK.mem_of_tendsto ((hg.tendsto (k : A)).comp hlimA) (Eventually.of_forall fun n ↦ ?_)
  have hfac : g ((uL n : A) * (k : A) * (uR n : A)) =
      ⟨(b₁ : A) * a * (uL n : A), B.mul_mul_mem b₁.2 a (uL n).2⟩ * k *
        ⟨(uR n : A) * c * (b₂ : A), B.mul_mul_mem (uR n).2 c b₂.2⟩ := by
    ext
    simp only [g, MulMemClass.coe_mul, mul_assoc]
  dsimp only [Function.comp_def]
  rw [hfac]
  exact K.mul_mem_right _ _ (K.mul_mem_left _ _ hk)

private lemma mul_mul_mem_of_mem_extendIdeal (B : NonUnitalStarSubalgebra ℂ A)
    [(B : Set A).OrdConnected] (K : TwoSidedIdeal B) [hK : IsClosed (K : Set B)] {y : A}
    (hy : y ∈ B.extendIdeal K) (b₁ b₂ : B) (a c : A) :
    (⟨(b₁ : A) * (a * y * c) * (b₂ : A), B.mul_mul_mem b₁.2 (a * y * c) b₂.2⟩ : B) ∈ K := by
  let g : B → B → A → A → A → B := fun b₁ b₂ a c z ↦
    ⟨(b₁ : A) * (a * z * c) * (b₂ : A), B.mul_mul_mem b₁.2 (a * z * c) b₂.2⟩
  have hspan {z : A} (hz : z ∈ K.map (NonUnitalStarSubalgebraClass.subtype B)) :
      ∀ (b₁ b₂ : B) (a c : A), g b₁ b₂ a c z ∈ K := by
    rw [TwoSidedIdeal.map] at hz
    refine TwoSidedIdeal.span_induction
      (p := fun z _ ↦ ∀ (b₁ b₂ : B) (a c : A), g b₁ b₂ a c z ∈ K)
      (fun _ hk b₁ b₂ a c ↦ ?_)
      (fun b₁ b₂ a c ↦ ?_)
      (fun x w _ _ hx hw b₁ b₂ a c ↦ ?_)
      (fun x _ hx b₁ b₂ a c ↦ ?_)
      (fun d x _ hx b₁ b₂ a c ↦ by simpa only [g, mul_assoc] using hx b₁ b₂ (a * d) c)
      (fun d x _ hx b₁ b₂ a c ↦ by simpa only [g, mul_assoc] using hx b₁ b₂ a (d * c))
      hz
    · rcases hk with ⟨k, hk, rfl⟩
      exact B.mul_mul_coe_mem_ideal K hk b₁ b₂ a c
    · convert K.zero_mem
      ext
      simp only [g, ZeroMemClass.coe_zero, mul_zero, zero_mul]
    · convert K.add_mem (hx b₁ b₂ a c) (hw b₁ b₂ a c)
      ext
      simp only [g, AddMemClass.coe_add]
      noncomm_ring
    · convert K.neg_mem (hx b₁ b₂ a c)
      ext
      simp only [g, NegMemClass.coe_neg, mul_neg, neg_mul]
  rw [B.extendIdeal_def, TwoSidedIdeal.mem_topologicalClosure] at hy
  have hmaps : Set.MapsTo (g b₁ b₂ a c)
      (K.map (NonUnitalStarSubalgebraClass.subtype B) : Set A) (K : Set B) :=
    fun z hz ↦ hspan hz b₁ b₂ a c
  exact hmaps.closure_left (Continuous.subtype_mk (by fun_prop) _) hK hy

/-- For an order-connected nonunital ⋆-subalgebra `B` and a closed two-sided ideal `K` of `B`,
restricting `B.extendIdeal K` back to `B` recovers `K`. -/
@[simp]
theorem comap_subtype_extendIdeal (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    (K : TwoSidedIdeal B) [hK : IsClosed (K : Set B)] :
    (B.extendIdeal K).comap (NonUnitalStarSubalgebraClass.subtype B) = K := by
  ext b
  rw [TwoSidedIdeal.mem_comap]
  refine ⟨fun hb ↦ ?_, fun hb ↦ B.coe_mem_extendIdeal K hb⟩
  obtain ⟨uL, uR, huL₁, huR₁, huL_lim, huR_lim, hinner⟩ := B.exists_seq_mul_tendsto b
  have hlimB : Tendsto (fun n ↦ uL n * (uL n * b * uR n) * uR n) atTop (𝓝 b) :=
    tendsto_subtype_rng.mpr <| by
      simpa only [MulMemClass.coe_mul] using
        TauCeti.tendsto_mul_mul_of_tendsto (Eventually.of_forall huL₁) (Eventually.of_forall huR₁)
          hinner huL_lim huR_lim
  exact hK.mem_of_tendsto hlimB (Eventually.of_forall fun n ↦
    B.mul_mul_mem_of_mem_extendIdeal K hb (uL n) (uR n) (uL n : A) (uR n : A))

private lemma closedIdeal_mul_ideal_mul_closedIdeal_mem_extendIdeal_comap
    (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    (J : TwoSidedIdeal A) {u j w : A} (hu : u ∈ B.closedIdeal) (hj : j ∈ J)
    (hw : w ∈ B.closedIdeal) :
    u * j * w ∈ B.extendIdeal (J.comap (NonUnitalStarSubalgebraClass.subtype B)) := by
  let E : TwoSidedIdeal A := B.extendIdeal (J.comap (NonUnitalStarSubalgebraClass.subtype B))
  have hleft {u' : A} (hu' : u' ∈ TwoSidedIdeal.span (B : Set A)) (b : B) :
      ∀ ⦃j' : A⦄, j' ∈ J → u' * j' * (b : A) ∈ E := by
    refine TwoSidedIdeal.span_induction
      (p := fun u' _ ↦ ∀ ⦃j' : A⦄, j' ∈ J → u' * j' * (b : A) ∈ E)
      (fun b₁ hb₁ j' hj' ↦ ?_)
      (fun _ _ ↦ by simpa only [zero_mul] using E.zero_mem)
      (fun x y _ _ hx hy j' hj' ↦ by
        rw [show (x + y) * j' * (b : A) = x * j' * (b : A) + y * j' * (b : A) by noncomm_ring]
        exact E.add_mem (hx hj') (hy hj'))
      (fun x _ hx j' hj' ↦ by simpa only [neg_mul] using E.neg_mem (hx hj'))
      (fun d x _ hx j' hj' ↦ by simpa only [mul_assoc] using E.mul_mem_left d _ (hx hj'))
      (fun d x _ hx j' hj' ↦ by simpa only [mul_assoc] using hx (J.mul_mem_left d j' hj'))
      hu'
    exact B.coe_mem_extendIdeal (J.comap (NonUnitalStarSubalgebraClass.subtype B))
      (k := ⟨b₁ * j' * (b : A), B.mul_mul_mem hb₁ j' b.2⟩)
      ((TwoSidedIdeal.mem_comap _).mpr (J.mul_mem_right _ _ (J.mul_mem_left _ _ hj')))
  have hboth {w' : A} (hw' : w' ∈ TwoSidedIdeal.span (B : Set A))
      {u' : A} (hu' : u' ∈ TwoSidedIdeal.span (B : Set A)) :
      ∀ ⦃j' : A⦄, j' ∈ J → u' * j' * w' ∈ E :=
    TwoSidedIdeal.span_induction
      (p := fun w' _ ↦ ∀ ⦃j' : A⦄, j' ∈ J → u' * j' * w' ∈ E)
      (fun b₂ hb₂ j' hj' ↦ hleft hu' ⟨b₂, hb₂⟩ hj')
      (fun _ _ ↦ by simpa only [mul_zero] using E.zero_mem)
      (fun x y _ _ hx hy j' hj' ↦ by rw [mul_add]; exact E.add_mem (hx hj') (hy hj'))
      (fun x _ hx j' hj' ↦ by simpa only [mul_neg] using E.neg_mem (hx hj'))
      (fun d x _ hx j' hj' ↦ by
        rw [show u' * j' * (d * x) = u' * (j' * d) * x by simp only [mul_assoc]]
        exact hx (J.mul_mem_right j' d hj'))
      (fun d x _ hx j' hj' ↦ by rw [← mul_assoc]; exact E.mul_mem_right _ d (hx hj'))
      hw'
  rw [B.closedIdeal_def, TwoSidedIdeal.mem_topologicalClosure] at hu hw
  rw [← SetLike.mem_coe, ← (B.isClosed_extendIdeal _).closure_eq]
  exact map_mem_closure₂ (f := fun x y : A ↦ x * j * y) (by fun_prop) hu hw
    fun x hx y hy ↦ hboth hy hx hj

/-- For an order-connected nonunital ⋆-subalgebra `B` and a closed two-sided ideal `J` of `A`
contained in `B.closedIdeal`, extending `J ∩ B` back to `A` recovers `J`. -/
theorem extendIdeal_comap_subtype (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    {J : TwoSidedIdeal A} [IsClosed (J : Set A)] (hJB : J ≤ B.closedIdeal) :
    B.extendIdeal (J.comap (NonUnitalStarSubalgebraClass.subtype B)) = J := by
  refine le_antisymm ((B.extendIdeal_le_iff _ J).mpr le_rfl) fun j hj ↦ ?_
  let S := J.toNonUnitalStarSubalgebra
  let jS : S := ⟨j, J.mem_toNonUnitalStarSubalgebra.mpr hj⟩
  let l : Filter S := CStarAlgebra.approximateUnit S
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit S
  have hlim : Tendsto (fun v : S ↦ (v : A) * j * (v : A)) l (𝓝 j) := by
    refine ((continuous_subtype_val.tendsto jS).comp (hl.tendsto_mul_mul jS)).congr fun v ↦ ?_
    simp only [Function.comp_def, MulMemClass.coe_mul]
    rfl
  refine (B.isClosed_extendIdeal _).mem_of_tendsto hlim (Eventually.of_forall fun v ↦ ?_)
  have hvB : (v : A) ∈ B.closedIdeal := hJB (J.mem_toNonUnitalStarSubalgebra.mp v.2)
  exact B.closedIdeal_mul_ideal_mul_closedIdeal_mem_extendIdeal_comap J hvB hj hvB

/-- For an order-connected nonunital ⋆-subalgebra `B` of `A`, restriction `J ↦ J ∩ B` and extension
`K ↦ (K.map (NonUnitalStarSubalgebraClass.subtype B)).topologicalClosure` form an order isomorphism
between closed two-sided ideals of `A` contained in `B.closedIdeal` and closed two-sided ideals of
`B`. -/
def closedIdealOrderIso (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected] :
    {J : TwoSidedIdeal A // IsClosed (J : Set A) ∧ J ≤ B.closedIdeal} ≃o
      {K : TwoSidedIdeal B // IsClosed (K : Set B)} where
  toFun := fun ⟨J, hJc, _⟩ ↦
    haveI : IsClosed (J : Set A) := hJc
    ⟨J.comap (NonUnitalStarSubalgebraClass.subtype B), B.isClosed_comap_subtype J⟩
  invFun := fun ⟨K, _⟩ ↦
    ⟨B.extendIdeal K, B.isClosed_extendIdeal K, B.extendIdeal_le_closedIdeal K⟩
  left_inv := fun ⟨J, hJc, hJle⟩ ↦ by
    have : IsClosed (J : Set A) := hJc
    exact Subtype.ext (B.extendIdeal_comap_subtype hJle)
  right_inv := fun ⟨K, hKc⟩ ↦ by
    have : IsClosed (K : Set B) := hKc
    exact Subtype.ext (B.comap_subtype_extendIdeal K)
  map_rel_iff' := fun {J₁ J₂} ↦ by
    obtain ⟨J₁, hJ₁c, hJ₁le⟩ := J₁
    obtain ⟨J₂, hJ₂c, hJ₂le⟩ := J₂
    have : IsClosed (J₁ : Set A) := hJ₁c
    have : IsClosed (J₂ : Set A) := hJ₂c
    refine ⟨fun h ↦ ?_, fun h _ hx ↦
      (TwoSidedIdeal.mem_comap _).mpr (h ((TwoSidedIdeal.mem_comap _).mp hx))⟩
    rw [Subtype.mk_le_mk] at h ⊢
    rw [← B.extendIdeal_comap_subtype hJ₁le, ← B.extendIdeal_comap_subtype hJ₂le]
    exact B.extendIdeal_mono h

@[simp]
theorem coe_closedIdealOrderIso_apply (B : NonUnitalStarSubalgebra ℂ A) [(B : Set A).OrdConnected]
    (J : {J : TwoSidedIdeal A // IsClosed (J : Set A) ∧ J ≤ B.closedIdeal}) :
    (B.closedIdealOrderIso J).1 = J.1.comap (NonUnitalStarSubalgebraClass.subtype B) :=
  (rfl)

@[simp]
theorem coe_closedIdealOrderIso_symm_apply (B : NonUnitalStarSubalgebra ℂ A)
    [(B : Set A).OrdConnected] (K : {K : TwoSidedIdeal B // IsClosed (K : Set B)}) :
    (B.closedIdealOrderIso.symm K).1 = B.extendIdeal K.1 :=
  (rfl)

end ClosedIdealCorrespondence

end NonUnitalStarSubalgebra

/-! ### Order isomorphisms, generated hereditary subalgebras, and strict positivity -/

namespace TauCeti.CStarAlgebra

section OrderIsoCorrespondences

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Order isomorphism between closed hereditary C⋆-subalgebras of `A` and closed complex left ideals
of `A`, sending `B` to `B.hereditaryLeftIdeal = {x : A | star x * x ∈ B}` and `L` to
`L.starCore = L ∩ star ⁻¹' L`. -/
def hereditarySubalgebraLeftIdealOrderIso :
    {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected} ≃o
      {L : Submodule ℂ A // IsClosed (L : Set A) ∧ ∀ a : A, ∀ x ∈ L, a * x ∈ L} where
  toFun B :=
    haveI : IsClosed (B.1 : Set A) := B.2.1
    haveI : (B.1 : Set A).OrdConnected := B.2.2
    ⟨B.1.hereditaryLeftIdeal, B.1.isClosed_hereditaryLeftIdeal, B.1.mul_mem_hereditaryLeftIdeal⟩
  invFun L :=
    haveI : IsClosed (L.1 : Set A) := L.2.1
    ⟨L.1.starCore L.2.2, L.1.isClosed_starCore L.2.2, L.1.ordConnected_starCore L.2.2⟩
  left_inv B := by
    have : IsClosed (B.1 : Set A) := B.2.1
    have : (B.1 : Set A).OrdConnected := B.2.2
    exact Subtype.ext B.1.starCore_hereditaryLeftIdeal
  right_inv L := by
    have : IsClosed (L.1 : Set A) := L.2.1
    exact Subtype.ext (NonUnitalStarSubalgebra.hereditaryLeftIdeal_starCore L.1 L.2.2)
  map_rel_iff' {B₁ B₂} := by
    have : IsClosed (B₁.1 : Set A) := B₁.2.1
    have : (B₁.1 : Set A).OrdConnected := B₁.2.2
    have : IsClosed (B₂.1 : Set A) := B₂.2.1
    have : (B₂.1 : Set A).OrdConnected := B₂.2.2
    refine ⟨fun h ↦ ?_, fun h ↦ B₁.1.hereditaryLeftIdeal_mono h⟩
    rw [Subtype.mk_le_mk] at h ⊢
    rw [← B₁.1.starCore_hereditaryLeftIdeal, ← B₂.1.starCore_hereditaryLeftIdeal]
    exact Submodule.starCore_mono h

@[simp]
theorem coe_hereditarySubalgebraLeftIdealOrderIso_apply
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected}) :
    (hereditarySubalgebraLeftIdealOrderIso B).1 = B.1.hereditaryLeftIdeal (hB := B.2.2) :=
  (rfl)

@[simp]
theorem coe_hereditarySubalgebraLeftIdealOrderIso_symm_apply
    (L : {L : Submodule ℂ A // IsClosed (L : Set A) ∧ ∀ a : A, ∀ x ∈ L, a * x ∈ L}) :
    (hereditarySubalgebraLeftIdealOrderIso.symm L).1 = L.1.starCore L.2.2 :=
  (rfl)

/-- Order isomorphism between closed hereditary C⋆-subalgebras of `A` and closed order-connected
proper subcones of `ProperCone.positive ℝ A`, sending `B` to `B.positiveCone = {a ∈ B | 0 ≤ a}`. -/
def hereditarySubalgebraPositiveConeOrderIso :
    {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected} ≃o
      {C : ProperCone ℝ A // C ≤ ProperCone.positive ℝ A ∧ (C : Set A).OrdConnected} where
  toFun B :=
    haveI : IsClosed (B.1 : Set A) := B.2.1
    haveI : (B.1 : Set A).OrdConnected := B.2.2
    ⟨B.1.positiveCone, B.1.positiveCone_le_positive, B.1.ordConnected_positiveCone⟩
  invFun C :=
    haveI : (C.1 : Set A).OrdConnected := C.2.2
    ⟨C.1.hereditaryLeftIdeal.starCore C.1.mul_mem_hereditaryLeftIdeal,
      C.1.hereditaryLeftIdeal.isClosed_starCore C.1.mul_mem_hereditaryLeftIdeal,
      C.1.hereditaryLeftIdeal.ordConnected_starCore C.1.mul_mem_hereditaryLeftIdeal⟩
  left_inv B := by
    have : IsClosed (B.1 : Set A) := B.2.1
    have : (B.1 : Set A).OrdConnected := B.2.2
    have hEq :
        B.1.positiveCone.hereditaryLeftIdeal.starCore
          B.1.positiveCone.mul_mem_hereditaryLeftIdeal =
        B.1.hereditaryLeftIdeal.starCore B.1.mul_mem_hereditaryLeftIdeal := by
      ext x
      simp only [Submodule.mem_starCore, NonUnitalStarSubalgebra.hereditaryLeftIdeal_positiveCone]
    exact Subtype.ext (hEq.trans B.1.starCore_hereditaryLeftIdeal)
  right_inv C := by
    have : (C.1 : Set A).OrdConnected := C.2.2
    exact Subtype.ext (C.1.positiveCone_starCore_hereditaryLeftIdeal C.2.1)
  map_rel_iff' {B₁ B₂} := by
    have : IsClosed (B₁.1 : Set A) := B₁.2.1
    have : (B₁.1 : Set A).OrdConnected := B₁.2.2
    have : IsClosed (B₂.1 : Set A) := B₂.2.1
    have : (B₂.1 : Set A).OrdConnected := B₂.2.2
    refine ⟨fun h ↦ ?_, fun h ↦ B₁.1.positiveCone_mono h⟩
    rw [Subtype.mk_le_mk] at h ⊢
    rw [← B₁.1.starCore_hereditaryLeftIdeal, ← B₂.1.starCore_hereditaryLeftIdeal]
    have hL : B₁.1.hereditaryLeftIdeal ≤ B₂.1.hereditaryLeftIdeal := by
      rw [← B₁.1.hereditaryLeftIdeal_positiveCone, ← B₂.1.hereditaryLeftIdeal_positiveCone]
      exact ProperCone.hereditaryLeftIdeal_mono h
    exact Submodule.starCore_mono hL

@[simp]
theorem coe_hereditarySubalgebraPositiveConeOrderIso_apply
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected}) :
    (hereditarySubalgebraPositiveConeOrderIso B).1 = B.1.positiveCone (hB := B.2.1) :=
  (rfl)

@[simp]
theorem coe_hereditarySubalgebraPositiveConeOrderIso_symm_apply
    (C : {C : ProperCone ℝ A // C ≤ ProperCone.positive ℝ A ∧ (C : Set A).OrdConnected}) :
    (hereditarySubalgebraPositiveConeOrderIso.symm C).1 =
      (C.1.hereditaryLeftIdeal (hC := C.2.2)).starCore
        (C.1.mul_mem_hereditaryLeftIdeal (hC := C.2.2)) :=
  (rfl)

/-- Order isomorphism between closed complex left ideals of `A` and closed order-connected proper
subcones of `ProperCone.positive ℝ A`. -/
noncomputable def closedLeftIdealPositiveConeOrderIso :
    {L : Submodule ℂ A // IsClosed (L : Set A) ∧ ∀ a : A, ∀ x ∈ L, a * x ∈ L} ≃o
      {C : ProperCone ℝ A // C ≤ ProperCone.positive ℝ A ∧ (C : Set A).OrdConnected} :=
  hereditarySubalgebraLeftIdealOrderIso.symm.trans hereditarySubalgebraPositiveConeOrderIso

@[simp]
theorem coe_closedLeftIdealPositiveConeOrderIso_apply
    (L : {L : Submodule ℂ A // IsClosed (L : Set A) ∧ ∀ a : A, ∀ x ∈ L, a * x ∈ L}) :
    (closedLeftIdealPositiveConeOrderIso L).1 =
      (L.1.starCore L.2.2).positiveCone (hB := L.1.isClosed_starCore L.2.2 (hLc := L.2.1)) :=
  (rfl)

@[simp]
theorem coe_closedLeftIdealPositiveConeOrderIso_symm_apply
    (C : {C : ProperCone ℝ A // C ≤ ProperCone.positive ℝ A ∧ (C : Set A).OrdConnected}) :
    (closedLeftIdealPositiveConeOrderIso.symm C).1 = C.1.hereditaryLeftIdeal (hC := C.2.2) := by
  have : (C.1 : Set A).OrdConnected := C.2.2
  simp [closedLeftIdealPositiveConeOrderIso]

/-- In a unital C⋆-algebra `A`, closed hereditary C⋆-subalgebras correspond via an order isomorphism
to closed left ideals `Ideal A`. -/
noncomputable def hereditarySubalgebraClosedIdealOrderIso {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected} ≃o
      {I : Ideal A // IsClosed (I : Set A)} :=
  hereditarySubalgebraLeftIdealOrderIso.trans
    { toFun := fun L ↦
        ⟨{ carrier := L.1
           add_mem' := L.1.add_mem
           zero_mem' := L.1.zero_mem
           smul_mem' := fun a {x} hx ↦ L.2.2 a x hx }, L.2.1⟩
      invFun := fun I ↦
        ⟨I.1.restrictScalars ℂ, (Submodule.coe_restrictScalars (S := ℂ) I.1).symm ▸ I.2,
          fun a x hx ↦ (I.1.restrictScalars_mem ℂ _).mpr
            (I.1.mul_mem_left a ((I.1.restrictScalars_mem ℂ x).mp hx))⟩
      left_inv := fun _ ↦ Subtype.ext (Submodule.ext fun _ ↦ Iff.rfl)
      right_inv := fun I ↦ Subtype.ext (Submodule.ext fun x ↦ I.1.restrictScalars_mem ℂ x)
      map_rel_iff' := fun {_ _} ↦
        ⟨fun h _ hx ↦ h hx, fun h _ hx ↦ h hx⟩ }

@[simp]
theorem mem_coe_hereditarySubalgebraClosedIdealOrderIso_apply {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected})
    {x : A} :
    x ∈ (hereditarySubalgebraClosedIdealOrderIso B).1 ↔ star x * x ∈ B.1 :=
  Iff.rfl

@[simp]
theorem restrictScalars_coe_hereditarySubalgebraClosedIdealOrderIso_apply {A : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ (B : Set A).OrdConnected}) :
    ((hereditarySubalgebraClosedIdealOrderIso B).1).restrictScalars ℂ =
      B.1.hereditaryLeftIdeal (hB := B.2.2) :=
  (rfl)

@[simp]
theorem coe_hereditarySubalgebraClosedIdealOrderIso_symm_apply {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (I : {I : Ideal A // IsClosed (I : Set A)}) :
    (hereditarySubalgebraClosedIdealOrderIso.symm I).1 =
      (I.1.restrictScalars ℂ).starCore (fun a x hx ↦
        (I.1.restrictScalars_mem ℂ _).mpr
          (I.1.mul_mem_left a ((I.1.restrictScalars_mem ℂ x).mp hx))) :=
  (rfl)

end OrderIsoCorrespondences

section GeneratedHereditary

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The unclosed ⋆-subalgebra `{a * x * a | x : A}` associated to a self-adjoint element `a`. -/
private def hereditarySubalgebraRaw (a : A) (ha : IsSelfAdjoint a) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range fun x : A ↦ a * x * a
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * a * a * y, by simp only [mul_assoc]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  zero_mem' := ⟨0, by simp only [mul_zero, zero_mul]⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    refine ⟨c • x, ?_⟩
    dsimp only
    rw [mul_smul_comm, smul_mul_assoc]
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    refine ⟨star x, ?_⟩
    dsimp only
    rw [star_mul, star_mul, ha.star_eq, mul_assoc]

/-- The closed hereditary C⋆-subalgebra `closure {a * x * a | x : A}` generated by a self-adjoint
element `a` (in particular by any nonnegative element `0 ≤ a`). -/
def hereditarySubalgebra (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    NonUnitalStarSubalgebra ℂ A :=
  (hereditarySubalgebraRaw a ha).topologicalClosure

@[simp]
theorem coe_hereditarySubalgebra {a : A} {ha : IsSelfAdjoint a} :
    (hereditarySubalgebra a ha : Set A) = closure (Set.range fun x : A ↦ a * x * a) :=
  (rfl)

/-- Membership characterization for `hereditarySubalgebra a`: `x ∈ hereditarySubalgebra a` if and
only if `x` lies in `closure {a * y * a | y : A}`. -/
theorem mem_hereditarySubalgebra {a x : A} {ha : IsSelfAdjoint a} :
    x ∈ hereditarySubalgebra a ha ↔ x ∈ closure (Set.range fun y : A ↦ a * y * a) :=
  Iff.rfl

/-- Every sandwich product `a * x * a` belongs to `hereditarySubalgebra a`. -/
@[simp]
theorem mul_mul_mem_hereditarySubalgebra (a x : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a * x * a ∈ hereditarySubalgebra a ha :=
  mem_hereditarySubalgebra.mpr (subset_closure ⟨x, rfl⟩)

/-- `hereditarySubalgebra a` is closed in `A`. -/
instance isClosed_hereditarySubalgebra {a : A} {ha : IsSelfAdjoint a} :
    IsClosed (hereditarySubalgebra a ha : Set A) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

@[simp]
theorem hereditarySubalgebra_zero : hereditarySubalgebra (0 : A) = ⊥ := by
  rw [← SetLike.coe_set_eq, coe_hereditarySubalgebra, NonUnitalStarAlgebra.coe_bot]
  have hrange : (Set.range fun x : A ↦ (0 : A) * x * 0) = {0} := by
    ext y
    simp
  rw [hrange, closure_singleton]

/-- Every self-adjoint element `a` belongs to `hereditarySubalgebra a`. -/
@[simp]
theorem self_mem_hereditarySubalgebra (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a ∈ hereditarySubalgebra a ha := by
  rw [mem_hereditarySubalgebra]
  let f : ℕ → ℝ → ℝ := fun n t ↦ t / (t ^ 2 + (((n : ℝ) + 1)⁻¹) ^ 2)
  have hf_cont : ∀ n : ℕ, Continuous (f n) := fun n ↦
    continuous_id.div (by fun_prop) fun t ↦ by positivity
  have hf_zero : ∀ n : ℕ, f n 0 = 0 := fun n ↦ by simp [f]
  have hlim : Tendsto (fun n : ℕ ↦ a * cfcₙ (f n) a * a) atTop (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hle : ∀ n : ℕ, ‖a * cfcₙ (f n) a * a - a‖ ≤ ((n : ℝ) + 1)⁻¹ := fun n ↦ by
      let δ : ℝ := ((n : ℝ) + 1)⁻¹
      have hδ : 0 < δ := by positivity
      have hcfc : a * cfcₙ (f n) a * a - a = cfcₙ (fun t : ℝ ↦ t * f n t * t - t) a := by
        symm
        rw [cfcₙ_sub (fun t : ℝ ↦ t * f n t * t) (fun t : ℝ ↦ t) a
            (hf := Continuous.continuousOn (by fun_prop))
            (hf0 := by simp [hf_zero n]) (hg := continuousOn_id) (hg0 := rfl),
          cfcₙ_mul (fun t : ℝ ↦ t * f n t) (fun t : ℝ ↦ t) a
            (hf := Continuous.continuousOn (by fun_prop)) (hf0 := by simp [hf_zero n])
            (hg := continuousOn_id) (hg0 := rfl),
          cfcₙ_mul (fun t : ℝ ↦ t) (f n) a (hf := continuousOn_id) (hf0 := rfl)
            (hg := (hf_cont n).continuousOn) (hg0 := hf_zero n),
          cfcₙ_id' ℝ a]
      rw [hcfc]
      refine norm_cfcₙ_le fun t _ ↦ ?_
      have hden : 0 < t ^ 2 + δ ^ 2 := by positivity
      have halg : t * f n t * t - t = -(δ ^ 2 * t) / (t ^ 2 + δ ^ 2) := by
        have hft : f n t = t / (t ^ 2 + δ ^ 2) := rfl
        rw [hft]
        field_simp [hden.ne']
        ring
      rw [Real.norm_eq_abs, halg, abs_div, abs_neg, abs_mul, abs_of_pos (sq_pos_of_pos hδ),
        abs_of_pos hden, div_le_iff₀ hden]
      nlinarith [sq_nonneg (|t| - δ), sq_abs t, abs_nonneg t]
    refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_of_nonneg (norm_nonneg _), one_div]
    exact hle n
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n ↦ ⟨cfcₙ (f n) a, rfl⟩)

variable [PartialOrder A] [StarOrderedRing A]

/-- `hereditarySubalgebra a` is hereditary (`Set.OrdConnected`). -/
instance ordConnected_hereditarySubalgebra {a : A} {ha : IsSelfAdjoint a} :
    (hereditarySubalgebra a ha : Set A).OrdConnected := by
  rw [(hereditarySubalgebra a ha).ordConnected_iff_mul_mul_mem]
  intro b₁ hb₁ z b₂ hb₂
  rw [mem_hereditarySubalgebra] at hb₁ hb₂ ⊢
  refine map_mem_closure₂ (f := fun x y : A ↦ x * z * y) (by fun_prop) hb₁ hb₂ ?_
  rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩
  exact ⟨x₁ * a * z * a * x₂, by dsimp only; simp only [mul_assoc]⟩

/-- `hereditarySubalgebra a` is the smallest closed hereditary C⋆-subalgebra of `A` containing `a`.
-/
@[simp]
theorem hereditarySubalgebra_le_iff {a : A} {ha : IsSelfAdjoint a}
    (B : NonUnitalStarSubalgebra ℂ A) [hB : IsClosed (B : Set A)] [(B : Set A).OrdConnected] :
    hereditarySubalgebra a ha ≤ B ↔ a ∈ B := by
  refine ⟨fun h ↦ h (self_mem_hereditarySubalgebra a ha), fun haB ↦ ?_⟩
  rw [← SetLike.coe_subset_coe, coe_hereditarySubalgebra]
  refine closure_minimal ?_ hB
  rintro _ ⟨x, rfl⟩
  exact B.mul_mul_mem haB x haB

/-! #### Full positive elements vs strictly positive elements -/

/-- A nonnegative element `a` of a C⋆-algebra `A` is *full positive* if the closed two-sided ideal
it generates is all of `A`. -/
structure IsFullPositive (a : A) : Prop where
  /-- A full positive element is nonnegative. -/
  nonneg : 0 ≤ a
  /-- The closed two-sided ideal generated by `a` is the whole C⋆-algebra. -/
  topologicalClosure_span_eq_top : (TwoSidedIdeal.span ({a} : Set A)).topologicalClosure = ⊤

attribute [aesop 20% apply (rule_sets := [CStarAlgebra])] IsFullPositive.nonneg

omit [StarOrderedRing A] in
/-- Characterization of full positivity as `0 ≤ a` together with density of the two-sided ideal
generated by `a`. -/
theorem isFullPositive_iff {a : A} :
    IsFullPositive a ↔ 0 ≤ a ∧ (TwoSidedIdeal.span ({a} : Set A)).topologicalClosure = ⊤ :=
  ⟨fun h ↦ ⟨h.nonneg, h.topologicalClosure_span_eq_top⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- A nonnegative element `a` of a (possibly nonunital) C⋆-algebra `A` is *strictly positive* if the
closed hereditary C⋆-subalgebra `hereditarySubalgebra a` generated by `a` is all of `A`. -/
structure IsStrictlyPositive (a : A) : Prop where
  /-- A strictly positive element is nonnegative. -/
  nonneg : 0 ≤ a
  /-- The closed hereditary C⋆-subalgebra generated by `a` is the whole C⋆-algebra. -/
  hereditarySubalgebra_eq_top : hereditarySubalgebra a nonneg.isSelfAdjoint = ⊤

attribute [aesop 20% apply (rule_sets := [CStarAlgebra])] IsStrictlyPositive.nonneg

/-- For a nonnegative element `a`, strict positivity is equivalent to
`hereditarySubalgebra a = ⊤`. -/
theorem isStrictlyPositive_iff_of_nonneg {a : A} (ha : 0 ≤ a) :
    IsStrictlyPositive a ↔ hereditarySubalgebra a ha.isSelfAdjoint = ⊤ :=
  ⟨fun h ↦ h.hereditarySubalgebra_eq_top, fun h ↦ ⟨ha, h⟩⟩

@[grind →]
theorem IsFullPositive.isSelfAdjoint {a : A} (ha : IsFullPositive a) : IsSelfAdjoint a :=
  ha.nonneg.isSelfAdjoint

@[grind →]
theorem IsStrictlyPositive.isSelfAdjoint {a : A} (ha : IsStrictlyPositive a) : IsSelfAdjoint a :=
  ha.nonneg.isSelfAdjoint

/-- Scaling a strictly positive element by a positive real scalar preserves strict positivity. -/
@[grind ←, aesop safe apply]
theorem IsStrictlyPositive.smul {c : ℝ} (hc : 0 < c) {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (c • a) where
  nonneg := smul_nonneg hc.le ha.nonneg
  hereditarySubalgebra_eq_top := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ hereditarySubalgebra a ha.isSelfAdjoint := by
      rw [ha.hereditarySubalgebra_eq_top]
      trivial
    rw [mem_hereditarySubalgebra] at hy ⊢
    refine closure_mono ?_ hy
    rintro _ ⟨x, rfl⟩
    refine ⟨c⁻¹ • c⁻¹ • x, ?_⟩
    simp only [smul_mul_assoc, mul_smul_comm, smul_inv_smul₀ hc.ne', inv_smul_smul₀ hc.ne']

/-- Every strictly positive element of a C⋆-algebra is full positive. -/
theorem IsStrictlyPositive.isFullPositive {a : A} (ha : IsStrictlyPositive a) :
    IsFullPositive a where
  nonneg := ha.nonneg
  topologicalClosure_span_eq_top := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ hereditarySubalgebra a ha.isSelfAdjoint := by
      rw [ha.hereditarySubalgebra_eq_top]
      trivial
    rw [mem_hereditarySubalgebra] at hy
    rw [TwoSidedIdeal.mem_topologicalClosure]
    refine closure_mono ?_ hy
    rintro _ ⟨x, rfl⟩
    exact (TwoSidedIdeal.span ({a} : Set A)).mul_mem_right (a * x) a
      ((TwoSidedIdeal.span ({a} : Set A)).mul_mem_right a x (TwoSidedIdeal.subset_span rfl))

/-- A strictly positive element has trivial right annihilator: `a * x = 0 ↔ x = 0`. -/
theorem IsStrictlyPositive.mul_right_eq_zero_iff {a : A} (ha : IsStrictlyPositive a) {x : A} :
    a * x = 0 ↔ x = 0 := by
  refine ⟨fun hax ↦ ?_, fun hx ↦ by simp [hx]⟩
  have hclosed : IsClosed {b : A | b * x = 0} :=
    isClosed_eq (continuous_id.mul continuous_const) continuous_const
  have hsub : (hereditarySubalgebra a ha.isSelfAdjoint : Set A) ⊆ {b : A | b * x = 0} := by
    rw [coe_hereditarySubalgebra]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨z, rfl⟩
    simp only [Set.mem_ofPred, mul_assoc, hax, mul_zero]
  have hstar : star x ∈ hereditarySubalgebra a ha.isSelfAdjoint := by
    rw [ha.hereditarySubalgebra_eq_top]
    trivial
  exact star_mul_self_eq_zero.mp (hsub hstar)

/-- A strictly positive element has trivial left annihilator: `x * a = 0 ↔ x = 0`. -/
theorem IsStrictlyPositive.mul_left_eq_zero_iff {a : A} (ha : IsStrictlyPositive a) {x : A} :
    x * a = 0 ↔ x = 0 := by
  refine ⟨fun hxa ↦ ?_, fun hx ↦ by simp [hx]⟩
  have h : a * star x = 0 := by
    simpa only [star_mul, ha.isSelfAdjoint.star_eq, star_zero] using congrArg star hxa
  exact star_eq_zero.mp (ha.mul_right_eq_zero_iff.mp h)

/-- Every strictly positive element is both left- and right-regular (`IsRegular`). -/
theorem IsStrictlyPositive.isRegular {a : A} (ha : IsStrictlyPositive a) : IsRegular a :=
  ⟨fun x y (hxy : a * x = a * y) ↦
      sub_eq_zero.mp (ha.mul_right_eq_zero_iff.mp (by rw [mul_sub, hxy, sub_self])),
    fun x y (hxy : x * a = y * a) ↦
      sub_eq_zero.mp (ha.mul_left_eq_zero_iff.mp (by rw [sub_mul, hxy, sub_self]))⟩

/-- In a unital C⋆-algebra `A`, `TauCeti.CStarAlgebra.IsStrictlyPositive a`
(`hereditarySubalgebra a = ⊤`) is equivalent to Mathlib's `IsStrictlyPositive a`
(`0 ≤ a ∧ IsUnit a`). -/
theorem isStrictlyPositive_iff_of_unital {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} :
    IsStrictlyPositive a ↔ _root_.IsStrictlyPositive a := by
  rw [_root_.IsStrictlyPositive.iff_of_unital]
  refine ⟨fun ha ↦ ⟨ha.nonneg, ?_⟩, fun ⟨ha₀, hu⟩ ↦ ⟨ha₀, ?_⟩⟩
  · have h1 : (1 : A) ∈ closure (Set.range fun x : A ↦ a * x * a) := by
      rw [← mem_hereditarySubalgebra (ha := ha.isSelfAdjoint), ha.hereditarySubalgebra_eq_top]
      trivial
    obtain ⟨_, hu, x, hux⟩ := mem_closure_iff.mp h1 _ Units.isOpen isUnit_one
    dsimp only at hux
    obtain ⟨u, rfl⟩ := hu
    refine isUnit_iff_exists_and_exists.mpr ⟨⟨x * a * ↑u⁻¹, ?_⟩, ⟨↑u⁻¹ * a * x, ?_⟩⟩
    · calc
        a * (x * a * ↑u⁻¹) = (a * x * a) * ↑u⁻¹ := by simp only [mul_assoc]
        _ = (u : A) * ↑u⁻¹ := by rw [hux]
        _ = 1 := u.mul_inv
    · calc
        (↑u⁻¹ * a * x) * a = ↑u⁻¹ * (a * x * a) := by simp only [mul_assoc]
        _ = ↑u⁻¹ * (u : A) := by rw [hux]
        _ = 1 := u.inv_mul
  · obtain ⟨u, rfl⟩ := hu
    rw [eq_top_iff]
    intro y _
    rw [mem_hereditarySubalgebra]
    refine subset_closure (Set.mem_range.mpr ⟨↑u⁻¹ * y * ↑u⁻¹, ?_⟩)
    calc
      (u : A) * (↑u⁻¹ * y * ↑u⁻¹) * (u : A) = ((u : A) * ↑u⁻¹) * y * (↑u⁻¹ * (u : A)) := by
        simp only [mul_assoc]
      _ = y := by rw [u.mul_inv, u.inv_mul, one_mul, mul_one]

end GeneratedHereditary

end TauCeti.CStarAlgebra
