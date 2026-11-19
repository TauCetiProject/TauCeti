/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Hereditary C⋆-subalgebras

A star subalgebra `B` of a C⋆-algebra `A` is *hereditary* when `0 ≤ a ≤ b` and `b ∈ B` force
`a ∈ B`. Hereditary C⋆-subalgebras are the noncommutative analogues of open subsets: closed
two-sided ideals are hereditary, and so are the corners `pAp` of projections and the closures of
`aAa` for positive `a`.

The basic characterization is that a closed star subalgebra `B` is hereditary exactly when
`B * A * B ⊆ B`. The forward direction compares `star b * x * b` with `‖x‖ • (star b * b)` for
positive `x` and polarizes. For the converse, if `0 ≤ star y * y ≤ b` with `b ∈ B` and `e` runs
through an approximate unit of `B`, then `‖y - y * e‖ ^ 2 ≤ 2 * ‖b - b * e‖ → 0`
(`TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le`), so `star y * y` is the limit of the
elements `e * (star y * y) * e` of `B`. The same estimate shows that `x ∈ B` as soon as
`star x * x ∈ B` and `x * star x ∈ B`, which is what makes the left-ideal correspondence bijective.

## Main declarations

* `NonUnitalStarSubalgebra.IsHereditary`: heredity of a star subalgebra.
* `NonUnitalStarSubalgebra.IsHereditary.mul_mul_mem`: a hereditary star subalgebra of a C⋆-algebra
  satisfies `B * A * B ⊆ B`.
* `NonUnitalStarSubalgebra.isHereditary_iff_mul_mul_mem`: for closed `B`, heredity is equivalent to
  `B * A * B ⊆ B`.
* `TwoSidedIdeal.isHereditary_toNonUnitalStarSubalgebra` and `TwoSidedIdeal.mem_of_nonneg_of_le`:
  closed two-sided ideals of a C⋆-algebra are hereditary.
* `NonUnitalStarSubalgebra.IsHereditary.leftIdeal` and `Submodule.interStar`: the order-preserving
  correspondence between closed hereditary star subalgebras `B` and closed left ideals `L`, given by
  `B ↦ {x | star x * x ∈ B}` and `L ↦ L ∩ star L`. The two maps are mutually inverse:
  `NonUnitalStarSubalgebra.IsHereditary.interStar_leftIdeal` and `Submodule.leftIdeal_interStar`.
* `NonUnitalStarSubalgebra.hereditaryOf a`: the closure of `star a * A * a`, a closed hereditary
  star subalgebra. For positive `a` it is the smallest closed hereditary star subalgebra containing
  `a` (`NonUnitalStarSubalgebra.hereditaryOf_le_iff`).

Closed left ideals are represented as closed complex subspaces `L : Submodule ℂ A` with
`a * x ∈ L` whenever `x ∈ L`, since a nonunital `A` is not a module over itself in Mathlib's sense.

## References

* B. Blackadar, *Operator Algebras*, II.3.4 and II.5.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.2.2.
-/

public section

open Filter Topology
open scoped NNReal

namespace NonUnitalStarSubalgebra

section Defs

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] [LE A]

/-- A star subalgebra `B` is *hereditary* if every `a` with `0 ≤ a ≤ b` for some `b ∈ B` lies
in `B`. -/
def IsHereditary (B : NonUnitalStarSubalgebra R A) : Prop :=
  ∀ ⦃a b : A⦄, 0 ≤ a → a ≤ b → b ∈ B → a ∈ B

/-- Unfolding rule for heredity, usable from other modules to prove or use `B.IsHereditary`. -/
theorem isHereditary_iff {B : NonUnitalStarSubalgebra R A} :
    B.IsHereditary ↔ ∀ ⦃a b : A⦄, 0 ≤ a → a ≤ b → b ∈ B → a ∈ B :=
  Iff.rfl

/-- Elimination rule for heredity: `0 ≤ a ≤ b` with `b ∈ B` gives `a ∈ B`. -/
theorem IsHereditary.mem_of_nonneg_of_le {B : NonUnitalStarSubalgebra R A} (hB : B.IsHereditary)
    {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ B) : a ∈ B :=
  hB ha hab hb

end Defs

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : NonUnitalStarSubalgebra ℂ A}

/-- A hereditary star subalgebra of a C⋆-algebra contains `star b * x * b` for every `b` in it and
every `x`. -/
theorem IsHereditary.star_mul_mul_mem (hB : B.IsHereditary) {b : A} (hb : b ∈ B) (x : A) :
    star b * x * b ∈ B := by
  obtain ⟨y, hy, -, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg x
  have hbb : star b * b ∈ B := mul_mem (star_mem hb) hb
  have key (i : Fin 4) : star b * y i * b ∈ B := by
    refine hB (star_left_conjugate_nonneg (hy i) b)
      (CStarAlgebra.star_left_conjugate_le_norm_smul b (y i) (hy i).isSelfAdjoint) ?_
    rw [← Complex.coe_smul]
    exact SMulMemClass.smul_mem _ hbb
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact sum_mem fun i _ ↦ SMulMemClass.smul_mem _ (key i)

/-- A hereditary star subalgebra `B` of a C⋆-algebra satisfies `B * A * B ⊆ B`. -/
theorem IsHereditary.mul_mul_mem (hB : B.IsHereditary) {b c : A} (hb : b ∈ B) (x : A)
    (hc : c ∈ B) : b * x * c ∈ B := by
  -- Polarization: `4 • (star u * x * c) = ∑ₖ Iᵏ • star (c + Iᵏ • u) * x * (c + Iᵏ • u)`.
  set u := star b
  have hu : u ∈ B := star_mem hb
  have hpol : (4 : ℂ) • (star u * x * c) =
      star (c + u) * x * (c + u) + Complex.I • (star (c + Complex.I • u) * x *
        (c + Complex.I • u)) - star (c - u) * x * (c - u) -
        Complex.I • (star (c - Complex.I • u) * x * (c - Complex.I • u)) := by
    simp only [star_add, star_sub, star_smul, Complex.star_def, Complex.conj_I, add_mul, sub_mul,
      mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, neg_smul,
      neg_mul, smul_neg, Complex.I_mul_I]
    module
  have h4 : star u * x * c = (4 : ℂ)⁻¹ • ((4 : ℂ) • (star u * x * c)) := by
    rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [show b = star u from (star_star b).symm, h4, hpol]
  refine SMulMemClass.smul_mem _ (sub_mem (sub_mem (add_mem ?_ ?_) ?_) ?_)
  · exact hB.star_mul_mul_mem (add_mem hc hu) x
  · exact SMulMemClass.smul_mem _ <|
      hB.star_mul_mul_mem (add_mem hc (SMulMemClass.smul_mem _ hu)) x
  · exact hB.star_mul_mul_mem (sub_mem hc hu) x
  · exact SMulMemClass.smul_mem _ <|
      hB.star_mul_mul_mem (sub_mem hc (SMulMemClass.smul_mem _ hu)) x

/-- A closed star subalgebra `B` of a C⋆-algebra with `B * A * B ⊆ B` is hereditary. -/
theorem isHereditary_of_mul_mul_mem (hBc : IsClosed (B : Set A))
    (h : ∀ b ∈ B, ∀ x : A, ∀ c ∈ B, b * x * c ∈ B) : B.IsHereditary := by
  intro a b ha hab hb
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  obtain ⟨l, _, hlB, -, hsa, hnorm, hl⟩ := NonUnitalStarSubalgebra.exists_approximateUnit hBc
  -- A right approximate unit for `b` is one for `y`, hence for `star y * y` on both sides.
  have hr : Tendsto (star y * y * ·) l (𝓝 (star y * y)) := by
    simpa only [mul_assoc] using
      (TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le hsa hnorm hab
        (hl b hb).1).const_mul (star y)
  have hl' : Tendsto (· * (star y * y)) l (𝓝 (star y * y)) := by
    simpa only [star_mul, star_star] using TauCeti.tendsto_mul_star_of_tendsto_mul hsa hr
  exact mem_of_tendsto_mul hBc hlB hnorm (fun e he ↦ h e he _ e he) hr hl'

/-- A closed star subalgebra `B` of a C⋆-algebra is hereditary if and only if
`B * A * B ⊆ B`. -/
theorem isHereditary_iff_mul_mul_mem (hBc : IsClosed (B : Set A)) :
    B.IsHereditary ↔ ∀ b ∈ B, ∀ x : A, ∀ c ∈ B, b * x * c ∈ B :=
  ⟨fun hB _ hb x _ hc ↦ hB.mul_mul_mem hb x hc, isHereditary_of_mul_mul_mem hBc⟩

/-- In a closed hereditary star subalgebra `B`, an element `x` with `star x * x ∈ B` and
`x * star x ∈ B` lies in `B`. -/
theorem IsHereditary.mem_of_star_mul_self_mem_of_mul_star_self_mem (hB : B.IsHereditary)
    (hBc : IsClosed (B : Set A)) {x : A} (h₁ : star x * x ∈ B) (h₂ : x * star x ∈ B) : x ∈ B := by
  obtain ⟨l, _, hlB, -, hsa, hnorm, hl⟩ := NonUnitalStarSubalgebra.exists_approximateUnit hBc
  have hr := TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le hsa hnorm le_rfl (hl _ h₁).1
  have hr' := TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le (y := star x) hsa hnorm
    (by rw [star_star]) (hl _ h₂).1
  have hl' : Tendsto (· * x) l (𝓝 x) := by
    simpa only [star_star] using TauCeti.tendsto_mul_star_of_tendsto_mul hsa hr'
  exact mem_of_tendsto_mul hBc hlB hnorm (fun e he ↦ hB.mul_mul_mem he x he) hr hl'

/-- The left ideal `{x | star x * x ∈ B}` of a hereditary star subalgebra `B`, as a complex
subspace. It absorbs left multiplication (`IsHereditary.mul_mem_leftIdeal`) and is closed when `B`
is (`IsHereditary.isClosed_leftIdeal`). -/
def IsHereditary.leftIdeal (hB : B.IsHereditary) : Submodule ℂ A where
  carrier := {x | star x * x ∈ B}
  add_mem' {x y} hx hy := by
    -- `star (x + y) * (x + y) ≤ 2 • (star x * x + star y * y)`, which lies in `B`.
    refine hB (star_mul_self_nonneg _) (le_add_of_nonneg_right (star_mul_self_nonneg (x - y)))
      ?_
    have : star (x + y) * (x + y) + star (x - y) * (x - y) = 2 • (star x * x + star y * y) := by
      simp only [star_add, star_sub]
      noncomm_ring
    rw [this]
    exact nsmul_mem (add_mem hx hy) 2
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    exact SMulMemClass.smul_mem _ hx

/-- Membership in `{x | star x * x ∈ B}`. -/
@[simp]
theorem IsHereditary.mem_leftIdeal (hB : B.IsHereditary) {x : A} :
    x ∈ hB.leftIdeal ↔ star x * x ∈ B :=
  Iff.rfl

/-- `{x | star x * x ∈ B}` is a left ideal. -/
theorem IsHereditary.mul_mem_leftIdeal (hB : B.IsHereditary) (a : A) {x : A}
    (hx : x ∈ hB.leftIdeal) : a * x ∈ hB.leftIdeal := by
  rw [mem_leftIdeal] at hx ⊢
  have : star (a * x) * (a * x) = star x * (star a * a) * x := by
    simp only [star_mul]
    noncomm_ring
  rw [this]
  refine hB (star_left_conjugate_nonneg (star_mul_self_nonneg a) x)
    (CStarAlgebra.star_left_conjugate_le_norm_smul x _ (.star_mul_self a)) ?_
  rw [← Complex.coe_smul]
  exact SMulMemClass.smul_mem _ hx

/-- The left ideal of a closed hereditary star subalgebra is closed. -/
theorem IsHereditary.isClosed_leftIdeal (hB : B.IsHereditary) (hBc : IsClosed (B : Set A)) :
    IsClosed (hB.leftIdeal : Set A) :=
  hBc.preimage (continuous_star.mul continuous_id)

/-- A closed hereditary star subalgebra `B` consists of the `x` with `x` and `star x` in the left
ideal `{x | star x * x ∈ B}`. -/
theorem IsHereditary.mem_iff_mem_leftIdeal_and_star_mem_leftIdeal (hB : B.IsHereditary)
    (hBc : IsClosed (B : Set A)) {x : A} : x ∈ B ↔ x ∈ hB.leftIdeal ∧ star x ∈ hB.leftIdeal := by
  simp only [mem_leftIdeal, star_star]
  exact ⟨fun hx ↦ ⟨mul_mem (star_mem hx) hx, mul_mem hx (star_mem hx)⟩,
    fun h ↦ hB.mem_of_star_mul_self_mem_of_mul_star_self_mem hBc h.1 h.2⟩

/-- `B ↦ {x | star x * x ∈ B}` is monotone. -/
theorem IsHereditary.leftIdeal_mono {B' : NonUnitalStarSubalgebra ℂ A} (hB : B.IsHereditary)
    (hB' : B'.IsHereditary) (h : B ≤ B') : hB.leftIdeal ≤ hB'.leftIdeal :=
  fun _ hx ↦ h hx

end NonUnitalStarSubalgebra

namespace Submodule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {L : Submodule ℂ A} {hL : ∀ (a : A) {x : A}, x ∈ L → a * x ∈ L}

/-- For a closed left ideal `L`, the star subalgebra `L ∩ star L` is hereditary. -/
theorem isHereditary_interStar (hLc : IsClosed (L : Set A)) : (L.interStar hL).IsHereditary := by
  refine NonUnitalStarSubalgebra.isHereditary_of_mul_mul_mem (isClosed_interStar hLc)
    fun b hb x c hc ↦ mem_interStar.mpr ⟨hL _ (mem_interStar.mp hc).1, ?_⟩
  rw [star_mul, star_mul, ← mul_assoc]
  exact hL _ (mem_interStar.mp hb).2

/-- A closed left ideal `L` is recovered from the hereditary star subalgebra `L ∩ star L` as
`{x | star x * x ∈ L ∩ star L}`. -/
theorem leftIdeal_interStar (hLc : IsClosed (L : Set A)) :
    (isHereditary_interStar (hL := hL) hLc).leftIdeal = L := by
  ext x
  rw [NonUnitalStarSubalgebra.IsHereditary.mem_leftIdeal, mem_interStar, star_mul, star_star,
    and_self]
  refine ⟨fun hx ↦ ?_, fun hx ↦ hL _ hx⟩
  obtain ⟨l, _, hlB, -, hsa, hnorm, hl⟩ :=
    NonUnitalStarSubalgebra.exists_approximateUnit (B := L.interStar hL) (isClosed_interStar hLc)
  -- Along an approximate unit `e` of `L ∩ star L`, `x * e → x` and `x * e ∈ L`.
  have hr := TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le hsa hnorm le_rfl
    (hl _ (mem_interStar.mpr ⟨hx, by rw [star_mul, star_star]; exact hx⟩)).1
  exact hLc.mem_of_tendsto hr (hlB.mono fun e he ↦ hL x (mem_interStar.mp he).1)

/-- A closed hereditary star subalgebra `B` is recovered from its left ideal as
`{x | star x * x ∈ B} ∩ star {x | star x * x ∈ B}`. -/
theorem _root_.NonUnitalStarSubalgebra.IsHereditary.interStar_leftIdeal
    {B : NonUnitalStarSubalgebra ℂ A} (hB : B.IsHereditary) (hBc : IsClosed (B : Set A)) :
    hB.leftIdeal.interStar (fun a _ hx ↦ hB.mul_mem_leftIdeal a hx) = B := by
  ext x
  rw [mem_interStar, hB.mem_iff_mem_leftIdeal_and_star_mem_leftIdeal hBc]

end Submodule

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- A closed two-sided ideal of a C⋆-algebra is a hereditary star subalgebra. -/
theorem isHereditary_toNonUnitalStarSubalgebra : I.toNonUnitalStarSubalgebra.IsHereditary :=
  NonUnitalStarSubalgebra.isHereditary_of_mul_mul_mem (I.isClosed_toNonUnitalStarSubalgebra)
    fun _ hb _ _ _ ↦ I.mem_toNonUnitalStarSubalgebra.mpr <|
      I.mul_mem_right _ _ (I.mul_mem_right _ _ (I.mem_toNonUnitalStarSubalgebra.mp hb))

/-- A closed two-sided ideal of a C⋆-algebra is hereditary: if `0 ≤ a ≤ b` and `b ∈ I`, then
`a ∈ I`. -/
theorem mem_of_nonneg_of_le {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ I) : a ∈ I :=
  I.mem_toNonUnitalStarSubalgebra.mp <|
    I.isHereditary_toNonUnitalStarSubalgebra ha hab (I.mem_toNonUnitalStarSubalgebra.mpr hb)

end TwoSidedIdeal

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The star subalgebra `star a * A * a` of elements `star a * x * a`. -/
private def starMulMul (a : A) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range fun x ↦ star a * x * a
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  zero_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * a * star a * y, by noncomm_ring⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨c • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp [mul_assoc]⟩

/-- The closed star subalgebra `closure (star a * A * a)`. For positive `a` this is the hereditary
C⋆-subalgebra generated by `a`. -/
noncomputable def hereditaryOf (a : A) : NonUnitalStarSubalgebra ℂ A :=
  (starMulMul a).topologicalClosure

/-- `hereditaryOf a` is the closure of the set of elements `star a * x * a`. -/
@[simp]
theorem coe_hereditaryOf (a : A) :
    (hereditaryOf a : Set A) = closure (Set.range fun x ↦ star a * x * a) :=
  (rfl)

/-- `hereditaryOf a` is closed. -/
theorem isClosed_hereditaryOf (a : A) : IsClosed (hereditaryOf a : Set A) :=
  isClosed_topologicalClosure _

/-- `hereditaryOf a` contains every `star a * x * a`. -/
theorem star_mul_mul_mem_hereditaryOf (a x : A) : star a * x * a ∈ hereditaryOf a :=
  le_topologicalClosure _ ⟨x, rfl⟩

variable [PartialOrder A] [StarOrderedRing A] {B : NonUnitalStarSubalgebra ℂ A}

/-- `closure (star a * A * a)` is hereditary. -/
theorem isHereditary_hereditaryOf (a : A) : (hereditaryOf a).IsHereditary := by
  refine isHereditary_of_mul_mul_mem (isClosed_hereditaryOf a) fun b hb x c hc ↦ ?_
  rw [← SetLike.mem_coe, coe_hereditaryOf] at hb hc ⊢
  refine map_mem_closure₂ (f := fun b c ↦ b * x * c) (by fun_prop) hb hc ?_
  rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
  exact ⟨y * a * x * star a * z, by noncomm_ring⟩

/-- A positive element lies in the closure of `a * A * a`. -/
theorem mem_hereditaryOf_self {a : A} (ha : 0 ≤ a) : a ∈ hereditaryOf a := by
  have h3 : a ^ (3 : ℝ≥0) ∈ hereditaryOf a := by
    rw [CFC.nnrpow_three a ha]
    simpa [ha.star_eq] using star_mul_mul_mem_hereditaryOf a a
  have : IsClosed (hereditaryOf a : Set A) := isClosed_hereditaryOf a
  -- `a` is the cube root of `a ^ 3`, a continuous function of an element of `hereditaryOf a`.
  have key := cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ)
    (fun x : ℝ ↦ ((x.toNNReal.nnrpow (3 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)) h3
  rwa [← cfcₙ_nnreal_eq_real (fun x : ℝ≥0 ↦ x.nnrpow (3 : ℝ≥0)⁻¹) _ CFC.nnrpow_nonneg,
    ← CFC.nnrpow_def,
    CFC.nnrpow_nnrpow_inv a (by norm_num) ha] at key

/-- A closed hereditary star subalgebra containing `a` contains `closure (star a * A * a)`. -/
theorem hereditaryOf_le (hB : B.IsHereditary) (hBc : IsClosed (B : Set A)) {a : A} (ha : a ∈ B) :
    hereditaryOf a ≤ B :=
  topologicalClosure_minimal _ (by rintro _ ⟨x, rfl⟩; exact hB.mul_mul_mem (star_mem ha) x ha) hBc

/-- For positive `a`, `closure (a * A * a)` is the smallest closed hereditary star subalgebra
containing `a`. -/
theorem hereditaryOf_le_iff (hB : B.IsHereditary) (hBc : IsClosed (B : Set A)) {a : A}
    (ha : 0 ≤ a) : hereditaryOf a ≤ B ↔ a ∈ B :=
  ⟨fun h ↦ h (mem_hereditaryOf_self ha), hereditaryOf_le hB hBc⟩

end NonUnitalStarSubalgebra
