/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

/-!
# The Pin group and the even part of the normalized full Clifford cover

The normalized full Clifford cover `CliffordAlgebra.cliffordFullCover Q` consists of the Lipschitz
elements whose reverse norm `reverse x * x` is `1` or `-1`. Mathlib's Pin group consists of the
Lipschitz elements whose `star` norm `star x * x` is `1`. As `star = reverse ∘ involute`, the two
norms agree on even elements and are opposite on odd ones, so the full cover is also the set where
the `star` norm is `±1`, and the Pin group is the subgroup of the full cover where it is `1`. In
the same way the Spin group is the subgroup of even elements of reverse norm `1`.

Over a field in which `-1` is not a square, the kernel of the full-cover action on a nondegenerate
quadratic space is `{±1}`, which lies in the Spin group. Hence the Pin and Spin groups are the
inverse images in the full cover of their images in the orthogonal group, and an element of the full
cover has reverse norm `1` exactly when the spinor norm of its action is trivial. When moreover
every element is a square up to sign, as over `ℝ`, the even part of the full cover covers all of
`SO(Q)`, and the Spin group has index in it the number of values of the spinor norm on `SO(Q)`.

In rank one the full cover is a group of order four. It is cyclic exactly when some vector has
norm `-1`: then that vector has order four, whereas if some vector has norm `1`, it gives together
with `1` and `-1` three solutions of `x ^ 2 = 1`, which a cyclic group of order four cannot have.

## Main definitions

* `CliffordAlgebra.pinToCliffordFullCover`: the inclusion of the Pin group in the full cover.
* `CliffordAlgebra.cliffordFullCoverEven`: the subgroup of even elements of the full cover.

## Main results

* `CliffordAlgebra.mem_cliffordFullCover_iff_lipschitzNorm`: the full cover is the set where the
  `star` norm is `±1`.
* `CliffordAlgebra.mem_range_pinToCliffordFullCover_iff` and
  `CliffordAlgebra.mem_range_spinToCliffordFullCover_iff`: the Pin group is the part of the full
  cover of `star` norm `1`, and the Spin group its even part of reverse norm `1`.
* `CliffordAlgebra.comap_range_pinToOrthogonal` and `CliffordAlgebra.comap_range_spinToOrthogonal`:
  the Pin and Spin groups are the inverse images of their images in `O(Q)`.
* `CliffordAlgebra.map_cliffordFullCoverEven`: the even part of the full cover covers `SO(Q)`.
* `CliffordAlgebra.relIndex_range_spinToCliffordFullCover`: the index of the Spin group in the even
  part of the full cover is the number of values of the spinor norm on `SO(Q)`.
* `CliffordAlgebra.card_ker_cliffordFullCoverToOrthogonal`: the kernel `{±1}` has order two.
* `CliffordAlgebra.card_cliffordFullCover_of_finrank_eq_one` and
  `CliffordAlgebra.isCyclic_cliffordFullCover_iff_of_finrank_eq_one`: in rank one the full cover
  has order four, and it is cyclic exactly when some vector has norm `-1`
  (`CliffordAlgebra.isCyclic_cliffordFullCover_of_finrank_eq_one`), not when some vector has
  norm `1` (`CliffordAlgebra.not_isCyclic_cliffordFullCover_of_finrank_eq_one`).

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6 and Proposition 1.21, where `Pin(p, q)` is the norm `±1`
  cover.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe u v

section Ring

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] (Q : QuadraticForm R M)

/-- **The full cover through the `star` norm.** A Lipschitz element lies in the normalized full
cover exactly when its `star` norm `star x * x` is `1` or `-1`: on a homogeneous element it is the
reverse norm up to sign. -/
theorem mem_cliffordFullCover_iff_lipschitzNorm (x : lipschitzGroup Q) :
    x ∈ cliffordFullCover Q ↔ lipschitzNorm Q x = 1 ∨ lipschitzNorm Q x = -1 := by
  rw [mem_cliffordFullCover_iff]
  obtain ⟨p, hp⟩ := lipschitzGroup.exists_mem_evenOdd x.2
  fin_cases p
  · rw [lipschitzNorm_eq_cliffordNorm_of_mem_even x hp]
  · rw [lipschitzNorm_eq_neg_cliffordNorm_of_mem_odd x hp, neg_eq_iff_eq_neg, neg_inj, or_comm]

/-! ### The Pin group in the full cover -/

/-- The Pin group embeds in the normalized full cover through its canonical Lipschitz lift. -/
def pinToCliffordFullCover : pinGroup Q →* cliffordFullCover Q :=
  (pinToLipschitz Q).codRestrict _ fun x ↦
    (mem_cliffordFullCover_iff_lipschitzNorm Q _).2 (Or.inl (lipschitzNorm_pinToLipschitz Q x))

/-- The underlying Lipschitz element of the Pin-to-full-cover inclusion. -/
@[simp]
theorem coe_pinToCliffordFullCover_apply (x : pinGroup Q) :
    (pinToCliffordFullCover Q x : lipschitzGroup Q) = pinToLipschitz Q x := by
  simp only [pinToCliffordFullCover, MonoidHom.codRestrict_apply]

/-- The Pin-to-full-cover inclusion is injective. -/
theorem pinToCliffordFullCover_injective : Function.Injective (pinToCliffordFullCover Q) := by
  intro x y h
  apply Subtype.ext
  simpa only [coe_pinToCliffordFullCover_apply, coe_pinToLipschitz_apply] using
    congrArg (fun z : cliffordFullCover Q ↦
      (((z : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h

/-- The Pin action is the restriction of the full-cover action pointwise. -/
@[simp 1100]
theorem cliffordFullCoverToOrthogonal_pinToCliffordFullCover_apply (x : pinGroup Q) :
    cliffordFullCoverToOrthogonal Q (pinToCliffordFullCover Q x) = pinToOrthogonal Q x := by
  rw [cliffordFullCoverToOrthogonal_apply, coe_pinToCliffordFullCover_apply,
    pinToOrthogonal_eq_lipschitzToOrthogonal]

/-- The restricted orthogonal action agrees with the Pin action on the included subgroup. -/
@[simp]
theorem cliffordFullCoverToOrthogonal_comp_pinToCliffordFullCover :
    (cliffordFullCoverToOrthogonal Q).comp (pinToCliffordFullCover Q) = pinToOrthogonal Q :=
  MonoidHom.ext (cliffordFullCoverToOrthogonal_pinToCliffordFullCover_apply Q)

/-- The inclusion of the Spin group in the full cover factors through the Pin group. -/
@[simp]
theorem pinToCliffordFullCover_spinToPin (x : spinGroup Q) :
    pinToCliffordFullCover Q (spinToPin Q x) = spinToCliffordFullCover Q x :=
  Subtype.ext (by
    rw [coe_pinToCliffordFullCover_apply, coe_spinToCliffordFullCover_apply, spinToLipschitz_apply])

/-- The inclusion of the Spin group in the full cover factors through the Pin group. -/
@[simp]
theorem pinToCliffordFullCover_comp_spinToPin :
    (pinToCliffordFullCover Q).comp (spinToPin Q) = spinToCliffordFullCover Q :=
  MonoidHom.ext (pinToCliffordFullCover_spinToPin Q)

/-- **The Pin group inside the full cover** is the subgroup of elements of `star` norm `1`. -/
theorem mem_range_pinToCliffordFullCover_iff (x : cliffordFullCover Q) :
    x ∈ (pinToCliffordFullCover Q).range ↔ lipschitzNorm Q x = 1 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [coe_pinToCliffordFullCover_apply, lipschitzNorm_pinToLipschitz]
  · intro h
    refine ⟨⟨_, (mem_pinGroup_iff_lipschitzNorm_eq_one Q x).2 h⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact Units.ext (by rw [coe_pinToCliffordFullCover_apply, coe_pinToLipschitz_apply])

/-- **The Spin group inside the full cover** is the subgroup of even elements of reverse norm
`1`. -/
theorem mem_range_spinToCliffordFullCover_iff (x : cliffordFullCover Q) :
    x ∈ (spinToCliffordFullCover Q).range ↔
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q ∧
        cliffordNorm Q x = 1 := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule,
    ← mem_spinGroup_iff_mem_even_and_cliffordNorm_eq_one]
  constructor
  · rintro ⟨s, rfl⟩
    rw [coe_spinToCliffordFullCover_apply, coe_spinToLipschitz_apply]
    exact s.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
    rw [coe_spinToCliffordFullCover_apply, coe_spinToLipschitz_apply]

/-! ### The even part of the full cover -/

/-- The subgroup of even elements of the normalized full cover. -/
def cliffordFullCoverEven : Subgroup (cliffordFullCover Q) where
  carrier := {x | (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q}
  one_mem' := (even Q).one_mem
  mul_mem' hx hy := (even Q).mul_mem hx hy
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, ← Subalgebra.mem_toSubmodule, even_toSubmodule,
      ← involute_eq_self_iff, InvMemClass.coe_inv] at hx ⊢
    -- The grade involution is multiplicative, so it fixes the inverse of a unit it fixes.
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    nth_rw 1 [← hx]
    rw [← map_mul, Units.mul_inv, map_one]

/-- Membership in the even part of the full cover is evenness of the underlying Clifford
element. -/
@[simp]
theorem mem_cliffordFullCoverEven_iff (x : cliffordFullCover Q) :
    x ∈ cliffordFullCoverEven Q ↔
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
  Iff.rfl

/-- The Spin group lies in the even part of the full cover. -/
theorem range_spinToCliffordFullCover_le_cliffordFullCoverEven :
    (spinToCliffordFullCover Q).range ≤ cliffordFullCoverEven Q :=
  fun x hx ↦ ((mem_range_spinToCliffordFullCover_iff Q x).1 hx).1

end Ring

/-! ### Comparison over a field -/

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- When `-1` is not a square, the kernel `{±1}` of the full-cover action of a nondegenerate
quadratic space lies in the Spin group. -/
theorem ker_cliffordFullCoverToOrthogonal_le_range_spinToCliffordFullCover
    (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K)) :
    (cliffordFullCoverToOrthogonal Q).ker ≤ (spinToCliffordFullCover Q).range := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · intro x _
    have hx : (x : lipschitzGroup Q) = 1 :=
      Subtype.ext ((Subgroup.mem_bot.1 (lipschitzGroup_eq_bot (Q := Q) ▸ (x : lipschitzGroup Q).2)))
    exact ⟨1, Subtype.ext (by rw [map_one, hx, OneMemClass.coe_one])⟩
  · rw [ker_cliffordFullCoverToOrthogonal hQ h]
    exact Subgroup.map_le_range _ _

/-- **The kernel of the full-cover action has order two.** When `-1` is not a square, the kernel of
the full-cover action of a nontrivial nondegenerate quadratic space is `{1, -1}`. -/
theorem card_ker_cliffordFullCoverToOrthogonal [Nontrivial V] (hQ : Q.Nondegenerate)
    (h : ¬IsSquare (-1 : K)) :
    Nat.card (cliffordFullCoverToOrthogonal Q).ker = 2 := by
  refine Nat.card_eq_two_iff.2 ⟨1,
    ⟨spinToCliffordFullCover Q (spinGroup.negOne Q hQ.ne_zero),
      (mem_ker_cliffordFullCoverToOrthogonal_iff hQ h _).2 (Or.inr rfl)⟩, fun h1 ↦ ?_,
    Set.eq_univ_of_forall fun x ↦ ?_⟩
  · refine spinGroup.negOne_ne_one Q hQ.ne_zero (spinToCliffordFullCover_injective Q ?_)
    rw [map_one]
    exact (congrArg Subtype.val h1).symm
  · rcases (mem_ker_cliffordFullCoverToOrthogonal_iff hQ h x).1 x.2 with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)

/-- **The Spin group is the inverse image of its image.** When `-1` is not a square, an element
of the full cover of a nondegenerate quadratic space acts like a Spin element exactly when it is
one: the kernel `{±1}` of the full-cover action lies in the Spin group. -/
theorem comap_range_spinToOrthogonal (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K)) :
    (spinToOrthogonal Q).range.comap (cliffordFullCoverToOrthogonal Q) =
      (spinToCliffordFullCover Q).range := by
  rw [← cliffordFullCoverToOrthogonal_comp_spinToCliffordFullCover, ← MonoidHom.map_range,
    Subgroup.comap_map_eq,
    sup_eq_left.2 (ker_cliffordFullCoverToOrthogonal_le_range_spinToCliffordFullCover hQ h)]

/-- **The Pin group is the inverse image of its image.** When `-1` is not a square, an element of
the full cover of a nondegenerate quadratic space acts like a Pin element exactly when it is one:
the kernel `{±1}` of the full-cover action lies in the Pin group. -/
theorem comap_range_pinToOrthogonal (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K)) :
    (pinToOrthogonal Q).range.comap (cliffordFullCoverToOrthogonal Q) =
      (pinToCliffordFullCover Q).range := by
  have hker : (cliffordFullCoverToOrthogonal Q).ker ≤ (pinToCliffordFullCover Q).range := by
    refine (ker_cliffordFullCoverToOrthogonal_le_range_spinToCliffordFullCover hQ h).trans ?_
    rw [← pinToCliffordFullCover_comp_spinToPin, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  rw [← cliffordFullCoverToOrthogonal_comp_pinToCliffordFullCover, ← MonoidHom.map_range,
    Subgroup.comap_map_eq, sup_eq_left.2 hker]

/-- **Reverse norm and spinor norm.** When `-1` is not a square, an element of the full cover of
a nondegenerate quadratic space has reverse norm `1`, rather than `-1`, exactly when the spinor
norm of its action is trivial. -/
theorem cliffordNorm_eq_one_iff_orthogonalSpinorNorm_eq_one (hQ : Q.Nondegenerate)
    (h : ¬IsSquare (-1 : K)) (x : cliffordFullCover Q) :
    cliffordNorm Q x = 1 ↔
      orthogonalSpinorNorm Q hQ (cliffordFullCoverToOrthogonal Q x) = 1 := by
  rw [cliffordFullCoverToOrthogonal_apply, orthogonalSpinorNorm_lipschitzToOrthogonal,
    squareClassHom_eq_one_iff]
  rcases (mem_cliffordFullCover_iff Q x).1 x.2 with h1 | h1 <;> rw [h1]
  · simp
  · refine iff_of_false (fun h2 ↦ ?_) fun h2 ↦ h ?_
    · have h3 : (-1 : K) = 1 := by simpa using congrArg Units.val h2
      exact two_ne_zero (by linear_combination -h3 : (2 : K) = 0)
    · simpa using Units.isSquare_coe_iff.mpr h2

/-- **The Spin group inside the even full cover.** When `-1` is not a square, the Spin group is
the subgroup of even elements of the full cover whose action has trivial spinor norm. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_inf (hQ : Q.Nondegenerate)
    (h : ¬IsSquare (-1 : K)) :
    (spinToCliffordFullCover Q).range =
      cliffordFullCoverEven Q ⊓
        ((orthogonalSpinorNorm Q hQ).comp (cliffordFullCoverToOrthogonal Q)).ker := by
  ext x
  rw [mem_range_spinToCliffordFullCover_iff, Subgroup.mem_inf, mem_cliffordFullCoverEven_iff,
    MonoidHom.mem_ker, MonoidHom.comp_apply,
    cliffordNorm_eq_one_iff_orthogonalSpinorNorm_eq_one hQ h]

/-- **The even part of the full cover covers `SO(Q)`.** Over a field in which every element is a
square up to sign, the image of the even part of the full cover of a finite-dimensional
nondegenerate quadratic space is `SO(Q)`. -/
theorem map_cliffordFullCoverEven (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    (cliffordFullCoverEven Q).map (cliffordFullCoverToOrthogonal Q) =
      QuadraticMap.specialOrthogonalWithin Q := by
  ext g
  rw [← exists_cliffordFullCoverToOrthogonal_eq_and_mem_even_iff hQ hK, Subgroup.mem_map]
  simp only [mem_cliffordFullCoverEven_iff, and_comm]

/-- **The index of the Spin group in the even full cover.** Over a field in which `-1` is not a
square but every element is a square up to sign, the Spin group has index in the even part of the
full cover equal to the number of values of the spinor norm on `SO(Q)`. -/
theorem relIndex_range_spinToCliffordFullCover (hQ : Q.Nondegenerate) (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    (spinToCliffordFullCover Q).range.relIndex (cliffordFullCoverEven Q) =
      Nat.card (spinorNorm Q hQ).range := by
  have hθ : spinorNorm Q hQ = (orthogonalSpinorNorm Q hQ).comp
      (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) :=
    MonoidHom.ext (spinorNorm_apply Q hQ)
  rw [range_spinToCliffordFullCover_eq_cliffordFullCoverEven_inf hQ h, Subgroup.inf_relIndex_left,
    Subgroup.relIndex_ker, ← Subgroup.map_map, map_cliffordFullCoverEven hQ hK, hθ,
    MonoidHom.range_comp, _root_.QuadraticMap.range_specialOrthogonalToOrthogonal]

/-! ### Rank one -/

section RankOne

variable (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 1)
include hQ hV

/-- **The full cover in rank one has order four.** Over a field in which `-1` is not a square but
every element is a square up to sign, the full cover of a nondegenerate line is an extension of
`O(Q) = {±1}` by the kernel `{±1}`. -/
theorem card_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    Nat.card (cliffordFullCover Q) = 4 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  rw [← Subgroup.card_ker_mul_card_range (cliffordFullCoverToOrthogonal Q),
    card_ker_cliffordFullCoverToOrthogonal hQ h,
    MonoidHom.range_eq_top.2 (cliffordFullCoverToOrthogonal_surjective hQ hK), Subgroup.card_top,
    QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ.ne_zero hV]

omit hQ hV in
/-- A vector `v` of norm `Q v = ±1` as an element of the full cover. -/
private def cliffordFullCoverOfNorm (v : V) [Invertible (Q v)] (hv : Q v = 1 ∨ Q v = -1) :
    cliffordFullCover Q :=
  ⟨⟨unitι Q v, unitι_mem_lipschitzGroup v⟩, (mem_cliffordFullCover_iff Q _).2 (by
    rw [cliffordNorm_unitι, Units.ext_iff, Units.ext_iff, val_unitOfInvertible]
    simpa using hv)⟩

omit hQ hV [FiniteDimensional K V] in
private theorem coe_cliffordFullCoverOfNorm_pow (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) (n : ℕ) :
    ((((cliffordFullCoverOfNorm v hv ^ n : cliffordFullCover Q) : lipschitzGroup Q) :
      (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ι Q v ^ n := by
  simp [cliffordFullCoverOfNorm, coe_unitι]

omit hQ in
/-- In rank one the element of a vector of norm `±1` acts on the line by `-1`. -/
private theorem cliffordFullCoverToOrthogonal_cliffordFullCoverOfNorm (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) :
    cliffordFullCoverToOrthogonal Q (cliffordFullCoverOfNorm v hv) = Q.negOrthogonal := by
  rw [cliffordFullCoverToOrthogonal_apply, cliffordFullCoverOfNorm, lipschitzToOrthogonal_unitι,
    QuadraticMap.reflectionOrthogonal_eq_negOrthogonal_of_finrank_eq_one Q v hV]

omit hQ in
/-- In rank one the element of a vector of norm `±1` does not act trivially. -/
private theorem cliffordFullCoverOfNorm_notMem_ker (v : V) [Invertible (Q v)]
    (hv : Q v = 1 ∨ Q v = -1) :
    cliffordFullCoverOfNorm v hv ∉ (cliffordFullCoverToOrthogonal Q).ker := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  rw [MonoidHom.mem_ker, cliffordFullCoverToOrthogonal_cliffordFullCoverOfNorm hV v hv]
  exact Q.negOrthogonal_ne_one

omit hQ hV [FiniteDimensional K V] in
/-- An element of the full cover is determined by its underlying Clifford element. -/
private theorem cliffordFullCover_ext_iff {x y : cliffordFullCover Q} :
    x = y ↔ (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (((y : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [Subtype.ext_iff, Subtype.ext_iff, Units.ext_iff]

/-- **A cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, if some vector `e` of a nondegenerate line has norm `-1`, then
`e ^ 2 = -1`, so `e` has order four and generates the full cover. -/
theorem isCyclic_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) {v : V} (hv : Q v = -1) :
    IsCyclic (cliffordFullCover Q) := by
  have hcard := card_cliffordFullCover_of_finrank_eq_one hQ hV h hK
  have : Finite (cliffordFullCover Q) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Invertible (Q v) := invertibleOfNonzero (by rw [hv]; exact neg_ne_zero.2 one_ne_zero)
  refine isCyclic_of_orderOf_eq_card (cliffordFullCoverOfNorm v (Or.inr hv)) ?_
  rw [hcard]
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow, pow_one, sq, ι_sq_scalar, hv]
    intro h1
    have h2 : (-1 : K) = 1 := (algebraMap_injective Q).eq_iff.1 (by simpa using h1)
    exact two_ne_zero (by linear_combination -h2 : (2 : K) = 0)
  · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow,
      show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, sq (ι Q v), ι_sq_scalar, hv]
    simp

/-- **A non-cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, if some vector `e` of a nondegenerate line has norm `1`, then `1`,
`-1` and `e` are three solutions of `x ^ 2 = 1` in the full cover, which a cyclic group of order
four cannot have. -/
theorem not_isCyclic_cliffordFullCover_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) {v : V} (hv : Q v = 1) :
    ¬IsCyclic (cliffordFullCover Q) := by
  intro hcyc
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have hcard := card_cliffordFullCover_of_finrank_eq_one hQ hV h hK
  have : Finite (cliffordFullCover Q) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Invertible (Q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  let _ : Fintype (cliffordFullCover Q) := Fintype.ofFinite _
  classical
  let e := cliffordFullCoverOfNorm v (Or.inl hv)
  let m := spinToCliffordFullCover Q (spinGroup.negOne Q hQ.ne_zero)
  have hm : m ∈ (cliffordFullCoverToOrthogonal Q).ker :=
    (mem_ker_cliffordFullCoverToOrthogonal_iff hQ h m).2 (Or.inr rfl)
  have hm1 : m ≠ 1 := fun h1 ↦ spinGroup.negOne_ne_one Q hQ.ne_zero
    (spinToCliffordFullCover_injective Q (by rw [map_one]; exact h1))
  have he : e ∉ (cliffordFullCoverToOrthogonal Q).ker := cliffordFullCoverOfNorm_notMem_ker hV v _
  have hsub : ({1, m, e} : Finset (cliffordFullCover Q)) ⊆
      Finset.univ.filter fun a ↦ a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with ha | ha | ha <;> rw [ha]
    · exact one_pow 2
    · rw [sq, ← map_mul, spinGroup.negOne_mul_self, map_one]
    · rw [cliffordFullCover_ext_iff, coe_cliffordFullCoverOfNorm_pow, sq, ι_sq_scalar, hv, map_one,
        OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one]
  have h3 : ({1, m, e} : Finset (cliffordFullCover Q)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, m, e, hm1.symm, fun h1 ↦ he (h1 ▸ one_mem _),
      fun h1 ↦ he (h1 ▸ hm), rfl⟩
  have := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := cliffordFullCover Q) two_pos)
  omega

/-- **The cyclic full cover in rank one.** Over a field in which `-1` is not a square but every
element is a square up to sign, the full cover of a nondegenerate line, a group of order four, is
cyclic exactly when some vector has norm `-1`. Otherwise some vector has norm `1`, obtained by
rescaling a vector of nonzero norm by a square root of its norm. -/
theorem isCyclic_cliffordFullCover_iff_of_finrank_eq_one (h : ¬IsSquare (-1 : K))
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    IsCyclic (cliffordFullCover Q) ↔ ∃ v, Q v = -1 := by
  refine ⟨fun hcyc ↦ ?_, fun ⟨v, hv⟩ ↦ isCyclic_cliffordFullCover_of_finrank_eq_one hQ hV h hK hv⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨w, hw⟩ := hQ.exists_isUnit
  rcases hK (Q w) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hr0 : r ≠ 0 := by rintro rfl; simp [hr] at hw
    refine absurd hcyc (not_isCyclic_cliffordFullCover_of_finrank_eq_one hQ hV h hK
      (v := r⁻¹ • w) ?_)
    rw [QuadraticMap.map_smul, smul_eq_mul, hr]
    field_simp
  · have hr0 : r ≠ 0 := by rintro rfl; simp at hr; simp [hr] at hw
    refine ⟨r⁻¹ • w, ?_⟩
    rw [QuadraticMap.map_smul, smul_eq_mul, ← neg_neg (Q w), hr]
    field_simp

end RankOne

end Field

end CliffordAlgebra
