/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Alcove
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Basic
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.RootSystem.Lowering

/-!
# The affine Weyl group is transitive on the alcoves

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over an
archimedean linearly ordered ring, with simple roots `αᵢ` and highest root `θ`. The affine root
hyperplanes `H_{α,k} = {x | α(x) = k}` of the coweight space `N` cut it into alcoves, and the
fundamental alcove `A` is the one cut out by the walls `αᵢ = 0` and `θ = 1`. This file proves that
the affine Weyl group `W_aff` (`RootPairing.affineWeylGroup`) moves every point into the closed
fundamental alcove, and so permutes the alcoves transitively: every alcove is `f⁻¹(A)` for some
`f ∈ W_aff`.

The proof is the classical descent of Bourbaki and Humphreys, made purely combinatorial. An affine
root is a pair `(j, k)` of a root index and an integer, standing for the affine function
`αⱼ - k`; call it positive when it is positive on `A`, that is when `k < 0`, or `k = 0` and `αⱼ`
is a positive root. A point `x` lies on the far side of the hyperplane of a positive affine root
when `αⱼ(x) < k`, and only finitely many positive affine roots have this property, because the
ring is archimedean. If `x` is not in the closed fundamental alcove, it lies on the far side of a
wall of `A`: `αᵢ(x) < 0` for a simple root, or `θ(x) > 1`. The reflection `s` in that wall
exchanges the two affine roots of the wall and permutes all the other positive affine roots, so
`s x` lies on the far side of exactly one fewer hyperplane than `x`. Induction on this number
finishes the proof.

For a simple wall, that `s` permutes the other positive affine roots is the fact that a simple
reflection permutes the positive roots other than its own
(`RootPairing.Base.isPos_reflectionPerm_iff`).
For the wall `θ = 1` it is a computation with heights: reflecting in `θ` changes the height of a
root by a multiple of the height of `θ`, and every root other than `±θ` has height strictly between
`-ht(θ)` and `ht(θ)`.

## Main results

* `RootPairing.exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove`: **every point of the
  coweight space is carried into the closed fundamental alcove by the affine Weyl group.**
* `RootPairing.iUnion_image_closedFundamentalAlcove_eq_univ`: the translates of the closed
  fundamental alcove under the affine Weyl group cover the coweight space.
* `RootPairing.exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove`: a point lying on no affine
  root hyperplane is carried into the open fundamental alcove.
* `RootPairing.exists_mem_affineWeylGroup_preimage_fundamentalAlcove_eq`: **the affine Weyl group
  is transitive on the alcoves**: the alcove of a point lying on no affine root hyperplane, the set
  of points lying on no such hyperplane and on the same side of each of them, is the preimage of
  the fundamental alcove under an element of the affine Weyl group.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §3.2 and Ch. VI, §2.1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, §4.3 and §4.5.
-/

public section

open Set

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-! ### Affine reflections acting on affine roots -/

section WallPerm

variable (P : RootPairing ι R M N)

variable [CharZero R] [P.IsCrystallographic]

/-- The affine roots under the affine reflection `s_{αⱼ₀,c}`: `(αⱼ - k) ∘ s_{αⱼ₀,c}` is the affine
root `α_{s_{j₀} j} - (k - ⟨αⱼ, αⱼ₀^∨⟩ c)`. -/
private noncomputable def wallPerm (j₀ : ι) (c : ℤ) (p : ι × ℤ) : ι × ℤ :=
  (P.reflectionPerm j₀ p.1, p.2 - P.pairingIn ℤ p.1 j₀ * c)

omit [CharZero R] in
private lemma wallPerm_injective (j₀ : ι) (c : ℤ) : Function.Injective (wallPerm P j₀ c) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [wallPerm, Prod.mk.injEq] at h
  obtain rfl := (P.reflectionPerm j₀).injective h.1
  simpa using h.2

private lemma wallPerm_wall (j₀ : ι) (c : ℤ) :
    wallPerm P j₀ c (j₀, c) = (P.reflectionPerm j₀ j₀, -c) := by
  simp only [wallPerm, pairingIn_same, Prod.mk.injEq, true_and]
  ring

private lemma wallPerm_wall' (j₀ : ι) (c : ℤ) :
    wallPerm P j₀ c (P.reflectionPerm j₀ j₀, -c) = (j₀, c) := by
  simp only [wallPerm, reflectionPerm_self, pairingIn_reflectionPerm_self_left, pairingIn_same,
    Prod.mk.injEq, true_and]
  ring

end WallPerm

/-! ### Positive affine roots and the hyperplanes separating a point from the alcove -/

section Separation

variable [LinearOrder R] [IsStrictOrderedRing R] {P : RootPairing ι R M N} (b : P.Base)

/-- The affine root `αⱼ - k`, encoded as `(j, k)`, is positive on the fundamental alcove: `k < 0`,
or `k = 0` and `αⱼ` is a positive root. -/
private def IsAffinePos (p : ι × ℤ) : Prop :=
  p.2 < 0 ∨ (p.2 = 0 ∧ 0 < b.height p.1)

/-- The positive affine roots whose hyperplane separates `x` from the fundamental alcove. -/
private def sepSet (x : N) : Set (ι × ℤ) :=
  {p | IsAffinePos b p ∧ P.root' p.1 x < p.2}

/-- Only finitely many affine root hyperplanes separate a point from the fundamental alcove. -/
private lemma sepSet_finite [Finite ι] [Archimedean R] (x : N) : (sepSet b x).Finite := by
  choose n hn using fun j ↦ exists_int_lt (P.root' j x)
  refine (Set.finite_iUnion fun j ↦
    (Set.finite_singleton j).prod (Set.finite_Icc (n j) 0)).subset ?_
  rintro ⟨j, k⟩ ⟨hpos, hk⟩
  refine Set.mem_iUnion.mpr ⟨j, Set.mem_prod.mpr ⟨rfl, ?_, ?_⟩⟩
  · exact (Int.cast_lt.mp ((hn j).trans hk)).le
  · rcases hpos with h | h
    · exact h.le
    · exact h.1.le

/-- At most one of the two affine roots of a wall is positive. -/
private lemma not_isAffinePos_and (j₀ : ι) (c : ℤ) :
    ¬ (IsAffinePos b (j₀, c) ∧ IsAffinePos b (P.reflectionPerm j₀ j₀, -c)) := by
  let := P.indexNeg
  have : b.height (P.reflectionPerm j₀ j₀) = -b.height j₀ := b.height_reflectionPerm_self j₀
  simp only [IsAffinePos]
  omega

variable [P.IsCrystallographic]

/-- **The descent step.** Let `s` be the affine reflection in the hyperplane `αⱼ₀ = c`, and suppose
that `s` permutes the positive affine roots other than the two affine roots `±(αⱼ₀ - c)` of its
hyperplane. If that hyperplane separates `x` from the fundamental alcove, then `s x` is separated
from the alcove by strictly fewer affine root hyperplanes than `x`. -/
private lemma ncard_sepSet_affineCoreflection_lt [Finite ι] [Archimedean R] {j₀ : ι} {c : ℤ}
    (hpres : ∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
      (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p))
    {x : N} {w : ι × ℤ} (hw : w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c))
    (hwx : w ∈ sepSet b x) :
    (sepSet b (P.affineCoreflection j₀ c x)).ncard < (sepSet b x).ncard := by
  set y := P.affineCoreflection j₀ c x
  have hy : P.root' j₀ y = 2 * c - P.root' j₀ x := root'_affineCoreflection_self P j₀ c x
  -- Neither affine root of the wall separates `y` from the alcove: one of them is not positive,
  -- and the reflection carries `x` to the alcove's side of the wall.
  have hwall₁ : (j₀, c) ∉ sepSet b y := by
    rintro ⟨hpos, hlt⟩
    rcases hw with rfl | rfl
    · have := hwx.2
      simp only at hlt this
      linarith
    · exact not_isAffinePos_and b j₀ c ⟨hpos, hwx.1⟩
  have hwall₂ : (P.reflectionPerm j₀ j₀, -c) ∉ sepSet b y := by
    rintro ⟨hpos, hlt⟩
    rcases hw with rfl | rfl
    · exact not_isAffinePos_and b j₀ c ⟨hwx.1, hpos⟩
    · have := hwx.2
      simp only [root'_reflectionPerm_self, LinearMap.neg_apply, Int.cast_neg] at hlt this
      linarith
  -- So `wallPerm` maps the hyperplanes separating `y` injectively to the other hyperplanes
  -- separating `x`.
  have hmaps : ∀ p ∈ sepSet b y, wallPerm P j₀ c p ∈ sepSet b x \ {w} := by
    rintro ⟨j, k⟩ hp
    have hp₁ : (j, k) ≠ (j₀, c) := fun h ↦ hwall₁ (h ▸ hp)
    have hp₂ : (j, k) ≠ (P.reflectionPerm j₀ j₀, -c) := fun h ↦ hwall₂ (h ▸ hp)
    refine ⟨⟨(hpres _ hp₁ hp₂).mpr hp.1, ?_⟩, fun h ↦ ?_⟩
    · have := hp.2
      simp only [y, root'_affineCoreflection_intCast] at this
      simp only [wallPerm, Int.cast_sub]
      linarith
    · rcases hw with rfl | rfl
      · exact hp₂ (wallPerm_injective P j₀ c (h.trans (wallPerm_wall' P j₀ c).symm))
      · exact hp₁ (wallPerm_injective P j₀ c (h.trans (wallPerm_wall P j₀ c).symm))
  calc (sepSet b y).ncard ≤ (sepSet b x \ {w}).ncard :=
        ncard_le_ncard_of_injOn _ hmaps (wallPerm_injective P j₀ c).injOn
          ((sepSet_finite b x).sdiff)
    _ < (sepSet b x).ncard := ncard_sdiff_singleton_lt_of_mem hwx (sepSet_finite b x)

/-- A simple reflection permutes the positive affine roots other than `±αᵢ`. -/
private lemma isAffinePos_wallPerm_simple [Finite ι] [P.IsReduced] {i : ι} (hi : i ∈ b.support)
    {p : ι × ℤ} (hp₁ : p ≠ (i, (0 : ℤ))) (hp₂ : p ≠ (P.reflectionPerm i i, -(0 : ℤ))) :
    IsAffinePos b (wallPerm P i 0 p) ↔ IsAffinePos b p := by
  obtain ⟨j, k⟩ := p
  simp only [wallPerm, mul_zero, sub_zero, IsAffinePos]
  rcases eq_or_ne k 0 with rfl | hk
  · have hj₁ : j ≠ i := fun h ↦ hp₁ (by rw [h])
    have hj₂ : j ≠ P.reflectionPerm i i := fun h ↦ hp₂ (by rw [h, neg_zero])
    have := Base.isPos_reflectionPerm_iff P b hi hj₁ hj₂
    simp only [Base.IsPos] at this
    simp [this]
  · simp [hk]

variable [Finite ι] [Nonempty ι] [P.IsReduced] [P.IsIrreducible]

/-- The reflection in the wall `θ = 1` permutes the positive affine roots other than `±(θ - 1)`. -/
private lemma isAffinePos_wallPerm_highestRoot {p : ι × ℤ} (hp₁ : p ≠ (b.highestRoot, 1))
    (hp₂ : p ≠ (P.reflectionPerm b.highestRoot b.highestRoot, -1)) :
    IsAffinePos b (wallPerm P b.highestRoot 1 p) ↔ IsAffinePos b p := by
  obtain ⟨j, k⟩ := p
  simp only [wallPerm, mul_one, IsAffinePos, TauCeti.height_reflectionPerm P b b.highestRoot j]
  have hθ : 0 < b.height b.highestRoot := b.isPos_highestRoot
  have hlo := b.neg_height_highestRoot_le_height j
  have hhi := b.height_le_height_highestRoot j
  have hlo' := b.neg_height_highestRoot_le_height (P.reflectionPerm b.highestRoot j)
  have hhi' := b.height_le_height_highestRoot (P.reflectionPerm b.highestRoot j)
  rw [TauCeti.height_reflectionPerm P b b.highestRoot j] at hlo' hhi'
  have h₀ := b.height_ne_zero j
  have htop' : b.height j = b.height b.highestRoot → k ≠ 1 := fun h hk ↦ hp₁ <| by
    rw [hk, not_ne_iff.mp fun hne ↦ (b.height_lt_height_highestRoot hne).ne h]
  have hbot' : b.height j = -b.height b.highestRoot → k ≠ -1 := fun h hk ↦ hp₂ <| by
    rw [hk, not_ne_iff.mp fun hne ↦ (b.neg_height_highestRoot_lt_height hne).ne' h]
  set m := P.pairingIn ℤ j b.highestRoot
  have hm₁ : m ≤ 2 := by nlinarith
  have hm₂ : -2 ≤ m := by nlinarith
  interval_cases m <;> omega

end Separation

/-! ### Transitivity -/

variable [LinearOrder R] [IsStrictOrderedRing R] {P : RootPairing ι R M N} (b : P.Base)
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
  [Archimedean R]

/-- **The affine Weyl group carries every point into the closed fundamental alcove.** -/
theorem exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove (x : N) :
    ∃ f ∈ P.affineWeylGroup, f x ∈ closedFundamentalAlcove P b := by
  -- Induction on the number of affine root hyperplanes separating `x` from the alcove.
  induction hn : (sepSet b x).ncard using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hx : x ∈ closedFundamentalAlcove P b
  · exact ⟨1, one_mem _, hx⟩
  -- Otherwise `x` is beyond a wall `αⱼ₀ = c` of the alcove, and reflecting in it lowers `n`.
  obtain ⟨j₀, c, hpres, w, hw, hwx⟩ : ∃ (j₀ : ι) (c : ℤ),
      (∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
        (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p)) ∧
      ∃ w, (w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c)) ∧ w ∈ sepSet b x := by
    simp only [mem_closedFundamentalAlcove, not_and_or, not_forall, not_le] at hx
    rcases hx with ⟨i, hi, hix⟩ | hθx
    · refine ⟨i, 0, fun p ↦ isAffinePos_wallPerm_simple b hi, (i, 0), .inl rfl, ?_, ?_⟩
      · exact .inr ⟨rfl, b.isPos_of_mem_support hi⟩
      · simpa using hix
    · refine ⟨b.highestRoot, 1, fun p ↦ isAffinePos_wallPerm_highestRoot b,
        (P.reflectionPerm b.highestRoot b.highestRoot, -1), .inr rfl, .inl (by omega), ?_⟩
      simpa [root'_reflectionPerm_self] using hθx
  obtain ⟨f, hf, hfx⟩ := ih _ (hn ▸ ncard_sepSet_affineCoreflection_lt b hpres hw hwx) _ rfl
  exact ⟨f * P.affineCoreflection j₀ c, mul_mem hf (P.affineCoreflection_mem_affineWeylGroup j₀ c),
    hfx⟩

/-- The translates of the closed fundamental alcove under the affine Weyl group cover the coweight
space. -/
theorem iUnion_image_closedFundamentalAlcove_eq_univ :
    ⋃ f ∈ P.affineWeylGroup, f '' closedFundamentalAlcove P b = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨f, hf, hfx⟩ := exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove b x
  exact mem_iUnion₂.mpr ⟨f⁻¹, inv_mem hf, f x, hfx, by simp [AffineEquiv.inv_def]⟩

/-- **A point lying on no affine root hyperplane is carried into the open fundamental alcove** by
the affine Weyl group. -/
theorem exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove {x : N}
    (hx : ∀ j (k : ℤ), P.root' j x ≠ k) :
    ∃ f ∈ P.affineWeylGroup, f x ∈ fundamentalAlcove P b := by
  obtain ⟨f, hf, hfx⟩ := exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove b x
  exact ⟨f, hf, mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove.mpr
    ⟨hfx, P.root'_apply_ne_intCast_of_mem_affineWeylGroup hf hx⟩⟩

/-- **The affine Weyl group is transitive on the alcoves.** The alcove of a point `x` lying on no
affine root hyperplane, the set of points lying on no affine root hyperplane and on the same side
as `x` of each of them, is the preimage of the fundamental alcove under an element of the affine
Weyl group. -/
theorem exists_mem_affineWeylGroup_preimage_fundamentalAlcove_eq {x : N}
    (hx : ∀ j (k : ℤ), P.root' j x ≠ k) :
    ∃ f ∈ P.affineWeylGroup, f ⁻¹' fundamentalAlcove P b =
      {y | ∀ j (k : ℤ), ((k : R) < P.root' j y ↔ (k : R) < P.root' j x) ∧ P.root' j y ≠ k} := by
  obtain ⟨f, hf, hfx⟩ := exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove b hx
  refine ⟨f, hf, Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩⟩
  · have hy' := (mem_fundamentalAlcove_iff_of_mem hfx).mp hy
    have h₁ := P.intCast_lt_root'_apply_iff_of_mem_affineWeylGroup (inv_mem hf)
      fun j k ↦ (hy' j k).1
    have h₂ := P.root'_apply_ne_intCast_of_mem_affineWeylGroup (inv_mem hf) fun j k ↦ (hy' j k).2
    simp only [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] at h₁ h₂
    exact fun j k ↦ ⟨h₁ j k, h₂ j k⟩
  · exact (mem_fundamentalAlcove_iff_of_mem hfx).mpr fun j k ↦
      ⟨P.intCast_lt_root'_apply_iff_of_mem_affineWeylGroup hf (fun j k ↦ (hy j k).1) j k,
        P.root'_apply_ne_intCast_of_mem_affineWeylGroup hf (fun j k ↦ (hy j k).2) j k⟩

end RootPairing
