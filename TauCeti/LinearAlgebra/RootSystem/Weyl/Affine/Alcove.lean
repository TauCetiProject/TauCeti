/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Alcove
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Basic
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice
import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber

/-!
# The affine Weyl group acts simply transitively on the alcoves

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over a
linearly ordered ring, with simple roots `αᵢ` and highest root `θ`. The affine root hyperplanes
`H_{α,k} = {x | α(x) = k}` of the coweight space `N` cut it into alcoves, and the fundamental alcove
`A` is the one cut out by the walls `αᵢ = 0` and `θ = 1`. This file proves that the reflections in
the walls of `A`, the affine simple reflections (`RootPairing.Base.affineSimpleReflection`), move
into the closed fundamental alcove every point at which every root is bounded below by an integer.
Only the corollaries about every point need the ring to be archimedean: over an archimedean ring
the affine Weyl group `W_aff` (`RootPairing.affineWeylGroup`) moves every point into the closed
fundamental alcove, and so permutes the alcoves transitively: every alcove is `f⁻¹(A)` for some
`f ∈ W_aff`. The file then proves, over any linearly ordered ring, that `W_aff` acts freely on the
translates of `A`, so that this `f` is unique.

The proof is the classical descent of Bourbaki and Humphreys, made purely combinatorial. An affine
root is a pair `(j, k)` of a root index and an integer, standing for the affine function `αⱼ - k`;
call it positive when it is positive on `A`, that is when `k < 0`, or `k = 0` and `αⱼ` is a positive
root. A point `x` lies on the far side of the hyperplane of a positive affine root when `αⱼ(x) < k`,
and only finitely many positive affine roots have this property when every root is bounded below by
an integer at `x`, which holds at every point when the ring is archimedean. If `x` is not in the
closed fundamental alcove, it lies on the far side of a wall of `A`: `αᵢ(x) < 0` for a simple root,
or `θ(x) > 1`. The reflection `s` in that wall exchanges the two affine roots of the wall and
permutes all the other positive affine roots, so `s x` lies on the far side of exactly one fewer
hyperplane than `x`. Induction on this number finishes the proof. Only the reflections in the walls
of `A` are used, so they already carry into the closed alcove every point at which every root is
bounded below by an integer; such points include every point over an archimedean ring, and the
images under the affine Weyl group of the points of `A`
(`RootPairing.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup`). Seen from a point of `A`, the
positive affine roots are the affine roots positive at that point, so the affine roots counted are
those of `RootPairing.separatingAffineRoots`.

For a simple wall, that `s` permutes the other positive affine roots is the fact that a simple
reflection permutes the positive roots other than its own
(`RootPairing.Base.isPos_reflectionPerm_iff`).
For the wall `θ = 1` it is a computation with heights: reflecting in `θ` changes the height of a
root by a multiple of the height of `θ`, and every root other than `±θ` has height strictly between
`-ht(θ)` and `ht(θ)`.

Freeness on the translates of `A` needs no archimedean hypothesis. Write an element of `W_aff`
as `f = t_v ∘ w`, with `w` in the coweight image of the Weyl group and `v` in the coroot lattice
`Q∨` (`RootPairing.mem_affineWeylGroup_iff`). Every root takes its values in `(-1, 1)` on `A`, so
if `f` carries a point of `A` into `A`, every root takes a value in `(-2, 2)` at `v`. A minuscule
element of the coroot lattice is zero
(`RootPairing.eq_zero_of_mem_corootSpan_of_forall_abs_root'_lt_two`), so `v = 0`, and `w` then
carries a point of the open dominant chamber into the dominant chamber, which forces `w = 1`
(`TauCeti.eq_one_of_smul_mem_dominantChamber`). This replaces the usual gallery argument with the
Coxeter generators by the free action of the finite Weyl group on the chambers.

## Main results

* `RootPairing.exists_mem_apply_mem_closedFundamentalAlcove_of_affineCoreflection_mem`: **a point
  at which every root is bounded below by an integer is carried into the closed fundamental alcove
  by the reflections in the walls of the alcove**, `s_{αᵢ,0}` and `s_{θ,1}`; and so, over an
  archimedean ring, `RootPairing.exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove`:
  every point is carried into it by the affine Weyl group.
* `RootPairing.exists_wallWord_apply_mem_closedFundamentalAlcove`: such a point is carried into the
  closed fundamental alcove by a word in the wall reflections with one letter for each affine root
  separating it from the fundamental alcove.
* The wall step,
  `RootPairing.ncard_separatingAffineRoots_affineSimpleReflection_add_one_of_affineSimpleRoot_neg`:
  the reflection in a wall separating a point from the fundamental alcove lowers the number of
  affine root hyperplanes separating it from the alcove by exactly one, when every root is bounded
  below by an integer at the point.
* `RootPairing.iUnion_image_closedFundamentalAlcove_eq_univ`: the translates of the closed
  fundamental alcove under the affine Weyl group cover the coweight space.
* `RootPairing.exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove`: a point lying on no affine
  root hyperplane is carried into the open fundamental alcove.
* `RootPairing.eq_zero_of_mem_corootSpan_of_mem_closedFundamentalAlcove`: the only point of the
  coroot lattice in the closed fundamental alcove is `0`.
* `RootPairing.exists_mem_affineWeylGroup_preimage_fundamentalAlcove_eq`: **the affine Weyl group
  is transitive on the alcoves**: the alcove of a point lying on no affine root hyperplane, the set
  of points lying on no such hyperplane and on the same side of each of them, is the preimage of
  the fundamental alcove under an element of the affine Weyl group.
* `RootPairing.eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove`: **the affine Weyl
  group acts freely on the translates of the fundamental alcove**: an element carrying a point of
  the fundamental alcove into the fundamental alcove is the identity.
* `RootPairing.exists_wallWord_eq_inv_of_mem_affineWeylGroup`: the inverse of an element `f` of the
  affine Weyl group is a word in the wall reflections with one letter for each affine root
  separating a point of the fundamental alcove from its image under `f`.
* `RootPairing.eq_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove` and
  `RootPairing.eq_one_of_mem_affineWeylGroup_of_mapsTo`: two elements carrying the same point into
  the fundamental alcove are equal, and the stabilizer of a nonempty fundamental alcove is trivial.
* `RootPairing.existsUnique_mem_affineWeylGroup_preimage_fundamentalAlcove_eq`: **the affine Weyl
  group acts simply transitively on the alcoves.**

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

/-! ### The reflections in the walls of the fundamental alcove -/

namespace Base

section WallReflection

variable {P : RootPairing ι R M N} (b : P.Base) [CharZero R] [Finite ι] [Nonempty ι]

/-- The **affine simple reflections** of a base `b`, the reflections in the walls of the
fundamental alcove, the zero sets of the affine simple roots `aₖ`
(`RootPairing.Base.affineSimpleRoot`): the affine reflection `s_{θ,1}` in the wall `θ = 1` at the
affine node `none`, and the simple coreflection `s_{αᵢ,0}` in the wall `αᵢ = 0` at a simple node
`some i`. -/
noncomputable def affineSimpleReflection : Option b.support → N ≃ᵃ[R] N
  | none => P.affineCoreflection b.highestRoot 1
  | some i => (P.coreflection i).toAffineEquiv

@[simp]
lemma affineSimpleReflection_none :
    b.affineSimpleReflection none = P.affineCoreflection b.highestRoot 1 :=
  (rfl)

@[simp]
lemma affineSimpleReflection_some (i : b.support) :
    b.affineSimpleReflection (some i) = (P.coreflection i).toAffineEquiv :=
  (rfl)

@[simp]
lemma affineSimpleReflection_mem_affineWeylGroup (k : Option b.support) :
    b.affineSimpleReflection k ∈ P.affineWeylGroup := by
  rcases k with _ | i
  · simpa using P.affineCoreflection_mem_affineWeylGroup b.highestRoot 1
  · simpa using P.affineCoreflection_mem_affineWeylGroup i 0

/-- The affine simple reflection at `k` is `x ↦ x - aₖ(x) αₖ^∨`, with `α₀^∨ = -θ^∨`. -/
lemma affineSimpleReflection_apply (k : Option b.support) (x : N) :
    b.affineSimpleReflection k x =
      x - b.affineSimpleRoot k x • P.coroot (b.affineSimpleRootIndex k) := by
  rcases k with _ | i
  · simp only [affineSimpleReflection_none, affineCoreflection_apply_eq_sub, affineSimpleRoot_none,
      affineSimpleRootIndex_none, coroot_reflectionPerm, coreflection_apply_self]
    module
  · rw [affineSimpleReflection_some, ← affineCoreflection_zero]
    simp only [affineCoreflection_apply_eq_sub, affineSimpleRoot_some, affineSimpleRootIndex_some,
      sub_zero]

/-- The affine simple reflection at `k` negates the affine simple root `aₖ`. -/
@[simp]
lemma affineSimpleRoot_affineSimpleReflection (k : Option b.support) (x : N) :
    b.affineSimpleRoot k (b.affineSimpleReflection k x) = -b.affineSimpleRoot k x := by
  rcases k with _ | i
  · simp only [affineSimpleReflection_none, affineSimpleRoot_none, root'_affineCoreflection_self]
    ring
  · rw [affineSimpleReflection_some, ← affineCoreflection_zero]
    simp only [affineSimpleRoot_some, root'_affineCoreflection_self]
    ring

@[simp]
lemma affineSimpleReflection_affineSimpleReflection (k : Option b.support) (x : N) :
    b.affineSimpleReflection k (b.affineSimpleReflection k x) = x := by
  rcases k with _ | i <;> simp

/-- A word in the affine simple reflections lies in every subgroup containing them. -/
lemma list_prod_map_affineSimpleReflection_mem {G : Subgroup (N ≃ᵃ[R] N)}
    (hG : ∀ k, b.affineSimpleReflection k ∈ G) (ω : List (Option b.support)) :
    (ω.map b.affineSimpleReflection).prod ∈ G :=
  G.list_prod_mem fun _ hf ↦ by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hf
    exact hG k

end WallReflection

end Base

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

/-- Only finitely many affine root hyperplanes separate a point from the fundamental alcove, when
every root is bounded below by an integer at the point (always, over an archimedean ring). -/
private lemma sepSet_finite [Finite ι] {x : N} (hx : ∀ j, ∃ n : ℤ, (n : R) < P.root' j x) :
    (sepSet b x).Finite := by
  choose n hn using hx
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

/-- Let `s` be the affine reflection in the hyperplane `αⱼ₀ = c`, and suppose that `s` permutes
the positive affine roots other than the two affine roots `±(αⱼ₀ - c)` of its hyperplane. If one of
them separates `x` from the fundamental alcove, then the other hyperplanes separating `x` correspond
under `wallPerm` to hyperplanes separating `s x`: the wall's other affine root is not positive. -/
private lemma mapsTo_wallPerm_sepSet_sdiff {j₀ : ι} {c : ℤ}
    (hpres : ∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
      (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p))
    {x : N} {w : ι × ℤ} (hw : w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c))
    (hwx : w ∈ sepSet b x) :
    ∀ p ∈ sepSet b x \ {w}, wallPerm P j₀ c p ∈ sepSet b (P.affineCoreflection j₀ c x) := by
  rintro ⟨j, k⟩ ⟨hp, hpw⟩
  have hpw : (j, k) ≠ w := Set.notMem_singleton_iff.mp hpw
  have hp₁ : (j, k) ≠ (j₀, c) := by
    intro h
    rcases hw with rfl | rfl
    · exact hpw h
    · exact not_isAffinePos_and b j₀ c ⟨h ▸ hp.1, hwx.1⟩
  have hp₂ : (j, k) ≠ (P.reflectionPerm j₀ j₀, -c) := by
    rintro h
    rcases hw with rfl | rfl
    · exact not_isAffinePos_and b j₀ c ⟨hwx.1, h ▸ hp.1⟩
    · exact hpw h
  refine ⟨(hpres _ hp₁ hp₂).mpr hp.1, ?_⟩
  have := hp.2
  simp only [wallPerm, root'_affineCoreflection_intCast, reflectionPerm_self,
    ← pairingIn_reflectionPerm, pairingIn_reflectionPerm_self_right, Int.cast_sub,
    Int.cast_mul, Int.cast_neg] at this ⊢
  linarith

/-- **The descent step.** Let `s` be the affine reflection in the hyperplane `αⱼ₀ = c`, and suppose
that `s` permutes the positive affine roots other than the two affine roots `±(αⱼ₀ - c)` of its
hyperplane. If that hyperplane separates `x` from the fundamental alcove, then `s x` is separated
from the alcove by exactly one fewer affine root hyperplane than `x`. -/
private lemma ncard_sepSet_affineCoreflection_add_one [Finite ι] {j₀ : ι} {c : ℤ}
    (hpres : ∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
      (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p))
    {x : N} (hx : ∀ j, ∃ n : ℤ, (n : R) < P.root' j x) {w : ι × ℤ}
    (hw : w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c))
    (hwx : w ∈ sepSet b x) :
    (sepSet b (P.affineCoreflection j₀ c x)).ncard + 1 = (sepSet b x).ncard := by
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
  have hfin := sepSet_finite b hx
  have hle := ncard_le_ncard_of_injOn _ hmaps (wallPerm_injective P j₀ c).injOn hfin.sdiff
  have hge : (sepSet b x \ {w}).ncard ≤ (sepSet b y).ncard :=
    ncard_le_ncard_of_injOn _ (mapsTo_wallPerm_sepSet_sdiff b hpres hw hwx)
    (wallPerm_injective P j₀ c).injOn
    (sepSet_finite b (P.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup
      (P.affineCoreflection_mem_affineWeylGroup j₀ c) hx))
  rw [← ncard_sdiff_singleton_add_one hwx hfin]
  omega

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

/-- Seen from a point `x` of the fundamental alcove, the affine roots positive at `x` are the
positive affine roots, so the affine roots separating `x` from `y` are those separating `y` from
the alcove. -/
private lemma separatingAffineRoots_eq_sepSet {x : N} (hx : x ∈ fundamentalAlcove P b) (y : N) :
    P.separatingAffineRoots x y = sepSet b y := by
  ext ⟨j, k⟩
  suffices IsAffinePos b (j, k) ↔ (k : R) < P.root' j x by
    simp only [mem_separatingAffineRoots, sepSet, Set.mem_ofPred_eq, this]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro (hk | ⟨rfl, hj⟩)
    · have hk' : k ≤ -1 := by omega
      have : (k : R) ≤ -1 := by exact_mod_cast hk'
      linarith [neg_one_lt_root'_of_mem_fundamentalAlcove hx j]
    · simpa using root'_pos_of_isPos ((mem_fundamentalAlcove P b).mp hx).1 hj
  · have hk : k < 1 := by exact_mod_cast h.trans (root'_lt_one_of_mem_fundamentalAlcove hx j)
    have hk' : k < 0 ∨ k = 0 := by omega
    rcases hk' with hk | rfl
    · exact .inl hk
    · refine .inr ⟨rfl, ?_⟩
      by_contra hj
      exact (root'_neg_of_not_isPos ((mem_fundamentalAlcove P b).mp hx).1 hj).not_gt
        (by simpa using h)

/-- The reflection in the wall `θ = 1` permutes the positive affine roots other than `±(θ - 1)`. -/
private lemma isAffinePos_wallPerm_highestRoot {p : ι × ℤ} (hp₁ : p ≠ (b.highestRoot, 1))
    (hp₂ : p ≠ (P.reflectionPerm b.highestRoot b.highestRoot, -1)) :
    IsAffinePos b (wallPerm P b.highestRoot 1 p) ↔ IsAffinePos b p := by
  obtain ⟨j, k⟩ := p
  simp only [wallPerm, mul_one, IsAffinePos, b.height_reflectionPerm b.highestRoot j]
  have hθ : 0 < b.height b.highestRoot := b.isPos_highestRoot
  have hlo := b.neg_height_highestRoot_le_height j
  have hhi := b.height_le_height_highestRoot j
  have hlo' := b.neg_height_highestRoot_le_height (P.reflectionPerm b.highestRoot j)
  have hhi' := b.height_le_height_highestRoot (P.reflectionPerm b.highestRoot j)
  rw [b.height_reflectionPerm b.highestRoot j] at hlo' hhi'
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

variable [LinearOrder R] [IsStrictOrderedRing R] {P : RootPairing ι R M N} (b : P.Base)
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-! ### Transitivity -/

/-- Descent records its wall word and one letter for each separating root removed. -/
private lemma exists_wallWord_apply_mem_closedFundamentalAlcove_aux {x : N}
    (hx : ∀ j, ∃ n : ℤ, (n : R) < P.root' j x) :
    ∃ ω : List (Option b.support),
      (ω.map b.affineSimpleReflection).prod x ∈ closedFundamentalAlcove P b ∧
        ω.length + (sepSet b ((ω.map b.affineSimpleReflection).prod x)).ncard =
          (sepSet b x).ncard := by
  induction hn : (sepSet b x).ncard using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hxA : x ∈ closedFundamentalAlcove P b
  · exact ⟨[], by simpa using hxA, by simpa using hn⟩
  -- Choose a wall beyond which `x` lies; reflecting in it removes one separating root.
  obtain ⟨k, j₀, c, hk, hpres, w, hw, hwx⟩ : ∃ (k : Option b.support) (j₀ : ι) (c : ℤ),
      b.affineSimpleReflection k = P.affineCoreflection j₀ c ∧
      (∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
        (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p)) ∧
      ∃ w, (w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c)) ∧ w ∈ sepSet b x := by
    simp only [mem_closedFundamentalAlcove, not_and_or, not_forall, not_le] at hxA
    rcases hxA with ⟨i, hi, hix⟩ | hθx
    · refine ⟨some ⟨i, hi⟩, i, 0, by simp, fun p ↦ isAffinePos_wallPerm_simple b hi,
        (i, 0), .inl rfl, ?_, ?_⟩
      · exact .inr ⟨rfl, b.isPos_of_mem_support hi⟩
      · simpa using hix
    · refine ⟨none, b.highestRoot, 1, by simp, fun p ↦ isAffinePos_wallPerm_highestRoot b,
        (P.reflectionPerm b.highestRoot b.highestRoot, -1), .inr rfl, .inl (by omega), ?_⟩
      simpa [root'_reflectionPerm_self] using hθx
  have hlt := ncard_sepSet_affineCoreflection_add_one b hpres hx hw hwx
  obtain ⟨ω, hω, hlen⟩ := ih (sepSet b (P.affineCoreflection j₀ c x)).ncard (by omega)
    (P.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup
      (P.affineCoreflection_mem_affineWeylGroup j₀ c) hx) rfl
  refine ⟨ω ++ [k], ?_, ?_⟩
  · simpa only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      hk, AffineEquiv.coe_mul, Function.comp_apply] using hω
  · simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      List.length_append, List.length_singleton, hk, AffineEquiv.coe_mul, Function.comp_apply]
    omega

/-- A point `y` whose roots are bounded below by integers is carried into the closed fundamental
alcove by a word in the reflections in the walls of the alcove
(`RootPairing.Base.affineSimpleReflection`) with exactly one letter for each affine root separating
a point `x` of the fundamental alcove from `y`. -/
theorem exists_wallWord_apply_mem_closedFundamentalAlcove {x y : N}
    (hx : x ∈ fundamentalAlcove P b) (hy : ∀ j, ∃ n : ℤ, (n : R) < P.root' j y) :
    ∃ ω : List (Option b.support),
      (ω.map b.affineSimpleReflection).prod y ∈ closedFundamentalAlcove P b ∧
        ω.length = (P.separatingAffineRoots x y).ncard := by
  obtain ⟨ω, hω, hcount⟩ := exists_wallWord_apply_mem_closedFundamentalAlcove_aux b hy
  refine ⟨ω, hω, ?_⟩
  have hend := separatingAffineRoots_eq_empty_of_mem_closedFundamentalAlcove
    (fundamentalAlcove_subset_closedFundamentalAlcove P b hx) hω
  rw [separatingAffineRoots_eq_sepSet b hx] at hend ⊢
  rwa [hend, Set.ncard_empty, add_zero] at hcount

/-- **The reflections in the walls of the fundamental alcove carry a point into the closed
fundamental alcove.** If a subgroup `G` of the affine automorphisms of the coweight space contains
the reflections `s_{αᵢ,0}` in the simple walls and the reflection `s_{θ,1}` in the wall `θ = 1`,
then a point at which every root is bounded below by an integer is carried into the closed
fundamental alcove by an element of `G`. Over an archimedean ring every point is such a point. -/
theorem exists_mem_apply_mem_closedFundamentalAlcove_of_affineCoreflection_mem
    {G : Subgroup (N ≃ᵃ[R] N)} (hG : ∀ i ∈ b.support, P.affineCoreflection i 0 ∈ G)
    (hθ : P.affineCoreflection b.highestRoot 1 ∈ G) {x : N}
    (hx : ∀ j, ∃ n : ℤ, (n : R) < P.root' j x) :
    ∃ f ∈ G, f x ∈ closedFundamentalAlcove P b := by
  obtain ⟨ω, hω, -⟩ := exists_wallWord_apply_mem_closedFundamentalAlcove_aux b hx
  refine ⟨_, b.list_prod_map_affineSimpleReflection_mem ?_ ω, hω⟩
  rintro (_ | ⟨i, hi⟩)
  · exact hθ
  · simpa using hG i hi

/-- **Reflecting in a wall removes one separating hyperplane.** For a point `x` of the fundamental
alcove and a point `y` on the far side of the wall at the node `k` of the affine Dynkin diagram,
where the affine simple root `aₖ` is negative, and at which every root is bounded below by an
integer, the reflection in that wall (`RootPairing.Base.affineSimpleReflection`) carries `y` to
a point separated from `x` by exactly one fewer affine root hyperplane. -/
theorem ncard_separatingAffineRoots_affineSimpleReflection_add_one_of_affineSimpleRoot_neg
    {x y : N} (hx : x ∈ fundamentalAlcove P b) (hy : ∀ j, ∃ n : ℤ, (n : R) < P.root' j y)
    {k : Option b.support} (hky : b.affineSimpleRoot k y < 0) :
    (P.separatingAffineRoots x (b.affineSimpleReflection k y)).ncard + 1 =
      (P.separatingAffineRoots x y).ncard := by
  rw [separatingAffineRoots_eq_sepSet b hx, separatingAffineRoots_eq_sepSet b hx]
  rcases k with _ | ⟨i, hi⟩
  · have hθy : 1 < P.root' b.highestRoot y := by
      rw [Base.affineSimpleRoot_none] at hky
      linarith
    simpa using ncard_sepSet_affineCoreflection_add_one b (j₀ := b.highestRoot) (c := 1)
      (fun p ↦ isAffinePos_wallPerm_highestRoot b) hy (.inr rfl)
      ⟨.inl (by omega), by simpa [root'_reflectionPerm_self] using hθy⟩
  · rw [Base.affineSimpleRoot_some] at hky
    simpa using ncard_sepSet_affineCoreflection_add_one b (j₀ := i) (c := 0)
      (fun p ↦ isAffinePos_wallPerm_simple b hi) hy (.inl rfl)
      ⟨.inr ⟨rfl, b.isPos_of_mem_support hi⟩, by simpa using hky⟩

section Transitivity

variable [Archimedean R]

/-- **The affine Weyl group carries every point into the closed fundamental alcove.** -/
theorem exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove (x : N) :
    ∃ f ∈ P.affineWeylGroup, f x ∈ closedFundamentalAlcove P b :=
  exists_mem_apply_mem_closedFundamentalAlcove_of_affineCoreflection_mem b
    (fun i _ ↦ by simpa using P.affineCoreflection_mem_affineWeylGroup i 0)
    (by simpa using P.affineCoreflection_mem_affineWeylGroup b.highestRoot 1)
    fun j ↦ exists_int_lt (P.root' j x)

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

end Transitivity

/-- **The only point of the coroot lattice in the closed fundamental alcove is `0`.** -/
theorem eq_zero_of_mem_corootSpan_of_mem_closedFundamentalAlcove {v : N}
    (hv : v ∈ P.corootSpan ℤ) (hv' : v ∈ closedFundamentalAlcove P b) : v = 0 := by
  -- Every root takes a value in `[-1, 1]` on the closed alcove, and a minuscule element of the
  -- coroot lattice vanishes.
  refine P.eq_zero_of_mem_corootSpan_of_forall_abs_root'_lt_two hv fun j ↦ ?_
  obtain ⟨hsimple, hθ⟩ := (mem_closedFundamentalAlcove P b).mp hv'
  let := P.indexNeg
  have h₁ := (root'_le_root'_highestRoot hsimple j).trans hθ
  have h₂ := (root'_le_root'_highestRoot hsimple (-j)).trans hθ
  simp only [root', root_neg_index, map_neg, LinearMap.neg_apply] at h₂
  rw [abs_lt]
  constructor <;> linarith

/-! ### Freeness and simple transitivity -/

/-- **The affine Weyl group acts freely on the translates of the fundamental alcove**: an element
of the affine Weyl group carrying a point of the fundamental alcove into the fundamental alcove is
the identity. -/
theorem eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.affineWeylGroup) {x : N} (hx : x ∈ fundamentalAlcove P b)
    (hfx : f x ∈ fundamentalAlcove P b) : f = 1 := by
  obtain ⟨hl, h0⟩ := P.mem_affineWeylGroup_iff.mp hf
  -- The translation part `f 0` is a minuscule element of the coroot lattice.
  have hf0 : f 0 = 0 := by
    refine P.eq_zero_of_mem_corootSpan_of_forall_abs_root'_lt_two h0 fun j ↦ ?_
    obtain ⟨j', hj'⟩ := P.exists_root'_apply_eq_of_mem_closure_range_coreflection hl j
    have hfx' : P.root' j (f x) = P.root' j' x + P.root' j (f 0) := by
      rw [AffineEquiv.apply_eq_linear_add f x, map_add, hj']
    have := root'_lt_one_of_mem_fundamentalAlcove hfx j
    have := neg_one_lt_root'_of_mem_fundamentalAlcove hfx j
    have := root'_lt_one_of_mem_fundamentalAlcove hx j'
    have := neg_one_lt_root'_of_mem_fundamentalAlcove hx j'
    rw [abs_lt]
    constructor <;> linarith
  -- The linear part is an element of the Weyl group of `P.flip` keeping `x` dominant.
  obtain ⟨w, hw⟩ : f.linear ∈
      MonoidHom.range ((Equiv.weightHom P.flip).domRestrict P.flip.weylGroup) := by
    rw [range_weylGroup_weightHom]
    -- `P.flip.reflection` is `P.coreflection` by definition.
    exact hl
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : P.flip.IsReduced := P.instFlipIsReduced
  -- `P.flip.flip` is `P` by definition.
  have : P.flip.flip.IsReduced := ‹P.IsReduced›
  have hw1 : w = 1 := by
    refine TauCeti.eq_one_of_smul_mem_dominantChamber P.flip b.flip w
      (fundamentalAlcove_subset_openDominantChamber P b hx) ?_
    have : w • x = f x := by
      rw [AffineEquiv.apply_eq_linear_add f x, hf0, add_zero, ← hw]
      -- The Weyl group of `P.flip` acts on `N` through `Equiv.weightHom` by definition.
      rfl
    rw [this]
    exact openDominantChamber_subset_dominantChamber _ _
      (fundamentalAlcove_subset_openDominantChamber P b hfx)
  have hlin : f.linear = 1 := by
    rw [← hw, hw1, map_one]
  ext y
  simp [AffineEquiv.apply_eq_linear_add f y, hf0, hlin]

/-- The inverse of an element `f` of the affine Weyl group is a word in the wall reflections
(`RootPairing.Base.affineSimpleReflection`) with exactly one letter for each affine root
separating a point `x` of the fundamental alcove from `f x`. -/
theorem exists_wallWord_eq_inv_of_mem_affineWeylGroup {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.affineWeylGroup) {x : N} (hx : x ∈ fundamentalAlcove P b) :
    ∃ ω : List (Option b.support), (ω.map b.affineSimpleReflection).prod = f⁻¹ ∧
      ω.length = (P.separatingAffineRoots x (f x)).ncard := by
  obtain ⟨ω, hω, hcount⟩ := exists_wallWord_apply_mem_closedFundamentalAlcove b hx
    (P.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup hf
      (exists_intCast_lt_root'_of_mem_fundamentalAlcove hx))
  set g := (ω.map b.affineSimpleReflection).prod
  have hg : g ∈ P.affineWeylGroup :=
    b.list_prod_map_affineSimpleReflection_mem b.affineSimpleReflection_mem_affineWeylGroup ω
  have hgf : g * f = 1 := eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b
    (mul_mem hg hf) hx (mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove.mpr
      ⟨hω, P.root'_apply_ne_intCast_of_mem_affineWeylGroup (mul_mem hg hf)
        (root'_ne_intCast_of_mem_fundamentalAlcove hx)⟩)
  exact ⟨ω, eq_inv_of_mul_eq_one_left hgf, hcount⟩

/-- Two elements of the affine Weyl group carrying the same point into the fundamental alcove are
equal. -/
theorem eq_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove {f g : N ≃ᵃ[R] N}
    (hf : f ∈ P.affineWeylGroup) (hg : g ∈ P.affineWeylGroup) {x : N}
    (hfx : f x ∈ fundamentalAlcove P b) (hgx : g x ∈ fundamentalAlcove P b) : f = g := by
  refine mul_inv_eq_one.mp (eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b
    (mul_mem hf (inv_mem hg)) hgx ?_)
  simpa [AffineEquiv.inv_def] using hfx

/-- **The stabilizer of the fundamental alcove in the affine Weyl group is trivial**: an element
of the affine Weyl group mapping the nonempty fundamental alcove into itself is the identity. Over
a linearly ordered field the alcove is nonempty by `RootPairing.fundamentalAlcove_nonempty`. -/
theorem eq_one_of_mem_affineWeylGroup_of_mapsTo (hA : (fundamentalAlcove P b).Nonempty)
    {f : N ≃ᵃ[R] N} (hf : f ∈ P.affineWeylGroup)
    (h : MapsTo f (fundamentalAlcove P b) (fundamentalAlcove P b)) : f = 1 :=
  have ⟨_, hx⟩ := hA
  eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b hf hx (h hx)

/-- **The affine Weyl group acts simply transitively on the alcoves.** For a point `x` lying on no
affine root hyperplane, exactly one element of the affine Weyl group pulls the fundamental alcove
back to the alcove of `x`: the set of points lying on no affine root hyperplane and on the same
side as `x` of each of them. -/
theorem existsUnique_mem_affineWeylGroup_preimage_fundamentalAlcove_eq [Archimedean R] {x : N}
    (hx : ∀ j (k : ℤ), P.root' j x ≠ k) :
    ∃! f, f ∈ P.affineWeylGroup ∧ f ⁻¹' fundamentalAlcove P b =
      {y | ∀ j (k : ℤ), ((k : R) < P.root' j y ↔ (k : R) < P.root' j x) ∧ P.root' j y ≠ k} := by
  obtain ⟨f, hf, hfA⟩ := exists_mem_affineWeylGroup_preimage_fundamentalAlcove_eq b hx
  have hxA : x ∈ f ⁻¹' fundamentalAlcove P b := hfA ▸ fun j k ↦ ⟨Iff.rfl, hx j k⟩
  refine ⟨f, ⟨hf, hfA⟩, fun g ⟨hg, hgA⟩ ↦ ?_⟩
  have hxg : x ∈ g ⁻¹' fundamentalAlcove P b := hgA ▸ hfA ▸ hxA
  exact eq_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b hg hf hxg hxA

end RootPairing
