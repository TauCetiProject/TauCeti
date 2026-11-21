/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Alcove.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Basic
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice
import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber

/-!
# The affine Weyl group acts simply transitively on the alcoves

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over a
linearly ordered ring, with simple roots `αᵢ` and highest root `θ`. The affine root hyperplanes
`H_{α,k} = {x | α(x) = k}` of the coweight space `N` cut it into alcoves, and the fundamental
alcove `A` is the one cut out by the walls `αᵢ = 0` and `θ = 1`. Over an archimedean ring, this
file proves that the affine Weyl group `W_aff` (`RootPairing.affineWeylGroup`) moves every point
into the closed fundamental alcove, and so permutes the alcoves transitively: every alcove is
`f⁻¹(A)` for some `f ∈ W_aff`. Over any linearly ordered ring, it proves a local wall-reflection
descent without the archimedean hypothesis and shows that an element of `W_aff` sending a point of
the open fundamental alcove back into it is the identity (so `W_aff` acts freely on
`W_aff`-translates of `A`, and over an archimedean ring on all alcoves, making `f` unique). Over an
archimedean linearly ordered field, the open fundamental alcove is nonempty, and combining
transitivity with freeness at `A` shows that the affine simple reflections generate `W_aff`
(`RootPairing.Base.closure_range_affineSimpleReflection`).

The transitivity proof is the classical descent of Bourbaki and Humphreys, made purely
combinatorial. An affine root is a pair `(j, k)` of a root index and an integer, standing for the
affine function `αⱼ - k`; define it combinatorially to be positive when `k < 0`, or `k = 0` and
`αⱼ` is a positive root (when the open fundamental alcove `A` is nonempty, this is equivalent to
positivity on `A`). A point `x` lies on the far side of the hyperplane of a
positive affine root when `αⱼ(x) < k`; when the ring is archimedean, only finitely many positive
affine roots have this property. If `x` is not in the closed fundamental alcove, it lies on the
far side of a wall of `A`: `αᵢ(x) < 0` for a simple root, or `θ(x) > 1`. The reflection `s` in
that wall exchanges the two affine roots of the wall and permutes all the other positive affine
roots, so `s x` lies on the far side of one fewer hyperplane than `x` whenever the separating set
is finite, and induction on this number finishes the global descent. When every separating
hyperplane of `z` passes through a fixed point `y`, at most one hyperplane in each root direction
can occur, giving finiteness without `[Archimedean R]` and carrying `z` into the closed
fundamental alcove by wall reflections fixing `y`
(`RootPairing.exists_mem_closure_affineWallReflections_apply_mem_closedFundamentalAlcove`).

For a simple wall, that `s` permutes the other positive affine roots is the fact that a simple
reflection permutes the positive roots other than its own
(`RootPairing.Base.isPos_reflectionPerm_iff`).
For the wall `θ = 1` it is a computation with heights: reflecting in `θ` changes the height of a
root by a multiple of the height of `θ`, and every root other than `±θ` has height strictly between
`-ht(θ)` and `ht(θ)`.

Stabilizer-freeness at the fundamental alcove needs no archimedean hypothesis. Write an element of
`W_aff` as `f = t_v ∘ w`, with `w`
in the coweight image of the Weyl group and `v` in the coroot lattice `Q∨`
(`RootPairing.mem_affineWeylGroup_iff`). Every root takes its values in `(-1, 1)` on `A`, so if `f`
carries a point of `A` into `A`, every root takes a value in `(-2, 2)` at `v`. A minuscule element
of the coroot lattice is zero (`RootPairing.eq_zero_of_mem_corootSpan_of_forall_abs_root'_lt_two`),
so `v = 0`, and `w` then carries a point of the open dominant chamber into the dominant chamber,
which forces `w = 1` (`TauCeti.eq_one_of_smul_mem_dominantChamber`). This replaces the usual
gallery argument with the Coxeter generators by the free action of the finite Weyl group on the
chambers.

## Main definitions

* `RootPairing.Base.affineSimpleReflection`: the affine reflections `s_{θ,1}` and `s_{αᵢ,0}` in the
  walls of the fundamental alcove, indexed by `Option b.support`.
* `RootPairing.Base.affineWallReflections`: at a point `x`, the affine simple reflections in the
  walls of the fundamental alcove passing through `x`.

## Main results

* `RootPairing.Base.affineSimpleRoot_affineSimpleReflection`: the affine Cartan matrix governs the
  action of the affine simple reflections on the affine simple roots:
  `aₗ(sₖ x) = aₗ(x) - A_{l,k} aₖ(x)`.
* `RootPairing.Base.affineSimpleReflection_injective`: distinct affine nodes define distinct
  affine simple reflections.
* `RootPairing.exists_mem_closure_affineWallReflections_apply_mem_closedFundamentalAlcove`:
  if every positive affine root hyperplane separating `z` from the fundamental alcove passes
  through `y`, then a product of wall reflections fixing `y` carries `z` into the closed
  fundamental alcove.
* `RootPairing.exists_mem_closure_range_affineSimpleReflection_apply_mem_closedFundamentalAlcove`
  and `RootPairing.exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove`: **every point of
  the coweight space is carried into the closed fundamental alcove by the affine simple
  reflections**, and in particular by the affine Weyl group.
* `RootPairing.iUnion_image_closedFundamentalAlcove_eq_univ`: the translates of the closed
  fundamental alcove under the affine Weyl group cover the coweight space.
* `RootPairing.exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove`: a point lying on no affine
  root hyperplane is carried into the open fundamental alcove.
* `RootPairing.eq_zero_of_mem_corootSpan_of_mem_closedFundamentalAlcove`: the only point of the
  coroot lattice in the closed fundamental alcove is `0`.
* `RootPairing.exists_mem_affineWeylGroup_preimage_fundamentalAlcove_eq`: **over an archimedean
  ring, the affine Weyl group is transitive on the alcoves**: the alcove of a point lying on no
  affine root hyperplane, the set of points lying on no such hyperplane and on the same side of
  each of them, is the preimage of the fundamental alcove under an element of the affine Weyl group.
* `RootPairing.eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove`: an element of `W_aff`
  carrying a point of the open fundamental alcove back into the open fundamental alcove is the
  identity (so `W_aff` acts freely on translates of the fundamental alcove, and over an archimedean
  ring on all alcoves).
* `RootPairing.eq_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove`,
  `RootPairing.eq_one_of_mem_affineWeylGroup_of_mapsTo`, and
  `RootPairing.affinePointStabilizer_eq_bot_of_mem_fundamentalAlcove`: two elements carrying the
  same point into the fundamental alcove are equal, the stabilizer of a nonempty fundamental alcove
  is trivial, and the point stabilizer in `W_aff` of any point of the open fundamental alcove is
  trivial.
* `RootPairing.existsUnique_mem_affineWeylGroup_preimage_fundamentalAlcove_eq`: **over an
  archimedean ring, the affine Weyl group acts simply transitively on the alcoves.**
* `RootPairing.Base.closure_range_affineSimpleReflection`: **Coxeter generation of `W_aff`**: over
  an archimedean linearly ordered field, the affine simple reflections generate `W_aff`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §3.2 and Ch. VI, §2.1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, §4.3 and §4.5.
-/

public section

open Set

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-! ### The affine simple reflections -/

section AffineSimpleReflection

variable {P : RootPairing ι R M N} [CharZero R] [Finite ι] [Nonempty ι] (b : P.Base)

namespace Base

/-- The **affine simple reflections** of a base `b`, the reflections in the walls of the
fundamental alcove (`RootPairing.Base.affineSimpleRoot`): the affine reflection `s_{θ,1}` in the
wall `θ = 1` at the affine node `none`, and the simple coreflection `s_{αᵢ,0}` in the wall `αᵢ = 0`
at a simple node `some i`. -/
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
lemma linear_affineSimpleReflection (k : Option b.support) :
    (b.affineSimpleReflection k).linear = P.coreflection (b.affineSimpleRootIndex k) := by
  rcases k with _ | i
  · rw [affineSimpleReflection_none, linear_affineCoreflection, affineSimpleRootIndex_none]
    ext x
    rw [coreflection_apply, coreflection_apply]
    simp [P.root'_reflectionPerm_self, P.coroot_reflectionPerm, P.coreflection_apply_self]
  · rw [affineSimpleReflection_some, affineSimpleRootIndex_some]
    rfl

/-- The formula for an affine simple reflection in terms of its affine simple root `aₖ` and the
coroot at `RootPairing.Base.affineSimpleRootIndex`: `sₖ(x) = x - aₖ(x) αₖ^∨`. -/
lemma affineSimpleReflection_apply (k : Option b.support) (x : N) :
    b.affineSimpleReflection k x =
      x - b.affineSimpleRoot k x • P.coroot (b.affineSimpleRootIndex k) := by
  rcases k with _ | i
  · simp only [affineSimpleReflection_none, affineCoreflection_apply_eq_sub, affineSimpleRoot_none,
      affineSimpleRootIndex_none, P.coroot_reflectionPerm, P.coreflection_apply_self, smul_neg,
      sub_neg_eq_add]
    rw [← neg_sub (1 : R), neg_smul]
    abel
  · simp [coreflection_apply]

@[simp]
lemma affineSimpleReflection_affineSimpleReflection (k : Option b.support) (x : N) :
    b.affineSimpleReflection k (b.affineSimpleReflection k x) = x := by
  rcases k with _ | i <;> simp

@[simp]
lemma affineSimpleReflection_mul_self (k : Option b.support) :
    b.affineSimpleReflection k * b.affineSimpleReflection k = 1 := by
  ext x
  simp

@[simp]
lemma inv_affineSimpleReflection (k : Option b.support) :
    (b.affineSimpleReflection k)⁻¹ = b.affineSimpleReflection k :=
  inv_eq_of_mul_eq_one_right (b.affineSimpleReflection_mul_self k)

@[simp]
lemma symm_affineSimpleReflection (k : Option b.support) :
    (b.affineSimpleReflection k).symm = b.affineSimpleReflection k := by
  rw [← AffineEquiv.inv_def, b.inv_affineSimpleReflection]

/-- Distinct affine nodes define distinct affine simple reflections. -/
theorem affineSimpleReflection_injective : Function.Injective b.affineSimpleReflection := by
  have hnone (i : b.support) :
      b.affineSimpleReflection none ≠ b.affineSimpleReflection (some i) := fun h ↦ by
    have h0 : P.coroot b.highestRoot = 0 := by
      have := congrArg (fun f ↦ f 0) h
      simpa [affineCoreflection_apply] using this
    have h2 : (2 : R) = 0 := by
      simpa [h0] using (P.root'_coroot_eq_pairing b.highestRoot b.highestRoot).symm
    exact two_ne_zero h2
  rintro (_ | i) (_ | j) h
  · rfl
  · exact absurd h (hnone j)
  · exact absurd h.symm (hnone i)
  · refine congrArg some ?_
    by_contra hne
    have hroot : (2 : R) • P.root i = P.pairing i j • P.root j := by
      refine P.toPerfPair.injective (LinearMap.ext fun x ↦ ?_)
      have hx : P.coreflection i x = P.coreflection j x := by
        have h' := congrArg (fun f ↦ f x) h
        simpa [affineSimpleReflection_some, LinearEquiv.coe_toAffineEquiv] using h'
      have hsub : P.root' i x • P.coroot i = P.root' j x • P.coroot j := by
        simp only [coreflection_apply] at hx
        exact sub_right_inj.mp hx
      have hval := congrArg (P.root' i) hsub
      simp only [map_smul, root'_coroot_eq_pairing, pairing_same, smul_eq_mul] at hval
      simpa [root', smul_eq_mul, mul_comm] using hval
    have hlin : Finsupp.linearCombination R (fun k : b.support ↦ P.root k)
        (Finsupp.single i (2 : R) - Finsupp.single j (P.pairing i j)) = 0 := by
      simp only [map_sub, Finsupp.linearCombination_single, hroot, sub_self]
    have hzero := linearIndependent_iff.mp b.linearIndepOn_root _ hlin
    have h2 := DFunLike.congr_fun hzero i
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne, sub_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    exact two_ne_zero h2

@[simp]
lemma affineSimpleReflection_inj {k l : Option b.support} :
    b.affineSimpleReflection k = b.affineSimpleReflection l ↔ k = l :=
  b.affineSimpleReflection_injective.eq_iff

/-- An affine simple reflection fixes the wall where its affine simple root vanishes. -/
lemma affineSimpleReflection_apply_of_affineSimpleRoot_eq_zero {k : Option b.support} {x : N}
    (h : b.affineSimpleRoot k x = 0) : b.affineSimpleReflection k x = x := by
  rw [b.affineSimpleReflection_apply, h, zero_smul, sub_zero]

/-- When `R` has no zero divisors, the fixed points of `sₖ` are the wall `aₖ(x) = 0`. -/
@[simp]
lemma affineSimpleReflection_apply_eq_self_iff [NoZeroDivisors R]
    {k : Option b.support} {x : N} :
    b.affineSimpleReflection k x = x ↔ b.affineSimpleRoot k x = 0 := by
  rcases k with _ | i
  · rw [affineSimpleReflection_none, P.affineCoreflection_apply_eq_self_iff,
      affineSimpleRoot_none, sub_eq_zero, eq_comm]
  · rw [affineSimpleReflection_some, ← P.affineCoreflection_zero,
      P.affineCoreflection_apply_eq_self_iff, affineSimpleRoot_some]

/-- **The affine Cartan matrix governs the action of `sₖ` on the affine simple roots**:
`aₗ(sₖ x) = aₗ(x) - A_{l,k} aₖ(x)`. -/
theorem affineSimpleRoot_affineSimpleReflection [P.IsCrystallographic]
    (k l : Option b.support) (x : N) :
    b.affineSimpleRoot l (b.affineSimpleReflection k x) =
      b.affineSimpleRoot l x - b.affineCartanMatrix l k * b.affineSimpleRoot k x := by
  rw [b.affineSimpleRoot_eq_root'_add l (b.affineSimpleReflection k x),
    b.affineSimpleRoot_eq_root'_add l x, b.affineSimpleReflection_apply,
    b.affineCartanMatrix_apply]
  simp only [map_sub, map_smul, root'_coroot_eq_pairing, smul_eq_mul,
    ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]
  ring

@[simp]
lemma affineSimpleRoot_affineSimpleReflection_self (k : Option b.support) (x : N) :
    b.affineSimpleRoot k (b.affineSimpleReflection k x) = -b.affineSimpleRoot k x := by
  rw [b.affineSimpleReflection_apply, b.affineSimpleRoot_eq_root'_add k]
  simp only [map_sub, map_smul, root'_coroot_eq_pairing, pairing_same, smul_eq_mul]
  rw [b.affineSimpleRoot_eq_root'_add k x]
  ring

/-- Every affine simple reflection belongs to the affine Weyl group. -/
@[simp]
lemma affineSimpleReflection_mem_affineWeylGroup (k : Option b.support) :
    b.affineSimpleReflection k ∈ P.affineWeylGroup := by
  rcases k with _ | i
  · simpa using P.affineCoreflection_mem_affineWeylGroup b.highestRoot 1
  · simpa using P.affineCoreflection_mem_affineWeylGroup i 0

/-- The subgroup generated by the affine simple reflections is contained in the affine Weyl
group. -/
lemma closure_range_affineSimpleReflection_le_affineWeylGroup :
    Subgroup.closure (range b.affineSimpleReflection) ≤ P.affineWeylGroup :=
  (Subgroup.closure_le _).mpr <| by
    rintro _ ⟨k, rfl⟩
    exact b.affineSimpleReflection_mem_affineWeylGroup k

/-- The reflections in the walls of the fundamental alcove passing through `x`: the affine simple
reflections `sₖ` at the nodes `k` where the affine simple root `aₖ(x)` vanishes. -/
noncomputable def affineWallReflections (x : N) : Set (N ≃ᵃ[R] N) :=
  b.affineSimpleReflection '' {k | b.affineSimpleRoot k x = 0}

lemma affineWallReflections_def (x : N) :
    b.affineWallReflections x = b.affineSimpleReflection '' {k | b.affineSimpleRoot k x = 0} :=
  (rfl)

@[simp]
lemma mem_affineWallReflections {x : N} {s : N ≃ᵃ[R] N} :
    s ∈ b.affineWallReflections x ↔
      ∃ k, b.affineSimpleRoot k x = 0 ∧ b.affineSimpleReflection k = s :=
  Iff.rfl

/-- Every reflection in a wall of the fundamental alcove passing through `x` fixes `x`. -/
lemma apply_eq_self_of_mem_affineWallReflections {x : N} {s : N ≃ᵃ[R] N}
    (hs : s ∈ b.affineWallReflections x) : s x = x := by
  obtain ⟨k, hk, rfl⟩ := b.mem_affineWallReflections.mp hs
  exact b.affineSimpleReflection_apply_of_affineSimpleRoot_eq_zero hk

/-- No wall of the fundamental alcove passes through a point of the open fundamental alcove. -/
theorem affineWallReflections_eq_empty_of_mem_fundamentalAlcove [PartialOrder R]
    [IsOrderedAddMonoid R] {x : N} (hx : x ∈ fundamentalAlcove P b) :
    b.affineWallReflections x = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun s hs ↦ ?_
  obtain ⟨k, hk, -⟩ := b.mem_affineWallReflections.mp hs
  exact ((mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b).mp hx k).ne' hk

/-- Every wall reflection of a base `b` at `x` is a root-hyperplane reflection at `x`. -/
lemma affineWallReflections_subset_affineRootReflections (x : N) :
    b.affineWallReflections x ⊆ P.affineRootReflections x := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := b.mem_affineWallReflections.mp hs
  refine P.mem_affineRootReflections.mpr ?_
  rcases k with _ | i
  · rw [affineSimpleRoot_none] at hk
    exact ⟨b.highestRoot, 1, by simpa using (sub_eq_zero.mp hk).symm, by simp⟩
  · exact ⟨i, 0, by simpa using hk, by simp⟩

/-- The subgroup generated by the wall reflections of `b` at `x` is contained in the point
stabilizer of `x` in `W_aff`. -/
lemma closure_affineWallReflections_le_affinePointStabilizer (x : N) :
    Subgroup.closure (b.affineWallReflections x) ≤ P.affinePointStabilizer x :=
  (Subgroup.closure_mono (b.affineWallReflections_subset_affineRootReflections x)).trans
    (P.closure_affineRootReflections_le_affinePointStabilizer x)

end Base

end AffineSimpleReflection

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

/-- Let `s` be the affine reflection in the hyperplane `αⱼ₀ = c`, and suppose that `s` permutes the
positive affine roots other than the two affine roots `±(αⱼ₀ - c)` of its hyperplane. If that
hyperplane separates `x` from the fundamental alcove, then `wallPerm` maps the hyperplanes
separating `s x` into the remaining hyperplanes separating `x`. -/
private lemma sepSet_affineCoreflection_mapsTo {j₀ : ι} {c : ℤ}
    (hpres : ∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
      (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p))
    {x : N} {w : ι × ℤ} (hw : w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c))
    (hwx : w ∈ sepSet b x) :
    ∀ p ∈ sepSet b (P.affineCoreflection j₀ c x), wallPerm P j₀ c p ∈ sepSet b x \ {w} := by
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

/-- **The descent step.** Under the hypotheses of `sepSet_affineCoreflection_mapsTo`, when the
separating set of `x` is finite, `s x` is separated from the fundamental alcove by strictly fewer
affine root hyperplanes than `x`. -/
private lemma ncard_sepSet_affineCoreflection_lt {j₀ : ι} {c : ℤ}
    (hpres : ∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
      (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p))
    {x : N} (hfin : (sepSet b x).Finite) {w : ι × ℤ}
    (hw : w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c)) (hwx : w ∈ sepSet b x) :
    (sepSet b (P.affineCoreflection j₀ c x)).ncard < (sepSet b x).ncard :=
  calc (sepSet b (P.affineCoreflection j₀ c x)).ncard
      ≤ (sepSet b x \ {w}).ncard :=
        ncard_le_ncard_of_injOn _ (sepSet_affineCoreflection_mapsTo b hpres hw hwx)
          (wallPerm_injective P j₀ c).injOn hfin.sdiff
    _ < (sepSet b x).ncard := ncard_sdiff_singleton_lt_of_mem hwx hfin

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

/-- A point outside the closed fundamental alcove is separated from the alcove by the hyperplane
of an affine simple reflection `s_{k₀}`. -/
private lemma exists_wall_sepSet_of_notMem_closedFundamentalAlcove {x : N}
    (hx : x ∉ closedFundamentalAlcove P b) :
    ∃ (k₀ : Option b.support) (j₀ : ι) (c : ℤ),
      b.affineSimpleReflection k₀ = P.affineCoreflection j₀ c ∧
      (∀ y, P.root' j₀ y = c → b.affineSimpleRoot k₀ y = 0) ∧
      (∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
        (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p)) ∧
      ∃ w, (w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c)) ∧ w ∈ sepSet b x := by
  simp only [mem_closedFundamentalAlcove, not_and_or, not_forall, not_le] at hx
  rcases hx with ⟨i, hi, hix⟩ | hθx
  · refine ⟨some ⟨i, hi⟩, i, 0, by simp, fun y hy ↦ by simpa using hy,
      fun p ↦ isAffinePos_wallPerm_simple b hi, (i, 0), .inl rfl,
      ⟨.inr ⟨rfl, b.isPos_of_mem_support hi⟩, by simpa using hix⟩⟩
  · refine ⟨none, b.highestRoot, 1, by simp, fun y hy ↦ by simp [hy],
      fun p ↦ isAffinePos_wallPerm_highestRoot b,
      (P.reflectionPerm b.highestRoot b.highestRoot, -1), .inr rfl,
      ⟨.inl (by omega), by simpa [root'_reflectionPerm_self] using hθx⟩⟩

end Separation

variable [LinearOrder R] [IsStrictOrderedRing R] {P : RootPairing ι R M N} (b : P.Base)
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- Shared strong-induction descent to the closed fundamental alcove parameterized by a point
invariant `P_inv` and allowed generator set `S`. -/
private lemma exists_mem_closure_apply_mem_closedFundamentalAlcove_of_invariant
    (S : Set (N ≃ᵃ[R] N)) (P_inv : N → Prop)
    (hfin : ∀ u, P_inv u → (sepSet b u).Finite)
    (hstep : ∀ u (k₀ : Option b.support) (j₀ : ι) (c : ℤ),
      P_inv u → b.affineSimpleReflection k₀ = P.affineCoreflection j₀ c →
      (∀ y, P.root' j₀ y = c → b.affineSimpleRoot k₀ y = 0) →
      (∀ p : ι × ℤ, p ≠ (j₀, c) → p ≠ (P.reflectionPerm j₀ j₀, -c) →
        (IsAffinePos b (wallPerm P j₀ c p) ↔ IsAffinePos b p)) →
      ∀ w, (w = (j₀, c) ∨ w = (P.reflectionPerm j₀ j₀, -c)) → w ∈ sepSet b u →
        b.affineSimpleReflection k₀ ∈ S ∧ P_inv (P.affineCoreflection j₀ c u))
    {z : N} (hz : P_inv z) :
    ∃ g ∈ Subgroup.closure S, g z ∈ closedFundamentalAlcove P b := by
  induction hn : (sepSet b z).ncard using Nat.strong_induction_on generalizing z with
  | _ n ih =>
  by_cases hzA : z ∈ closedFundamentalAlcove P b
  · exact ⟨1, one_mem _, hzA⟩
  obtain ⟨k₀, j₀, c, hrefl, hwall0, hpres, w, hw, hwz⟩ :=
    exists_wall_sepSet_of_notMem_closedFundamentalAlcove b hzA
  obtain ⟨hk₀, hz'⟩ := hstep z k₀ j₀ c hz hrefl hwall0 hpres w hw hwz
  obtain ⟨g, hg, hgz⟩ := ih _ (hn ▸ ncard_sepSet_affineCoreflection_lt b hpres
    (hfin z hz) hw hwz) hz' rfl
  refine ⟨g * b.affineSimpleReflection k₀, mul_mem hg (Subgroup.subset_closure hk₀), ?_⟩
  simpa [hrefl] using hgz

/-- **Local gallery descent to the closed fundamental alcove.** If every positive affine root
hyperplane separating `z` from the fundamental alcove passes through `y`, then `z` is carried into
the closed fundamental alcove by a product of reflections in the walls of the alcove passing
through `y`. No archimedean hypothesis is needed, because at most one hyperplane in each root
direction passes through `y`. -/
theorem exists_mem_closure_affineWallReflections_apply_mem_closedFundamentalAlcove
    {y z : N}
    (hsep : ∀ (j : ι) (k : ℤ), (k < 0 ∨ k = 0 ∧ 0 < b.height j) →
      P.root' j z < k → P.root' j y = k) :
    ∃ g ∈ Subgroup.closure (b.affineWallReflections y),
      g z ∈ closedFundamentalAlcove P b := by
  refine exists_mem_closure_apply_mem_closedFundamentalAlcove_of_invariant b
    (b.affineWallReflections y)
    (fun u ↦ ∀ (j : ι) (k : ℤ), IsAffinePos b (j, k) → P.root' j u < k → P.root' j y = k)
    (fun u hu ↦ by
      refine Set.Finite.of_injOn (f := Prod.fst) (fun _ _ ↦ mem_univ _) ?_ finite_univ
      rintro ⟨j₁, k₁⟩ h₁ ⟨j₂, k₂⟩ h₂ (rfl : j₁ = j₂)
      exact Prod.ext rfl (Int.cast_injective
        ((hu j₁ k₁ h₁.1 h₁.2).symm.trans (hu j₁ k₂ h₂.1 h₂.2))))
    (fun u k₀ j₀ c hu _ hwall0 hpres w hw hwz ↦ ?_) hsep
  have hj₀y : P.root' j₀ y = c := by
    rcases hw with rfl | rfl
    · exact hu j₀ c hwz.1 hwz.2
    · have h := hu (P.reflectionPerm j₀ j₀) (-c) hwz.1 hwz.2
      simp only [root'_reflectionPerm_self, LinearMap.neg_apply, Int.cast_neg, neg_inj] at h
      exact h
  have hsy : P.affineCoreflection j₀ c y = y := P.affineCoreflection_apply_of_root'_eq hj₀y
  have hmaps := sepSet_affineCoreflection_mapsTo b hpres hw hwz
  refine ⟨⟨k₀, hwall0 y hj₀y, rfl⟩, fun j k hpos hlt ↦ ?_⟩
  have hw' := hmaps (j, k) ⟨hpos, hlt⟩
  have hwy := hu _ _ hw'.1.1 hw'.1.2
  have hcalc := P.root'_affineCoreflection_intCast j₀ j c y
  rw [hsy] at hcalc
  simp only [Int.cast_sub] at hwy
  linarith

/-! ### Transitivity -/

section Transitivity

variable [Archimedean R]

/-- **Every point of the coweight space is carried into the closed fundamental alcove by a product
of affine simple reflections.** -/
theorem exists_mem_closure_range_affineSimpleReflection_apply_mem_closedFundamentalAlcove (x : N) :
    ∃ f ∈ Subgroup.closure (range b.affineSimpleReflection),
      f x ∈ closedFundamentalAlcove P b :=
  exists_mem_closure_apply_mem_closedFundamentalAlcove_of_invariant b
    (range b.affineSimpleReflection) (fun _ ↦ True) (fun u _ ↦ sepSet_finite b u)
    (fun _ k₀ _ _ _ _ _ _ _ _ _ ↦ ⟨mem_range_self k₀, trivial⟩) trivial

/-- **The affine Weyl group carries every point into the closed fundamental alcove.** -/
theorem exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove (x : N) :
    ∃ f ∈ P.affineWeylGroup, f x ∈ closedFundamentalAlcove P b := by
  obtain ⟨f, hf, hfx⟩ :=
    exists_mem_closure_range_affineSimpleReflection_apply_mem_closedFundamentalAlcove b x
  exact ⟨f, b.closure_range_affineSimpleReflection_le_affineWeylGroup hf, hfx⟩

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

/-- An element of the affine Weyl group carrying a point of the open fundamental alcove back into
the open fundamental alcove is the identity (so `W_aff` acts freely on translates of
`fundamentalAlcove P b`, and over an archimedean ring on all alcoves). -/
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

/-- An element of the affine Weyl group carrying a point of the open fundamental alcove into the
closed fundamental alcove is the identity: its image still avoids every affine root hyperplane and
therefore lies in the open fundamental alcove. -/
theorem eq_one_of_mem_affineWeylGroup_of_apply_mem_closedFundamentalAlcove {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.affineWeylGroup) {x : N} (hx : x ∈ fundamentalAlcove P b)
    (hfx : f x ∈ closedFundamentalAlcove P b) : f = 1 :=
  eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b hf hx
    (mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove.mpr
      ⟨hfx, P.root'_apply_ne_intCast_of_mem_affineWeylGroup hf
        (root'_ne_intCast_of_mem_fundamentalAlcove hx)⟩)

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

/-- The stabilizer in `W_aff` of any point of the open fundamental alcove is trivial. -/
theorem affinePointStabilizer_eq_bot_of_mem_fundamentalAlcove {x : N}
    (hx : x ∈ fundamentalAlcove P b) : P.affinePointStabilizer x = ⊥ :=
  eq_bot_iff.mpr fun _ hf ↦
    have ⟨hfW, hfx⟩ := P.mem_affinePointStabilizer.mp hf
    eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove b hfW hx (hfx.symm ▸ hx)

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

end CommRing

/-! ### Coxeter generation of the affine Weyl group -/

section Field

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Coxeter generation of `W_aff`**: over an archimedean linearly ordered field, the affine Weyl
group is generated by the affine simple reflections `b.affineSimpleReflection`. -/
@[simp]
theorem Base.closure_range_affineSimpleReflection [Archimedean R] :
    Subgroup.closure (range b.affineSimpleReflection) = P.affineWeylGroup := by
  refine le_antisymm b.closure_range_affineSimpleReflection_le_affineWeylGroup fun f hf ↦ ?_
  obtain ⟨x₀, hx₀⟩ := fundamentalAlcove_nonempty b
  obtain ⟨g, hg, hgfx⟩ :=
    exists_mem_closure_range_affineSimpleReflection_apply_mem_closedFundamentalAlcove b (f x₀)
  have hgf : g * f ∈ P.affineWeylGroup :=
    mul_mem (b.closure_range_affineSimpleReflection_le_affineWeylGroup hg) hf
  have hfeq : f = g⁻¹ := eq_inv_of_mul_eq_one_right
    (eq_one_of_mem_affineWeylGroup_of_apply_mem_closedFundamentalAlcove b hgf hx₀ hgfx)
  exact hfeq ▸ inv_mem hg

end Field

end RootPairing
