/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import TauCeti.Analysis.Polynomial.RealRoots.Common
public import TauCeti.Geometry.RealAlgebraic.Stack.Sign
import TauCeti.Algebra.MvPolynomial.Equiv
import TauCeti.Algebra.Polynomial.Thom
import TauCeti.FieldTheory.IsRealClosed.Real
import TauCeti.FieldTheory.RealClosure.AbstractRolle
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Delineations of families of real polynomials

Let `P k x`, for `k` in an index type `ι`, be real polynomials depending on a parameter `x` in a
base `X`. A *delineation* of `P` is a common stack for the whole family: finitely many
continuous functions `θ₀ < θ₁ < ⋯ < θₘ₋₁` on `X` such that

* each member is either the zero polynomial at every point of the base or at none, and has the
  same degree at every point;
* at every point, the roots of every nonzero member are among the values `θᵢ x`, every `θᵢ x` is
  a root of some member, and the multiplicity of `θᵢ x` as a root of `P k x` does not depend on
  `x`;
* every member is sign-invariant on each section and each sector of the stack.

This is the conclusion of Collins' delineability theorem, the step that lifts a cylindrical
algebraic decomposition by one dimension.

Over a nonempty base the ordered list of root functions of a delineation is the increasing
enumeration of the real roots of the nonzero members, so a delineation is unique. Delineations
restrict along continuous maps of bases.

The main theorem `TauCeti.nonempty_delineation` constructs a delineation over a preconnected base
from invariant algebraic data: if the coefficients of every member are continuous, every member is
nullified everywhere or nowhere, and the degree of every member, its number of distinct complex
roots and the degree of the gcd of every pair of distinct members are constant on the base, then
the family has a delineation. Its root functions are the common ordered real roots given by the
family matching lemma `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`.

When the derivative of every member is zero or a member, Thom's lemma shows that two points of
one fiber at which all members have the same signs lie in the same section or sector. So the cells
of the stack are cut out by sign conditions on the members.

For a family obtained from polynomials `f` in `n + 1` variables by singling out the first one with
`MvPolynomial.finSuccEquiv`, every `f` is sign-invariant on each cell of the stack in
`ℝ^(n + 1)`, the cells being the images of the sections and sectors under `TauCeti.cylinder`.

## Main declarations

* `TauCeti.Delineation`: a common stack of the roots of a family of real polynomials.
* `TauCeti.Delineation.range_root`: the root functions enumerate the real roots of the nonzero
  members.
* `TauCeti.Delineation.isRoot_iff`: the roots of a nonzero member are the sections in which it has
  positive multiplicity.
* `TauCeti.Delineation.instSubsingleton`: over a nonempty base a family has at most one
  delineation.
* `TauCeti.Delineation.comp`: restriction of a delineation along a continuous map of bases.
* `TauCeti.nonempty_delineation`: existence of a delineation over a preconnected base from
  constant degrees, numbers of distinct complex roots and pairwise gcd degrees.
* `TauCeti.Delineation.root_notMem_uIcc_of_sign_eval_eq`,
  `TauCeti.Delineation.mk_mem_sectionSet_iff_of_sign_eval_eq`,
  `TauCeti.Delineation.mk_mem_sectorSet_iff_of_sign_eval_eq`: when the derivative of every
  member is zero or a member, points of one fiber with the same signs are not separated by the
  stack.
* `TauCeti.Delineation.signInvariant_eval₂_of_mem_stackCells`: the polynomials in `n + 1`
  variables behind a family are sign-invariant on every ambient cell of a delineation.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (Theorem 5.16).
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : ι → X → ℝ[X]}

/-- A *delineation* of a family `P k x` of real polynomials over a base `X` is a common stack of
their roots: continuous functions `root 0 < ⋯ < root (count - 1)` on `X` such that each member is
zero everywhere or nowhere and has constant degree, the roots of each nonzero member are among
the `root i x`, each `root i` is a root of some member, the multiplicity of `root i x` as a root of
`P k x` is a constant `multiplicity k i`, and each member is sign-invariant on every section and
every sector of the stack. -/
structure Delineation (P : ι → X → ℝ[X]) where
  /-- The number of sections of the stack. -/
  count : ℕ
  /-- The root functions, listed in increasing order. -/
  root : Fin count → X → ℝ
  /-- Each root function is continuous. -/
  continuous_root (i : Fin count) : Continuous (root i)
  /-- At each point the root functions are strictly increasing in their index. -/
  strictMono_root (x : X) : StrictMono fun i ↦ root i x
  /-- The multiplicity of the `i`-th root function as a root of the `k`-th member. -/
  multiplicity : ι → Fin count → ℕ
  /-- The multiplicity of `root i x` as a root of `P k x` is `multiplicity k i` at every `x`. -/
  rootMultiplicity_root (k : ι) (i : Fin count) (x : X) :
    (P k x).rootMultiplicity (root i x) = multiplicity k i
  /-- Every root of a nonzero member is the value of a root function. -/
  exists_root_eq (k : ι) (x : X) : P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, root i x = t
  /-- Every root function is a root of some member. -/
  exists_multiplicity_pos (i : Fin count) : ∃ k, 0 < multiplicity k i
  /-- Each member is the zero polynomial at every point or at none. -/
  eq_zero_or_ne_zero (k : ι) : (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0
  /-- Each member has the same degree at every point. -/
  natDegree_eq (k : ι) (x y : X) : (P k x).natDegree = (P k y).natDegree
  /-- Each member is sign-invariant on each section. -/
  signInvariant_sectionSet (k : ι) (i : Fin count) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectionSet root i)
  /-- Each member is sign-invariant on each sector. -/
  signInvariant_sectorSet (k : ι) (j : Fin (count + 1)) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectorSet root j)

namespace Delineation

/-- Any family of real polynomials over an empty base has a delineation. -/
theorem nonempty_of_isEmpty [IsEmpty X] (P : ι → X → ℝ[X]) : Nonempty (Delineation P) :=
  ⟨{
    count := 0
    root := Fin.elim0
    continuous_root := fun i ↦ i.elim0
    strictMono_root := fun x ↦ isEmptyElim x
    multiplicity := fun _ ↦ Fin.elim0
    rootMultiplicity_root := fun _ i ↦ i.elim0
    exists_root_eq := fun _ x ↦ isEmptyElim x
    exists_multiplicity_pos := fun i ↦ i.elim0
    eq_zero_or_ne_zero := fun _ ↦ .inl isEmptyElim
    natDegree_eq := fun _ x ↦ isEmptyElim x
    signInvariant_sectionSet := fun _ i ↦ i.elim0
    signInvariant_sectorSet := fun _ _ ↦ subsingleton_of_subsingleton.signInvariant }⟩

variable (D : Delineation P)

/-- The roots of a nonzero member of the family are exactly the values of the root functions in
which it has positive multiplicity. -/
theorem isRoot_iff {k : ι} {x : X} (hk : P k x ≠ 0) (t : ℝ) :
    (P k x).IsRoot t ↔ ∃ i, D.root i x = t ∧ 0 < D.multiplicity k i :=
  isRoot_iff_of_rootMultiplicity (fun i ↦ D.rootMultiplicity_root k i x)
    (D.exists_root_eq k x hk) hk t

/-- On a sector, the evaluation of a nonzero fiber cannot vanish: every root lies
on a section, and sections are disjoint from sectors. -/
theorem eval_ne_zero_of_mem_sectorSet {k : ι} {j : Fin (D.count + 1)} {z : X × ℝ}
    (hk : P k z.1 ≠ 0) (hz : z ∈ sectorSet D.root j) : (P k z.1).eval z.2 ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := D.exists_root_eq k z.1 hk z.2 hzero
  exact disjoint_left.1 (disjoint_sectionSet_sectorSet D.root i j)
    (mem_sectionSet.2 hi) hz

/-- A member of the family has positive multiplicity in a root function exactly when it is
nonzero and vanishes there. -/
theorem multiplicity_pos_iff {k : ι} {i : Fin D.count} (x : X) :
    0 < D.multiplicity k i ↔ P k x ≠ 0 ∧ (P k x).IsRoot (D.root i x) := by
  rw [← D.rootMultiplicity_root k i x, rootMultiplicity_pos']

/-- A member of the family that is zero somewhere has multiplicity zero in every root function. -/
theorem multiplicity_eq_zero {k : ι} {x : X} (hk : P k x = 0) (i : Fin D.count) :
    D.multiplicity k i = 0 := by
  rw [← D.rootMultiplicity_root k i x, hk, rootMultiplicity_zero]

/-- At every point of the base, the values of the root functions are exactly the real roots of
the nonzero members of the family. -/
theorem range_root (x : X) :
    range (fun i ↦ D.root i x) = {t | ∃ k, P k x ≠ 0 ∧ (P k x).IsRoot t} := by
  ext t
  refine ⟨?_, fun ⟨k, hk, ht⟩ ↦ D.exists_root_eq k x hk t ht⟩
  rintro ⟨i, rfl⟩
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  exact ⟨k, (D.multiplicity_pos_iff x).1 hk⟩

/-- Over a nonempty base a family of real polynomials has at most one delineation: the root
functions are the increasing enumeration of the real roots of the nonzero members, and the
multiplicities are their root multiplicities. -/
instance instSubsingleton [Nonempty X] : Subsingleton (Delineation P) where
  allEq D D' := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hrange (y : X) : range (fun i ↦ D.root i y) = range fun i ↦ D'.root i y := by
      rw [D.range_root, D'.range_root]
    -- the two stacks have the same number of sections, the number of roots at `x`
    have hcount : D.count = D'.count := by
      have h := congrArg (fun s : Set ℝ ↦ Nat.card s) (hrange x)
      simp only [Nat.card_range_of_injective (D.strictMono_root x).injective,
        Nat.card_range_of_injective (D'.strictMono_root x).injective, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h
      exact h
    revert hrange hcount
    obtain ⟨c, r, -, hr, m, hm, -⟩ := D
    obtain ⟨c', r', -, hr', m', hm', -⟩ := D'
    rintro hrange (rfl : c = c')
    obtain rfl : r = r' := funext fun i ↦ funext fun y ↦ congrFun
      (((hr y).range_inj_of_wellFoundedLT (hr' y)).1 (hrange y)) i
    obtain rfl : m = m' := funext fun k ↦ funext fun i ↦ (hm k i x).symm.trans (hm' k i x)
    rfl

/-- Restriction of a delineation along a continuous map of bases. -/
def comp (f : Y → X) (hf : Continuous f) : Delineation fun k y ↦ P k (f y) where
  count := D.count
  root i y := D.root i (f y)
  continuous_root i := (D.continuous_root i).comp hf
  strictMono_root y := D.strictMono_root (f y)
  multiplicity := D.multiplicity
  rootMultiplicity_root k i y := D.rootMultiplicity_root k i (f y)
  exists_root_eq k y := D.exists_root_eq k (f y)
  exists_multiplicity_pos := D.exists_multiplicity_pos
  eq_zero_or_ne_zero k := (D.eq_zero_or_ne_zero k).imp (fun h y ↦ h (f y)) fun h y ↦ h (f y)
  natDegree_eq k y y' := D.natDegree_eq k (f y) (f y')
  signInvariant_sectionSet k i := by
    refine (congrArg _ (sectionSet_comp D.root f i)).mpr ?_
    exact signInvariant_image (u := Prod.map f id).1
      ((D.signInvariant_sectionSet k i).mono (image_preimage_subset _ _))
  signInvariant_sectorSet k j := by
    refine (congrArg _ (sectorSet_comp D.root f j)).mpr ?_
    exact signInvariant_image (u := Prod.map f id).1
      ((D.signInvariant_sectorSet k j).mono (image_preimage_subset _ _))

/-- The restriction of a delineation has the same number of sections. -/
@[simp]
theorem comp_count (f : Y → X) (hf : Continuous f) : (D.comp f hf).count = D.count := (rfl)

/-- The root functions of the restriction of a delineation are the original root functions
composed with the map of bases. -/
@[simp]
theorem comp_root (f : Y → X) (hf : Continuous f) (i : Fin (D.comp f hf).count) (y : Y) :
    (D.comp f hf).root i y = D.root (Fin.cast (D.comp_count f hf) i) (f y) := (rfl)

/-- The restriction of a delineation has the same multiplicities. -/
@[simp]
theorem comp_multiplicity (f : Y → X) (hf : Continuous f) (k : ι) (i : Fin (D.comp f hf).count) :
    (D.comp f hf).multiplicity k i = D.multiplicity k (Fin.cast (D.comp_count f hf) i) := (rfl)

end Delineation

/-- **Delineability from invariant fiber data.** Let `P k x`, for `k` in a finite index type, be
real polynomials whose coefficients depend continuously on a parameter `x` in a preconnected
space. Suppose that each member is zero everywhere or nowhere, and that the degree of each member,
its number of distinct complex roots and the degree of the gcd of every pair of distinct members
do not depend on `x`. Then the family has a delineation. -/
theorem nonempty_delineation [Finite ι] [PreconnectedSpace X]
    (hcoeff : ∀ k i, Continuous fun x ↦ (P k x).coeff i)
    (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
    (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (hcard : ∀ k x y, ((P k x).aroots ℂ).toFinset.card = ((P k y).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l ↦ ∀ x y, (EuclideanDomain.gcd (P k x) (P l x)).natDegree =
      (EuclideanDomain.gcd (P k y) (P l y)).natDegree) :
    Nonempty (Delineation P) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Delineation.nonempty_of_isEmpty P
  obtain ⟨x₀⟩ := id hX
  -- the common ordered real roots of the members that are nowhere zero
  obtain ⟨n, r, hrc, hrm, hroot, hmult⟩ :=
    exists_continuous_ordered_common_roots_of_preconnectedSpace
      (ι := {k // ∀ x, P k x ≠ 0}) (F := fun k ↦ P k.1) (d := fun k ↦ (P k.1 x₀).natDegree)
      (fun k i _ ↦ hcoeff k.1 i)
      (fun k x ↦ by rw [degree_eq_natDegree (k.2 x), hdeg k.1 x x₀])
      (fun k x₀ ↦ .of_forall fun x ↦ (hcard k.1 x x₀).le)
      (fun k l hkl x₀ ↦ .of_forall fun x ↦ hgcd (Subtype.coe_ne_coe.2 hkl) x x₀)
  -- a member which is zero somewhere is zero everywhere
  have hzero {k : ι} (h : ¬∀ x, P k x ≠ 0) (x : X) : P k x = 0 :=
    (hnull k).resolve_right h x
  let m (k : ι) (i : Fin n) : ℕ := (P k x₀).rootMultiplicity (r x₀ i)
  have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r x i) = m k i := by
    by_cases hk : ∀ x, P k x ≠ 0
    · exact hmult ⟨k, hk⟩ i x x₀
    · simp only [m, hzero hk, rootMultiplicity_zero]
  have hsub (k : ι) (x : X) (hk : P k x ≠ 0) (t : ℝ) (ht : (P k x).IsRoot t) :
      ∃ i, r x i = t :=
    (hroot x t).1 ⟨⟨k, fun y h ↦ hk (hzero (fun h' ↦ h' y h) x)⟩, ht⟩
  have hP (k : ι) : Continuous fun z : X × ℝ ↦ (P k z.1).eval z.2 :=
    continuous_eval_of_continuous_coeff (fun i _ ↦ hcoeff k i) (fun x ↦ (hdeg k x x₀).le)
  refine ⟨{
    count := n
    root := fun i x ↦ r x i
    continuous_root := hrc
    strictMono_root := hrm
    multiplicity := m
    rootMultiplicity_root := hm
    exists_root_eq := hsub
    exists_multiplicity_pos := fun i ↦ ?_
    eq_zero_or_ne_zero := hnull
    natDegree_eq := hdeg
    signInvariant_sectionSet := fun k i ↦ ?_
    signInvariant_sectorSet := fun k j ↦ ?_ }⟩
  · obtain ⟨⟨k, hk⟩, hki⟩ := (hroot x₀ (r x₀ i)).2 ⟨i, rfl⟩
    exact ⟨k, (rootMultiplicity_pos (hk x₀)).2 hki⟩
  · exact signInvariant_eval_sectionSet (I := {i | 0 < m k i}) (hP k) (hrc i)
      (fun x ↦ (hrm x).injective) (hnull k) fun x hk t ↦
        (isRoot_iff_of_rootMultiplicity (fun i ↦ hm k i x) (hsub k x hk) hk t).trans <| by
          simp only [mem_ofPred_eq, and_comm]
  · exact signInvariant_eval_sectorSet (hP k) hrc hrm (hnull k) fun x hk ↦ hsub k x hk

/-! ### Families closed under differentiation up to zero -/

namespace Delineation

variable (D : Delineation P)

/-- **Thom's lemma for delineations.** Suppose that at a point `x` of the base the derivative of
every member of the family is zero or a member. If every member has the same sign at two distinct
points `t ≠ t'` of the fiber over `x`, then no root function takes a value in `[t, t']` at `x`. -/
theorem root_notMem_uIcc_of_sign_eval_eq {x : X}
    (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x))
    {t t' : ℝ} (htt' : t ≠ t')
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : D.root i x ∉ uIcc t t' := by
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  obtain ⟨hk0, hroot⟩ := (D.multiplicity_pos_iff x).1 hk
  -- every iterated derivative of a member is zero or a member, so it has the same sign at `t`
  -- and `t'`
  have hiter (j : ℕ) : derivative^[j] (P k x) = 0 ∨ ∃ l, P l x = derivative^[j] (P k x) := by
    induction j with
    | zero => exact .inr ⟨k, rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain h0 | ⟨l, hl⟩ := ih
      · exact .inl (by rw [h0, derivative_zero])
      · rw [← hl]
        exact hder l
  have hsign (j : ℕ) : derivativeSign (P k x) t j = derivativeSign (P k x) t' j := by
    obtain h0 | ⟨l, hl⟩ := hiter j
    · simp only [derivativeSign_def, h0, eval_zero]
    · simpa only [derivativeSign_def, hl] using h l
  exact fun hi ↦ eval_ne_zero_of_derivativeSign_eq _
    (RealClosure.polynomialRolle_of_isRealClosed (R := ℝ)) hk0 htt' hsign hi hroot.eq_zero

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sections. -/
theorem mk_mem_sectionSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : (x, t) ∈ sectionSet D.root i ↔ (x, t') ∈ sectionSet D.root i := by
  rcases eq_or_ne t t' with rfl | htt'
  · rfl
  have hi := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
  simp only [mem_sectionSet]
  exact iff_of_false (fun he ↦ hi (he ▸ left_mem_uIcc)) fun he ↦ hi (he ▸ right_mem_uIcc)

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sectors. -/
theorem mk_mem_sectorSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (j : Fin (D.count + 1)) : (x, t) ∈ sectorSet D.root j ↔ (x, t') ∈ sectorSet D.root j := by
  rcases eq_or_ne t t' with rfl | htt'
  · rfl
  have hi (i : Fin D.count) :
      (D.root i x < t ↔ D.root i x < t') ∧ (t < D.root i x ↔ t' < D.root i x) := by
    have := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
    rw [mem_uIcc] at this
    grind
  simp only [mem_sectorSet, hi]

end Delineation

section MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {S : Set (Fin n → ℝ)}

/-- For a delineation of the fibers of `MvPolynomial.finSuccEquiv A n f` over `S`, the polynomial
`f` in `n + 1` variables, evaluated along `φ`, is sign-invariant on every cell of the stack in
`ℝ^(n + 1)`. -/
theorem Delineation.signInvariant_eval₂_of_mem_stackCells
    (D : Delineation fun (p : F) (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom φ x.1))
    {f : MvPolynomial (Fin (n + 1)) A} (hf : MvPolynomial.finSuccEquiv A n f ∈ F)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    SignInvariant (fun y ↦ MvPolynomial.eval₂ φ y f) E := by
  have key : (fun y ↦ MvPolynomial.eval₂ φ y f) ∘ cylinder S =
      fun z ↦ ((MvPolynomial.finSuccEquiv A n f).map (MvPolynomial.eval₂Hom φ z.1.1)).eval z.2 :=
    funext fun z ↦ by
      rw [Function.comp_apply, cylinder_def, MvPolynomial.polynomial_eval_map_finSuccEquiv]
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [signInvariant_image, key]
  exacts [D.signInvariant_sectionSet ⟨_, hf⟩ i, D.signInvariant_sectorSet ⟨_, hf⟩ j]

end MvPolynomial

end TauCeti
