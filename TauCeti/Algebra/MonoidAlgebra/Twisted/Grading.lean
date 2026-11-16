/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width

/-!
# Weight gradings on twisted monoid algebras

Every function `w : G → ι` on a monoid `G` decomposes the twisted monoid algebra
`TauCeti.twistedMonoidAlgebra k G α` as the internal direct sum of the submodules
`TauCeti.TwistedMonoidAlgebra.gradeBy k G α w i` spanned by the twisted basis elements `of g` in the
fiber `w g = i`. Each graded piece is free over `k` on `{g : G // w g = i}`.

When `w : Additive G →+ ι` is an additive homomorphism out of `Additive G`, the twisted
multiplication table `of g * of h = α g h • of (g * h)` respects `w`, making
`TauCeti.TwistedMonoidAlgebra.gradeByHom k G α w` an internal `GradedAlgebra` structure on the
(generally noncommutative) algebra `twistedMonoidAlgebra k G α`. Specializing to `w = id` gives the
fine `Additive G`-grading `TauCeti.TwistedMonoidAlgebra.grade k G α`, and specializing to
`G = Multiplicative L` for an additive monoid `L` gives `gradeByAddHom` for twisted lattice and
quantum torus algebras. For the trivial factor set `1`, `addMonoidAlgebraEquiv` identifies
`twistedMonoidAlgebra k (Multiplicative L) 1` with `AddMonoidAlgebra k L` compatibly with `gradeBy`.

## Main definitions

* `TauCeti.TwistedMonoidAlgebra.gradeBy` and `TauCeti.TwistedMonoidAlgebra.basisGradeBy`: the
  fiber submodules of `w : G → ι` and their canonical `k`-bases.
* `TauCeti.TwistedMonoidAlgebra.gradeByHom`, `TauCeti.TwistedMonoidAlgebra.grade`, and
  `TauCeti.TwistedMonoidAlgebra.gradeByAddHom`: internal `GradedAlgebra` structures induced by
  additive weights on monoids and lattices.
* `TauCeti.TwistedMonoidAlgebra.addMonoidAlgebraEquiv`: the `k`-algebra equivalence between
  `twistedMonoidAlgebra k (Multiplicative L) 1` and `AddMonoidAlgebra k L`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.gradeBy_isInternal`, `TauCeti.TwistedMonoidAlgebra.finrank_gradeBy`,
  `TauCeti.TwistedMonoidAlgebra.repr_decompose_gradeBy`: internal direct-sum decomposition, piece
  ranks, and coordinate restriction under projection.
* `TauCeti.TwistedMonoidAlgebra.degWidth_of_mul`, `TauCeti.TwistedMonoidAlgebra.degWidth_mul_of`:
  invariance of degree width under multiplication by twisted basis units `of g`.
* `TauCeti.TwistedMonoidAlgebra.map_gradeBy_addMonoidAlgebraEquiv`: compatibility of `gradeBy` with
  `AddMonoidAlgebra.gradeBy` for the trivial factor set `1`.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open _root_.DirectSum Module

section GradeBy

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- The `i`-th piece of `k_α[G]` for a weight function `w : G → ι`: the `k`-span of the basis
elements `of g` with `w g = i`. -/
noncomputable def gradeBy {ι : Type*} (w : G → ι) (i : ι) :
    Submodule k (twistedMonoidAlgebra k G α) :=
  Submodule.span k (of '' {g : G | w g = i})

variable {k G α}

theorem gradeBy_eq_span_basis {ι : Type*} (w : G → ι) (i : ι) :
    gradeBy k G α w i = Submodule.span k (basis k G α '' {g : G | w g = i}) := by
  have hof : (of : G → twistedMonoidAlgebra k G α) = basis k G α :=
    funext fun g ↦ (basis_apply k G α g).symm
  rw [gradeBy, hof]

/-- An element of `k_α[G]` lies in the piece of grade `i` if and only if every `g` in its basis
support has weight `i`. -/
theorem mem_gradeBy_iff {ι : Type*} (w : G → ι) (i : ι) (x : twistedMonoidAlgebra k G α) :
    x ∈ gradeBy k G α w i ↔ ∀ g ∈ ((basis k G α).repr x).support, w g = i := by
  rw [gradeBy_eq_span_basis, Basis.mem_span_image]
  rfl

theorem of_mem_gradeBy {ι : Type*} (w : G → ι) (g : G) :
    (of g : twistedMonoidAlgebra k G α) ∈ gradeBy k G α w (w g) :=
  Submodule.subset_span ⟨g, rfl, rfl⟩

theorem smul_of_mem_gradeBy {ι : Type*} (w : G → ι) (c : k) (g : G) :
    c • (of g : twistedMonoidAlgebra k G α) ∈ gradeBy k G α w (w g) :=
  Submodule.smul_mem _ c (of_mem_gradeBy w g)

variable (k G α)

/-- The fibers of any map `w : G → ι` decompose `k_α[G]` as an internal direct sum. -/
theorem gradeBy_isInternal {ι : Type*} [DecidableEq ι] (w : G → ι) :
    DirectSum.IsInternal (gradeBy k G α w) := by
  have h : gradeBy k G α w = fun c ↦ Submodule.span k (basis k G α '' {g : G | w g = c}) :=
    funext (gradeBy_eq_span_basis w)
  rw [h]
  exact (basis k G α).isInternal_span_image_fiber w

noncomputable instance instDecompositionGradeBy {ι : Type*} [DecidableEq ι] (w : G → ι) :
    DirectSum.Decomposition (gradeBy k G α w) :=
  (gradeBy_isInternal k G α w).chooseDecomposition

/-- The basis of `gradeBy k G α w i` formed by the elements `of g` with `w g = i`. -/
noncomputable def basisGradeBy {ι : Type*} (w : G → ι) (i : ι) :
    Basis {g : G // w g = i} k (gradeBy k G α w i) :=
  Basis.mk
    (v := fun g ↦ ⟨of g.1, Submodule.subset_span ⟨g.1, g.2, rfl⟩⟩)
    (LinearIndependent.of_comp (Submodule.subtype _) <| by
      simpa only [Function.comp_def, Submodule.coe_subtype, ← basis_apply k G α] using
        (basis k G α).linearIndependent.comp Subtype.val Subtype.val_injective)
    (by
      rintro ⟨x, hx⟩ -
      refine Submodule.span_induction (p := fun y hy ↦ (⟨y, hy⟩ : gradeBy k G α w i) ∈ _)
        (fun y ⟨g, hg, hy⟩ ↦ by subst hy; exact Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩) (zero_mem _)
        (fun _ _ _ _ ha hb ↦ add_mem ha hb)
        (fun c _ _ ha ↦ Submodule.smul_mem _ c ha) hx)

@[simp]
theorem coe_basisGradeBy {ι : Type*} (w : G → ι) (i : ι) (g : {g : G // w g = i}) :
    ((basisGradeBy k G α w i g : gradeBy k G α w i) : twistedMonoidAlgebra k G α) = of g.1 := by
  simp [basisGradeBy]

instance {ι : Type*} (w : G → ι) (i : ι) : Module.Free k (gradeBy k G α w i) :=
  Module.Free.of_basis (basisGradeBy k G α w i)

/-- The dimension of the `i`-th graded piece of `k_α[G]` is the cardinality of the fiber
`w ⁻¹' {i}`. -/
theorem finrank_gradeBy [StrongRankCondition k] {ι : Type*} (w : G → ι) (i : ι) :
    finrank k (gradeBy k G α w i) = Nat.card {g : G // w g = i} :=
  finrank_eq_nat_card_basis (basisGradeBy k G α w i)

variable {k G α}

/-- Homogeneous projection onto grade `i` restricts the basis coordinates to the fiber `w g = i`. -/
theorem repr_decompose_gradeBy {ι : Type*} [DecidableEq ι] (w : G → ι)
    (x : twistedMonoidAlgebra k G α) (i : ι) (g : G) :
    (basis k G α).repr (decompose (gradeBy k G α w) x i : twistedMonoidAlgebra k G α) g =
      if w g = i then (basis k G α).repr x g else 0 := by
  induction x using Decomposition.inductionOn (gradeBy k G α w) with
  | zero => simp
  | @homogeneous j y =>
    have hy : ∀ h ∈ ((basis k G α).repr (y : twistedMonoidAlgebra k G α)).support, w h = j :=
      (mem_gradeBy_iff w j (y : twistedMonoidAlgebra k G α)).mp y.2
    by_cases hji : j = i
    · subst hji
      rw [decompose_of_mem_same _ y.2]
      split_ifs with hg
      · rfl
      · exact Finsupp.notMem_support_iff.mp fun hmem ↦ hg (hy g hmem)
    · rw [decompose_of_mem_ne _ y.2 hji, map_zero, Finsupp.zero_apply]
      split_ifs with hg
      · symm
        exact Finsupp.notMem_support_iff.mp fun hmem ↦ hji ((hy g hmem).symm.trans hg)
      · rfl
  | add x y hx hy => simp [hx, hy, ite_add_zero]

theorem coe_decompose_gradeBy_ne_zero_iff {ι : Type*} [DecidableEq ι] (w : G → ι)
    (x : twistedMonoidAlgebra k G α) (i : ι) :
    (decompose (gradeBy k G α w) x i : twistedMonoidAlgebra k G α) ≠ 0 ↔
      ∃ g ∈ ((basis k G α).repr x).support, w g = i := by
  rw [← (basis k G α).repr.map_ne_zero_iff, Finsupp.ne_iff]
  simp only [Finsupp.zero_apply, repr_decompose_gradeBy, ne_eq, ite_eq_right_iff, not_forall,
    exists_prop, Finsupp.mem_support_iff, and_comm]

end GradeBy

section GradeByHom

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- Grading of `k_α[G]` by an additive homomorphism `w : Additive G →+ ι`. -/
noncomputable def gradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (i : ι) :
    Submodule k (twistedMonoidAlgebra k G α) :=
  gradeBy k G α (fun g ↦ w (Additive.ofMul g)) i

/-- The fine `Additive G`-grading of `k_α[G]`, in which `of g` has degree `Additive.ofMul g`. -/
noncomputable abbrev grade : Additive G → Submodule k (twistedMonoidAlgebra k G α) :=
  gradeByHom k G α (AddMonoidHom.id (Additive G))

theorem gradeByHom_def {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (i : ι) :
    gradeByHom k G α w i = gradeBy k G α (fun g ↦ w (Additive.ofMul g)) i :=
  (rfl)

theorem mem_gradeByHom_iff {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (i : ι)
    (x : twistedMonoidAlgebra k G α) :
    x ∈ gradeByHom k G α w i ↔
      ∀ g ∈ ((basis k G α).repr x).support, w (Additive.ofMul g) = i :=
  mem_gradeBy_iff _ i x

theorem of_mem_gradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (g : G) :
    (of g : twistedMonoidAlgebra k G α) ∈ gradeByHom k G α w (w (Additive.ofMul g)) :=
  of_mem_gradeBy _ g

theorem smul_of_mem_gradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (c : k) (g : G) :
    c • (of g : twistedMonoidAlgebra k G α) ∈ gradeByHom k G α w (w (Additive.ofMul g)) :=
  smul_of_mem_gradeBy _ c g

instance instGradedMonoidGradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) :
    SetLike.GradedMonoid (gradeByHom k G α w) where
  one_mem := by
    rw [← of_one (k := k) (G := G) (α := α)]
    simpa only [ofMul_one, map_zero] using of_mem_gradeByHom k G α w 1
  mul_mem i j x y hx hy := by
    rw [gradeByHom_def, gradeBy] at hx hy
    refine Submodule.span_induction (p := fun x _ ↦ x * y ∈ gradeByHom k G α w (i + j))
      (fun _ hx' ↦ ?_) (by simp) (fun a b _ _ ha hb ↦ by rw [add_mul]; exact add_mem ha hb)
      (fun c a _ ha ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha) hx
    obtain ⟨g, hg : w (Additive.ofMul g) = i, rfl⟩ := hx'
    refine Submodule.span_induction (p := fun y _ ↦ of g * y ∈ gradeByHom k G α w (i + j))
      (fun _ hy' ↦ ?_) (by simp) (fun a b _ _ ha hb ↦ by rw [mul_add]; exact add_mem ha hb)
      (fun c a _ ha ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha) hy
    obtain ⟨h, hh : w (Additive.ofMul h) = j, rfl⟩ := hy'
    rw [of_mul_of, ← hg, ← hh, ← map_add, ← ofMul_mul]
    exact smul_of_mem_gradeByHom k G α w (α g h : k) (g * h)

noncomputable instance instDecompositionGradeByHom {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (w : Additive G →+ ι) : DirectSum.Decomposition (gradeByHom k G α w) :=
  inferInstanceAs <| DirectSum.Decomposition (gradeBy k G α fun g ↦ w (Additive.ofMul g))

/-- `twistedMonoidAlgebra k G α` is internally graded by any additive homomorphism
`w : Additive G →+ ι`. -/
noncomputable instance instGradedAlgebraGradeByHom {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (w : Additive G →+ ι) : GradedAlgebra (gradeByHom k G α w) :=
  { instGradedMonoidGradeByHom k G α w, instDecompositionGradeByHom k G α w with }

section Degree

variable {k G α}
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι] [LinearOrder ι]

theorem minDeg_smul_of (w : Additive G →+ ι) {c : k} (hc : c ≠ 0) (g : G) :
    GradedAlgebra.minDeg (gradeByHom k G α w) (c • (of g : twistedMonoidAlgebra k G α)) =
      w (Additive.ofMul g) := by
  refine GradedAlgebra.minDeg_of_mem_ne_zero _ (smul_of_mem_gradeByHom k G α w c g) fun h0 ↦ hc ?_
  have h := congrArg (fun x ↦ (basis k G α).repr x g) h0
  rw [← basis_apply k G α g, map_smul, Basis.repr_self, Finsupp.smul_single_one,
    Finsupp.single_eq_same, map_zero, Finsupp.zero_apply] at h
  exact h

theorem maxDeg_smul_of (w : Additive G →+ ι) {c : k} (hc : c ≠ 0) (g : G) :
    GradedAlgebra.maxDeg (gradeByHom k G α w) (c • (of g : twistedMonoidAlgebra k G α)) =
      w (Additive.ofMul g) := by
  refine GradedAlgebra.maxDeg_of_mem_ne_zero _ (smul_of_mem_gradeByHom k G α w c g) fun h0 ↦ hc ?_
  have h := congrArg (fun x ↦ (basis k G α).repr x g) h0
  rw [← basis_apply k G α g, map_smul, Basis.repr_self, Finsupp.smul_single_one,
    Finsupp.single_eq_same, map_zero, Finsupp.zero_apply] at h
  exact h

end Degree

section GroupWidth

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]
variable {ι : Type*} [DecidableEq ι] [AddCommGroup ι] [LinearOrder ι]

@[simp]
theorem degWidth_of (w : Additive G →+ ι) (g : G) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (of g : twistedMonoidAlgebra k G α) = 0 :=
  GradedAlgebra.degWidth_of_mem _ (of_mem_gradeByHom k G α w g)

/-- In a twisted group algebra without zero divisors, multiplying on the left by any twisted basis
unit `of g` preserves the degree width. -/
theorem degWidth_of_mul [IsOrderedAddMonoid ι]
    [NoZeroDivisors (twistedMonoidAlgebra k G α)] (w : Additive G →+ ι)
    (g : G) (x : twistedMonoidAlgebra k G α) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (of g * x) =
      GradedAlgebra.degWidth (gradeByHom k G α w) x :=
  GradedAlgebra.degWidth_mul_of_isUnit_left _ (isUnit_of g) x

/-- In a twisted group algebra without zero divisors, multiplying on the right by any twisted basis
unit `of g` preserves the degree width. -/
theorem degWidth_mul_of [IsOrderedAddMonoid ι]
    [NoZeroDivisors (twistedMonoidAlgebra k G α)] (w : Additive G →+ ι)
    (x : twistedMonoidAlgebra k G α) (g : G) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (x * of g) =
      GradedAlgebra.degWidth (gradeByHom k G α w) x :=
  GradedAlgebra.degWidth_mul_of_isUnit_right _ (isUnit_of g) x

end GroupWidth

end GradeByHom

section Lattice

variable (k L : Type*) [CommSemiring k] [AddMonoid L]

/-- The canonical additive homomorphism identifying `Additive (Multiplicative L)` with `L`. -/
def additiveMultiplicativeHom : Additive (Multiplicative L) →+ L where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem additiveMultiplicativeHom_ofMul_ofAdd (m : L) :
    additiveMultiplicativeHom L (Additive.ofMul (Multiplicative.ofAdd m)) = m :=
  (rfl)

/-- Grading of a twisted additive-monoid (or lattice) algebra
`twistedMonoidAlgebra k (Multiplicative L) α` by an additive weight `w : L →+ ι`. -/
noncomputable abbrev gradeByAddHom {ι : Type*} [AddMonoid ι]
    (α : Multiplicative L → Multiplicative L → kˣ) [IsFactorSet α] (w : L →+ ι) :
    ι → Submodule k (twistedMonoidAlgebra k (Multiplicative L) α) :=
  gradeByHom k (Multiplicative L) α (w.comp (additiveMultiplicativeHom L))

/-- For the trivial factor set `1`, `twistedMonoidAlgebra k (Multiplicative L) 1` is canonically
isomorphic as a `k`-algebra to `AddMonoidAlgebra k L`. -/
noncomputable def addMonoidAlgebraEquiv :
    twistedMonoidAlgebra k (Multiplicative L) (1 : Multiplicative L → Multiplicative L → kˣ) ≃ₐ[k]
      AddMonoidAlgebra k L :=
  (monoidAlgebraEquiv k (Multiplicative L)).trans
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k L).symm

@[simp]
theorem addMonoidAlgebraEquiv_of (m : L) :
    addMonoidAlgebraEquiv k L (of (Multiplicative.ofAdd m)) = AddMonoidAlgebra.single m 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k L).injective
  simp [addMonoidAlgebraEquiv]

@[simp]
theorem addMonoidAlgebraEquiv_symm_single (m : L) (c : k) :
    (addMonoidAlgebraEquiv k L).symm (AddMonoidAlgebra.single m c) =
      c • of (Multiplicative.ofAdd m) := by
  apply (addMonoidAlgebraEquiv k L).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, addMonoidAlgebraEquiv_of,
    AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Under `addMonoidAlgebraEquiv`, the fiber grading of the trivial-twist algebra matches
`AddMonoidAlgebra.gradeBy`. -/
@[simp]
theorem map_gradeBy_addMonoidAlgebraEquiv {ι : Type*} (w : L → ι) (i : ι) :
    (gradeBy k (Multiplicative L) 1 (w ∘ Multiplicative.toAdd) i).map
        (addMonoidAlgebraEquiv k L).toLinearMap =
      AddMonoidAlgebra.gradeBy k w i := by
  rw [gradeBy, Submodule.map_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx ↦ ?_
  · rintro _ ⟨_, ⟨g, hg : w g.toAdd = i, rfl⟩, rfl⟩
    rw [AlgEquiv.toLinearMap_apply, ← ofAdd_toAdd g, addMonoidAlgebraEquiv_of]
    exact hg ▸ AddMonoidAlgebra.single_mem_gradeBy w g.toAdd 1
  · rw [← AddMonoidAlgebra.sum_coeff_single x]
    refine Submodule.sum_mem _ fun m hm ↦ ?_
    have hwm : w m = i := (AddMonoidAlgebra.mem_gradeBy_iff k w i x).mp hx hm
    have hsingle : AddMonoidAlgebra.single m (x.coeff m) =
        x.coeff m • addMonoidAlgebraEquiv k L (of (Multiplicative.ofAdd m)) := by
      rw [addMonoidAlgebraEquiv_of, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, ⟨Multiplicative.ofAdd m, hwm, rfl⟩, rfl⟩)

end Lattice

end TauCeti.TwistedMonoidAlgebra
