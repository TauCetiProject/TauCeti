/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.Twisted.NoZeroDivisors
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width

/-!
# Weight gradings on twisted monoid algebras

Every function `w : G → ι` decomposes `TauCeti.twistedMonoidAlgebra k G α` as the internal direct
sum of the fiber submodules `TauCeti.TwistedMonoidAlgebra.gradeBy k G α w i`, each free over `k` on
`{g : G // w g = i}`. When `w : Additive G →+ ι` is additive, `gradeByHom k G α w` is an internal
`GradedAlgebra` structure; specializing to `w = id` gives `grade k G α` and specializing to
`G = Multiplicative L` gives `gradeByAddHom` for twisted lattice algebras. Over `[NoZeroDivisors k]`
and `[AddCancelCommMonoid L] [IsAddTorsionFree L]`, `TauCeti.Algebra.Group.UniqueProds.TorsionFree`
and `TauCeti.Algebra.MonoidAlgebra.Twisted.NoZeroDivisors` supply `NoZeroDivisors` (and `IsDomain`
over a domain `k`), making `minHomogPart` and `maxHomogPart` nonzero and multiplicative and
`minDeg`, `maxDeg`, `degWidth` additive on nonzero products. For `α = 1`, `addMonoidAlgebraEquiv`
identifies the algebra with `AddMonoidAlgebra k L`.

## Main definitions and results

* `TauCeti.TwistedMonoidAlgebra.gradeBy`, `basisGradeBy`, `gradeBy_isInternal`, `finrank_gradeBy`,
  `repr_decompose_gradeBy`: fiber submodules, bases, direct-sum decomposition, ranks, and
  projections.
* `TauCeti.TwistedMonoidAlgebra.gradeByHom`, `grade`, `gradeByAddHom`, `degWidth_of_mul`,
  `degWidth_mul_of`: additive weight `GradedAlgebra` structures and basis-unit width invariance.
* `TauCeti.TwistedMonoidAlgebra.map_gradeBy_addMonoidAlgebraEquiv`,
  `TauCeti.TwistedMonoidAlgebra.map_gradeByAddHom_addMonoidAlgebraEquiv`: compatibility of the
  trivial-twist fiber and additive-weight gradings with `AddMonoidAlgebra.gradeBy` under
  `addMonoidAlgebraEquiv`.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open _root_.DirectSum _root_.Module

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
  simp [Set.subset_def]

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
  ((basis k G α).spanImageFiber w i).map (LinearEquiv.ofEq _ _ (gradeBy_eq_span_basis w i).symm)

@[simp]
theorem coe_basisGradeBy {ι : Type*} (w : G → ι) (i : ι) (g : {g : G // w g = i}) :
    ((basisGradeBy k G α w i g : gradeBy k G α w i) : twistedMonoidAlgebra k G α) = of g.val := by
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
@[simp]
theorem repr_decompose_gradeBy {ι : Type*} [DecidableEq ι] (w : G → ι)
    (x : twistedMonoidAlgebra k G α) (i : ι) (g : G) :
    (basis k G α).repr (decompose (gradeBy k G α w) x i : twistedMonoidAlgebra k G α) g =
      if w g = i then (basis k G α).repr x g else 0 := by
  induction x using Decomposition.inductionOn (gradeBy k G α w) with
  | zero => simp
  | @homogeneous j y =>
    have hy : ∀ h ∈ ((basis k G α).repr (y : twistedMonoidAlgebra k G α)).support, w h = j :=
      (mem_gradeBy_iff w j (y : twistedMonoidAlgebra k G α)).mp y.property
    by_cases hji : j = i
    · subst hji
      rw [decompose_of_mem_same _ y.property]
      split_ifs with hg
      · rfl
      · exact Finsupp.notMem_support_iff.mp fun hmem ↦ hg (hy g hmem)
    · rw [decompose_of_mem_ne _ y.property hji, map_zero, Finsupp.zero_apply]
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
      ∀ g ∈ ((basis k G α).repr x).support, w (Additive.ofMul g) = i := by
  rw [gradeByHom_def]
  exact mem_gradeBy_iff _ i x

theorem of_mem_gradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (g : G) :
    (of g : twistedMonoidAlgebra k G α) ∈ gradeByHom k G α w (w (Additive.ofMul g)) := by
  rw [gradeByHom_def]
  exact of_mem_gradeBy _ g

theorem smul_of_mem_gradeByHom {ι : Type*} [AddMonoid ι] (w : Additive G →+ ι) (c : k) (g : G) :
    c • (of g : twistedMonoidAlgebra k G α) ∈ gradeByHom k G α w (w (Additive.ofMul g)) := by
  rw [gradeByHom_def]
  exact smul_of_mem_gradeBy _ c g

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
  simpa using congrArg (fun x ↦ (basis k G α).repr x g) h0

theorem maxDeg_smul_of (w : Additive G →+ ι) {c : k} (hc : c ≠ 0) (g : G) :
    GradedAlgebra.maxDeg (gradeByHom k G α w) (c • (of g : twistedMonoidAlgebra k G α)) =
      w (Additive.ofMul g) := by
  refine GradedAlgebra.maxDeg_of_mem_ne_zero _ (smul_of_mem_gradeByHom k G α w c g) fun h0 ↦ hc ?_
  simpa using congrArg (fun x ↦ (basis k G α).repr x g) h0

end Degree

section GroupWidth

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]
variable {ι : Type*} [DecidableEq ι] [AddCommGroup ι] [LinearOrder ι]

@[simp]
theorem degWidth_of (w : Additive G →+ ι) (g : G) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (of g : twistedMonoidAlgebra k G α) = 0 :=
  GradedAlgebra.degWidth_of_mem _ (of_mem_gradeByHom k G α w g)

/-- In a twisted group algebra, multiplying on the left by any twisted basis unit `of g` preserves
the degree width. -/
theorem degWidth_of_mul [IsOrderedAddMonoid ι] (w : Additive G →+ ι)
    (g : G) (x : twistedMonoidAlgebra k G α) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (of g * x) =
      GradedAlgebra.degWidth (gradeByHom k G α w) x :=
  GradedAlgebra.degWidth_mul_of_isUnit_of_mem_left _ (isUnit_of g) (of_mem_gradeByHom k G α w g) x

/-- In a twisted group algebra, multiplying on the right by any twisted basis unit `of g` preserves
the degree width. -/
theorem degWidth_mul_of [IsOrderedAddMonoid ι] (w : Additive G →+ ι)
    (x : twistedMonoidAlgebra k G α) (g : G) :
    GradedAlgebra.degWidth (gradeByHom k G α w) (x * of g) =
      GradedAlgebra.degWidth (gradeByHom k G α w) x :=
  GradedAlgebra.degWidth_mul_of_isUnit_of_mem_right _ (isUnit_of g) (of_mem_gradeByHom k G α w g) x

end GroupWidth

end GradeByHom

section Lattice

variable (k L : Type*) [CommSemiring k] [AddMonoid L]

/-- Grading of a twisted additive-monoid (or lattice) algebra
`twistedMonoidAlgebra k (Multiplicative L) α` by an additive weight `w : L →+ ι`. -/
noncomputable abbrev gradeByAddHom {ι : Type*} [AddMonoid ι]
    (α : Multiplicative L → Multiplicative L → kˣ) [IsFactorSet α] (w : L →+ ι) :
    ι → Submodule k (twistedMonoidAlgebra k (Multiplicative L) α) :=
  gradeByHom k (Multiplicative L) α (w.comp (AddEquiv.additiveMultiplicative L).toAddMonoidHom)

theorem gradeByAddHom_eq {ι : Type*} [AddMonoid ι]
    (α : Multiplicative L → Multiplicative L → kˣ) [IsFactorSet α] (w : L →+ ι) (i : ι) :
    gradeByAddHom k L α w i = gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd) i := by
  ext x
  simp [gradeByAddHom, mem_gradeByHom_iff, mem_gradeBy_iff]

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

/-- Under `addMonoidAlgebraEquiv`, `gradeByAddHom` for the trivial factor set matches
`AddMonoidAlgebra.gradeBy`. -/
@[simp]
theorem map_gradeByAddHom_addMonoidAlgebraEquiv {ι : Type*} [AddMonoid ι]
    (w : L →+ ι) (i : ι) :
    (gradeByAddHom k L 1 w i).map (addMonoidAlgebraEquiv k L).toLinearMap =
      AddMonoidAlgebra.gradeBy k w i := by
  rw [gradeByAddHom_eq, map_gradeBy_addMonoidAlgebraEquiv]

end Lattice

/-! ### Checks -/

example {k L : Type*} [CommRing k] [IsDomain k] [AddCommGroup L] [IsAddTorsionFree L]
    (α : Multiplicative L → Multiplicative L → kˣ) [IsFactorSet α] (w : L →+ ℤ)
    {x y : twistedMonoidAlgebra k (Multiplicative L) α} (hx : x ≠ 0) (hy : y ≠ 0) :
    let 𝒜 := gradeByAddHom k L α w
    GradedAlgebra.minHomogPart 𝒜 x ≠ 0 ∧ GradedAlgebra.maxHomogPart 𝒜 x ≠ 0 ∧
      GradedAlgebra.minHomogPart 𝒜 (x * y) =
        GradedAlgebra.minHomogPart 𝒜 x * GradedAlgebra.minHomogPart 𝒜 y ∧
      GradedAlgebra.maxHomogPart 𝒜 (x * y) =
        GradedAlgebra.maxHomogPart 𝒜 x * GradedAlgebra.maxHomogPart 𝒜 y ∧
      GradedAlgebra.minDeg 𝒜 (x * y) = GradedAlgebra.minDeg 𝒜 x + GradedAlgebra.minDeg 𝒜 y ∧
      GradedAlgebra.maxDeg 𝒜 (x * y) = GradedAlgebra.maxDeg 𝒜 x + GradedAlgebra.maxDeg 𝒜 y ∧
      GradedAlgebra.degWidth 𝒜 (x * y) = GradedAlgebra.degWidth 𝒜 x + GradedAlgebra.degWidth 𝒜 y :=
  ⟨GradedAlgebra.minHomogPart_ne_zero _ hx, GradedAlgebra.maxHomogPart_ne_zero _ hx,
    GradedAlgebra.minHomogPart_mul _ x y, GradedAlgebra.maxHomogPart_mul _ x y,
    GradedAlgebra.minDeg_mul _ hx hy, GradedAlgebra.maxDeg_mul _ hx hy,
    GradedAlgebra.degWidth_mul _ hx hy⟩

end TauCeti.TwistedMonoidAlgebra
