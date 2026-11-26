/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Internal weight grading of twisted monoid algebras

In the twisted monoid algebra `twistedMonoidAlgebra k G α`, multiplying basis elements rescales the
product basis element by a scalar unit (`of g * of h = α g h • of (g * h)`), so the twist preserves
exponents. Any weight `f : G → M` into an additive monoid `M` satisfying `f 1 = 0` and
`f (g * h) = f g + f h` therefore equips `twistedMonoidAlgebra k G α` with an internal `M`-grading
`TwistedMonoidAlgebra.gradeBy k G α f` whose `m`-th piece is spanned by `{of g | f g = m}`.

In particular:
* any multiplicative weight `f : G →* Multiplicative M` induces a `GradedAlgebra` structure on
  `gradeBy k G α (Multiplicative.toAdd ∘ f)`;
* on a twisted lattice algebra `twistedMonoidAlgebra k (Multiplicative L) α`, any additive weight
  `w : L →+ M` (for instance an integer weight `w : L →+ ℤ`) induces a `GradedAlgebra` structure on
  `gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd)`, and for the trivial factor set
  `α = 1` the canonical algebra equivalence `addMonoidAlgebraEquiv` identifies this grading with
  `AddMonoidAlgebra.gradeBy k w`.

Combined with the `NoZeroDivisors (twistedMonoidAlgebra k G α)` instance from
`TauCeti.Algebra.MonoidAlgebra.Twisted.NoZeroDivisors` and
`TauCeti.GradedAlgebra.width`, integer weights on twisted lattice algebras over domains give
multiplicative extreme homogeneous parts and additive extreme degrees and width.

## Main definitions and results

* `TauCeti.TwistedMonoidAlgebra.gradeBy k G α f m`: the `k`-submodule spanned by `of g` with
  `f g = m`, characterized in coordinates by `mem_gradeBy_iff`.
* `TauCeti.TwistedMonoidAlgebra.gradedAlgebraOfMap`: `GradedAlgebra (gradeBy k G α f)` for any
  `f : G → M` sending `1` to `0` and products to sums, with automatic instances for
  `f : G →* Multiplicative M` and for `w : L →+ M` on `Multiplicative L`.
* `TauCeti.TwistedMonoidAlgebra.map_gradeBy_addMonoidAlgebraEquiv`: `addMonoidAlgebraEquiv`
  intertwines `gradeBy` on `twistedMonoidAlgebra k (Multiplicative L) 1` with
  `AddMonoidAlgebra.gradeBy`.

## Implementation notes

The grading construction (`gradeBy`, `gradedMonoidOfMap`, `decomposeAlgHom`,
`decomposeAlgHom_of_mem_aux`, and `gradedAlgebraOfMap`) and the span-induction step of
`map_gradeBy_addMonoidAlgebraEquiv` are adapted from `Mathlib.Algebra.MonoidAlgebra.Grading`
(`AddMonoidAlgebra.gradeBy`, `decomposeAux`, `decomposeAux_coe`, and `gradeBy.gradedAlgebra`),
replacing untwisted monomial multiplication with the factor-set rule
`of g * of h = α g h • of (g * h)` via `TwistedMonoidAlgebra.lift`.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open DirectSum

section GradeBy

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]

/-- The `m`-th homogeneous piece of `twistedMonoidAlgebra k G α` under a weight `f : G → M`,
defined as the `k`-span of the basis elements `of g` with `f g = m`. -/
noncomputable def gradeBy {M : Type*} (f : G → M) (m : M) :
    Submodule k (twistedMonoidAlgebra k G α) :=
  Submodule.span k (of '' {g : G | f g = m})

variable {k G α}

/-- Coordinate characterization of `gradeBy`: an element lies in degree `m` if and only if every
basis element in its coordinate support has weight `m`. -/
theorem mem_gradeBy_iff {M : Type*} {f : G → M} {m : M}
    {x : twistedMonoidAlgebra k G α} :
    x ∈ gradeBy k G α f m ↔ ∀ g ∈ ((basis k G α).repr x).support, f g = m := by
  have hfun : (of : G → twistedMonoidAlgebra k G α) = ⇑(basis k G α) :=
    funext fun g ↦ (basis_apply k G α g).symm
  rw [gradeBy, hfun, Module.Basis.mem_span_image]
  exact ⟨fun h g hg ↦ h hg, fun h g hg ↦ h g hg⟩

theorem of_mem_gradeBy {M : Type*} (f : G → M) (g : G) :
    (of g : twistedMonoidAlgebra k G α) ∈ gradeBy k G α f (f g) :=
  Submodule.subset_span ⟨g, rfl, rfl⟩

@[simp]
theorem of_mem_gradeBy_iff [Nontrivial k] {M : Type*} {f : G → M} {m : M} {g : G} :
    (of g : twistedMonoidAlgebra k G α) ∈ gradeBy k G α f m ↔ f g = m := by
  refine ⟨fun h ↦ mem_gradeBy_iff.mp h g ?_, fun h ↦ h ▸ of_mem_gradeBy f g⟩
  rw [repr_of, Finsupp.mem_support_iff, Finsupp.single_eq_same]
  exact one_ne_zero

end GradeBy

section GradedAlgebra

variable (k G : Type*) [CommSemiring k] [Monoid G] (α : G → G → kˣ) [IsFactorSet α]
  {M : Type*} [AddMonoid M]

/-- Any weight `f : G → M` with `f 1 = 0` and `f (g * h) = f g + f h` makes `gradeBy k G α f` a
`SetLike.GradedMonoid`. -/
theorem gradedMonoidOfMap {f : G → M} (hf₁ : f 1 = 0)
    (hf_mul : ∀ g h : G, f (g * h) = f g + f h) :
    SetLike.GradedMonoid (gradeBy k G α f) where
  one_mem := by
    rw [← of_one, ← hf₁]
    exact of_mem_gradeBy f 1
  mul_mem i j x y hx hy := by
    refine Submodule.mul_le.mp ?_ x hx y hy
    rw [gradeBy, gradeBy, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, hg : f g = i, rfl⟩, _, ⟨h, hh : f h = j, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, of_mul_of]
    refine Submodule.smul_mem _ _ ?_
    have hgh : f (g * h) = i + j := by rw [hf_mul, hg, hh]
    exact hgh ▸ of_mem_gradeBy f (g * h)

/-- The canonical algebra map decomposing `twistedMonoidAlgebra k G α` into `⨁ m, gradeBy k G α f m`
for an additive weight `f` on `G`. -/
noncomputable def decomposeAlgHom [DecidableEq M] {f : G → M} (hf₁ : f 1 = 0)
    (hf_mul : ∀ g h : G, f (g * h) = f g + f h) :
    letI := gradedMonoidOfMap k G α hf₁ hf_mul
    twistedMonoidAlgebra k G α →ₐ[k] ⨁ m, gradeBy k G α f m :=
  letI := gradedMonoidOfMap k G α hf₁ hf_mul
  lift (fun g ↦ DirectSum.of (fun m ↦ gradeBy k G α f m) (f g) ⟨of g, of_mem_gradeBy f g⟩)
    (by
      rw [DirectSum.one_def]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext hf₁ of_one))
    (fun g h ↦ by
      rw [DirectSum.of_mul_of, ← DirectSum.of_smul]
      exact DirectSum.of_eq_of_gradedMonoid_eq
        (Sigma.subtype_ext (hf_mul g h).symm (of_mul_of g h)))

/-- `decomposeAlgHom` sends each basis element `of g` to its homogeneous piece at degree `f g`. -/
@[simp]
theorem decomposeAlgHom_of [DecidableEq M] {f : G → M} (hf₁ : f 1 = 0)
    (hf_mul : ∀ g h : G, f (g * h) = f g + f h) (g : G) :
    letI := gradedMonoidOfMap k G α hf₁ hf_mul
    decomposeAlgHom k G α hf₁ hf_mul (of g) =
      DirectSum.of (fun m ↦ gradeBy k G α f m) (f g) ⟨of g, of_mem_gradeBy f g⟩ := by
  let _ := gradedMonoidOfMap k G α hf₁ hf_mul
  exact lift_of ..

private theorem decomposeAlgHom_of_mem_aux [DecidableEq M] {f : G → M} (hf₁ : f 1 = 0)
    (hf_mul : ∀ g h : G, f (g * h) = f g + f h) {m : M} {x : twistedMonoidAlgebra k G α}
    (hx : x ∈ gradeBy k G α f m) :
    letI := gradedMonoidOfMap k G α hf₁ hf_mul
    decomposeAlgHom k G α hf₁ hf_mul x =
      DirectSum.of (fun m' ↦ gradeBy k G α f m') m ⟨x, hx⟩ := by
  let _ := gradedMonoidOfMap k G α hf₁ hf_mul
  unfold gradeBy at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl, rfl⟩ := hy
    exact decomposeAlgHom_of k G α hf₁ hf_mul g
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add y z hy hz ihy ihz =>
    rw [map_add, ihy, ihz, ← map_add]
    exact congrArg _ (Subtype.ext rfl)
  | smul c y hy ih =>
    rw [map_smul, ih, ← DirectSum.of_smul]
    exact congrArg _ (Subtype.ext rfl)

/-- Any weight `f : G → M` with `f 1 = 0` and `f (g * h) = f g + f h` equips
`twistedMonoidAlgebra k G α` with a `GradedAlgebra` structure. -/
@[instance_reducible]
noncomputable def gradedAlgebraOfMap [DecidableEq M] {f : G → M} (hf₁ : f 1 = 0)
    (hf_mul : ∀ g h : G, f (g * h) = f g + f h) :
    GradedAlgebra (gradeBy k G α f) :=
  letI := gradedMonoidOfMap k G α hf₁ hf_mul
  GradedAlgebra.ofAlgHom (gradeBy k G α f) (decomposeAlgHom k G α hf₁ hf_mul)
    (algHom_ext fun g ↦ by
      simp [decomposeAlgHom_of])
    (fun _ x ↦ decomposeAlgHom_of_mem_aux k G α hf₁ hf_mul x.property)

instance gradeBy.instGradedMonoid (f : G →* Multiplicative M) :
    SetLike.GradedMonoid (gradeBy k G α (Multiplicative.toAdd ∘ f)) :=
  gradedMonoidOfMap k G α (by simp) (fun g h ↦ by simp [map_mul])

noncomputable instance gradeBy.instGradedAlgebra [DecidableEq M] (f : G →* Multiplicative M) :
    GradedAlgebra (gradeBy k G α (Multiplicative.toAdd ∘ f)) :=
  gradedAlgebraOfMap k G α (by simp) (fun g h ↦ by simp [map_mul])

@[simp]
theorem decompose_gradeBy_of [DecidableEq M] (f : G →* Multiplicative M) (g : G) :
    DirectSum.decompose (gradeBy k G α (Multiplicative.toAdd ∘ f)) (of g) =
      DirectSum.of (fun m ↦ gradeBy k G α (Multiplicative.toAdd ∘ f) m)
        (Multiplicative.toAdd (f g)) ⟨of g, of_mem_gradeBy (Multiplicative.toAdd ∘ f) g⟩ :=
  DirectSum.decompose_of_mem _ (of_mem_gradeBy (Multiplicative.toAdd ∘ f) g)

end GradedAlgebra

section MultiplicativeLattice

variable (k L : Type*) [CommSemiring k] [AddMonoid L]

/-- Under `addMonoidAlgebraEquiv`, the weight grading `gradeBy` of the trivial-twist lattice
algebra maps onto `AddMonoidAlgebra.gradeBy`. -/
theorem map_gradeBy_addMonoidAlgebraEquiv {M : Type*} (w : L → M) (m : M) :
    (gradeBy k (Multiplicative L) (1 : Multiplicative L → Multiplicative L → kˣ)
      (w ∘ Multiplicative.toAdd) m).map (addMonoidAlgebraEquiv k L).toLinearMap =
      AddMonoidAlgebra.gradeBy k w m := by
  refine le_antisymm ?_ ?_
  · rw [gradeBy, Submodule.map_span_le]
    rintro _ ⟨a, rfl : w (Multiplicative.toAdd a) = m, rfl⟩
    rw [AlgEquiv.toLinearMap_apply, ← ofAdd_toAdd a, addMonoidAlgebraEquiv_of]
    exact AddMonoidAlgebra.single_mem_gradeBy w (Multiplicative.toAdd a) 1
  · intro p hp
    rw [← p.sum_coeff_single, Finsupp.sum]
    refine Submodule.sum_mem _ fun a ha ↦ ⟨p.coeff a • of (Multiplicative.ofAdd a), ?_, ?_⟩
    · have hwa : w a = m := (AddMonoidAlgebra.mem_gradeBy_iff k w m p).mp hp ha
      refine Submodule.smul_mem _ (p.coeff a) ?_
      simpa only [Function.comp_apply, toAdd_ofAdd, hwa] using
        of_mem_gradeBy (k := k) (α := (1 : Multiplicative L → Multiplicative L → kˣ))
          (w ∘ Multiplicative.toAdd) (Multiplicative.ofAdd a)
    · simp [addMonoidAlgebraEquiv_of]

variable (α : Multiplicative L → Multiplicative L → kˣ) [IsFactorSet α]
  {M : Type*} [AddMonoid M]

instance weightGradeBy.instGradedMonoid (w : L →+ M) :
    SetLike.GradedMonoid (gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd)) :=
  gradedMonoidOfMap k (Multiplicative L) α (by simp) (fun g h ↦ by simp [toAdd_mul])

noncomputable instance weightGradeBy.instGradedAlgebra [DecidableEq M] (w : L →+ M) :
    GradedAlgebra (gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd)) :=
  gradedAlgebraOfMap k (Multiplicative L) α (by simp) (fun g h ↦ by simp [toAdd_mul])

@[simp]
theorem decompose_weightGradeBy_of [DecidableEq M] (w : L →+ M) (a : L) :
    DirectSum.decompose (gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd))
      (of (Multiplicative.ofAdd a)) =
      DirectSum.of (fun m ↦ gradeBy k (Multiplicative L) α (w ∘ Multiplicative.toAdd) m) (w a)
        ⟨of (Multiplicative.ofAdd a), of_mem_gradeBy (w ∘ Multiplicative.toAdd) _⟩ :=
  DirectSum.decompose_of_mem _ (of_mem_gradeBy (w ∘ Multiplicative.toAdd) (Multiplicative.ofAdd a))

end MultiplicativeLattice

end TauCeti.TwistedMonoidAlgebra
