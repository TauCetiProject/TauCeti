/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.Algebra.Polynomial.Eval.IntCast
import TauCeti.RingTheory.Length

/-!
# Lengths of graded pieces and eventual length polynomials

This file records basic properties of `Module.length` on internally graded modules and of
polynomials that eventually agree with the `ENat.toNat` lengths of graded pieces:

* For a homogeneous linear map `f : M → N` of degree `r` between internally `ι`-graded modules,
  the exact sequences `0 → K_p → M_p → N_{p+r} → C_{p+r} → 0` give
  `ℓ(K_p) + ℓ(N_{p+r}) = ℓ(M_p) + ℓ(C_{p+r})`
  (`TauCeti.InternalGrading.length_ker_piece_add_length_piece_add`).
* In a short exact sequence of internally `ι`-graded `S`-modules (over any cancellative additive
  monoid `ι`), homogeneous maps of degrees `r₁` and `r₂` induce short exact sequences on each
  graded piece, giving `ℓ((ℳ₂)_{d + r₁}) = ℓ((ℳ₁)_d) + ℓ((ℳ₃)_{d + r₁ + r₂})`
  (`TauCeti.GradedModule.length_piece_eq_add_of_exact`).
* Over any ring `R` with unique additive division (`HasUniqueDiv R`), polynomials eventually
  agreeing with `(Module.length A (ℳᵢ d)).toNat` add across degree-zero short exact sequences
  (`TauCeti.GradedModule.eq_add_of_exact_of_eventually_eval_length`) and shift by `X + C a` under
  degree shifts (`TauCeti.GradedModule.eq_comp_X_add_C_of_eventually_eval_length`).

## Main results

* `TauCeti.InternalGrading.length_ker_piece_add_length_piece_add`: the lengths of the graded
  pieces of the kernel, source, target and cokernel of a homogeneous map satisfy
  `ℓ(K_p) + ℓ(N_{p+r}) = ℓ(M_p) + ℓ(C_{p+r})`.
* `TauCeti.GradedModule.length_piece_eq_add_of_exact`: additivity of piece lengths in a homogeneous
  short exact sequence over any cancellative grading monoid.
* `TauCeti.GradedModule.length_ker_piece_le` and `TauCeti.GradedModule.length_quotient_piece_le`:
  length bounds on graded pieces of kernels and quotients.
* `TauCeti.GradedModule.eq_add_of_exact_of_eventually_eval_length`: additivity of eventual length
  polynomials in degree-zero short exact sequences.
* `TauCeti.GradedModule.eq_comp_X_add_C_of_eventually_eval_length`: behavior of eventual length
  polynomials under degree shifts.
-/

public section

open DirectSum

namespace TauCeti.InternalGrading

variable {ι R S M N : Type*} [DecidableEq ι] [AddRightCancelMonoid ι] [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A homogeneous map `f` of degree `r`, with kernel `K` and cokernel `C`, gives exact sequences
`0 → K_p → M_p → N_{p+r} → C_{p+r} → 0`, hence this identity of lengths. -/
theorem length_ker_piece_add_length_piece_add (G : InternalGrading R M ι)
    {H : InternalGrading R N ι} {f : M →ₗ[S] N} {r : ι}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (p : ι) :
    Module.length R ((G.ker hf).piece p) + Module.length R (H.piece (p + r)) =
      Module.length R (G.piece p) +
        Module.length R ((H.quotient _ hf.isHomogeneous_range).piece (p + r)) := by
  let U := LinearMap.range f
  -- The three maps of the sequence: inclusion, `f`, and the quotient map.
  let f₁ : (G.ker hf).piece p →ₗ[R] G.piece p :=
    ((LinearMap.ker f).subtype.restrictScalars R).restrict fun _ hz ↦ (G.mem_ker_piece hf).1 hz
  let f₂ : G.piece p →ₗ[R] H.piece (p + r) :=
    (f.restrictScalars R).restrict fun _ hx ↦ by
      rw [LinearMap.restrictScalars_apply]
      exact hf.map_mem hx
  let f₃ : H.piece (p + r) →ₗ[R] (H.quotient U hf.isHomogeneous_range).piece (p + r) :=
    (U.mkQ.restrictScalars R).restrict fun _ hx ↦ by
      rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
      exact H.mk_mem_quotient_piece U _ hx
  -- `LinearMap.restrict_apply` does not match `f₁` syntactically through the kernel's module
  -- structure, so `simp` unfolds `LinearMap.restrict` there.
  have hf₁ (z) : (f₁ z : M) = ((z : LinearMap.ker f) : M) := by simp [f₁, LinearMap.restrict]
  have hf₂ (x) : (f₂ x : N) = f x := by simp [f₂]
  have hf₃ (x) : (f₃ x : N ⧸ U) = Submodule.Quotient.mk (x : N) := by simp [f₃]
  refine length_add_length_eq_length_add_length_of_exact (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
    (fun z₁ z₂ h ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_)
  · exact Subtype.ext (Subtype.ext (by rw [← hf₁, ← hf₁, h]))
  · rw [← Subtype.coe_inj, hf₂, ZeroMemClass.coe_zero]
    constructor
    · intro hy
      exact ⟨⟨⟨y, hy⟩, (G.mem_ker_piece hf).2 y.property⟩, Subtype.ext (hf₁ _)⟩
    · rintro ⟨z, rfl⟩
      rw [hf₁]
      exact (z : LinearMap.ker f).property
  · rw [← Subtype.coe_inj, hf₃, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero]
    constructor
    · -- The degree-`p` component of a preimage is a homogeneous preimage.
      rintro ⟨m, hm⟩
      refine ⟨⟨_, (decompose G.piece m p).property⟩, Subtype.ext ?_⟩
      rw [hf₂, hf.map_decompose, hm, decompose_of_mem_same H.piece y.property]
    · rintro ⟨x, rfl⟩
      rw [hf₂]
      exact LinearMap.mem_range_self f x
  · obtain ⟨x, hx, hxy⟩ := (H.mem_quotient_piece_iff U _).mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end TauCeti.InternalGrading

namespace TauCeti.GradedModule

section ExactLength

/-- In a short exact sequence of internally `ι`-graded `S`-modules where `f` has degree `r₁` and
`g` has degree `r₂` (over any cancellative additive monoid `ι`), the `A`-lengths of the pieces
satisfy `ℓ((ℳ₂)_{d + r₁}) = ℓ((ℳ₁)_d) + ℓ((ℳ₃)_{d + r₁ + r₂})`. -/
theorem length_piece_eq_add_of_exact {A S ι M₁ M₂ M₃ : Type*} [Ring A] [Semiring S] [SMul A S]
    [DecidableEq ι] [AddRightCancelMonoid ι]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    [IsScalarTower A S M₁] [IsScalarTower A S M₂] [IsScalarTower A S M₃]
    (ℳ₁ : ι → Submodule A M₁) [DirectSum.Decomposition ℳ₁]
    (ℳ₂ : ι → Submodule A M₂) [DirectSum.Decomposition ℳ₂]
    (ℳ₃ : ι → Submodule A M₃) [DirectSum.Decomposition ℳ₃]
    {f : M₁ →ₗ[S] M₂} {g : M₂ →ₗ[S] M₃} {r₁ r₂ : ι}
    (hf_hom : LinearMap.IsHomogeneous f ℳ₁ ℳ₂ r₁)
    (hg_hom : LinearMap.IsHomogeneous g ℳ₂ ℳ₃ r₂)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) (d : ι) :
    Module.length A (ℳ₂ (d + r₁)) =
      Module.length A (ℳ₁ d) + Module.length A (ℳ₃ (d + r₁ + r₂)) := by
  let fd : ℳ₁ d →ₗ[A] ℳ₂ (d + r₁) :=
    ((f.restrictScalars A).domRestrict (ℳ₁ d)).codRestrict (ℳ₂ (d + r₁)) fun x ↦
      hf_hom.map_mem x.property
  let gd : ℳ₂ (d + r₁) →ₗ[A] ℳ₃ (d + r₁ + r₂) :=
    ((g.restrictScalars A).domRestrict (ℳ₂ (d + r₁))).codRestrict (ℳ₃ (d + r₁ + r₂)) fun y ↦
      hg_hom.map_mem y.property
  refine Module.length_eq_add_of_exact fd gd
    (fun x y h ↦ Subtype.ext (hf (congrArg Subtype.val h))) (fun z ↦ ?_) (fun y ↦ ?_)
  · obtain ⟨y, hy⟩ := hg z
    refine ⟨decompose ℳ₂ y (d + r₁), Subtype.ext ?_⟩
    have hdec := hg_hom.map_decompose (d + r₁) y
    rw [hy, decompose_of_mem_same ℳ₃ z.property] at hdec
    exact hdec
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hex y).mp (congrArg Subtype.val hy)
      refine ⟨decompose ℳ₁ x d, Subtype.ext ?_⟩
      have hdec := hf_hom.map_decompose d x
      rw [hx, decompose_of_mem_same ℳ₂ y.property] at hdec
      exact hdec
    · rintro ⟨x, rfl⟩
      exact Subtype.ext ((hex (f x)).mpr ⟨x, rfl⟩)

/-- The `A`-length of each graded piece of the kernel of a homogeneous map is at most that of the
source piece. -/
theorem length_ker_piece_le {A S ι M N : Type*} [Ring A] [Ring S] [SMul A S]
    [DecidableEq ι] [AddRightCancelMonoid ι]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    [AddCommGroup N] [Module A N] [Module S N]
    (G : InternalGrading A M ι) {H : InternalGrading A N ι} {f : M →ₗ[S] N} {r : ι}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (d : ι) :
    Module.length A ((G.ker hf).piece d) ≤ Module.length A (G.piece d) :=
  Module.length_le_of_injective
    ((((LinearMap.ker f).subtype.restrictScalars A).domRestrict ((G.ker hf).piece d)).codRestrict
      (G.piece d) fun x ↦ (G.mem_ker_piece hf).mp x.property)
    fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (Subtype.val : G.piece d → M) h))

/-- The `A`-length of each graded piece of a homogeneous quotient is at most that of the ambient
piece. -/
theorem length_quotient_piece_le {A S ι M : Type*} [Ring A] [Ring S] [SMul A S]
    [DecidableEq ι] [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (G : InternalGrading A M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)
    (d : ι) :
    Module.length A ((G.quotient U hU).piece d) ≤ Module.length A (G.piece d) :=
  Module.length_le_of_surjective
    (((U.mkQ.restrictScalars A).domRestrict (G.piece d)).codRestrict
      ((G.quotient U hU).piece d) fun x ↦ G.mk_mem_quotient_piece U hU x.property)
    fun y ↦ by
      obtain ⟨x, hx, hxy⟩ := (G.mem_quotient_piece_iff U hU).mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end ExactLength

section EventualLength

/-- **Additivity of eventual length polynomials.** In a degree-zero short exact sequence of
internally `ℤ`-graded `S`-modules (where `S` acts compatibly with `A`) whose middle pieces have
finite `A`-length for sufficiently large degrees, any polynomials over a ring with unique additive
division eventually agreeing with the `ENat.toNat` piece lengths satisfy `P₂ = P₁ + P₃`. -/
theorem eq_add_of_exact_of_eventually_eval_length {A S M₁ M₂ M₃ R : Type*} [Ring A] [Semiring S]
    [SMul A S] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    [IsScalarTower A S M₁] [IsScalarTower A S M₂] [IsScalarTower A S M₃]
    (ℳ₁ : ℤ → Submodule A M₁) [DirectSum.Decomposition ℳ₁]
    (ℳ₂ : ℤ → Submodule A M₂) [DirectSum.Decomposition ℳ₂]
    (ℳ₃ : ℤ → Submodule A M₃) [DirectSum.Decomposition ℳ₃]
    {f : M₁ →ₗ[S] M₂} {g : M₂ →ₗ[S] M₃}
    (hf_hom : LinearMap.IsHomogeneous f ℳ₁ ℳ₂ 0)
    (hg_hom : LinearMap.IsHomogeneous g ℳ₂ ℳ₃ 0)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    [Ring R] [HasUniqueDiv R]
    {P₁ P₂ P₃ : Polynomial R} {N₀ N₁ N₂ N₃ : ℤ}
    (hfin : ∀ d : ℤ, N₀ ≤ d → Module.length A (ℳ₂ d) ≠ ⊤)
    (hP₁ : ∀ d : ℤ, N₁ ≤ d → P₁.eval (d : R) = ((Module.length A (ℳ₁ d)).toNat : R))
    (hP₂ : ∀ d : ℤ, N₂ ≤ d → P₂.eval (d : R) = ((Module.length A (ℳ₂ d)).toNat : R))
    (hP₃ : ∀ d : ℤ, N₃ ≤ d → P₃.eval (d : R) = ((Module.length A (ℳ₃ d)).toNat : R)) :
    P₂ = P₁ + P₃ := by
  refine Polynomial.eq_of_forall_ge_intCast_eval_eq (N := max (max N₀ N₂) (max N₁ N₃)) fun d hd ↦ ?_
  have hd0 : N₀ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_left hd)
  have hd2 : N₂ ≤ d := le_trans (le_max_right _ _) (le_of_max_le_left hd)
  have hd1 : N₁ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_right hd)
  have hd3 : N₃ ≤ d := le_trans (le_max_right _ _) (le_of_max_le_right hd)
  have hadd := length_piece_eq_add_of_exact ℳ₁ ℳ₂ ℳ₃ hf_hom hg_hom hf hg hex d
  rw [add_zero, add_zero] at hadd
  have hfin2 : Module.length A (ℳ₂ d) ≠ ⊤ := hfin d hd0
  have hfin1 : Module.length A (ℳ₁ d) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (hadd ▸ le_self_add)
  have hfin3 : Module.length A (ℳ₃ d) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (hadd ▸ le_add_self)
  rw [Polynomial.eval_add, hP₁ d hd1, hP₂ d hd2, hP₃ d hd3, hadd,
    ENat.toNat_add hfin1 hfin3, Nat.cast_add]

/-- **Degree shifts of eventual length polynomials.** If `ℳ' d` has the same `A`-length as
`ℳ (d + a)` for all sufficiently large degrees `d`, then any polynomials over a ring with unique
additive division eventually agreeing with their `ENat.toNat` piece lengths satisfy
`P' = P.comp (X + C a)`. -/
theorem eq_comp_X_add_C_of_eventually_eval_length {A M M' R : Type*} [Ring A]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    (ℳ : ℤ → Submodule A M) (ℳ' : ℤ → Submodule A M') (a : ℤ)
    [Ring R] [HasUniqueDiv R]
    {P P' : Polynomial R} {N₀ N N' : ℤ}
    (hshift : ∀ d : ℤ, N₀ ≤ d → Module.length A (ℳ' d) = Module.length A (ℳ (d + a)))
    (hP : ∀ d : ℤ, N ≤ d → P.eval (d : R) = ((Module.length A (ℳ d)).toNat : R))
    (hP' : ∀ d : ℤ, N' ≤ d → P'.eval (d : R) = ((Module.length A (ℳ' d)).toNat : R)) :
    P' = P.comp (Polynomial.X + Polynomial.C (a : R)) := by
  refine Polynomial.eq_of_forall_ge_intCast_eval_eq (N := max (max N₀ N') (N - a)) fun d hd ↦ ?_
  have hd0 : N₀ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_left hd)
  have hd' : N' ≤ d := le_trans (le_max_right _ _) (le_of_max_le_left hd)
  have hda : N ≤ d + a := by have := le_of_max_le_right hd; omega
  rw [hP' d hd', hshift d hd0, Polynomial.eval_comp_intCast, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, ← Int.cast_add, hP (d + a) hda]

end EventualLength

end TauCeti.GradedModule
