/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.Module.GradedModule.Trivial
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Duals of internally graded modules

This file gives the linear dual of an internally graded module its canonical grading. A functional
has degree `p` when it is supported on the original degree `-p` piece, and restriction identifies
that degree with the linear dual of `G.piece (-p)`. Consequently, evaluation can be nonzero only on
degrees summing to zero.

The homogeneous pieces exhaust the dual as soon as only finitely many dual pieces are nonzero,
and no projectivity is needed for that. This holds whenever the original grading has finitely many
nonzero pieces, through `InternalGrading.finite_dualPiece_ne_bot`; finite generation of the module
is one source of this stronger hypothesis, through `InternalGrading.finite_piece_ne_bot`.
Tensor-duality comparisons use the finite-projectivity hypotheses needed to identify duals of
tensor products.

The construction follows the graded-dual convention used for DG and `A∞` objects in B. Keller,
*Introduction to A-infinity algebras and modules*, Sections 3 and 7.

## Main definitions

* `InternalGrading.homPiece` and `InternalGrading.dualPiece`: the degree-`p` submodule of linear
  maps `M →ₗ[R] V`, and its specialization to the linear dual `Module.Dual R M`.
* `InternalGrading.homPieceEquiv` and `InternalGrading.dualPieceEquiv`: the identification of that
  submodule with linear maps out of the original degree-`-p` piece, by restriction.
* `InternalGrading.dual`: the internal grading of the linear dual when only finitely many dual
  pieces are nonzero.

## Main results

* `InternalGrading.mem_homPiece_iff`, `InternalGrading.mem_dualPiece_iff`, and
  `InternalGrading.mem_dualPiece_iff_isHomogeneous_trivialGrading`: a degree-`p` map vanishes
  on every original degree other than `-p`, equivalently is homogeneous of degree `p` into
  `trivialGrading R R` when `V = R`.
* `InternalGrading.homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero` and
  `InternalGrading.dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero`: evaluation vanishes unless
  the degrees of the map and vector sum to zero.
* `InternalGrading.homPiece_apply_eq_apply_decompose` and
  `InternalGrading.dualPiece_apply_eq_apply_decompose`: a degree-`p` map sees only the
  degree-`-p` homogeneous component of its argument.
* `InternalGrading.finite_homPiece_ne_bot` and `InternalGrading.finite_dualPiece_ne_bot`: the
  graded hom space has finitely many nonzero pieces as soon as the original grading does.
* `InternalGrading.coeLinearMap_homPiece_injective`, `InternalGrading.iSupIndep_homPiece`, and
  `InternalGrading.iSupIndep_dualPiece`: the degreewise pieces are independent, without a
  finiteness hypothesis.
* `InternalGrading.mem_range_coeLinearMap_homPiece_iff`: a linear map lies in the direct sum of
  the `homPiece` submodules iff it vanishes on all homogeneous pieces outside a finite set.
* `InternalGrading.dual_decompose_apply`: the degree-`p` component of a functional evaluates an
  arbitrary vector through its original degree-`-p` component.
* `InternalGrading.dual_decompose_apply_of_mem_piece`: on the degree-`q` piece, a functional agrees
  with its own degree-`-q` homogeneous component.

## Implementation notes

The construction lives over a commutative semiring. Although independence and spanning do not in
general assemble an internal direct sum without additive inverses, injectivity of the canonical map
for these graded hom pieces follows directly by evaluating each summand on its matching primal
piece.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v w

namespace InternalGrading

variable {R : Type u} {M : Type v}

section HomPiece

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`p` part of the graded `R`-linear maps `M →ₗ[R] V` consists of the linear maps
vanishing on every homogeneous piece except degree `-p`. -/
def homPiece (G : InternalGrading R M ℤ) (V : Type w) [AddCommMonoid V] [Module R V] (p : ℤ) :
    Submodule R (M →ₗ[R] V) where
  carrier := {φ | ∀ q (x : M), x ∈ G.piece q → q ≠ -p → φ x = 0}
  zero_mem' _ _ _ _ := rfl
  add_mem' h₁ h₂ q x hx hq := by simp [h₁ q x hx hq, h₂ q x hx hq]
  smul_mem' c φ hφ q x hx hq := by simp [hφ q x hx hq]

/-- A linear map belongs to degree `p` of `homPiece` exactly when it vanishes on every original
degree other than `-p`. -/
@[simp]
theorem mem_homPiece_iff (G : InternalGrading R M ℤ) (V : Type w) [AddCommMonoid V] [Module R V]
    (p : ℤ) (φ : M →ₗ[R] V) :
    φ ∈ G.homPiece V p ↔ ∀ q (x : M), x ∈ G.piece q → q ≠ -p → φ x = 0 :=
  Iff.rfl

/-- A linear map in `homPiece` degree `p` vanishes on an original homogeneous vector of degree `q`
unless `p + q = 0`. -/
@[grind →]
theorem homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero (G : InternalGrading R M ℤ)
    (V : Type w) [AddCommMonoid V] [Module R V] {p q : ℤ} {φ : M →ₗ[R] V} {x : M}
    (hφ : φ ∈ G.homPiece V p) (hx : x ∈ G.piece q) (hpq : p + q ≠ 0) : φ x = 0 :=
  (mem_homPiece_iff G V p φ).mp hφ q x hx (by omega)

/-- The homogeneous component of degree `p`, as a linear map to that piece. -/
private noncomputable def projection (G : InternalGrading R M ℤ) (p : ℤ) : M →ₗ[R] G.piece p :=
  DirectSum.component R ℤ (fun q ↦ G.piece q) p ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

@[simp]
private theorem projection_apply (G : InternalGrading R M ℤ) (p : ℤ) (x : M) :
    projection G p x = DirectSum.decompose G.piece x p :=
  rfl

/-- A linear map of `homPiece` degree `p` sees only the degree-`-p` homogeneous component of its
argument: it annihilates every other component of the decomposition. -/
theorem homPiece_apply_eq_apply_decompose (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] {p : ℤ} {φ : M →ₗ[R] V} (hφ : φ ∈ G.homPiece V p) (x : M) :
    φ x = φ (DirectSum.decompose G.piece x (-p) : M) :=
  G.map_eq_map_decompose φ.toAddMonoidHom
    (fun q y hy hq ↦ (mem_homPiece_iff G V p φ).mp hφ q y hy hq) x

/-- Restricting a linear map of `homPiece` degree `p` to the degree-`-p` piece identifies
`G.homPiece V p` with `G.piece (-p) →ₗ[R] V`: the restriction determines the map, and every linear
map on the piece extends along the homogeneous component of degree `-p`. -/
noncomputable def homPieceEquiv (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (p : ℤ) :
    G.homPiece V p ≃ₗ[R] (G.piece (-p) →ₗ[R] V) where
  toFun φ := (φ : M →ₗ[R] V) ∘ₗ (G.piece (-p)).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    ⟨ψ ∘ₗ projection G (-p), by
      rw [mem_homPiece_iff]
      intro q x hx hq
      rw [LinearMap.comp_apply, projection_apply,
        Submodule.coe_eq_zero.mp (DirectSum.decompose_of_mem_ne G.piece hx hq), map_zero]⟩
  left_inv φ :=
    Subtype.ext (LinearMap.ext fun x ↦ (homPiece_apply_eq_apply_decompose G V φ.property x).symm)
  right_inv ψ := LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, projection_apply,
      Subtype.ext (DirectSum.decompose_of_mem_same G.piece y.property)]

/-- A linear map of `homPiece` degree `p` restricts to the degree-`-p` piece by evaluation. -/
@[simp]
theorem homPieceEquiv_apply (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (p : ℤ) (φ : G.homPiece V p) (y : G.piece (-p)) :
    G.homPieceEquiv V p φ y = (φ : M →ₗ[R] V) y :=
  (rfl)

/-- The linear map of `homPiece` degree `p` extending `ψ` evaluates an arbitrary vector on its
degree-`-p` homogeneous component. -/
theorem homPieceEquiv_symm_apply (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (p : ℤ) (ψ : G.piece (-p) →ₗ[R] V) (x : M) :
    ((G.homPieceEquiv V p).symm ψ : M →ₗ[R] V) x =
      ψ (DirectSum.decompose G.piece x (-p)) :=
  (rfl)

/-- The linear map of `homPiece` degree `p` extending `ψ` restricts to `ψ` on the degree-`-p`
piece. -/
@[simp]
theorem homPieceEquiv_symm_apply_coe (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (p : ℤ) (ψ : G.piece (-p) →ₗ[R] V) (y : G.piece (-p)) :
    ((G.homPieceEquiv V p).symm ψ : M →ₗ[R] V) (y : M) = ψ y :=
  DFunLike.congr_fun ((G.homPieceEquiv V p).apply_symm_apply ψ) y

/-- `homPiece` degree `p` is zero as soon as the original degree `-p` is. -/
theorem homPiece_eq_bot_of_piece_eq_bot (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] {p : ℤ} (h : G.piece (-p) = ⊥) : G.homPiece V p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun φ hφ ↦ LinearMap.ext fun x ↦ ?_
  have hx : (DirectSum.decompose G.piece x (-p) : M) = 0 :=
    (Submodule.eq_bot_iff _).mp h _ (DirectSum.decompose G.piece x (-p)).property
  rw [homPiece_apply_eq_apply_decompose G V hφ x, hx, map_zero, LinearMap.zero_apply]

/-- `homPiece` has only finitely many nonzero degrees as soon as the original grading does. -/
theorem finite_homPiece_ne_bot (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (hG : {p | G.piece p ≠ ⊥}.Finite) :
    {p | G.homPiece V p ≠ ⊥}.Finite :=
  (hG.image fun q ↦ -q).subset fun p hp ↦
    ⟨-p, fun h ↦ hp (G.homPiece_eq_bot_of_piece_eq_bot V h), neg_neg p⟩

/-- A linear map `M →ₗ[R] V` lies in the range of `DirectSum.coeLinearMap (G.homPiece V)` iff it
vanishes on all homogeneous pieces outside a finite set of degrees. -/
theorem mem_range_coeLinearMap_homPiece_iff (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (φ : M →ₗ[R] V) :
    φ ∈ LinearMap.range (DirectSum.coeLinearMap (G.homPiece V)) ↔
      ∃ s : Finset ℤ, ∀ q (x : M), x ∈ G.piece q → q ∉ s → φ x = 0 := by
  classical
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z.support.image Neg.neg, fun q x hx hq ↦ ?_⟩
    rw [← z.sum_support_of, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have hqp : q ≠ -p := fun h ↦ hq (Finset.mem_image.mpr ⟨p, hp, h.symm⟩)
    simpa only [DirectSum.coeLinearMap_of] using
      (mem_homPiece_iff G V p _).mp (z p).property q x hx hqp
  · rintro ⟨s, hs⟩
    refine ⟨∑ p ∈ s.image Neg.neg, DirectSum.lof R ℤ (fun q ↦ G.homPiece V q) p
        ((G.homPieceEquiv V p).symm (φ ∘ₗ (G.piece (-p)).subtype)), ?_⟩
    apply G.linearMap_ext
    intro q x hx
    simp only [map_sum, DirectSum.coeLinearMap_lof, LinearMap.sum_apply]
    by_cases hqs : q ∈ s
    · rw [Finset.sum_eq_single (-q)]
      · simp only [homPieceEquiv_symm_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        have hdec : (DirectSum.decompose G.piece x (- -q) : M) = x := by
          rw [neg_neg]
          exact DirectSum.decompose_of_mem_same G.piece hx
        rw [hdec]
      · intro p _ hp
        exact G.homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero V
          ((G.homPieceEquiv V p).symm _).property hx (by omega)
      · intro hnq
        exact (hnq (Finset.mem_image.mpr ⟨q, hqs, rfl⟩)).elim
    · rw [hs q x hx hqs]
      exact Finset.sum_eq_zero fun p hp ↦ by
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
        refine G.homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero V
          ((G.homPieceEquiv V (-r)).symm _).property hx ?_
        intro hqr
        have : q = r := by omega
        exact hqs (this ▸ hr)

private theorem iSup_homPiece_eq_top (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] (hD : {p | G.homPiece V p ≠ ⊥}.Finite) :
    ⨆ p, G.homPiece V p = ⊤ := by
  classical
  rw [← DirectSum.range_coeLinearMap]
  refine top_unique fun φ _ ↦ (G.mem_range_coeLinearMap_homPiece_iff V φ).mpr ?_
  refine ⟨hD.toFinset.image Neg.neg, fun q x hx hq ↦ ?_⟩
  have hbot : G.homPiece V (-q) = ⊥ := by
    by_contra hne
    exact hq (Finset.mem_image.mpr ⟨-q, hD.mem_toFinset.mpr hne, neg_neg q⟩)
  let φq : G.homPiece V (-q) :=
    (G.homPieceEquiv V (-q)).symm (φ ∘ₗ (G.piece (- -q)).subtype)
  have hzero : (φq : M →ₗ[R] V) = 0 := by
    simpa only [hbot, Submodule.mem_bot] using φq.property
  have heval := congrArg (fun f : M →ₗ[R] V ↦ f x) hzero
  have hdec : (DirectSum.decompose G.piece x (- -q) : M) = x := by
    rw [neg_neg]
    exact DirectSum.decompose_of_mem_same G.piece hx
  simpa only [φq, homPieceEquiv_symm_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    hdec, LinearMap.zero_apply] using heval

/-- The direct sum of `homPiece` submodules embeds in `M →ₗ[R] V` without a finiteness
hypothesis. -/
theorem coeLinearMap_homPiece_injective (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] :
    Function.Injective (DirectSum.coeLinearMap (G.homPiece V)) := by
  intro a b hab
  ext p x
  rw [homPiece_apply_eq_apply_decompose G V (a p).property,
    homPiece_apply_eq_apply_decompose G V (b p).property]
  have hcomponent : ∀ c : ⨁ p, G.homPiece V p,
      DirectSum.coeLinearMap (G.homPiece V) c
        (DirectSum.decompose G.piece x (-p) : M) =
        (c p : M →ₗ[R] V) (DirectSum.decompose G.piece x (-p) : M) := by
    intro c
    induction c using DirectSum.induction_on with
    | zero => simp
    | of q φ =>
      by_cases hqp : q = p
      · subst q
        simp
      · rw [DirectSum.coeLinearMap_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hqp)]
        simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
        exact homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G V φ.property
          (DirectSum.decompose G.piece x (-p)).property (by omega)
    | add c d hc hd => simp [hc, hd]
  rw [← hcomponent a, hab, hcomponent b]

/-- The pieces of `homPiece` are independent, even when the original grading has infinitely many
nonzero pieces. -/
theorem iSupIndep_homPiece (G : InternalGrading R M ℤ) (V : Type w)
    [AddCommMonoid V] [Module R V] :
    iSupIndep (G.homPiece V) :=
  iSupIndep_of_dfinsupp_lsum_injective _ (coeLinearMap_homPiece_injective G V)

end HomPiece

section DualPiece

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`p` part of the graded dual consists of the functionals vanishing on every
homogeneous piece except degree `-p`. -/
def dualPiece (G : InternalGrading R M ℤ) (p : ℤ) : Submodule R (Module.Dual R M) :=
  G.homPiece R p

/-- A functional belongs to degree `p` of the graded dual exactly when it vanishes on every
original degree other than `-p`. -/
@[simp]
theorem mem_dualPiece_iff (G : InternalGrading R M ℤ) (p : ℤ) (φ : Module.Dual R M) :
    φ ∈ G.dualPiece p ↔ ∀ q (x : M), x ∈ G.piece q → q ≠ -p → φ x = 0 :=
  Iff.rfl

/-- Membership in `InternalGrading.dualPiece q` is equivalent to homogeneity of degree `q` into the
trivial grading of the base ring. -/
theorem mem_dualPiece_iff_isHomogeneous_trivialGrading (G : InternalGrading R M ℤ) (q : ℤ)
    (φ : Module.Dual R M) :
    φ ∈ G.dualPiece q ↔ LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) q := by
  rw [G.mem_dualPiece_iff, LinearMap.isHomogeneous_def]
  refine ⟨fun hφ p x hx => (mem_trivialGrading_iff R R).mpr ?_, fun hφ p x hx hp =>
    ((mem_trivialGrading_iff R R).mp (hφ p x hx)).resolve_left (by omega)⟩
  exact if hp : p + q = 0 then Or.inl hp else Or.inr (hφ p x hx (by omega))

/-- A functional in dual degree `p` vanishes on an original homogeneous vector of degree `q`
unless `p + q = 0`. -/
@[grind →]
theorem dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero (G : InternalGrading R M ℤ) {p q : ℤ}
    {φ : Module.Dual R M} {x : M} (hφ : φ ∈ G.dualPiece p) (hx : x ∈ G.piece q)
    (hpq : p + q ≠ 0) : φ x = 0 :=
  G.homPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero R hφ hx hpq

/-- A functional of dual degree `p` sees only the degree-`-p` homogeneous component of its
argument: it annihilates every other component of the decomposition. -/
theorem dualPiece_apply_eq_apply_decompose (G : InternalGrading R M ℤ) {p : ℤ}
    {φ : Module.Dual R M} (hφ : φ ∈ G.dualPiece p) (x : M) :
    φ x = φ (DirectSum.decompose G.piece x (-p) : M) :=
  G.homPiece_apply_eq_apply_decompose R hφ x

/-- Restricting a functional of dual degree `p` to the degree-`-p` piece identifies `G.dualPiece p`
with the linear dual of that piece: the restriction determines the functional, and every functional
on the piece extends along the homogeneous component of degree `-p`. -/
noncomputable def dualPieceEquiv (G : InternalGrading R M ℤ) (p : ℤ) :
    G.dualPiece p ≃ₗ[R] Module.Dual R (G.piece (-p)) :=
  G.homPieceEquiv R p

/-- A functional of dual degree `p` restricts to the degree-`-p` piece by evaluation. -/
@[simp]
theorem dualPieceEquiv_apply (G : InternalGrading R M ℤ) (p : ℤ) (φ : G.dualPiece p)
    (y : G.piece (-p)) : G.dualPieceEquiv p φ y = (φ : Module.Dual R M) y :=
  (rfl)

/-- The functional of dual degree `p` extending `ψ` evaluates an arbitrary vector on its degree-`-p`
homogeneous component. -/
theorem dualPieceEquiv_symm_apply (G : InternalGrading R M ℤ) (p : ℤ)
    (ψ : Module.Dual R (G.piece (-p))) (x : M) :
    ((G.dualPieceEquiv p).symm ψ : Module.Dual R M) x =
      ψ (DirectSum.decompose G.piece x (-p)) :=
  (rfl)

/-- The functional of dual degree `p` extending `ψ` restricts to `ψ` on the degree-`-p` piece. -/
@[simp]
theorem dualPieceEquiv_symm_apply_coe (G : InternalGrading R M ℤ) (p : ℤ)
    (ψ : Module.Dual R (G.piece (-p))) (y : G.piece (-p)) :
    ((G.dualPieceEquiv p).symm ψ : Module.Dual R M) (y : M) = ψ y :=
  G.homPieceEquiv_symm_apply_coe R p ψ y

/-- Dual degree `p` is zero as soon as the original degree `-p` is: a functional of dual degree `p`
sees only that piece of its argument. -/
theorem dualPiece_eq_bot_of_piece_eq_bot (G : InternalGrading R M ℤ) {p : ℤ}
    (h : G.piece (-p) = ⊥) : G.dualPiece p = ⊥ :=
  G.homPiece_eq_bot_of_piece_eq_bot R h

/-- The dual grading has only finitely many nonzero pieces as soon as the original one does, the
degree-`p` piece of the dual being carried by the original degree `-p`. -/
theorem finite_dualPiece_ne_bot (G : InternalGrading R M ℤ) (hG : {p | G.piece p ≠ ⊥}.Finite) :
    {p | G.dualPiece p ≠ ⊥}.Finite :=
  G.finite_homPiece_ne_bot R hG

/-- The pieces of the graded dual are independent, even when the original grading has infinitely
many nonzero pieces. -/
theorem iSupIndep_dualPiece (G : InternalGrading R M ℤ) :
    iSupIndep G.dualPiece :=
  G.iSupIndep_homPiece R

/-- The internal grading on the linear dual when only finitely many dual pieces are nonzero.

The degree is reversed: a functional of degree `p` is supported on the original degree `-p`
piece. -/
noncomputable def dual (G : InternalGrading R M ℤ) (hD : {p | G.dualPiece p ≠ ⊥}.Finite) :
    InternalGrading R (Module.Dual R M) ℤ where
  piece := G.dualPiece
  isInternal := by
    -- Mathlib defines `IsInternal` using the additive canonical map; `coeLinearMap` below has the
    -- same underlying function and lets the module-level range API prove surjectivity.
    constructor
    · exact coeLinearMap_homPiece_injective G R
    · have hsurj : Function.Surjective (DirectSum.coeLinearMap G.dualPiece) := by
        rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
        exact G.iSup_homPiece_eq_top R hD
      exact hsurj

/-- The degree-`p` piece of the dual grading is `dualPiece G p`. -/
@[simp]
theorem dual_piece (G : InternalGrading R M ℤ) (hD : {p | G.dualPiece p ≠ ⊥}.Finite) (p : ℤ) :
    (G.dual hD).piece p = G.dualPiece p :=
  (rfl)

/-- On the degree-`q` piece a functional agrees with its own degree-`-q` homogeneous component for
the dual grading: all the other components vanish there. -/
theorem dual_decompose_apply_of_mem_piece (G : InternalGrading R M ℤ)
    (hD : {p | G.dualPiece p ≠ ⊥}.Finite) (φ : Module.Dual R M) {q : ℤ} {x : M}
    (hx : x ∈ G.piece q) :
    ((DirectSum.decompose (G.dual hD).piece φ (-q) : (G.dual hD).piece (-q)) :
      Module.Dual R M) x = φ x := by
  symm
  exact (G.dual hD).map_eq_map_decompose (LinearMap.applyₗ x).toAddMonoidHom
    (fun p ψ hψ hp ↦ dualPiece_apply_eq_zero_of_mem_piece_of_add_ne_zero G
      (by simpa only [dual_piece] using hψ) hx (by omega)) φ

/-- The degree-`p` component of a functional evaluates an arbitrary vector by first taking its
original degree-`-p` homogeneous component. -/
@[simp]
theorem dual_decompose_apply (G : InternalGrading R M ℤ)
    (hD : {p | G.dualPiece p ≠ ⊥}.Finite) (φ : Module.Dual R M) (p : ℤ) (x : M) :
    ((DirectSum.decompose (G.dual hD).piece φ p : (G.dual hD).piece p) :
      Module.Dual R M) x = φ (DirectSum.decompose G.piece x (-p) : M) := by
  rw [dualPiece_apply_eq_apply_decompose G
    (by exact (DirectSum.decompose (G.dual hD).piece φ p).property)]
  have h := dual_decompose_apply_of_mem_piece G hD φ
    (DirectSum.decompose G.piece x (-p)).property
  have hp : - -p = p := by omega
  rw [hp] at h
  exact h

end DualPiece

end InternalGrading

end TauCeti
