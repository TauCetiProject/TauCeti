/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardForm
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# The mixed form of a non-orientable quadratic equation

Let `S = 1` be a standard non-orientable quadratic equation `x₀² ⋯ x²_{N-1} ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`
over `G`, of genus `N ≥ 1`. Its mixed form ([IFT], §7.5, (113) and (114)) is
`∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏_{i<n} [x₂ᵢ, x₂ᵢ₊₁] ∏_{k<r} x²_{2n+k} d = 1` on the same variables, where
`n = ⌊(N - 1)/2⌋` and `r = N - 2n`: the conjugated coefficients come first, followed by `n`
commutators and by one square when `N` is odd, two squares when `N` is even. In terms of surfaces,
`N` cross-caps are `n` handles and one or two cross-caps. [IFT] defines the basic sequence of
automorphisms of a non-orientable equation on its mixed form.

The mixed form is a change of coordinates of the standard form: an elementary `G`-automorphism of
`G[X]` carries its left side to the left side of `S`
(`Quadratic.Standard.exists_mem_elementaryAut_apply_mixedWord`). It is the composite of the rule
that `n` handles followed by `r ≥ 1` cross-caps are `2n + r` cross-caps
(`GX.exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq`) with the rule that moves the
product of the conjugated coefficients from the front of the squares to their back, where the
standard form has it (`GX.exists_mem_elementaryAut_apply_mul_prod_sq`).

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.mixedFst`, `mixedSnd`, `mixedSq`: the variables of the
  commutators and of the squares of the mixed form.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.mixedAtoms`, `mixedWord`: the atoms and the left side
  of the mixed form of a non-orientable standard quadratic equation.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.injective_sumElim_mixed`: the variables of the mixed form are
  pairwise distinct.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_mem_elementaryAut_apply_mixedWord`: an
  elementary automorphism carries the mixed form to the standard form.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 3, and §7.5, (112)–(114), p. 136.
* [GaXu] J. Gallier, D. Xu, *A guide to the classification theorem for compact surfaces*,
  Springer (2013), Chapter 6, Lemma 6.1.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom

variable {G X : Type*} [Group G]

namespace Quadratic

/-! ### The variables of the mixed form -/

section Vars

variable {N : ℕ} (x : Fin N → X)

/-- The first variables `x₂ᵢ` (`i < ⌊(N - 1)/2⌋`, indices from `0`) of the commutators of the mixed
form of `x₀² ⋯ x²_{N-1}`. -/
def mixedFst : Fin ((N - 1) / 2) → X :=
  fun i => x ⟨2 * i, by have := i.isLt; lia⟩

/-- The second variables `x₂ᵢ₊₁` of the commutators of the mixed form of `x₀² ⋯ x²_{N-1}`. -/
def mixedSnd : Fin ((N - 1) / 2) → X :=
  fun i => x ⟨2 * i + 1, by have := i.isLt; lia⟩

/-- The variables `x_{2n+k}`, `n = ⌊(N - 1)/2⌋`, of the squares of the mixed form of
`x₀² ⋯ x²_{N-1}`: one square for odd `N`, two for even `N ≥ 2` (none for `N = 0`). -/
def mixedSq : Fin (N - 2 * ((N - 1) / 2)) → X :=
  fun k => x ⟨2 * ((N - 1) / 2) + k, by have := k.isLt; lia⟩

@[simp]
theorem mixedFst_apply (i : Fin ((N - 1) / 2)) :
    mixedFst x i = x ⟨2 * i, by have := i.isLt; lia⟩ := (rfl)

@[simp]
theorem mixedSnd_apply (i : Fin ((N - 1) / 2)) :
    mixedSnd x i = x ⟨2 * i + 1, by have := i.isLt; lia⟩ := (rfl)

@[simp]
theorem mixedSq_apply (k : Fin (N - 2 * ((N - 1) / 2))) :
    mixedSq x k = x ⟨2 * ((N - 1) / 2) + k, by have := k.isLt; lia⟩ := (rfl)

variable {x} in
/-- The variables of the mixed form are pairwise distinct when those of the standard form are. -/
theorem injective_sumElim_mixed {ι : Type*} {z : ι → X} (inj : (Sum.elim x z).Injective) :
    (Sum.elim (Sum.elim (Sum.elim (mixedFst x) (mixedSnd x)) z) (mixedSq x)).Injective := by
  obtain ⟨hx, hz, hxz⟩ := Sum.elim_injective.1 inj
  rintro (((i | i) | j) | k) (((i' | i') | j') | k') h <;>
    simp [hx.eq_iff, hz.eq_iff, Fin.ext_iff, hxz, fun a b => (hxz a b).symm] at h ⊢ <;> lia

end Vars

namespace Standard

/-! ### The mixed form -/

/-- The atoms of the mixed form of [IFT], §7.5, (113) and (114), of a non-orientable standard
quadratic equation `x₀² ⋯ x²_{N-1} ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`: the conjugates `zⱼ⁻¹ cⱼ zⱼ`, then the
commutators `[x₂ᵢ, x₂ᵢ₊₁]` for `i < ⌊(N - 1)/2⌋`, then the squares of the one or two remaining
variables. -/
def mixedAtoms : (S : Standard G X) → ¬S.IsOrientable → List (GX G X)
  | .orientable _ hn _ _ inj, h => (h (isOrientable_orientable hn inj)).elim
  | .orientableCoeff _ _ hnm _ _ _ inj _ hc _ hd, h =>
    (h (isOrientable_orientableCoeff hnm inj hc hd)).elim
  | .nonorientable _ _ x _, _ =>
    List.ofFn (fun i => ⁅(inr (FreeGroup.of (mixedFst x i)) : GX G X)⁻¹,
        (inr (FreeGroup.of (mixedSnd x i)))⁻¹⁆) ++
      List.ofFn fun k => (inr (FreeGroup.of (mixedSq x k)) : GX G X) ^ 2
  | .nonorientableCoeff _ _ _ x z _ c _ _ _, _ =>
    List.ofFn (fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
        inr (FreeGroup.of (z j))) ++
      (List.ofFn (fun i => ⁅(inr (FreeGroup.of (mixedFst x i)) : GX G X)⁻¹,
          (inr (FreeGroup.of (mixedSnd x i)))⁻¹⁆) ++
        List.ofFn fun k => (inr (FreeGroup.of (mixedSq x k)) : GX G X) ^ 2)

/-- The left side `r₁ ⋯ r_k d` of the mixed form `r₁ ⋯ r_k d = 1` ([IFT], §7.5, (113), (114)) of a
non-orientable standard quadratic equation, where `r₁, …, r_k` are its mixed atoms and `d` is its
constant. -/
def mixedWord (S : Standard G X) (ho : ¬S.IsOrientable) : GX G X :=
  (S.mixedAtoms ho).prod * inl S.constant

theorem mixedWord_def (S : Standard G X) (ho : ¬S.IsOrientable) :
    S.mixedWord ho = (S.mixedAtoms ho).prod * inl S.constant := (rfl)

variable {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

@[simp]
theorem mixedAtoms_nonorientable (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).mixedAtoms (not_isOrientable_nonorientable hn inj) =
      List.ofFn (fun i => ⁅(inr (FreeGroup.of (mixedFst x i)) : GX G X)⁻¹,
          (inr (FreeGroup.of (mixedSnd x i)))⁻¹⁆) ++
        List.ofFn fun k => (inr (FreeGroup.of (mixedSq x k)) : GX G X) ^ 2 := (rfl)

@[simp]
theorem mixedAtoms_nonorientableCoeff (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).mixedAtoms
        (not_isOrientable_nonorientableCoeff hn inj hc hd) =
      List.ofFn (fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
          inr (FreeGroup.of (z j))) ++
        (List.ofFn (fun i => ⁅(inr (FreeGroup.of (mixedFst x i)) : GX G X)⁻¹,
            (inr (FreeGroup.of (mixedSnd x i)))⁻¹⁆) ++
          List.ofFn fun k => (inr (FreeGroup.of (mixedSq x k)) : GX G X) ^ 2) := (rfl)

/-- **The mixed form is a change of coordinates of the standard form** ([IFT], §7.5, where a
non-orientable equation is considered in the form (113) or (114)). For a non-orientable standard
quadratic equation `S = 1`, an elementary `G`-automorphism of `G[X]` carries the left side of its
mixed form to the left side of `S`. -/
theorem exists_mem_elementaryAut_apply_mixedWord (S : Standard G X) (ho : ¬S.IsOrientable) :
    ∃ f ∈ GX.elementaryAut G X, f (S.mixedWord ho) = S.toWord := by
  classical
  cases S with
  | orientable n hn x y inj => exact absurd (isOrientable_orientable hn inj) ho
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    exact absurd (isOrientable_orientableCoeff hnm inj hc hd) ho
  | nonorientable N hN x inj =>
    obtain ⟨f, hf, hfw, -⟩ := GX.exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq
      (G := G) (n := (N - 1) / 2) (r := N - 2 * ((N - 1) / 2)) (by lia) (by lia) inj
    exact ⟨f, hf, by simpa [mixedWord_def, toWord_def] using hfw⟩
  | nonorientableCoeff N m hN x z inj c hc d hd =>
    -- the handles and cross-caps become squares, then the product `P` of the conjugated
    -- coefficients moves behind the squares
    set P : GX G X := (List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
      inr (FreeGroup.of (z j))).prod with hP
    have hPx (i : Fin N) : P ∈ GX.avoiding (x i) := by
      refine list_prod_mem (List.forall_mem_ofFn_iff.2 fun j => ?_)
      have := GX.inr_of_mem_avoiding (G := G) fun h => (Sum.elim_injective.1 inj).2.2 i j h.symm
      exact mul_mem (mul_mem (inv_mem this) (GX.inl_mem_avoiding _ _)) this
    obtain ⟨f, hf, hfw, hfa⟩ := GX.exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq
      (G := G) (n := (N - 1) / 2) (r := N - 2 * ((N - 1) / 2)) (by lia) (by lia)
      (Sum.elim_injective.1 inj).1
    obtain ⟨κ, hκ, hκw, -⟩ := GX.exists_mem_elementaryAut_apply_mul_prod_sq hPx
    refine ⟨κ * f, mul_mem hκ hf, ?_⟩
    simp only [mixedWord_def, mixedAtoms_nonorientableCoeff, toWord_def, atoms_nonorientableCoeff,
      constant_nonorientableCoeff, List.prod_append, ← hP, mixedFst_apply, mixedSnd_apply,
      mixedSq_apply]
    rw [MulAut.mul_apply, map_mul f, map_mul f, hfa P hPx, hfw, map_mul, hκw,
      GX.apply_inl_of_mem_elementaryAut hf, GX.apply_inl_of_mem_elementaryAut hκ]

end Standard

end Quadratic

end TauCeti.GroupAlgGeom
