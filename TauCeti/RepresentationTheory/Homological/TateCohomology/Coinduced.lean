/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Induced
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree

/-!
# Tate cohomology of modules induced and coinduced from the trivial subgroup

For a finite group `G`, every Tate cohomology group of the representation `Coind_⊥^G X` coinduced
from the trivial subgroup vanishes (Milne, *Class Field Theory*, II 3.1): in positive degrees this
is Shapiro's lemma for cohomology, in degrees below `-1` Shapiro's lemma for homology (induction and
coinduction from the trivial subgroup agree for a finite group), and degrees `0` and `-1` are
checked by hand. The same holds for `Ind_⊥^G X`. For a finite subgroup `S` of an arbitrary
group `G`, the Tate cohomology of `S` with coefficients in the restrictions of `Coind_⊥^G X`,
`Ind_⊥^G X` and `k[G]` vanishes as well.

The statements follow `ClassFieldTheory/Cohomology/IndCoind/TrivialCohomology.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main statements

* `TauCeti.TateCohomology.isZero_coindBot`, `TauCeti.TateCohomology.isZero_indBot`: for a finite
  group `G`, `Ĥⁿ(G, Coind_⊥^G X) = 0` and `Ĥⁿ(G, Ind_⊥^G X) = 0` for all `n : ℤ` (Milne II 3.1).
* `TauCeti.TateCohomology.isZero_leftRegular`: for a finite group `G`, `Ĥⁿ(G, k[G]) = 0`.
* `TauCeti.TateCohomology.isZero_res_coindBot`, `TauCeti.TateCohomology.isZero_res_indBot`,
  `TauCeti.TateCohomology.isZero_res_leftRegular`: for a finite subgroup `S` of any group `G`,
  `Ĥⁿ(S, Coind_⊥^G X) = Ĥⁿ(S, Ind_⊥^G X) = Ĥⁿ(S, k[G]) = 0` for all `n : ℤ`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §3.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G]

section Fintype

variable [Fintype G] (X : Type u) [AddCommGroup X] [Module k X]

/-- Degree-zero Tate cohomology of a representation coinduced from the trivial subgroup vanishes
(Milne II 3.1, case `r = 0`). -/
theorem isZero_coindBot_zero : IsZero (tateCohomology (coindBot k G X) 0) := by
  classical
  have : Subsingleton (tateCohomology (coindBot k G X) 0) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x using H0_induction_on with
    | h y =>
      rw [H0π_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.mem_range]
      -- An invariant function is constant, with value `c := y 1`.
      have hconst : ∀ h : G, (y.1).1 h = (y.1).1 1 := fun h ↦ by
        have h1 := coindBot_ρ_apply_coe X h y.1 1
        rw [y.2 h, one_mul] at h1
        exact h1.symm
      -- The function supported at `1` with value `c` has norm the constant function `c`.
      refine ⟨(coindBotEquivPi k G X).symm fun h ↦ if h = 1 then (y.1).1 1 else 0, ?_⟩
      refine Subtype.ext (funext fun h ↦ ?_)
      have hval : ∀ g : G, (((coindBot k G X).ρ g)
          ((coindBotEquivPi k G X).symm fun h ↦ if h = 1 then (y.1).1 1 else 0)).1 h =
            if h * g = 1 then (y.1).1 1 else 0 := fun g ↦ by
        rw [coindBot_ρ_apply_coe, coindBotEquivPi_symm_apply_coe]
      rw [hconst h]
      simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
        hval]
      rw [Finset.sum_eq_single h⁻¹
        (fun g _ hg ↦ ite_eq_right fun H ↦ hg (mul_eq_one_iff_inv_eq.1 H).symm)
        (fun H ↦ (H (Finset.mem_univ _)).elim)]
      simp
  exact ModuleCat.isZero_of_subsingleton _

/-- Degree `-1` Tate cohomology of a representation coinduced from the trivial subgroup vanishes
(Milne II 3.1, case `r = -1`). -/
theorem isZero_coindBot_negOne : IsZero (tateCohomology (coindBot k G X) (-1)) := by
  classical
  have : Subsingleton (tateCohomology (coindBot k G X) (-1)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x using HNegOne_induction_on with
    | h y =>
      rw [HNegOneπ_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.subtype_apply]
      -- The point function at `1` with value `x`; `ρ g⁻¹` moves it to the point function at `g`.
      set δ : X → coindBot k G X :=
        fun x ↦ (coindBotEquivPi k G X).symm fun h ↦ if h = 1 then x else 0 with hδ
      clear_value δ
      have hδval : ∀ (h : G) (x : X), (δ x).1 h = if h = 1 then x else 0 := fun h x ↦ by
        rw [hδ, coindBotEquivPi_symm_apply_coe]
      have hδ_apply : ∀ (g h : G) (x : X), (((coindBot k G X).ρ g) (δ x)).1 h =
          if h * g = 1 then x else 0 := fun g h x ↦ by
        rw [coindBot_ρ_apply_coe, hδval]
      -- The norm of `y` vanishes, so the values of `y` sum to zero.
      have hsum : ∑ g : G, (y.1).1 g = 0 := by
        have hval : ∀ c : G, (((coindBot k G X).ρ c) y.1).1 1 = (y.1).1 c := fun c ↦ by
          rw [coindBot_ρ_apply_coe, one_mul]
        have h0 := congrArg (fun f : coindBot k G X ↦ f.1 1) y.2
        simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
          hval, ZeroMemClass.coe_zero, Pi.zero_apply] at h0
        exact h0
      -- `y` is the sum over `g` of `ρ g⁻¹ (δ (y g)) - δ (y g)`, each a generator of the
      -- augmentation submodule.
      have hdecomp : y.1 =
          ∑ g : G, (((coindBot k G X).ρ g⁻¹) (δ ((y.1).1 g)) - δ ((y.1).1 g)) := by
        refine Subtype.ext (funext fun h ↦ ?_)
        simp only [Submodule.coe_sum, Submodule.coe_sub, Finset.sum_apply, Pi.sub_apply,
          hδ_apply, hδval, Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single h (fun g _ hg ↦ ite_eq_right fun H ↦ hg (by
          simpa [eq_comm] using mul_inv_eq_one.1 H)) (fun H ↦ (H (Finset.mem_univ _)).elim)]
        by_cases hh : h = 1
        · subst hh
          simp [hsum]
        · simp [hh]
      rw [hdecomp]
      exact Submodule.sum_mem _ fun g _ ↦ Representation.Coinvariants.sub_mem_ker _ _
  exact ModuleCat.isZero_of_subsingleton _

/-- For a finite group, all Tate cohomology of a representation coinduced from the trivial
subgroup vanishes (Milne II 3.1). -/
theorem isZero_coindBot (n : ℤ) : IsZero (tateCohomology (coindBot k G X) n) :=
  match n with
  | .ofNat (n + 1) =>
    (groupCohomology.isZero_coindBot_succ X n).of_iso
      ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app (coindBot k G X))
  | 0 => isZero_coindBot_zero X
  | .negSucc 0 => isZero_coindBot_negOne X
  | .negSucc (n + 1) =>
    ((groupHomology.isZero_indBot_succ X n).of_iso
      ((groupHomology.functor k G (n + 1)).mapIso (indBotIsoCoindBot X).symm)).of_iso
      ((_root_.TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1) rfl).app
        (coindBot k G X))

/-- For a finite group, all Tate cohomology of a representation induced from the trivial
subgroup vanishes (Milne II 3.1). -/
theorem isZero_indBot (n : ℤ) : IsZero (tateCohomology (indBot k G X) n) :=
  (isZero_coindBot X n).of_iso ((tateCohomologyFunctor n).mapIso (indBotIsoCoindBot X))

omit X in
/-- For a finite group, all Tate cohomology of the left regular representation `k[G]` vanishes. -/
theorem isZero_leftRegular (n : ℤ) : IsZero (tateCohomology (leftRegular k G) n) :=
  (isZero_indBot k n).of_iso ((tateCohomologyFunctor n).mapIso indBotIsoLeftRegular.symm)

end Fintype

section Restriction

variable (S : Subgroup G) [Fintype S] (X : Type u) [AddCommGroup X] [Module k X] (n : ℤ)

/-- For a finite subgroup `S` of a group `G`, all Tate cohomology of the restriction to `S` of a
representation coinduced from the trivial subgroup of `G` vanishes. -/
theorem isZero_res_coindBot : IsZero (tateCohomology (res S.subtype (coindBot k G X)) n) :=
  (isZero_coindBot (G := S) (G ⧸ S → X) n).of_iso
    ((tateCohomologyFunctor n).mapIso (resCoindBotIso S X))

/-- For a finite subgroup `S` of a group `G`, all Tate cohomology of the restriction to `S` of a
representation induced from the trivial subgroup of `G` vanishes. -/
theorem isZero_res_indBot : IsZero (tateCohomology (res S.subtype (indBot k G X)) n) :=
  (isZero_indBot (G := S) (G ⧸ S →₀ X) n).of_iso
    ((tateCohomologyFunctor n).mapIso (resIndBotIso S X))

omit X in
/-- For a finite subgroup `S` of a group `G`, all Tate cohomology of the restriction to `S` of the
left regular representation `k[G]` vanishes. -/
theorem isZero_res_leftRegular : IsZero (tateCohomology (res S.subtype (leftRegular k G)) n) :=
  (isZero_res_indBot S k n).of_iso
    ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso indBotIsoLeftRegular.symm))

end Restriction

end TauCeti.TateCohomology
