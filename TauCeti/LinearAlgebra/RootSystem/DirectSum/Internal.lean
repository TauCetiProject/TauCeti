/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Basic
import Mathlib.Algebra.Ring.Regular
import TauCeti.LinearAlgebra.RootSystem.EquivComp
import TauCeti.LinearAlgebra.RootSystem.HomInvariance.Basic

/-!
# Finite internal direct sums of root pairings

Given an ambient module `M` decomposed as a finite internal direct sum of submodules
`E : κ → Submodule R M` (witnessed by `[Finite κ]`, `iSupIndep E`, and `⨆ c, E c = ⊤`, requiring
neither `Fintype κ` nor `DecidableEq κ`), and a root pairing `P c : RootPairing (ι c) R (E c) (N c)`
on each summand, `RootPairing.internalDirectSum hEi hEt P` assembles them into a root pairing on
`M` and its dual `Module.Dual R M` with the literal evaluation pairing `Module.Dual.eval R M`.

The key observation is that `Module.IsReflexive.pi` makes the product `∀ c, E c` reflexive over
any commutative ring `R`, so `Module.IsReflexive.equiv (internalDirectSumEquiv hEi hEt)` makes `M`
reflexive and `Module.Dual.eval R M` a perfect pairing with no field, freeness, or finiteness
hypotheses on `M` or the summands. Each root `⟨c, i⟩` is the inclusion `((P c).root i : M)`, and
each coroot `⟨c, i⟩` is `(P c).coroot' i` composed with `TauCeti.internalProjection hEi hEt c`.

When `[Fintype κ]` and `[DecidableEq κ]` are available, `RootPairing.piEquivInternalDirectSum`
identifies `RootPairing.pi P` with `RootPairing.internalDirectSum hEi hEt P`. Transporting the
external direct-sum theory along this equivalence yields root-system, subring-valuedness,
reducedness, and functoriality results for `internalDirectSum`, requiring only `[Finite κ]`
wherever no `Finset.univ` appears in the statement.

## Main definitions

* `RootPairing.internalDirectSum`: the finite internal direct sum of root pairings on submodules
  `E c ≤ M`, taking values in `M` and `Module.Dual R M` with `Module.Dual.eval R M`.
* `RootPairing.piEquivInternalDirectSum`: the canonical equivalence between `RootPairing.pi P` and
  `RootPairing.internalDirectSum hEi hEt P`.
* `RootPairing.Equiv.internalDirectSumCongr`: functoriality of `RootPairing.internalDirectSum`
  under reindexing and summand equivalences.

## Main results

* `RootPairing.toPerfPair_symm_internalDirectSum_coroot_comp_same`,
  `RootPairing.internalDirectSum_coroot_comp_ne`, `RootPairing.range_internalDirectSum_root`,
  `RootPairing.range_internalDirectSum_coroot`: coroot restriction formulas and characterization of
  roots and coroots of an internal direct sum inside `M` and `Module.Dual R M`.
* `RootPairing.piEquivInternalDirectSum_coweightEquiv_symm_apply`: formula assembling a tuple of
  summand coweights into an ambient functional.
* `RootPairing.isRootSystem_internalDirectSum_iff`,
  `RootPairing.isValuedIn_internalDirectSum_iff`,
  `RootPairing.isReduced_of_internalDirectSum`,
  `RootPairing.isReduced_internalDirectSum_iff_of_isRegular`,
  `RootPairing.isReduced_internalDirectSum_iff`: characterization and preservation of structural
  properties for internal direct sums.
* `RootPairing.Equiv.internalDirectSumCongr_id`, `RootPairing.Equiv.internalDirectSumCongr_comp`,
  `RootPairing.Equiv.toPerfPair_symm_internalDirectSumCongr_coweightMap`: identity, composition,
  and coweight coordinate formulas for `RootPairing.Equiv.internalDirectSumCongr`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23.
-/

public section

open Function Set Submodule TauCeti

namespace RootPairing

section Internal

variable {κ R M : Type*} [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (E c) (N c))

include hEi hEt in
private theorem internalDirectSum_root_injective :
    Function.Injective fun s : Σ c, ι c ↦ ((P s.1).root s.2 : M) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  by_cases hcd : c = d
  · subst hcd
    exact congrArg (Sigma.mk c) ((P c).root.injective (Subtype.ext h))
  · have h0 : (P c).root i = 0 := by
      have := congrArg (internalProjection hEi hEt c) h
      simpa [internalProjection_apply_of_ne hEi hEt (Ne.symm hcd)] using this
    exact ((P c).ne_zero i h0).elim

private theorem internalDirectSum_coroot_injective :
    Function.Injective fun s : Σ c, ι c ↦
      ((P s.1).coroot' s.2).comp (internalProjection hEi hEt s.1) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  by_cases hcd : c = d
  · subst hcd
    refine congrArg (Sigma.mk c) ((P c).coroot.injective ?_)
    refine (P c).flip.toPerfPair.injective (LinearMap.ext fun x ↦ ?_)
    have hx := LinearMap.congr_fun h (x : M)
    simpa [coroot'] using hx
  · have h0 : (2 : R) = 0 := by
      have hx := LinearMap.congr_fun h ((P c).root i : M)
      simpa [internalProjection_apply_of_ne hEi hEt hcd, root_coroot'_eq_pairing] using hx
    exact (two_ne_zero h0).elim

/-- **The finite internal direct sum of root pairings on submodules `E c ≤ M`.**

The weight space is `M`, the coweight space is `Module.Dual R M`, and the pairing is the literal
evaluation map `Module.Dual.eval R M`. Each root `⟨c, i⟩` is the inclusion `((P c).root i : M)` and
each coroot `⟨c, i⟩` is `(P c).coroot' i ∘ₗ TauCeti.internalProjection hEi hEt c`. -/
noncomputable def internalDirectSum [Finite κ] :
    RootPairing (Σ c, ι c) R M (Module.Dual R M) where
  toLinearMap := Module.Dual.eval R M
  isPerfPair_toLinearMap := by
    let _ : Fintype κ := Fintype.ofFinite κ
    have : ∀ c, Module.IsReflexive R (E c) := fun c ↦
      Module.IsReflexive.of_isPerfPair (P c).toLinearMap
    have : Module.IsReflexive R (∀ c, E c) := Module.IsReflexive.pi
    have : Module.IsReflexive R M :=
      Module.equiv (internalDirectSumEquiv hEi hEt)
    infer_instance
  root := ⟨fun s ↦ ((P s.1).root s.2 : M), internalDirectSum_root_injective hEi hEt P⟩
  coroot :=
    ⟨fun s ↦ ((P s.1).coroot' s.2).comp (internalProjection hEi hEt s.1),
      internalDirectSum_coroot_injective hEi hEt P⟩
  root_coroot_two s := by
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, LinearMap.comp_apply,
      internalProjection_apply, root_coroot'_eq_pairing, pairing_same]
  reflectionPerm :=
    let _ : Fintype κ := Fintype.ofFinite κ
    let _ : DecidableEq κ := Classical.decEq κ
    (pi P).reflectionPerm
  reflectionPerm_root := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    let _ : Fintype κ := Fintype.ofFinite κ
    let _ : DecidableEq κ := Classical.decEq κ
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, LinearMap.comp_apply]
    by_cases hcd : c = d
    · subst hcd
      rw [pi_reflectionPerm_same, internalProjection_apply]
      exact_mod_cast (P c).reflectionPerm_root i j
    · rw [pi_reflectionPerm_ne P hcd, internalProjection_apply_of_ne hEi hEt (Ne.symm hcd)]
      simp
  reflectionPerm_coroot := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    let _ : Fintype κ := Fintype.ofFinite κ
    let _ : DecidableEq κ := Classical.decEq κ
    refine LinearMap.ext fun x ↦ ?_
    simp only [Function.Embedding.coeFn_mk, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, Module.Dual.eval_apply, smul_eq_mul]
    by_cases hcd : c = d
    · subst hcd
      rw [pi_reflectionPerm_same, internalProjection_apply]
      have h := congrArg (fun y ↦ (P c).toLinearMap (internalProjection hEi hEt c x) y)
        ((P c).reflectionPerm_coroot i j)
      simpa [coroot', map_sub, map_smul, smul_eq_mul, mul_comm] using h
    · rw [pi_reflectionPerm_ne P hcd, internalProjection_apply_of_ne hEi hEt hcd]
      simp

section Evaluation

variable [Finite κ]

@[simp]
theorem internalDirectSum_toLinearMap :
    (internalDirectSum hEi hEt P).toLinearMap = Module.Dual.eval R M :=
  (rfl)

@[simp]
theorem internalDirectSum_root (c : κ) (i : ι c) :
    (internalDirectSum hEi hEt P).root ⟨c, i⟩ = ((P c).root i : M) :=
  (rfl)

@[simp]
theorem internalDirectSum_coroot (c : κ) (i : ι c) :
    (internalDirectSum hEi hEt P).coroot ⟨c, i⟩ =
      ((P c).coroot' i).comp (internalProjection hEi hEt c) :=
  (rfl)

theorem internalDirectSum_coroot'_apply (c : κ) (i : ι c) (x : M) :
    (internalDirectSum hEi hEt P).coroot' ⟨c, i⟩ x =
      (P c).coroot' i (internalProjection hEi hEt c x) :=
  (rfl)

/-- Restricting a coroot of `internalDirectSum` from summand `c` to `E c` recovers `(P c).coroot i`
via the summand perfect pairing. -/
theorem toPerfPair_symm_internalDirectSum_coroot_comp_same (c : κ) (i : ι c) :
    (P c).flip.toPerfPair.symm
        (((internalDirectSum hEi hEt P).coroot ⟨c, i⟩).comp (E c).subtype) =
      (P c).coroot i := by
  apply (P c).flip.toPerfPair.injective
  ext x
  simp [coroot']

/-- Restricting a coroot of `internalDirectSum` from summand `c` to a distinct summand `E d`
vanishes. -/
theorem internalDirectSum_coroot_comp_ne {c d : κ} (hdc : d ≠ c) (i : ι c) :
    ((internalDirectSum hEi hEt P).coroot ⟨c, i⟩).comp (E d).subtype = 0 := by
  ext x
  simp [internalProjection_apply_of_ne hEi hEt hdc]

@[simp]
theorem internalDirectSum_pairing_same (c : κ) (i j : ι c) :
    (internalDirectSum hEi hEt P).pairing ⟨c, i⟩ ⟨c, j⟩ = (P c).pairing i j := by
  rw [← root_coroot'_eq_pairing, internalDirectSum_coroot'_apply, internalDirectSum_root,
    internalProjection_apply, root_coroot'_eq_pairing]

@[simp]
theorem internalDirectSum_pairing_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (internalDirectSum hEi hEt P).pairing ⟨c, i⟩ ⟨d, j⟩ = 0 := by
  rw [← root_coroot'_eq_pairing, internalDirectSum_coroot'_apply, internalDirectSum_root,
    internalProjection_apply_of_ne hEi hEt hcd, map_zero]

/-- Roots in distinct summands of an internal direct sum are orthogonal. -/
theorem isOrthogonal_internalDirectSum_of_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (internalDirectSum hEi hEt P).IsOrthogonal ⟨c, i⟩ ⟨d, j⟩ :=
  ⟨internalDirectSum_pairing_ne hEi hEt P hcd i j,
    internalDirectSum_pairing_ne hEi hEt P hcd.symm j i⟩

@[simp]
theorem internalDirectSum_reflectionPerm_same (c : κ) (i j : ι c) :
    (internalDirectSum hEi hEt P).reflectionPerm ⟨c, i⟩ ⟨c, j⟩ = ⟨c, (P c).reflectionPerm i j⟩ := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  exact pi_reflectionPerm_same P c i j

@[simp]
theorem internalDirectSum_reflectionPerm_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (internalDirectSum hEi hEt P).reflectionPerm ⟨c, i⟩ ⟨d, j⟩ = ⟨d, j⟩ := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  exact pi_reflectionPerm_ne P hcd i j

/-- Formula for the reflection of an internal direct sum at `⟨c, i⟩` on an arbitrary vector. -/
theorem internalDirectSum_reflection_apply (c : κ) (i : ι c) (x : M) :
    (internalDirectSum hEi hEt P).reflection ⟨c, i⟩ x =
      x - (P c).coroot' i (internalProjection hEi hEt c x) • ((P c).root i : M) :=
  (rfl)

@[simp]
theorem internalDirectSum_reflection_apply_coe (c : κ) (i : ι c) (x : E c) :
    (internalDirectSum hEi hEt P).reflection ⟨c, i⟩ x = ((P c).reflection i x : M) := by
  simp [reflection_apply]

@[simp]
theorem internalDirectSum_reflection_apply_coe_of_ne {c d : κ} (hdc : d ≠ c) (i : ι c) (x : E d) :
    (internalDirectSum hEi hEt P).reflection ⟨c, i⟩ x = x := by
  simp [internalDirectSum_reflection_apply, internalProjection_apply_of_ne hEi hEt hdc]

@[simp]
theorem internalProjection_internalDirectSum_reflection_same (c : κ) (i : ι c) (x : M) :
    internalProjection hEi hEt c ((internalDirectSum hEi hEt P).reflection ⟨c, i⟩ x) =
      (P c).reflection i (internalProjection hEi hEt c x) := by
  simp [reflection_apply]

@[simp]
theorem internalProjection_internalDirectSum_reflection_ne {c d : κ} (hdc : d ≠ c) (i : ι c)
    (x : M) :
    internalProjection hEi hEt d ((internalDirectSum hEi hEt P).reflection ⟨c, i⟩ x) =
      internalProjection hEi hEt d x := by
  simp [internalDirectSum_reflection_apply, internalProjection_apply_of_ne hEi hEt hdc.symm]

/-- Formula for the coreflection of an internal direct sum at `⟨c, i⟩` on an arbitrary dual
functional. -/
theorem internalDirectSum_coreflection_apply (c : κ) (i : ι c) (f : Module.Dual R M) :
    (internalDirectSum hEi hEt P).coreflection ⟨c, i⟩ f =
      f - f ((P c).root i : M) • ((P c).coroot' i).comp (internalProjection hEi hEt c) :=
  (rfl)

@[simp]
theorem internalDirectSum_coreflection_comp_subtype_same (c : κ) (i : ι c)
    (f : Module.Dual R M) :
    ((internalDirectSum hEi hEt P).coreflection ⟨c, i⟩ f).comp (E c).subtype =
      (P c).flip.toPerfPair
        ((P c).coreflection i ((P c).flip.toPerfPair.symm (f.comp (E c).subtype))) := by
  ext x
  simp [coreflection_apply, root', coroot']

@[simp]
theorem internalDirectSum_coreflection_comp_subtype_ne {c d : κ} (hdc : d ≠ c) (i : ι c)
    (f : Module.Dual R M) :
    ((internalDirectSum hEi hEt P).coreflection ⟨c, i⟩ f).comp (E d).subtype =
      f.comp (E d).subtype := by
  ext x
  simp [coreflection_apply, internalProjection_apply_of_ne hEi hEt hdc]

/-- **The roots of a finite internal direct sum are the union of the summands' roots inside `M`.**
In particular, no sum of roots from distinct summands is a root. -/
theorem range_internalDirectSum_root :
    range (internalDirectSum hEi hEt P).root = ⋃ c, Subtype.val '' range (P c).root := by
  have h : ⇑(internalDirectSum hEi hEt P).root =
      fun s : Σ c, ι c ↦ ((P s.1).root s.2 : M) := rfl
  rw [h, Set.range_sigma_eq_iUnion_range]
  exact iUnion_congr fun c ↦ Set.range_comp' Subtype.val (P c).root

/-- **The coroots of a finite internal direct sum are the union of the summands' coroot
functionals extended by `TauCeti.internalProjection`.** -/
theorem range_internalDirectSum_coroot :
    range (internalDirectSum hEi hEt P).coroot =
      ⋃ c, (fun g : Module.Dual R (E c) ↦ g.comp (internalProjection hEi hEt c)) ''
        range (P c).coroot' := by
  have h : ⇑(internalDirectSum hEi hEt P).coroot =
      fun s : Σ c, ι c ↦ ((P s.1).coroot' s.2).comp (internalProjection hEi hEt s.1) := rfl
  rw [h, Set.range_sigma_eq_iUnion_range]
  exact iUnion_congr fun c ↦
    Set.range_comp' (fun g : Module.Dual R (E c) ↦ g.comp (internalProjection hEi hEt c))
      (P c).coroot'

end Evaluation

/-! ### Equivalence with the external direct sum -/

section EquivPi

variable [Fintype κ]

/-- The canonical linear equivalence `(∀ c, N c) ≃ₗ[R] Module.Dual R M` pairing each coweight
summand with `E c` via `internalDirectSumEquiv`. -/
private noncomputable def internalDirectSumCoweightEquiv :
    (∀ c, N c) ≃ₗ[R] Module.Dual R M :=
  (LinearMap.piPairing fun c ↦ (P c).flip.toLinearMap).toPerfPair.trans
    (internalDirectSumEquiv hEi hEt).symm.dualMap

omit [NeZero (2 : R)] in
private theorem internalDirectSumCoweightEquiv_symm_apply
    (f : Module.Dual R M) (c : κ) :
    (internalDirectSumCoweightEquiv hEi hEt P).symm f c =
      (P c).flip.toPerfPair.symm (f.comp (E c).subtype) := by
  classical
  rw [internalDirectSumCoweightEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearMap.toPerfPair_piPairing_symm_apply]
  congr 1
  ext x
  have hdual : (((internalDirectSumEquiv hEi hEt).symm.dualMap).symm f)
      (LinearMap.single R (fun c ↦ ↥(E c)) c x) =
      f (internalDirectSumEquiv hEi hEt (Pi.single c x)) := by
    simp [LinearEquiv.dualMap_apply]
  rw [LinearMap.comp_apply, hdual, internalDirectSumEquiv_single]
  rfl

/-- **Canonical equivalence between the external direct sum `RootPairing.pi P` and the internal
direct sum `RootPairing.internalDirectSum hEi hEt P`.** -/
noncomputable def piEquivInternalDirectSum [DecidableEq κ] :
    (pi P).Equiv (internalDirectSum hEi hEt P) where
  weightMap := (internalDirectSumEquiv hEi hEt).toLinearMap
  coweightMap := (internalDirectSumCoweightEquiv hEi hEt P).symm.toLinearMap
  indexEquiv := _root_.Equiv.refl (Σ c, ι c)
  weight_coweight_transpose := by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      LinearMap.toPerfPair_apply, flip_toLinearMap, LinearMap.flip_apply,
      internalDirectSum_toLinearMap, Module.Dual.eval_apply, pi_toLinearMap_apply,
      internalDirectSumEquiv_apply, internalDirectSumCoweightEquiv_symm_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have h := LinearMap.congr_fun ((P c).flip.toPerfPair.apply_symm_apply (f.comp (E c).subtype))
      (x c)
    simp only [LinearMap.toPerfPair_apply, flip_toLinearMap, LinearMap.flip_apply,
      LinearMap.comp_apply, Submodule.coe_subtype] at h
    exact h.symm
  root_weightMap := by
    ext ⟨c, i⟩
    simp only [comp_apply, LinearEquiv.coe_coe, _root_.Equiv.refl_apply, pi_root,
      internalDirectSumEquiv_single, internalDirectSum_root]
  coroot_coweightMap := by
    ext ⟨c, i⟩ d
    simp only [comp_apply, LinearEquiv.coe_coe, _root_.Equiv.refl_symm, _root_.Equiv.refl_apply,
      internalDirectSum_coroot, pi_coroot, internalDirectSumCoweightEquiv_symm_apply]
    apply (P d).flip.toPerfPair.injective
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearEquiv.apply_symm_apply]
    by_cases h : d = c
    · subst h
      simp [coroot']
    · simp [Pi.single_eq_of_ne h, internalProjection_apply_of_ne hEi hEt h]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

@[simp]
theorem piEquivInternalDirectSum_indexEquiv [DecidableEq κ] (s : Σ c, ι c) :
    (piEquivInternalDirectSum hEi hEt P).indexEquiv s = s :=
  (rfl)

@[simp]
theorem piEquivInternalDirectSum_indexEquiv_symm [DecidableEq κ] (s : Σ c, ι c) :
    (piEquivInternalDirectSum hEi hEt P).indexEquiv.symm s = s :=
  (rfl)

@[simp]
theorem piEquivInternalDirectSum_weightMap_apply [DecidableEq κ] (x : ∀ c, E c) :
    (piEquivInternalDirectSum hEi hEt P).weightMap x = ∑ c, (x c : M) :=
  internalDirectSumEquiv_apply hEi hEt x

@[simp]
theorem piEquivInternalDirectSum_weightEquiv_symm_apply [DecidableEq κ]
    (x : M) (c : κ) :
    (piEquivInternalDirectSum hEi hEt P).weightEquiv.symm x c = internalProjection hEi hEt c x := by
  have heq : (piEquivInternalDirectSum hEi hEt P).weightEquiv =
      internalDirectSumEquiv hEi hEt :=
    LinearEquiv.toLinearMap_injective rfl
  rw [heq, internalDirectSumEquiv_symm_apply]

@[simp]
theorem piEquivInternalDirectSum_coweightMap_apply [DecidableEq κ]
    (f : Module.Dual R M) (c : κ) :
    (piEquivInternalDirectSum hEi hEt P).coweightMap f c =
      (P c).flip.toPerfPair.symm (f.comp (E c).subtype) :=
  internalDirectSumCoweightEquiv_symm_apply hEi hEt P f c

/-- Assembling a tuple of summand coweights under
`(piEquivInternalDirectSum hEi hEt P).coweightEquiv.symm` evaluates on `x : M` as the sum of the
summand pairings against `internalProjection hEi hEt c x`. -/
@[simp]
theorem piEquivInternalDirectSum_coweightEquiv_symm_apply [DecidableEq κ]
    (y : ∀ c, N c) (x : M) :
    (piEquivInternalDirectSum hEi hEt P).coweightEquiv.symm y x =
      ∑ c, (P c).toLinearMap (internalProjection hEi hEt c x) (y c) := by
  have heq : (piEquivInternalDirectSum hEi hEt P).coweightEquiv =
      (internalDirectSumCoweightEquiv hEi hEt P).symm :=
    LinearEquiv.toLinearMap_injective rfl
  rw [heq, LinearEquiv.symm_symm, internalDirectSumCoweightEquiv, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply, LinearMap.toPerfPair_apply, LinearMap.piPairing_apply_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp

end EquivPi

/-! ### Structural properties -/

section Properties

variable [Finite κ]

/-- **A finite internal direct sum of root systems is a root system.** -/
instance isRootSystem_internalDirectSum [∀ c, (P c).IsRootSystem] :
    (internalDirectSum hEi hEt P).IsRootSystem :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (piEquivInternalDirectSum hEi hEt P).isRootSystem

/-- **A finite internal direct sum is a root system iff every summand is a root system.** -/
theorem isRootSystem_internalDirectSum_iff :
    (internalDirectSum hEi hEt P).IsRootSystem ↔ ∀ c, (P c).IsRootSystem :=
  ⟨fun _ ↦
    let _ : Fintype κ := Fintype.ofFinite κ
    let _ : DecidableEq κ := Classical.decEq κ
    let _ := (piEquivInternalDirectSum hEi hEt P).symm.isRootSystem
    (isRootSystem_pi_iff P).mp ‹_›,
   fun _ ↦ isRootSystem_internalDirectSum hEi hEt P⟩

/-- **A finite internal direct sum of `S`-valued root pairings is `S`-valued.** In particular, an
internal direct sum of crystallographic root pairings is crystallographic. -/
instance isValuedIn_internalDirectSum (S : Type*) [CommRing S] [Algebra S R]
    [∀ c, (P c).IsValuedIn S] : (internalDirectSum hEi hEt P).IsValuedIn S :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (piEquivInternalDirectSum hEi hEt P).toHom.isValuedIn S

/-- **A finite internal direct sum is `S`-valued iff every summand is `S`-valued.** -/
theorem isValuedIn_internalDirectSum_iff (S : Type*) [CommRing S] [Algebra S R] :
    (internalDirectSum hEi hEt P).IsValuedIn S ↔ ∀ c, (P c).IsValuedIn S :=
  ⟨fun _ ↦
    let _ : Fintype κ := Fintype.ofFinite κ
    let _ : DecidableEq κ := Classical.decEq κ
    let _ := (piEquivInternalDirectSum hEi hEt P).symm.toHom.isValuedIn S
    (isValuedIn_pi_iff P S).mp ‹_›,
   fun _ ↦ isValuedIn_internalDirectSum hEi hEt P S⟩

@[simp]
theorem internalDirectSum_pairingIn_same (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (c : κ) (i j : ι c) :
    (internalDirectSum hEi hEt P).pairingIn S ⟨c, i⟩ ⟨c, j⟩ = (P c).pairingIn S i j :=
  FaithfulSMul.algebraMap_injective S R <| by simp

@[simp]
theorem internalDirectSum_pairingIn_ne (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (internalDirectSum hEi hEt P).pairingIn S ⟨c, i⟩ ⟨d, j⟩ = 0 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [internalDirectSum_pairing_ne hEi hEt P hcd]

/-- **A finite internal direct sum of reduced root pairings is reduced**, provided `2` is regular
in `R`. -/
theorem isReduced_internalDirectSum_of_isRegular (h2 : IsRegular (2 : R)) [∀ c, (P c).IsReduced] :
    (internalDirectSum hEi hEt P).IsReduced :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let _ := isReduced_pi_of_isRegular P h2
  (piEquivInternalDirectSum hEi hEt P).isReduced

/-- Every summand of a reduced finite internal direct sum is reduced. -/
theorem isReduced_of_internalDirectSum [(internalDirectSum hEi hEt P).IsReduced] (c : κ) :
    (P c).IsReduced :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let _ := (piEquivInternalDirectSum hEi hEt P).symm.isReduced
  isReduced_of_pi P c

/-- **Under regularity of `2`, a finite internal direct sum is reduced iff every summand is
reduced.** -/
theorem isReduced_internalDirectSum_iff_of_isRegular (h2 : IsRegular (2 : R)) :
    (internalDirectSum hEi hEt P).IsReduced ↔ ∀ c, (P c).IsReduced :=
  ⟨fun _ c ↦ isReduced_of_internalDirectSum hEi hEt P c,
   fun _ ↦ isReduced_internalDirectSum_of_isRegular hEi hEt P h2⟩

/-- A finite internal direct sum of reduced root pairings over a ring with no zero divisors (and
`2 ≠ 0`) is reduced. -/
instance isReduced_internalDirectSum [NoZeroDivisors R] [∀ c, (P c).IsReduced] :
    (internalDirectSum hEi hEt P).IsReduced :=
  isReduced_internalDirectSum_of_isRegular hEi hEt P (IsRegular.of_ne_zero' two_ne_zero)

/-- **Over a ring with no zero divisors (and `2 ≠ 0`), a finite internal direct sum is reduced iff
every summand is reduced.** -/
theorem isReduced_internalDirectSum_iff [NoZeroDivisors R] :
    (internalDirectSum hEi hEt P).IsReduced ↔ ∀ c, (P c).IsReduced :=
  isReduced_internalDirectSum_iff_of_isRegular hEi hEt P (IsRegular.of_ne_zero' two_ne_zero)

end Properties

end Internal

/-! ### Functoriality -/

section Functoriality

variable {κ κ' R M M' : Type*} [Finite κ] [Finite κ'] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  {E : κ → Submodule R M} {E' : κ' → Submodule R M'}
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {ι' N' : κ' → Type*} [∀ c', AddCommGroup (N' c')] [∀ c', Module R (N' c')]
  {P : ∀ c, RootPairing (ι c) R (E c) (N c)}
  {Q : ∀ c', RootPairing (ι' c') R (E' c') (N' c')}

/-- **Functoriality of finite internal direct sums of root pairings**, obtained by conjugating
`RootPairing.Equiv.piCongr` with `RootPairing.piEquivInternalDirectSum`. -/
noncomputable def Equiv.internalDirectSumCongr
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c))) :
    (internalDirectSum hEi hEt P).Equiv (internalDirectSum hEi' hEt' Q) :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  Equiv.comp (piEquivInternalDirectSum hEi' hEt' Q)
    (Equiv.comp (Equiv.piCongr eκ e)
      ((piEquivInternalDirectSum hEi hEt P).symm))

@[simp]
theorem Equiv.internalDirectSumCongr_indexEquiv
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c))) (c : κ) (i : ι c) :
    (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).indexEquiv ⟨c, i⟩ =
      ⟨eκ c, (e c).indexEquiv i⟩ := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  simp [Equiv.internalDirectSumCongr, Equiv.toHom_comp]

@[simp]
theorem Equiv.internalDirectSumCongr_weightMap_coe
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c))) (c : κ) (x : E c) :
    (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).weightMap (x : M) =
      ((e c).weightMap x : M') := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  have hw : (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).weightMap (x : M) =
      (piEquivInternalDirectSum hEi' hEt' Q).weightMap
        ((Equiv.piCongr eκ e).weightMap
          ((piEquivInternalDirectSum hEi hEt P).weightEquiv.symm (x : M))) := by
    simp only [Equiv.internalDirectSumCongr, Equiv.toHom_comp, Hom.comp,
      LinearMap.comp_apply, Equiv.inv_weightMap, LinearEquiv.coe_coe]
  rw [hw, piEquivInternalDirectSum_weightMap_apply,
    Finset.sum_eq_single_of_mem (eκ c) (Finset.mem_univ (eκ c))]
  · simp [Equiv.piCongr_weightMap_apply]
  · intro c' _ hc'
    obtain ⟨d, rfl⟩ := eκ.surjective c'
    rw [Equiv.piCongr_weightMap_apply, piEquivInternalDirectSum_weightEquiv_symm_apply,
      internalProjection_apply_of_ne hEi hEt (by rintro rfl; exact hc' rfl)]
    simp

@[simp]
theorem Equiv.internalProjection_internalDirectSumCongr_weightMap
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c))) (c : κ) (x : M) :
    internalProjection hEi' hEt' (eκ c)
        ((Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).weightMap x) =
      (e c).weightMap (internalProjection hEi hEt c x) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  have he : ((Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).weightEquiv x) =
      (piEquivInternalDirectSum hEi' hEt' Q).weightEquiv
        ((Equiv.piCongr eκ e).weightEquiv
          ((piEquivInternalDirectSum hEi hEt P).weightEquiv.symm x)) := by
    simp only [Equiv.internalDirectSumCongr, Equiv.weightEquiv_apply, Equiv.toHom_comp,
      Hom.comp, LinearMap.comp_apply, Equiv.inv_weightMap, LinearEquiv.coe_coe]
  have hproj := congrFun
    (congrArg (piEquivInternalDirectSum hEi' hEt' Q).weightEquiv.symm he) (eκ c)
  rw [LinearEquiv.symm_apply_apply] at hproj
  simpa using hproj

/-- Coordinate formula for the coweight map of `Equiv.internalDirectSumCongr` restricted to each
summand submodule `E c` via the summand perfect pairing. -/
@[simp]
theorem Equiv.toPerfPair_symm_internalDirectSumCongr_coweightMap
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (g : Module.Dual R M') (c : κ) :
    (P c).toLinearMap.flip.toPerfPair.symm
        (((Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e).coweightMap g).comp (E c).subtype) =
      (e c).coweightMap
        ((Q (eκ c)).toLinearMap.flip.toPerfPair.symm (g.comp (E' (eκ c)).subtype)) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  simp only [← RootPairing.flip_toLinearMap]
  rw [← piEquivInternalDirectSum_coweightMap_apply hEi hEt P]
  simp only [Equiv.internalDirectSumCongr, Equiv.toHom_comp, Hom.comp, LinearMap.comp_apply,
    Equiv.inv_coweightMap, LinearEquiv.coe_coe, ← Equiv.coweightEquiv_apply,
    LinearEquiv.apply_symm_apply]
  simp only [Equiv.coweightEquiv_apply, Equiv.piCongr_coweightMap_apply,
    piEquivInternalDirectSum_coweightMap_apply]

/-- Assembling the identity equivalences along `Equiv.refl κ` gives the identity equivalence of
`RootPairing.internalDirectSum hEi hEt P`. -/
@[simp]
theorem Equiv.internalDirectSumCongr_id
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤) :
    Equiv.internalDirectSumCongr hEi hEt hEi hEt
        (_root_.Equiv.refl κ) (fun c ↦ Equiv.id (P c)) =
      Equiv.id (internalDirectSum hEi hEt P) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [Equiv.internalDirectSumCongr]

/-- Composing two `Equiv.internalDirectSumCongr` equivalences gives
`Equiv.internalDirectSumCongr` on the composite reindexing and reindexed composite summand
equivalences. -/
@[simp]
theorem Equiv.internalDirectSumCongr_comp
    {κ'' M'' : Type*} [Finite κ''] [AddCommGroup M''] [Module R M'']
    {E'' : κ'' → Submodule R M''}
    {ι'' N'' : κ'' → Type*} [∀ c, AddCommGroup (N'' c)] [∀ c, Module R (N'' c)]
    {S : ∀ c, RootPairing (ι'' c) R (E'' c) (N'' c)}
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (hEi'' : iSupIndep E'') (hEt'' : ⨆ c'', E'' c'' = ⊤)
    (eκ : κ ≃ κ') (eκ' : κ' ≃ κ'')
    (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (e' : ∀ c', (Q c').Equiv (S (eκ' c'))) :
    Equiv.comp (Equiv.internalDirectSumCongr hEi' hEt' hEi'' hEt'' eκ' e')
        (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e) =
      Equiv.internalDirectSumCongr hEi hEt hEi'' hEt'' (eκ.trans eκ')
        fun c ↦ Equiv.comp (e' (eκ c)) (e c) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  let _ : Fintype κ'' := Fintype.ofFinite κ''
  let _ : DecidableEq κ := Classical.decEq κ
  let _ : DecidableEq κ' := Classical.decEq κ'
  let _ : DecidableEq κ'' := Classical.decEq κ''
  simp only [Equiv.internalDirectSumCongr, Equiv.comp_assoc]
  congr 1
  rw [← Equiv.comp_assoc (piEquivInternalDirectSum hEi' hEt' Q).symm
      (piEquivInternalDirectSum hEi' hEt' Q),
    Equiv.symm_comp_self, Equiv.comp_id, ← Equiv.comp_assoc, Equiv.piCongr_comp]

end Functoriality

end RootPairing
