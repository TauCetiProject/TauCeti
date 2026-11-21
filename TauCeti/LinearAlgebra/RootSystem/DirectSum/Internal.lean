/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Basic
import Mathlib.Algebra.Ring.Regular
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

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
reducedness, anisotropy, base, base-restriction, height, positive-root, canonical bilinear form,
and functoriality results for `internalDirectSum`, requiring only `[Finite κ]` wherever no
`Finset.univ` appears in the statement.

## Main definitions

* `RootPairing.internalDirectSum`: the finite internal direct sum of root pairings on submodules
  `E c ≤ M`, taking values in `M` and `Module.Dual R M` with `Module.Dual.eval R M`.
* `RootPairing.piEquivInternalDirectSum`: the canonical equivalence between `RootPairing.pi P` and
  `RootPairing.internalDirectSum hEi hEt P`.
* `RootPairing.Base.internalDirectSum`: the base of `RootPairing.internalDirectSum hEi hEt P`
  assembled from bases of its summands.
* `RootPairing.Base.restrictInternalDirectSum`: the restriction of a base of
  `RootPairing.internalDirectSum hEi hEt P` to a summand.
* `RootPairing.Equiv.internalDirectSumCongr`: functoriality of `RootPairing.internalDirectSum`
  under reindexing and summand equivalences.

## Main results

* `RootPairing.range_internalDirectSum_root`: the roots of an internal direct sum are the union of
  the roots of its summands inside `M`.
* `RootPairing.isRootSystem_internalDirectSum`, `RootPairing.isValuedIn_internalDirectSum`,
  `RootPairing.isReduced_internalDirectSum`, `RootPairing.isAnisotropic_internalDirectSum`:
  structural properties preserved by internal direct sums.
* `RootPairing.internalDirectSum_rootForm_apply_apply` and
  `RootPairing.internalDirectSum_corootForm_apply_apply`: the canonical bilinear forms split as the
  orthogonal sums of the summands' forms.
* `RootPairing.Base.height_internalDirectSum`, `RootPairing.Base.isPos_internalDirectSum_iff`,
  `RootPairing.Base.internalDirectSum_restrictInternalDirectSum`,
  `RootPairing.Base.restrictInternalDirectSum_internalDirectSum`,
  `RootPairing.Base.map_internalDirectSumCongr`: coordinatewise decomposition and transport of
  bases, heights, and positivity.

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

/-- **The roots of a finite internal direct sum are the union of the summands' roots inside `M`.**
In particular, no sum of roots from distinct summands is a root. -/
theorem range_internalDirectSum_root :
    range (internalDirectSum hEi hEt P).root = ⋃ c, Subtype.val '' range (P c).root := by
  have h : ⇑(internalDirectSum hEi hEt P).root =
      fun s : Σ c, ι c ↦ ((P s.1).root s.2 : M) := rfl
  rw [h, Set.range_sigma_eq_iUnion_range]
  exact iUnion_congr fun c ↦ Set.range_comp' Subtype.val (P c).root

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
  rw [LinearMap.comp_apply, hdual, internalDirectSumEquiv_apply,
    Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp
  · intro d _ hdc
    simp [Pi.single_eq_of_ne hdc]

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
    simp only [comp_apply, LinearEquiv.coe_coe, pi_root, _root_.Equiv.refl_apply,
      internalDirectSum_root, internalDirectSumEquiv_apply]
    rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simp
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]
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

end EquivPi

/-! ### Structural properties -/

section Properties

variable [Finite κ]

/-- **A finite internal direct sum of root systems is a root system.** -/
instance isRootSystem_internalDirectSum [∀ c, (P c).IsRootSystem] :
    (internalDirectSum hEi hEt P).IsRootSystem := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  refine ⟨?_, ?_⟩
  · have h := congrArg (Submodule.map e.weightEquiv.toLinearMap)
      (IsRootSystem.span_root_eq_top (P := pi P))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    convert h using 2
    rw [← Set.range_comp]
    have hcomp : (e.weightEquiv : (∀ c, E c) → M) ∘ (pi P).root =
        (internalDirectSum hEi hEt P).root :=
      funext fun s ↦ congrFun e.root_weightMap s
    rw [← hcomp]
    rfl
  · have h := congrArg (Submodule.map e.coweightEquiv.symm.toLinearMap)
      (IsRootSystem.span_coroot_eq_top (P := pi P))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    convert h using 2
    rw [← Set.range_comp]
    have hcomp : (e.coweightEquiv.symm : (∀ c, N c) → Module.Dual R M) ∘ (pi P).coroot =
        (internalDirectSum hEi hEt P).coroot :=
      funext fun s ↦ congrFun e.symm.coroot_coweightMap s
    rw [← hcomp]
    rfl

/-- **A finite internal direct sum of `S`-valued root pairings is `S`-valued.** In particular, an
internal direct sum of crystallographic root pairings is crystallographic. -/
instance isValuedIn_internalDirectSum (S : Type*) [CommRing S] [Algebra S R]
    [∀ c, (P c).IsValuedIn S] : (internalDirectSum hEi hEt P).IsValuedIn S :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (piEquivInternalDirectSum hEi hEt P).toHom.isValuedIn S

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

/-- A finite internal direct sum of reduced root pairings over a ring with no zero divisors (and
`2 ≠ 0`) is reduced. -/
instance isReduced_internalDirectSum [NoZeroDivisors R] [∀ c, (P c).IsReduced] :
    (internalDirectSum hEi hEt P).IsReduced :=
  isReduced_internalDirectSum_of_isRegular hEi hEt P (IsRegular.of_ne_zero' two_ne_zero)

end Properties

/-! ### Canonical bilinear form and anisotropy -/

section RootForm

variable [Fintype κ] [∀ c, Fintype (ι c)]

/-- **The canonical bilinear form of an internal direct sum is the orthogonal sum of the summands'
canonical forms along `TauCeti.internalProjection`.** -/
@[simp]
theorem internalDirectSum_rootForm_apply_apply (x y : M) :
    (internalDirectSum hEi hEt P).RootForm x y =
      ∑ c, (P c).RootForm (internalProjection hEi hEt c x) (internalProjection hEi hEt c y) := by
  simp only [rootForm_apply_apply, Fintype.sum_sigma, internalDirectSum_coroot'_apply]

/-- **The canonical coroot bilinear form of an internal direct sum is the orthogonal sum of the
summands' coroot forms on the coordinates of
`(piEquivInternalDirectSum hEi hEt P).coweightMap`.** -/
@[simp]
theorem internalDirectSum_corootForm_apply_apply [DecidableEq κ] (f g : Module.Dual R M) :
    (internalDirectSum hEi hEt P).CorootForm f g =
      ∑ c, (P c).CorootForm
        ((piEquivInternalDirectSum hEi hEt P).coweightMap f c)
        ((piEquivInternalDirectSum hEi hEt P).coweightMap g c) := by
  simp only [corootForm_apply_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have heval (h : Module.Dual R M) :
      ((P c).toLinearMap ((P c).root i)) ((P c).flip.toPerfPair.symm (h.comp (E c).subtype)) =
        h ((P c).root i : M) := by
    simp
  simp only [root', internalDirectSum_toLinearMap, Module.Dual.eval_apply, internalDirectSum_root,
    piEquivInternalDirectSum_coweightMap_apply]
  rw [heval f, heval g]

/-- A finite internal direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_internalDirectSum [∀ c, (P c).IsAnisotropic] :
    (internalDirectSum hEi hEt P).IsAnisotropic where
  rootForm_root_ne_zero := by
    rintro ⟨c, i⟩
    rw [internalDirectSum_rootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.rootForm_root_ne_zero (P := P c) i
    · intro d _ hdc
      simp [internalProjection_apply_of_ne hEi hEt hdc.symm]
  corootForm_coroot_ne_zero := by
    let _ : DecidableEq κ := Classical.decEq κ
    rintro ⟨c, i⟩
    have hcor : (piEquivInternalDirectSum hEi hEt P).coweightMap
          ((internalDirectSum hEi hEt P).coroot ⟨c, i⟩) =
        (pi P).coroot ⟨c, i⟩ := by
      simpa using Hom.coroot_coweightMap_apply (pi P) (internalDirectSum hEi hEt P) ⟨c, i⟩
        (piEquivInternalDirectSum hEi hEt P).toHom
    rw [internalDirectSum_corootForm_apply_apply, hcor,
      Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simp only [pi_coroot, Pi.single_eq_same]
      exact IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i
    · intro d _ hdc
      simp [pi_coroot, Pi.single_eq_of_ne hdc]

end RootForm

/-! ### Bases, heights, and positivity -/

section Bases

variable [Finite κ]

/-- **The base of a finite internal direct sum** assembled from bases of its summands. -/
noncomputable def Base.internalDirectSum {P : ∀ c, RootPairing (ι c) R (E c) (N c)}
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤) (b : ∀ c, (P c).Base) :
    (RootPairing.internalDirectSum hEi hEt P).Base :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (Base.pi b).map (piEquivInternalDirectSum hEi hEt P)

variable {hEi hEt P}

@[simp]
theorem Base.mem_support_internalDirectSum (b : ∀ c, (P c).Base) (s : Σ c, ι c) :
    s ∈ (Base.internalDirectSum hEi hEt b).support ↔ s.2 ∈ (b s.1).support := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [Base.internalDirectSum, Base.map]

/-- **Restricting a base of `RootPairing.internalDirectSum hEi hEt P` to a summand** by taking
the simple roots lying in that summand. -/
noncomputable def Base.restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) (c : κ) : (P c).Base :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (b.map (piEquivInternalDirectSum hEi hEt P).symm).restrictPi c

@[simp]
theorem Base.mem_support_restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) (c : κ) (i : ι c) :
    i ∈ (b.restrictInternalDirectSum c).support ↔ ⟨c, i⟩ ∈ b.support := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [Base.restrictInternalDirectSum, Base.map]

/-- Assembling the restrictions of a base of `internalDirectSum` recovers the original base. -/
@[simp]
theorem Base.internalDirectSum_restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) :
    Base.internalDirectSum hEi hEt (fun c ↦ b.restrictInternalDirectSum c) = b := by
  ext ⟨c, i⟩
  simp

/-- Restricting an assembled base `Base.internalDirectSum hEi hEt b` to coordinate `c` recovers
`b c`. -/
@[simp]
theorem Base.restrictInternalDirectSum_internalDirectSum (b : ∀ c, (P c).Base) (c : κ) :
    (Base.internalDirectSum hEi hEt b).restrictInternalDirectSum c = b c := by
  ext i
  simp

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_same (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) (c : κ)
    (i j : (b c).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.val⟩, by simp [i.property]⟩ ⟨⟨c, j.val⟩, by simp [j.property]⟩ =
      (b c).cartanMatrixIn S i j := by
  simp [Base.cartanMatrixIn_def]

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_ne (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) {c d : κ} (hcd : c ≠ d)
    (i : (b c).support) (j : (b d).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.val⟩, by simp [i.property]⟩ ⟨⟨d, j.val⟩, by simp [j.property]⟩ = 0 := by
  simp [Base.cartanMatrixIn_def, internalDirectSum_pairingIn_ne hEi hEt P S hcd]

/-- The height of a root in a finite internal direct sum is its height in its own summand. -/
@[simp]
theorem Base.height_internalDirectSum [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.internalDirectSum hEi hEt b).height ⟨c, i⟩ = (b c).height i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  dsimp only [Base.internalDirectSum]
  rw [← piEquivInternalDirectSum_indexEquiv hEi hEt P ⟨c, i⟩, Base.height_map, Base.height_pi]

/-- A root of an internal direct sum is positive for `Base.internalDirectSum` iff it is positive in
its summand. -/
@[simp]
theorem Base.isPos_internalDirectSum_iff [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.internalDirectSum hEi hEt b).IsPos ⟨c, i⟩ ↔ (b c).IsPos i := by
  simp [Base.isPos_iff]

end Bases

theorem Base.support_internalDirectSum [Fintype κ] {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
    {P : ∀ c, RootPairing (ι c) R (E c) (N c)} (b : ∀ c, (P c).Base) :
    (Base.internalDirectSum hEi hEt b).support = Finset.univ.sigma fun c ↦ (b c).support := by
  ext ⟨c, i⟩
  simp

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

/-- Mapping an assembled base `Base.internalDirectSum hEi hEt b` along
`Equiv.internalDirectSumCongr` produces `Base.internalDirectSum hEi' hEt' b'` whenever `e c`
carries `b c` to `b' (eκ c)`. -/
theorem Base.map_internalDirectSumCongr
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    {b : ∀ c, (P c).Base} {b' : ∀ c', (Q c').Base}
    (hb : ∀ c, (b c).map (e c) = b' (eκ c)) :
    (Base.internalDirectSum hEi hEt b).map
        (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e) =
      Base.internalDirectSum hEi' hEt' b' := by
  classical
  ext ⟨c', j⟩
  obtain ⟨c, rfl⟩ := eκ.surjective c'
  simp only [Base.support_map_eq, Base.mem_support_internalDirectSum, Finset.mem_image,
    Sigma.exists]
  constructor
  · rintro ⟨d, i, hi, heq⟩
    rw [Equiv.internalDirectSumCongr_indexEquiv] at heq
    rcases Sigma.ext_iff.mp heq with ⟨hdc, hij⟩
    obtain rfl := eκ.injective hdc
    rw [heq_eq_eq] at hij
    rw [← hb d]
    simp only [Base.support_map_eq, Finset.mem_image]
    exact ⟨i, hi, hij⟩
  · intro hj
    rw [← hb c] at hj
    simp only [Base.support_map_eq, Finset.mem_image] at hj
    obtain ⟨i, hi, hij⟩ := hj
    exact ⟨c, i, hi, by rw [Equiv.internalDirectSumCongr_indexEquiv, hij]⟩

/-- Mapping an assembled base `Base.internalDirectSum hEi hEt b` along
`Equiv.internalDirectSumCongr hEi hEt hEi' hEt' (.refl κ) e` assembles the transported summand
bases. -/
@[simp]
theorem Base.map_internalDirectSumCongr_refl
    {E'' : κ → Submodule R M'}
    {ι'' N'' : κ → Type*} [∀ c, AddCommGroup (N'' c)] [∀ c, Module R (N'' c)]
    {Q : ∀ c, RootPairing (ι'' c) R (E'' c) (N'' c)}
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E'') (hEt' : ⨆ c, E'' c = ⊤)
    (e : ∀ c, (P c).Equiv (Q c)) (b : ∀ c, (P c).Base) :
    (Base.internalDirectSum hEi hEt b).map
        (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' (_root_.Equiv.refl κ) e) =
      Base.internalDirectSum hEi' hEt' fun c ↦ (b c).map (e c) :=
  Base.map_internalDirectSumCongr hEi hEt hEi' hEt' (_root_.Equiv.refl κ) e fun _ ↦ rfl

end Functoriality

end RootPairing
