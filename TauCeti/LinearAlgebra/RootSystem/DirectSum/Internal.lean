/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Basic
import Mathlib.Algebra.Ring.Regular
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# Finite internal direct sums of root pairings and component decomposition

Given an ambient module `M` decomposed as a finite internal direct sum of submodules
`E : κ → Submodule R M` (witnessed by `[Finite κ]`, `iSupIndep E`, and `⨆ c, E c = ⊤`, requiring
neither `Fintype κ` nor `DecidableEq κ`), and a root pairing `P c : RootPairing (ι c) R (E c) (N c)`
on each summand, `RootPairing.internalDirectSum hEi hEt P` assembles them into a root pairing on
`M` and its dual `Module.Dual R M` with the literal evaluation pairing `Module.Dual.eval R M`.

The key observation is that `LinearMap.IsPerfPair.pi` makes the product `∀ c, E c` reflexive over
any commutative ring `R`, so the canonical linear equivalence `(∀ c, E c) ≃ₗ[R] M` makes `M`
reflexive and `Module.Dual.eval R M` a perfect pairing with no field, freeness, or finiteness
hypotheses on `M` or the summands. Each root `⟨c, i⟩` is the inclusion `((P c).root i : M)`, and
each coroot `⟨c, i⟩` is `(P c).coroot' i` composed with `TauCeti.internalProjection hEi hEt c`.

When `[Fintype κ]` and `[DecidableEq κ]` are available, `RootPairing.piEquivInternalDirectSum`
identifies `RootPairing.pi P` with `RootPairing.internalDirectSum hEi hEt P`. Transporting the
external direct-sum theory along this equivalence yields root-system, subring-valuedness,
reducedness, anisotropy, base, height, positive-root, cone, dominance, chamber, canonical bilinear
form, and Weyl-group results for `internalDirectSum`, requiring only `[Finite κ]` wherever no
`Finset.univ` appears in the statement.

Finally, for a finite root system `P` over a field with `2 ≠ 0`,
`RootPairing.equivInternalDirectSumComponentPairing` identifies `P` with the internal direct sum
of its irreducible component pairings `P.componentPairing`. As a consequence, the Weyl group of `P`
splits as the product of the Weyl groups of its irreducible components
(`RootPairing.componentWeylGroupEquiv`).

## Main definitions

* `RootPairing.internalDirectSum`: the finite internal direct sum of root pairings on submodules
  `E c ≤ M`, taking values in `M` and `Module.Dual R M` with `Module.Dual.eval R M`.
* `RootPairing.piEquivInternalDirectSum`: the canonical equivalence between `RootPairing.pi P` and
  `RootPairing.internalDirectSum hEi hEt P`.
* `RootPairing.Base.internalDirectSum`: the base of `RootPairing.internalDirectSum hEi hEt P`
  assembled from bases of its summands.
* `RootPairing.internalDirectSumWeylGroupEquiv`: the canonical isomorphism
  `(RootPairing.internalDirectSum hEi hEt P).weylGroup ≃* ∀ c, (P c).weylGroup`.
* `RootPairing.equivInternalDirectSumComponentPairing`: the canonical equivalence between a finite
  root system and the internal direct sum of its irreducible component pairings.
* `RootPairing.componentWeylGroupEquiv`: the canonical isomorphism between the Weyl group of a
  finite root system and the product of the Weyl groups of its irreducible components.

## Main results

* `RootPairing.range_internalDirectSum_root`: the roots of an internal direct sum are the union of
  the roots of its summands inside `M`.
* `RootPairing.isRootSystem_internalDirectSum`, `RootPairing.isValuedIn_internalDirectSum`,
  `RootPairing.isReduced_internalDirectSum`, `RootPairing.isAnisotropic_internalDirectSum`:
  structural properties preserved by internal direct sums.
* `RootPairing.internalDirectSum_rootForm_apply_apply`: the canonical bilinear form splits as the
  orthogonal sum of the summands' forms along `TauCeti.internalProjection`.
* `RootPairing.Base.height_internalDirectSum`, `RootPairing.Base.isPos_internalDirectSum_iff`,
  `RootPairing.mem_posRootCone_internalDirectSum_iff`, `RootPairing.rootLE_internalDirectSum_iff`,
  `RootPairing.mem_dominantChamber_internalDirectSum_iff`,
  `RootPairing.mem_openDominantChamber_internalDirectSum_iff`: coordinatewise decomposition along
  `TauCeti.internalProjection`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2, Proposition 5.
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

omit [NeZero (2 : R)] in
/-- The ambient module `M` of a finite internal direct sum of root pairings is reflexive, so
`Module.Dual.eval R M` is a perfect pairing. -/
private theorem isReflexive_of_internalDirectSum [Finite κ]
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤) (P : ∀ c, RootPairing (ι c) R (E c) (N c)) :
    Module.IsReflexive R M := by
  let _ : Fintype κ := Fintype.ofFinite κ
  have : Module.IsReflexive R (∀ c, E c) :=
    Module.IsReflexive.of_isPerfPair (LinearMap.piPairing fun c ↦ (P c).toLinearMap)
  let e := internalDirectSumEquiv hEi hEt
  exact Module.IsReflexive.of_split e.symm.toLinearMap e.toLinearMap
    (LinearMap.ext fun x ↦ e.apply_symm_apply x)

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
    have := isReflexive_of_internalDirectSum hEi hEt P
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

theorem internalDirectSum_toLinearMap_apply (x : M) (f : Module.Dual R M) :
    (internalDirectSum hEi hEt P).toLinearMap x f = f x :=
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

theorem internalDirectSum_coroot_apply (c : κ) (i : ι c) (x : M) :
    (internalDirectSum hEi hEt P).coroot ⟨c, i⟩ x =
      (P c).coroot' i (internalProjection hEi hEt c x) :=
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
  ext x
  simp only [mem_range, mem_iUnion, mem_image, Sigma.exists]
  constructor
  · rintro ⟨c, i, rfl⟩
    exact ⟨c, (P c).root i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨c, _, ⟨i, rfl⟩, rfl⟩
    exact ⟨c, i, rfl⟩

end Evaluation

/-! ### Equivalence with the external direct sum -/

section EquivPi

variable [Fintype κ]

/-- The canonical linear equivalence `(∀ c, N c) ≃ₗ[R] Module.Dual R M` pairing each coweight
summand with `E c` via `internalProjection`. -/
private noncomputable def internalDirectSumCoweightEquiv :
    (∀ c, N c) ≃ₗ[R] Module.Dual R M :=
  LinearEquiv.ofLinearMap
    (∑ c, (internalProjection hEi hEt c).dualMap.comp
      ((P c).flip.toPerfPair.toLinearMap.comp (LinearMap.proj c)))
    (LinearMap.pi fun c ↦
      (P c).flip.toPerfPair.symm.toLinearMap.comp (E c).subtype.dualMap)
    (LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.pi_apply,
        LinearMap.dualMap_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
        LinearEquiv.apply_symm_apply, Submodule.coe_subtype, LinearMap.id_apply]
      rw [← map_sum, sum_coe_internalProjection hEi hEt x])
    (LinearMap.ext fun y ↦ funext fun c ↦ by
      apply (P c).flip.toPerfPair.injective
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply, Submodule.coe_subtype,
        LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
      rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
      · simp
      · intro d _ hdc
        simp [internalProjection_apply_of_ne hEi hEt hdc.symm])

omit [NeZero (2 : R)] in
private theorem internalDirectSumCoweightEquiv_symm_apply
    (f : Module.Dual R M) (c : κ) :
    (internalDirectSumCoweightEquiv hEi hEt P).symm f c =
      (P c).flip.toPerfPair.symm (f.comp (E c).subtype) :=
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
    [∀ c, (P c).IsValuedIn S] : (internalDirectSum hEi hEt P).IsValuedIn S where
  exists_value := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    by_cases hcd : c = d
    · subst hcd
      simpa using (P c).exists_value (S := S) i j
    · exact ⟨0, by simp [internalDirectSum_pairing_ne hEi hEt P hcd]⟩

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
    (internalDirectSum hEi hEt P).IsReduced := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  have := isReduced_pi_of_isRegular P h2
  let e := piEquivInternalDirectSum hEi hEt P
  have hroot : ∀ s, e.weightEquiv ((pi P).root s) = (internalDirectSum hEi hEt P).root s :=
    fun s ↦ congrFun e.root_weightMap s
  refine ⟨fun i j hdep ↦ ?_⟩
  have hdep' : ¬ LinearIndependent R ![(pi P).root i, (pi P).root j] := fun hli ↦ hdep <| by
    convert hli.map' e.weightEquiv.toLinearMap e.weightEquiv.ker using 1
    ext k
    fin_cases k <;> exact (hroot _).symm
  rcases IsReduced.eq_or_eq_neg (P := pi P) i j hdep' with h | h
  · exact Or.inl <| by rw [← hroot i, ← hroot j, h]
  · exact Or.inr <| by rw [← hroot i, ← hroot j, h, map_neg]

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
    rintro ⟨c, i⟩
    simp only [corootForm_apply_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · have h : ∑ j : ι c,
          (internalDirectSum hEi hEt P).root' ⟨c, j⟩
            ((internalDirectSum hEi hEt P).coroot ⟨c, i⟩) *
          (internalDirectSum hEi hEt P).root' ⟨c, j⟩
            ((internalDirectSum hEi hEt P).coroot ⟨c, i⟩) =
          (P c).CorootForm ((P c).coroot i) ((P c).coroot i) := by
        simp [corootForm_apply_apply, root', root_coroot_eq_pairing]
      rw [h]
      exact IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i
    · intro d _ hdc
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp [root', internalProjection_apply_of_ne hEi hEt hdc]

end RootForm

/-! ### Bases, positive roots, cones, dominance, and chambers -/

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

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_same (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) (c : κ)
    (i j : (b c).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.1⟩, by simp [i.2]⟩ ⟨⟨c, j.1⟩, by simp [j.2]⟩ =
      (b c).cartanMatrixIn S i j := by
  simp [Base.cartanMatrixIn_def]

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_ne (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) {c d : κ} (hcd : c ≠ d)
    (i : (b c).support) (j : (b d).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.1⟩, by simp [i.2]⟩ ⟨⟨d, j.1⟩, by simp [j.2]⟩ = 0 := by
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

/-- **The positive root cone of a finite internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_posRootCone_internalDirectSum_iff (b : ∀ c, (P c).Base) (x : M) :
    x ∈ posRootCone (internalDirectSum hEi hEt P) (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ posRootCone (P c) (b c) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  have h := e.rootLE_weightMap_iff (b := Base.pi b) (Base.internalDirectSum hEi hEt b)
    (fun s ↦ by simp [e]) 0 (e.weightEquiv.symm x)
  simp only [map_zero, Equiv.weightMap_weightEquiv_symm, rootLE_zero_left_iff] at h
  rw [h, mem_posRootCone_pi_iff]
  simp [e]

/-- **Integral root dominance on a finite internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem rootLE_internalDirectSum_iff (b : ∀ c, (P c).Base) (x y : M) :
    (internalDirectSum hEi hEt P).rootLE (Base.internalDirectSum hEi hEt b) x y ↔
      ∀ c, (P c).rootLE (b c) (internalProjection hEi hEt c x)
        (internalProjection hEi hEt c y) := by
  simpa [rootLE_iff_sub_mem_posRootCone, map_sub] using
    mem_posRootCone_internalDirectSum_iff (hEi := hEi) (hEt := hEt) b (y - x)

/-- A weight of an internal direct sum is regular iff every projection is regular. -/
theorem isRegularWeight_internalDirectSum_iff (x : M) :
    (internalDirectSum hEi hEt P).IsRegularWeight x ↔
      ∀ c, (P c).IsRegularWeight (internalProjection hEi hEt c x) := by
  simp [isRegularWeight_iff, Sigma.forall]

/-- **The closed dominant chamber of an internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_dominantChamber_internalDirectSum_iff [Preorder R] (b : ∀ c, (P c).Base) (x : M) :
    x ∈ (internalDirectSum hEi hEt P).dominantChamber (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ (P c).dominantChamber (b c) := by
  simp [mem_dominantChamber, Sigma.forall]

/-- **The open dominant chamber of an internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_openDominantChamber_internalDirectSum_iff [Preorder R] (b : ∀ c, (P c).Base) (x : M) :
    x ∈ (internalDirectSum hEi hEt P).openDominantChamber (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ (P c).openDominantChamber (b c) := by
  simp [mem_openDominantChamber, Sigma.forall]

end Bases

theorem Base.support_internalDirectSum [Fintype κ] {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
    {P : ∀ c, RootPairing (ι c) R (E c) (N c)} (b : ∀ c, (P c).Base) :
    (Base.internalDirectSum hEi hEt b).support = Finset.univ.sigma fun c ↦ (b c).support := by
  ext ⟨c, i⟩
  simp

/-! ### The Weyl group of an internal direct sum -/

private theorem piEquivInternalDirectSum_weylGroupEquiv_symm_ofIdx [Fintype κ] [DecidableEq κ]
    (c : κ) (i : ι c) :
    (piEquivInternalDirectSum hEi hEt P).weylGroupEquiv.symm
        (weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩) =
      weylGroup.ofIdx (pi P) ⟨c, i⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact ((piEquivInternalDirectSum hEi hEt P).weylGroupEquiv_ofIdx ⟨c, i⟩).symm

section WeylGroup

variable [Finite κ]

/-- **The Weyl group of a finite internal direct sum is canonically isomorphic to the product of
the Weyl groups of its summands.** -/
noncomputable def internalDirectSumWeylGroupEquiv :
    (internalDirectSum hEi hEt P).weylGroup ≃* ∀ c, (P c).weylGroup :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (piEquivInternalDirectSum hEi hEt P).weylGroupEquiv.symm.trans (piWeylGroupEquiv P)

/-- The Weyl-group isomorphism acts equivariantly on every internal projection. -/
theorem internalProjection_smul_internalDirectSum
    (w : (internalDirectSum hEi hEt P).weylGroup) (c : κ) (x : M) :
    internalProjection hEi hEt c (w • x) =
      internalDirectSumWeylGroupEquiv hEi hEt P w c • internalProjection hEi hEt c x := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  have h := e.weylGroupEquiv_smul (e.weylGroupEquiv.symm w) (e.weightEquiv.symm x)
  rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  have h' := congrFun (congrArg e.weightEquiv.symm h) c
  rw [LinearEquiv.symm_apply_apply] at h'
  simpa [internalDirectSumWeylGroupEquiv, e] using h'

@[simp]
theorem internalDirectSumWeylGroupEquiv_ofIdx_self (c : κ) (i : ι c) :
    internalDirectSumWeylGroupEquiv hEi hEt P
        (weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩) c =
      weylGroup.ofIdx (P c) i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp only [internalDirectSumWeylGroupEquiv, MulEquiv.trans_apply,
    piEquivInternalDirectSum_weylGroupEquiv_symm_ofIdx, piWeylGroupEquiv_ofIdx,
    Pi.mulSingle_eq_same]

@[simp]
theorem internalDirectSumWeylGroupEquiv_ofIdx_ne {c d : κ} (hdc : d ≠ c) (i : ι c) :
    internalDirectSumWeylGroupEquiv hEi hEt P
        (weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩) d = 1 := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp only [internalDirectSumWeylGroupEquiv, MulEquiv.trans_apply,
    piEquivInternalDirectSum_weylGroupEquiv_symm_ofIdx, piWeylGroupEquiv_ofIdx,
    Pi.mulSingle_eq_of_ne hdc]

end WeylGroup

end Internal

/-! ### Decomposition of a finite root system into its irreducible components -/

section ComponentProjection

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- The internal projection onto a component space agrees with `RootPairing.componentProj`. -/
theorem internalProjection_componentSpace_eq_componentProj [P.IsRootSystem] (C : P.Component)
    (x : M) :
    internalProjection P.iSupIndep_componentSpace
        (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) C x =
      P.componentProj C x := by
  have key : internalProjection P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) C = P.componentProj C := by
    refine LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun i ↦ ?_
    by_cases hi : P.componentOf i = C
    · subst hi
      rw [internalProjection_apply_of_mem _ _ (root_mem_componentSpace i),
        componentProj_root_self]
    · rw [internalProjection_apply_eq_zero_of_mem_of_ne _ _ hi (root_mem_componentSpace i),
        componentProj_root_of_ne hi]
  exact LinearMap.congr_fun key x

end ComponentProjection

section ComponentDecomposition

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)

/-- **Canonical decomposition of a finite root system into the internal direct sum of its
irreducible component pairings** (Bourbaki, Lie VI §1, no. 2). -/
noncomputable def equivInternalDirectSumComponentPairing [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] :
    P.Equiv (internalDirectSum P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) P.componentPairing) where
  weightMap := LinearMap.id
  coweightMap := P.flip.toPerfPair.symm.toLinearMap
  indexEquiv := (_root_.Equiv.sigmaFiberEquiv P.componentOf).symm
  weight_coweight_transpose := by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ ?_
    simp
  root_weightMap := by
    ext i
    exact (coe_componentPairing_root P (P.componentOf i) ⟨i, rfl⟩).symm
  coroot_coweightMap := by
    ext ⟨C, ⟨i, hi⟩⟩
    apply P.flip.toPerfPair.injective
    refine LinearMap.ext fun x ↦ ?_
    simp only [comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, internalDirectSum_coroot, LinearMap.comp_apply,
      internalProjection_componentSpace_eq_componentProj]
    exact componentPairing_coroot'_componentProj P C ⟨i, hi⟩ x
  bijective_weightMap := Function.bijective_id
  bijective_coweightMap := LinearEquiv.bijective _

@[simp]
theorem equivInternalDirectSumComponentPairing_weightMap [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] :
    (P.equivInternalDirectSumComponentPairing).weightMap = LinearMap.id :=
  (rfl)

@[simp]
theorem equivInternalDirectSumComponentPairing_indexEquiv [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] (i : ι) :
    (P.equivInternalDirectSumComponentPairing).indexEquiv i = ⟨P.componentOf i, ⟨i, rfl⟩⟩ :=
  (rfl)

/-- **The Weyl group of a finite root system splits canonically as the product of the Weyl groups
of its irreducible components** (Bourbaki, Lie VI §1, no. 2, Proposition 5). -/
noncomputable def componentWeylGroupEquiv [NeZero (2 : K)] [Finite ι] [P.IsRootSystem] :
    P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup :=
  (P.equivInternalDirectSumComponentPairing).weylGroupEquiv.trans
    (internalDirectSumWeylGroupEquiv P.iSupIndep_componentSpace
      (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top) P.componentPairing)

/-- The component Weyl-group isomorphism intertwines the action on `M` with the component actions
along `RootPairing.componentProj`. -/
theorem componentProj_smul_eq_componentWeylGroupEquiv [NeZero (2 : K)] [Finite ι]
    [P.IsRootSystem] (w : P.weylGroup) (C : P.Component) (x : M) :
    P.componentProj C (w • x) = P.componentWeylGroupEquiv w C • P.componentProj C x := by
  have h1 := P.equivInternalDirectSumComponentPairing.weylGroupEquiv_smul w x
  have hw : (P.equivInternalDirectSumComponentPairing.weylGroupEquiv w) • x = w • x := by
    simpa [Equiv.weightEquiv_apply] using h1
  rw [← internalProjection_componentSpace_eq_componentProj, ← hw,
    internalProjection_smul_internalDirectSum, internalProjection_componentSpace_eq_componentProj]
  rfl

@[simp]
theorem componentWeylGroupEquiv_ofIdx_self [NeZero (2 : K)] [Finite ι] [P.IsRootSystem] (i : ι) :
    P.componentWeylGroupEquiv (weylGroup.ofIdx P i) (P.componentOf i) =
      weylGroup.ofIdx (P.componentPairing (P.componentOf i)) ⟨i, rfl⟩ := by
  simp [componentWeylGroupEquiv]

@[simp]
theorem componentWeylGroupEquiv_ofIdx_ne [NeZero (2 : K)] [Finite ι] [P.IsRootSystem]
    {C : P.Component} {i : ι} (hC : C ≠ P.componentOf i) :
    P.componentWeylGroupEquiv (weylGroup.ofIdx P i) C = 1 := by
  simp [componentWeylGroupEquiv, hC]

end ComponentDecomposition

end RootPairing
