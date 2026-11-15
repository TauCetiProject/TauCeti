/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Orbit-sum realizations of folded root systems

Let `P` be a finite root pairing, `b` a base of `P`, and `σ` an automorphism of `P`. The distinct
orbit sums of `σ` lie in the fixed submodule `LinearMap.fixedSubmodule σ.weightMap` and are indexed
by `RootPairing.foldedIndices P σ`. An **orbit-sum realization** (`RootPairing.OrbitSumRealization`)
is a reduced crystallographic root system on that fixed space and its linear dual, paired by
evaluation, whose roots are the orbit sums and whose chosen base consists of the orbit sums of the
simple roots of `b`.

Not every automorphism `σ : P.Aut` admits an orbit-sum realization: for `σ = s_α` on `A₁`, the
single orbit `{α, -α}` sums to `0`, which cannot be a root over a characteristic-zero ring. Even
for a based diagram automorphism, distinct root orbits can share an orbit sum when simple orbits are
not orthogonal: in `A₂` with the diagram reversal, the two-element simple orbit `{α₁, α₂}` and the
fixed highest root `{α₁ + α₂}` both sum to `α₁ + α₂`, which is why `RootPairing.foldedIndices`
indexes folded roots by their image vectors in `M`. When an orbit-sum realization does exist, it is
uniquely determined over any characteristic-zero integral domain: `evaluation` fixes the pairing
map, `root_eq` fixes the roots, and a finite root system over a characteristic-zero domain is
determined by its pairing map and its roots (`RootPairing.IsRootSystem.ext`), after which `base_eq`
fixes the base (`RootPairing.Base.ext`).

Before any orthogonality assumption on `σ`, linear independence of `b.support` already forces every
`σ`-fixed combination of simple roots to have coefficients constant on `σ`-orbits. Consequently,
for any `F : P.OrbitSumRealization b σ` over a characteristic-zero ring with `σ` permuting
`b.support`:
* the positive root cone of `(F.pairing, F.base)` is the intersection of `posRootCone P b` with the
  fixed space (`RootPairing.OrbitSumRealization.mem_posRootCone_iff`);
* a folded root is positive for `F.base` if and only if each constituent root of an orbit
  representing it is positive for `b` (`RootPairing.OrbitSumRealization.isPos_foldedIndex_iff`);
* an orbit-sum realization for `σ = 1` is canonically equivalent to `(P, b)`
  (`RootPairing.OrbitSumRealization.equivOne`), and any equivalence of root pairings transports
  orbit-sum realizations along conjugation (`RootPairing.OrbitSumRealization.map`).

## Main definitions

* `RootPairing.foldedIndex`: the orbit sum of a root index `i` packaged as a member of
  `P.foldedIndices σ`.
* `RootPairing.OrbitSumRealization`: a reduced crystallographic root system on the fixed space of
  `σ` and its dual whose roots are the orbit sums and whose simple roots are the simple-orbit sums.
* `RootPairing.OrbitSumRealization.equivOne`: the equivalence `P.Equiv F.pairing` when `σ = 1`.
* `RootPairing.OrbitSumRealization.map`: transport of an orbit-sum realization along an equivalence
  `e : P.Equiv P₂`.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: over a characteristic-zero domain, at most
  one orbit-sum realization exists for given `(P, b, σ)`.
* `RootPairing.orbitSum_eq_orbitSum_iff_of_mem_support`: over a nontrivial ring, two simple roots
  have the same orbit sum if and only if they lie in the same `σ`-orbit.
* `RootPairing.OrbitSumRealization.mem_posRootCone_iff` and
  `RootPairing.OrbitSumRealization.isPos_foldedIndex_iff`: positivity and the positive cone of any
  orbit-sum realization agree with those of `(P, b)` on the fixed space.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, §2.
-/

public section

namespace RootPairing

open Finset Set Submodule TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-! ### Packaged folded indices and simple orbits -/

section FoldedIndex

variable (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)

/-- The orbit sum of `i` under `σ`, packaged as an element of `P.foldedIndices σ`. -/
noncomputable def foldedIndex (i : ι) : P.foldedIndices σ :=
  ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩

@[simp]
theorem coe_foldedIndex (i : ι) : (P.foldedIndex σ i : M) = P.orbitSum σ i := by
  rw [foldedIndex]

@[simp]
theorem foldedIndex_indexEquiv (i : ι) :
    P.foldedIndex σ (σ.indexEquiv i) = P.foldedIndex σ i :=
  Subtype.ext (P.orbitSum_indexEquiv σ i)

theorem foldedIndex_surjective : Function.Surjective (P.foldedIndex σ) := by
  intro β
  obtain ⟨i, hi⟩ := mem_foldedIndices.mp β.2
  exact ⟨i, Subtype.ext hi⟩

theorem foldedIndex_reflectionPerm_self (i : ι) :
    (P.foldedIndex σ (P.reflectionPerm i i) : M) = -(P.foldedIndex σ i : M) :=
  P.orbitSum_reflectionPerm_self σ i

variable {P σ}

theorem foldedIndex_eq_of_mem {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.foldedIndex σ j = P.foldedIndex σ i :=
  Subtype.ext (orbitSum_eq_of_mem h)

end FoldedIndex

section SimpleOrbits

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

omit [Finite ι] in
/-- When `σ` maps `b.support` into itself, membership in `b.support` is invariant under `σ`. -/
theorem Base.indexEquiv_mem_support_iff (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {i : ι} : σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  classical
  have hmap := b.map_eq_of_forall_mem_support hσ
  refine ⟨fun hi ↦ ?_, hσ i⟩
  rw [← hmap, b.support_map_eq, Finset.mem_image] at hi
  obtain ⟨j, hj, hji⟩ := hi
  exact σ.indexEquiv.injective hji ▸ hj

/-- The `σ`-orbit of any simple root of `b` is contained in `b.support`. -/
theorem orbitIndices_subset_support (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {i : ι} (hi : i ∈ b.support) : P.orbitIndices σ i ⊆ b.support := by
  intro j hj
  obtain ⟨k, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
  clear hj
  induction k with
  | zero => simpa using hi
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hσ _ ih

/-- Over a nontrivial ring, two simple roots have the same orbit sum if and only if they belong to
the same `σ`-orbit. -/
theorem orbitSum_eq_orbitSum_iff_of_mem_support [Nontrivial R]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.orbitSum σ i = P.orbitSum σ j ↔ j ∈ P.orbitIndices σ i := by
  refine ⟨fun heq ↦ ?_, fun hmem ↦ (orbitSum_eq_of_mem hmem).symm⟩
  by_contra hnot
  classical
  let s := P.orbitIndices σ i ∪ P.orbitIndices σ j
  have hs : (s : Set ι) ⊆ b.support := by
    rw [Finset.coe_union, Set.union_subset_iff]
    exact ⟨orbitIndices_subset_support hσ hi, orbitIndices_subset_support hσ hj⟩
  let c : ι → R := fun k ↦
    (if k ∈ P.orbitIndices σ i then 1 else 0) - if k ∈ P.orbitIndices σ j then 1 else 0
  have hzero : ∑ k ∈ s, c k • P.root k = 0 := by
    simp_rw [s, c, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
    rw [← orbitSum_def, ← orbitSum_def, heq, sub_self]
  have hcj := linearIndepOn_iff'.mp b.linearIndepOn_root s c hs hzero j
    (Finset.mem_union_right _ (self_mem_orbitIndices P σ j))
  simp only [c, hnot, self_mem_orbitIndices, ↓reduceIte, zero_sub, neg_eq_zero] at hcj
  exact one_ne_zero hcj

/-- If a `σ`-fixed weight is written as an `R`-linear combination of `b.support`, its coefficients
are constant along every `σ`-orbit in `b.support`. -/
theorem eq_of_mem_orbitIndices_of_sum_smul_root_eq
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {c : ι → R} {x : M}
    (hx : σ.weightMap x = x) (hc : x = ∑ k ∈ b.support, c k • P.root k) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ P.orbitIndices σ i) : c j = c i := by
  classical
  have hstep : ∀ k ∈ b.support, c (σ.indexEquiv k) = c k := by
    have hmap : ∑ k ∈ b.support, c k • P.root (σ.indexEquiv k) =
        ∑ k ∈ b.support, c k • P.root k := by
      calc ∑ k ∈ b.support, c k • P.root (σ.indexEquiv k)
          = σ.weightMap (∑ k ∈ b.support, c k • P.root k) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun k _ ↦ by
              rw [map_smul, Hom.root_weightMap_apply P P k σ.toHom]
        _ = ∑ k ∈ b.support, c k • P.root k := by rw [← hc, hx, hc]
    have hbij : ∑ k ∈ b.support, c k • P.root (σ.indexEquiv k) =
        ∑ l ∈ b.support, c (σ.indexEquiv.symm l) • P.root l :=
      Finset.sum_nbij' σ.indexEquiv σ.indexEquiv.symm
        (fun k hk ↦ hσ k hk)
        (fun l hl ↦ (b.indexEquiv_mem_support_iff hσ).mp (by simpa using hl))
        (fun k _ ↦ σ.indexEquiv.symm_apply_apply k)
        (fun l _ ↦ σ.indexEquiv.apply_symm_apply l)
        fun k _ ↦ by rw [σ.indexEquiv.symm_apply_apply]
    have hdiff : ∑ l ∈ b.support, (c (σ.indexEquiv.symm l) - c l) • P.root l = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib, ← hbij, hmap, sub_self]
    intro k hk
    have hzk := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hdiff
      (σ.indexEquiv k) (hσ k hk)
    rw [σ.indexEquiv.symm_apply_apply, sub_eq_zero] at hzk
    exact hzk.symm
  obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
  clear hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm : (σ.indexEquiv ^ m) i ∈ b.support :=
      orbitIndices_subset_support hσ hi (mem_orbitIndices_iff_exists_pow.mpr ⟨m, rfl⟩)
    rw [pow_succ', Equiv.Perm.mul_apply, hstep _ hm, ih]

/-- For an automorphism permuting `b.support`, an orbit sum lies in the positive root cone if and
only if its representative root is positive. -/
theorem orbitSum_mem_posRootCone_iff [CharZero R]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {i : ι} :
    P.orbitSum σ i ∈ posRootCone P b ↔ b.IsPos i := by
  refine ⟨fun hmem ↦ ?_, orbitSum_mem_posRootCone hσ⟩
  by_contra hni
  have hneg : -P.orbitSum σ i ∈ posRootCone P b := by
    rw [← P.orbitSum_reflectionPerm_self σ i]
    exact orbitSum_mem_posRootCone hσ
      ((isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hni))
  exact orbitSum_ne_zero hσ i
    (eq_zero_of_add_eq_zero_of_mem_posRootCone P b hmem hneg (add_neg_cancel _))

end SimpleOrbits

/-! ### Orbit-sum realizations -/

/-- An **orbit-sum realization** of the folding of `(P, b)` by `σ`: a reduced crystallographic root
system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, paired by evaluation, whose
roots are the orbit sums `P.foldedIndices σ` and whose simple roots are the orbit sums of the
simple roots of `b`. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι] (b : P.Base) (σ : P.Aut) where
  /-- The root pairing on the fixed space and its dual, indexed by the distinct orbit sums. -/
  pairing : RootPairing (P.foldedIndices σ) R
    (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- The base of the folded root pairing formed by the orbit sums of `b.support`. -/
  base : pairing.Base
  /-- The folded roots and coroots span the fixed space and its dual. -/
  rootSystem : pairing.IsRootSystem
  /-- The folded root pairing is reduced. -/
  reduced : pairing.IsReduced
  /-- The folded root pairing is crystallographic. -/
  crystallographic : pairing.IsCrystallographic
  /-- The pairing map is evaluation of dual functionals on the fixed space. -/
  evaluation (x : LinearMap.fixedSubmodule σ.weightMap)
      (f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    pairing.toLinearMap x f = f x
  /-- Each folded root vector is the orbit sum indexing it. -/
  root_eq (β : P.foldedIndices σ) : (pairing.root β : M) = β
  /-- The simple folded roots are the orbit sums of the simple roots of `b`. -/
  base_eq (β : P.foldedIndices σ) :
    β ∈ base.support ↔ ∃ i ∈ b.support, P.orbitSum σ i = β

attribute [instance] OrbitSumRealization.rootSystem OrbitSumRealization.reduced
  OrbitSumRealization.crystallographic

namespace OrbitSumRealization

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

section Basic

variable (F : P.OrbitSumRealization b σ)

@[simp]
theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x f = f x :=
  F.evaluation x f

theorem toLinearMap_eq :
    F.pairing.toLinearMap = LinearMap.id.flip := by
  ext x f
  exact F.evaluation x f

theorem coroot'_eq_coroot (β : P.foldedIndices σ) :
    F.pairing.coroot' β = F.pairing.coroot β := by
  ext x
  exact F.evaluation x (F.pairing.coroot β)

@[simp]
theorem coe_root (β : P.foldedIndices σ) : (F.pairing.root β : M) = (β : M) :=
  F.root_eq β

theorem coe_root_foldedIndex (i : ι) :
    (F.pairing.root (P.foldedIndex σ i) : M) = P.orbitSum σ i :=
  F.root_eq (P.foldedIndex σ i)

@[simp]
theorem mem_support_base_iff (β : P.foldedIndices σ) :
    β ∈ F.base.support ↔ ∃ i ∈ b.support, P.orbitSum σ i = (β : M) :=
  F.base_eq β

theorem foldedIndex_mem_support_base {i : ι} (hi : i ∈ b.support) :
    P.foldedIndex σ i ∈ F.base.support :=
  (F.base_eq _).mpr ⟨i, hi, rfl⟩

theorem support_base_eq [DecidableEq (P.foldedIndices σ)] :
    F.base.support = b.support.image (P.foldedIndex σ) := by
  ext β
  simp only [F.base_eq, Finset.mem_image, Subtype.ext_iff, coe_foldedIndex]

end Basic

/-- Over a characteristic-zero integral domain, an orbit-sum realization is uniquely determined by
`(P, b, σ)`: its pairing map is evaluation, its roots are the orbit sums, and its base support is
fixed by `base_eq`. -/
instance instSubsingleton [CharZero R] [IsDomain R] :
    Subsingleton (P.OrbitSumRealization b σ) where
  allEq F₁ F₂ := by
    have hp : F₁.pairing = F₂.pairing := by
      refine RootPairing.IsRootSystem.ext
        (LinearMap.ext₂ fun x f ↦ (F₁.evaluation x f).trans (F₂.evaluation x f).symm) ?_
      ext β : 1
      exact Subtype.ext ((F₁.root_eq β).trans (F₂.root_eq β).symm)
    cases F₁ with | mk p₁ b₁ rs₁ red₁ crys₁ ev₁ rt₁ bs₁ =>
    cases F₂ with | mk p₂ b₂ rs₂ red₂ crys₂ ev₂ rt₂ bs₂ =>
    dsimp at hp
    subst hp
    have hb : b₁ = b₂ := by
      ext β
      exact (bs₁ β).trans (bs₂ β).symm
    subst hb
    rfl

/-! ### Positive root cone, root lattice, and positivity -/

section Positivity

variable (F : P.OrbitSumRealization b σ)

/-- Rewrite a `σ`-orbit-constant linear combination of `b.support` as a linear combination of
`F.base.support`. -/
private theorem exists_sum_support_base_eq {S : Type*} [Semiring S] [Module S M] [SMul S R]
    [IsScalarTower S R M] [Nontrivial R]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} {c : ι → S}
    (hc : (x : M) = ∑ k ∈ b.support, c k • P.root k)
    (hconst : ∀ {i j : ι}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i) :
    ∃ d : P.foldedIndices σ → S, x = ∑ β ∈ F.base.support, d β • F.pairing.root β := by
  classical
  let d : P.foldedIndices σ → S := fun β ↦
    if h : ∃ i ∈ b.support, P.foldedIndex σ i = β then c h.choose else 0
  refine ⟨d, Subtype.ext ?_⟩
  rw [Submodule.coe_sum, F.support_base_eq, hc,
    ← Finset.sum_fiberwise_of_maps_to (g := P.foldedIndex σ)
      (fun i hi ↦ Finset.mem_image_of_mem _ hi)]
  refine Finset.sum_congr rfl fun β hβ ↦ ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hβ
  have hfib : b.support.filter (fun k ↦ P.foldedIndex σ k = P.foldedIndex σ i₀) =
      P.orbitIndices σ i₀ := by
    ext k
    simp only [Finset.mem_filter, Subtype.ext_iff, coe_foldedIndex]
    exact ⟨fun ⟨hk, hki⟩ ↦ (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi₀ hk).mp hki.symm,
      fun hk ↦ ⟨orbitIndices_subset_support hσ hi₀ hk, orbitSum_eq_of_mem hk⟩⟩
  rw [hfib, Submodule.coe_smul_of_tower, F.coe_root_foldedIndex, orbitSum_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hd : d (P.foldedIndex σ i₀) = c i₀ := by
    dsimp only [d]
    split_ifs with hex
    · exact hconst hi₀ ((orbitSum_eq_orbitSum_iff_of_mem_support hσ hi₀ hex.choose_spec.1).mp
        (congrArg Subtype.val hex.choose_spec.2).symm)
    · exact False.elim (hex ⟨i₀, hi₀, rfl⟩)
  rw [hd, hconst hi₀ hk]

variable [CharZero R]

/-- A `σ`-fixed vector lies in the positive root cone of `(F.pairing, F.base)` if and only if its
underlying vector in `M` lies in `posRootCone P b`. -/
theorem mem_posRootCone_iff (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} :
    x ∈ posRootCone F.pairing F.base ↔ (x : M) ∈ posRootCone P b := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨d, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
    rw [Submodule.coe_sum]
    refine sum_mem fun β hβ ↦ ?_
    obtain ⟨i, hi, hiβ⟩ := (F.base_eq β).mp hβ
    rw [Submodule.coe_smul_of_tower, F.coe_root, ← hiβ]
    exact nsmul_mem (orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hi)) (d β)
  · obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp hx
    refine (mem_posRootCone F.pairing F.base).mpr
      (F.exists_sum_support_base_eq hσ hc fun {i j} hi hj ↦ ?_)
    have hcsum : (x : M) = ∑ k ∈ b.support, (c k : R) • P.root k := by
      simp_rw [Nat.cast_smul_eq_nsmul]; exact hc
    exact Nat.cast_injective
      (eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
        (LinearMap.mem_fixedSubmodule_iff.mp x.2) hcsum hi hj)

/-- A folded root `P.foldedIndex σ i` is positive for `F.base` if and only if `i` is positive for
`b`. -/
@[simp]
theorem isPos_foldedIndex_iff (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : ι) :
    F.base.IsPos (P.foldedIndex σ i) ↔ b.IsPos i := by
  rw [← mem_posRoots F.pairing F.base, mem_posRoots_iff_root_mem_posRootCone,
    F.mem_posRootCone_iff hσ, F.coe_root_foldedIndex, orbitSum_mem_posRootCone_iff hσ]

/-- A folded root `β` is positive for `F.base` if and only if it is the orbit sum of a positive
root of `(P, b)`. -/
theorem isPos_iff_exists_isPos (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (β : P.foldedIndices σ) :
    F.base.IsPos β ↔ ∃ i, b.IsPos i ∧ P.orbitSum σ i = (β : M) := by
  obtain ⟨i, rfl⟩ := P.foldedIndex_surjective σ β
  refine ⟨fun h ↦ ⟨i, (F.isPos_foldedIndex_iff hσ i).mp h, rfl⟩, ?_⟩
  rintro ⟨j, hj, hjβ⟩
  have hfeq : P.foldedIndex σ j = P.foldedIndex σ i := Subtype.ext hjβ
  exact hfeq ▸ (F.isPos_foldedIndex_iff hσ j).mpr hj

/-- The root lattice of any orbit-sum realization is the intersection of the root lattice of `P`
with the fixed space of `σ`. -/
theorem mem_span_int_range_root_iff (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} :
    x ∈ span ℤ (range F.pairing.root) ↔ (x : M) ∈ span ℤ (range P.root) := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨β, rfl⟩ := hy
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp β.2
      rw [F.coe_root, ← hi, orbitSum_def]
      exact sum_mem fun j _ ↦ subset_span (mem_range_self j)
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | smul z _ _ h₁ => exact Submodule.smul_mem _ z h₁
  · have hsupp : (x : M) ∈ span ℤ (P.root '' b.support) := by
      refine span_le.mpr ?_ hx
      rintro _ ⟨i, rfl⟩
      exact b.root_mem_span_int i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℤ).mp hsupp
    obtain ⟨d, rfl⟩ := F.exists_sum_support_base_eq hσ hc.symm fun {i j} hi hj ↦ by
      have hcsum : (x : M) = ∑ k ∈ b.support, (c k : R) • P.root k := by
        simp_rw [Int.cast_smul_eq_zsmul]; exact hc.symm
      exact Int.cast_injective
        (eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
          (LinearMap.mem_fixedSubmodule_iff.mp x.2) hcsum hi hj)
    exact sum_mem fun β _ ↦ Submodule.smul_mem _ (d β) (subset_span (mem_range_self β))

end Positivity

end OrbitSumRealization

/-! ### Trivial fold (`σ = 1`) and transport along equivalences -/

section One

variable (P : RootPairing ι R M N) [Finite ι]

/-- The bijection `ι ≃ P.foldedIndices 1` sending `i` to `P.root i`. -/
noncomputable def foldedIndexOneEquiv : ι ≃ P.foldedIndices 1 :=
  _root_.Equiv.ofBijective (P.foldedIndex 1)
    ⟨fun i j hij ↦ P.root.injective (by simpa [coe_foldedIndex] using congrArg Subtype.val hij),
      P.foldedIndex_surjective 1⟩

@[simp]
theorem coe_foldedIndexOneEquiv_apply (i : ι) :
    ((P.foldedIndexOneEquiv i : P.foldedIndices 1) : M) = P.root i := by
  rw [foldedIndexOneEquiv]
  exact P.orbitSum_one i

variable {P} {b : P.Base}

/-- For `σ = 1`, any orbit-sum realization of `(P, b, 1)` is canonically equivalent to `(P, b)`. -/
noncomputable def OrbitSumRealization.equivOne [P.IsRootSystem] [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b 1) : P.Equiv F.pairing :=
  Equiv.mk' P F.pairing
    { toFun := fun x ↦ ⟨x, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    P.foldedIndexOneEquiv
    fun i ↦ Subtype.ext (by rw [F.coe_root, coe_foldedIndexOneEquiv_apply]; rfl)

@[simp]
theorem OrbitSumRealization.equivOne_indexEquiv [P.IsRootSystem] [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b 1) : F.equivOne.indexEquiv = P.foldedIndexOneEquiv := by
  rw [OrbitSumRealization.equivOne]
  rfl

theorem OrbitSumRealization.coe_equivOne_weightEquiv [P.IsRootSystem] [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b 1) (x : M) :
    (F.equivOne.weightEquiv x : M) = x := by
  rw [OrbitSumRealization.equivOne]
  rfl

@[simp]
theorem OrbitSumRealization.map_equivOne [P.IsRootSystem] [CharZero R] [IsDomain R]
    (F : P.OrbitSumRealization b 1) : b.map F.equivOne = F.base := by
  classical
  ext β
  rw [b.support_map_eq, F.mem_support_base_iff, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by simp⟩
  · rintro ⟨i, hi, hiβ⟩
    refine ⟨i, hi, Subtype.ext ?_⟩
    simpa using hiβ

end One

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}

/-- An equivalence `e : P.Equiv P₂` maps `LinearMap.fixedSubmodule σ.weightMap` linearly and
bijectively onto `LinearMap.fixedSubmodule (e.autCongr σ).weightMap`. -/
noncomputable def Equiv.fixedSubmoduleEquiv (e : P.Equiv P₂) (σ : P.Aut) :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R]
      LinearMap.fixedSubmodule (e.autCongr σ).weightMap where
  toFun x := ⟨e.weightEquiv (x : M), LinearMap.mem_fixedSubmodule_iff.mpr <| by
    have hx := LinearMap.mem_fixedSubmodule_iff.mp x.2
    rw [← Equiv.weightEquiv_apply (e.autCongr σ), Equiv.weightEquiv_autCongr_apply,
      LinearEquiv.symm_apply_apply, Equiv.weightEquiv_apply σ, hx]⟩
  invFun y := ⟨e.weightEquiv.symm (y : M₂), LinearMap.mem_fixedSubmodule_iff.mpr <| by
    have hy := LinearMap.mem_fixedSubmodule_iff.mp y.2
    apply e.weightEquiv.injective
    rw [← Equiv.weightEquiv_apply σ, ← Equiv.weightEquiv_autCongr_apply e σ (y : M₂),
      Equiv.weightEquiv_apply (e.autCongr σ), hy, LinearEquiv.apply_symm_apply]⟩
  map_add' x y := Subtype.ext (map_add e.weightEquiv (x : M) (y : M))
  map_smul' r x := Subtype.ext (map_smul e.weightEquiv r (x : M))
  left_inv x := Subtype.ext (e.weightEquiv.symm_apply_apply (x : M))
  right_inv y := Subtype.ext (e.weightEquiv.apply_symm_apply (y : M₂))

@[simp]
theorem Equiv.coe_fixedSubmoduleEquiv_apply (e : P.Equiv P₂) (σ : P.Aut)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (e.fixedSubmoduleEquiv σ x : M₂) = e.weightEquiv x := by
  rw [Equiv.fixedSubmoduleEquiv]
  rfl

variable [Finite ι] [Finite ι₂]

theorem Equiv.weightEquiv_orbitSum (e : P.Equiv P₂) (σ : P.Aut) (i : ι) :
    e.weightEquiv (P.orbitSum σ i) = P₂.orbitSum (e.autCongr σ) (e.indexEquiv i) := by
  rw [Equiv.weightEquiv_apply]
  exact weightMap_orbitSum e (σ := σ) (τ := e.autCongr σ)
    (fun j ↦ by rw [Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply]) i

/-- An equivalence `e : P.Equiv P₂` identifies the orbit sums of `σ` with those of `e.autCongr σ`.
-/
noncomputable def Equiv.foldedIndicesEquiv (e : P.Equiv P₂) (σ : P.Aut) :
    P.foldedIndices σ ≃ P₂.foldedIndices (e.autCongr σ) where
  toFun β := ⟨e.weightEquiv (β : M), mem_foldedIndices.mpr <| by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp β.2
    exact ⟨e.indexEquiv i, by rw [← hi, e.weightEquiv_orbitSum]⟩⟩
  invFun γ := ⟨e.weightEquiv.symm (γ : M₂), mem_foldedIndices.mpr <| by
    obtain ⟨j, hj⟩ := mem_foldedIndices.mp γ.2
    refine ⟨e.indexEquiv.symm j, e.weightEquiv.injective ?_⟩
    rw [e.weightEquiv_orbitSum, e.indexEquiv.apply_symm_apply, e.weightEquiv.apply_symm_apply, hj]⟩
  left_inv β := Subtype.ext (e.weightEquiv.symm_apply_apply (β : M))
  right_inv γ := Subtype.ext (e.weightEquiv.apply_symm_apply (γ : M₂))

@[simp]
theorem Equiv.coe_foldedIndicesEquiv_apply (e : P.Equiv P₂) (σ : P.Aut)
    (β : P.foldedIndices σ) :
    ((e.foldedIndicesEquiv σ β : P₂.foldedIndices (e.autCongr σ)) : M₂) = e.weightEquiv β := by
  rw [Equiv.foldedIndicesEquiv]
  rfl

@[simp]
theorem Equiv.coe_foldedIndicesEquiv_symm_apply (e : P.Equiv P₂) (σ : P.Aut)
    (γ : P₂.foldedIndices (e.autCongr σ)) :
    (((e.foldedIndicesEquiv σ).symm γ : P.foldedIndices σ) : M) = e.weightEquiv.symm γ := by
  rw [Equiv.foldedIndicesEquiv]
  rfl

@[simp]
theorem Equiv.foldedIndicesEquiv_foldedIndex (e : P.Equiv P₂) (σ : P.Aut) (i : ι) :
    e.foldedIndicesEquiv σ (P.foldedIndex σ i) =
      P₂.foldedIndex (e.autCongr σ) (e.indexEquiv i) :=
  Subtype.ext (by rw [Equiv.coe_foldedIndicesEquiv_apply, coe_foldedIndex, coe_foldedIndex,
    e.weightEquiv_orbitSum])

namespace OrbitSumRealization

variable {b : P.Base} {σ : P.Aut}

private theorem mapPairing_toLinearMap (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ)
    (x : LinearMap.fixedSubmodule (e.autCongr σ).weightMap)
    (g : Module.Dual R (LinearMap.fixedSubmodule (e.autCongr σ).weightMap)) :
    (F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
        (e.fixedSubmoduleEquiv σ).symm.dualMap).toLinearMap x g = g x := by
  change F.pairing.toLinearMap ((e.fixedSubmoduleEquiv σ).symm x)
    ((e.fixedSubmoduleEquiv σ).symm.dualMap.symm g) = g x
  rw [F.toLinearMap_apply]
  change g (e.fixedSubmoduleEquiv σ ((e.fixedSubmoduleEquiv σ).symm x)) = g x
  rw [LinearEquiv.apply_symm_apply]

private noncomputable def mapPairingEquiv (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ) :
    F.pairing.Equiv
      (F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
        (e.fixedSubmoduleEquiv σ).symm.dualMap) :=
  let fE := e.fixedSubmoduleEquiv σ
  let fN := fE.symm.dualMap
  { weightMap := fE.toLinearMap
    coweightMap := fN.symm.toLinearMap
    indexEquiv := e.foldedIndicesEquiv σ
    weight_coweight_transpose := by
      ext g x
      change (F.pairing.map (e.foldedIndicesEquiv σ) fE fN).flip.toLinearMap g (fE x) =
        F.pairing.flip.toLinearMap (fN.symm g) x
      rw [RootPairing.flip_toLinearMap, LinearMap.flip_apply, mapPairing_toLinearMap,
        RootPairing.flip_toLinearMap, LinearMap.flip_apply, F.toLinearMap_apply]
      rfl
    root_weightMap := funext fun β ↦
      congrArg (fun k ↦ fE (F.pairing.root k)) ((e.foldedIndicesEquiv σ).symm_apply_apply β).symm
    coroot_coweightMap := funext fun γ ↦
      fN.symm_apply_apply (F.pairing.coroot ((e.foldedIndicesEquiv σ).symm γ))
    bijective_weightMap := fE.bijective
    bijective_coweightMap := fN.symm.bijective }

/-- Transport an orbit-sum realization along an equivalence `e : P.Equiv P₂`, conjugating `σ` to
`e.autCongr σ` and pushing `b` forward to `b.map e`. -/
noncomputable def map (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ) :
    P₂.OrbitSumRealization (b.map e) (e.autCongr σ) :=
  let hEquiv := mapPairingEquiv e F
  { pairing := F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
      (e.fixedSubmoduleEquiv σ).symm.dualMap
    base := F.base.map hEquiv
    rootSystem := inferInstance
    reduced := ⟨fun γ₁ γ₂ hdep ↦ by
      have hdep' : ¬LinearIndependent R
          ![F.pairing.root ((e.foldedIndicesEquiv σ).symm γ₁),
            F.pairing.root ((e.foldedIndicesEquiv σ).symm γ₂)] := by
        have hli := hEquiv.toHom.linearIndependent_root_indexEquiv_iff
          hEquiv.bijective_weightMap.injective
          ((e.foldedIndicesEquiv σ).symm γ₁) ((e.foldedIndicesEquiv σ).symm γ₂)
        dsimp only [hEquiv, mapPairingEquiv] at hli
        rw [(e.foldedIndicesEquiv σ).apply_symm_apply,
          (e.foldedIndicesEquiv σ).apply_symm_apply] at hli
        exact hli.not.mp hdep
      rcases IsReduced.eq_or_eq_neg (P := F.pairing) ((e.foldedIndicesEquiv σ).symm γ₁)
          ((e.foldedIndicesEquiv σ).symm γ₂) hdep' with h | h
      · exact .inl (congrArg (e.fixedSubmoduleEquiv σ) h)
      · right
        change e.fixedSubmoduleEquiv σ (F.pairing.root ((e.foldedIndicesEquiv σ).symm γ₁)) =
          -e.fixedSubmoduleEquiv σ (F.pairing.root ((e.foldedIndicesEquiv σ).symm γ₂))
        rw [h, map_neg]⟩
    crystallographic := hEquiv.toHom.isValuedIn ℤ
    evaluation := mapPairing_toLinearMap e F
    root_eq := fun γ ↦ by
      change (e.fixedSubmoduleEquiv σ (F.pairing.root ((e.foldedIndicesEquiv σ).symm γ)) : M₂) = γ
      rw [Equiv.coe_fixedSubmoduleEquiv_apply, F.coe_root, Equiv.coe_foldedIndicesEquiv_symm_apply,
        e.weightEquiv.apply_symm_apply]
    base_eq := fun γ ↦ by
      classical
      rw [F.base.support_map_eq, b.support_map_eq, Finset.mem_image]
      dsimp only [hEquiv, mapPairingEquiv]
      refine ⟨?_, ?_⟩
      · rintro ⟨β, hβ, rfl⟩
        obtain ⟨i, hi, hiβ⟩ := (F.base_eq β).mp hβ
        exact ⟨e.indexEquiv i, Finset.mem_image_of_mem _ hi, by
          rw [Equiv.coe_foldedIndicesEquiv_apply, ← hiβ, e.weightEquiv_orbitSum]⟩
      · rintro ⟨j, hj, hjγ⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        refine ⟨P.foldedIndex σ i, F.foldedIndex_mem_support_base hi, ?_⟩
        rw [e.foldedIndicesEquiv_foldedIndex]
        exact Subtype.ext ((P₂.coe_foldedIndex _ _).trans hjγ) }

/-- Over a characteristic-zero domain, any equivalence `e : P.Equiv P₂` intertwining `σ` and `τ`
induces an equivalence between orbit-sum realizations of `(P, b, σ)` and `(P₂, b₂, τ)`. -/
noncomputable def equivOfEquiv [CharZero R] [IsDomain R] (e : P.Equiv P₂) {b₂ : P₂.Base}
    {τ : P₂.Aut} (hσ : e.autCongr σ = τ)
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) :
    F₁.pairing.Equiv F₂.pairing := by
  cases hσ
  exact Equiv.mk' F₁.pairing F₂.pairing
    (e.fixedSubmoduleEquiv σ)
    (e.foldedIndicesEquiv σ)
    fun β ↦ Subtype.ext <| by
      rw [Equiv.coe_fixedSubmoduleEquiv_apply, F₁.coe_root, F₂.coe_root,
        Equiv.coe_foldedIndicesEquiv_apply]

theorem map_equivOfEquiv [CharZero R] [IsDomain R] (e : P.Equiv P₂) {b₂ : P₂.Base}
    {τ : P₂.Aut} (hb : b.map e = b₂) (hσ : e.autCongr σ = τ)
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) :
    F₁.base.map (equivOfEquiv e hσ F₁ F₂) = F₂.base := by
  classical
  cases hb
  cases hσ
  have hidx : (equivOfEquiv e rfl F₁ F₂).indexEquiv = e.foldedIndicesEquiv σ := by
    rw [equivOfEquiv]
    rfl
  ext γ
  rw [F₁.base.support_map_eq, F₂.mem_support_base_iff, Finset.mem_image, hidx]
  refine ⟨?_, ?_⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨i, hi, hiβ⟩ := (F₁.base_eq β).mp hβ
    refine ⟨e.indexEquiv i, by rw [b.support_map_eq]; exact Finset.mem_image_of_mem _ hi, ?_⟩
    rw [Equiv.coe_foldedIndicesEquiv_apply, ← hiβ, e.weightEquiv_orbitSum]
  · rintro ⟨j, hj, hjγ⟩
    rw [b.support_map_eq, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    refine ⟨P.foldedIndex σ i, F₁.foldedIndex_mem_support_base hi, ?_⟩
    rw [e.foldedIndicesEquiv_foldedIndex]
    exact Subtype.ext ((P₂.coe_foldedIndex _ _).trans hjγ)

end OrbitSumRealization

end Map

end RootPairing
