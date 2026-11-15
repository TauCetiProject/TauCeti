/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.Folding.Realization
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.Data.Finset.NoncommProd
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.UniqueScale
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# The orthogonal orbit-sum fold of a simply-laced root system

Let `P` be a finite reduced crystallographic root system over a linearly ordered field `K` (such as
`ℝ`), `b` a base of `P` whose Cartan matrix is simply laced, and `σ` an automorphism of `P`
permuting the simple roots of `b` such that distinct simple roots in each `σ`-orbit are pairwise
orthogonal. Following Stembridge (*Folding by automorphisms*, 2008), this file constructs the
folded root system `RootPairing.orthogonalFold` as an `OrbitSumRealization` on the fixed submodule
`LinearMap.fixedSubmodule σ.weightMap` and establishes its metric, Cartan, and reflection formulas:

* **Component-normalized invariant form** (`RootPairing.simplyLacedForm`): rescaling the canonical
  positive-definite root form on each irreducible component gives the unique positive-definite
  invariant form taking value `2` on every root, invariant under all automorphisms of `P`.
* **Commuting block reflections** (`RootPairing.orbitReflection`): for any pairwise-orthogonal
  `σ`-orbit, the commuting product of its reflections in `P.weylGroup` is an involution in
  `P.weylGroup` commuting with `σ` that acts on `σ`-fixed weights `x` as
  `x - P.coroot' i x • P.orbitSum σ i`.
* **Height descent and Stembridge's Claim 4** (`RootPairing.pairing_eq_zero_of_mem_orbitIndices`,
  `RootPairing.isOrthogonal_of_mem_orbitIndices`): positive height descent under the simple block
  reflections moves every root into `b.support`, transporting pairwise orthogonality from the simple
  `σ`-orbits to *every* root `σ`-orbit. Consequently each orbit sum `P.orbitSum σ r` has squared
  norm `2 * #(P.orbitIndices σ r)` (`RootPairing.simplyLacedForm_orbitSum_self`), and two indices
  have the same orbit sum if and only if they lie in the same `σ`-orbit
  (`RootPairing.foldedIndex_eq_iff_mem_orbitIndices`).
* **The orthogonal fold** (`RootPairing.orthogonalFold`): the unique `P.OrbitSumRealization b σ`,
  together with the formulas valid on *any* `F : P.OrbitSumRealization b σ`:
  - `F.coroot'_foldedIndex_apply`: `F.pairing.coroot' (P.foldedIndex σ r) x = P.coroot' r x`;
  - `F.pairingIn_foldedIndex`: the folded Cartan pairing is `∑ k ∈ P.orbitIndices σ r, ⟨αₖ, αₜ^∨⟩`;
  - `F.card_orbitIndices_mul_pairingIn_foldedIndex` and `F.pairing_foldedIndex_eq_neg_card_div`:
    for distinct simple orbits `O, T`, `⟨βₒ, βₜ^∨⟩ = -N_{O, T} / |T|` where `N_{O, T}` counts
    non-orthogonal pairs between `O` and `T` (with `|T|`, not `|O|`, in the denominator);
  - `F.coe_reflection_foldedIndex`: reflection in `P.foldedIndex σ r` restricts
    `P.orbitReflection σ r` to the fixed submodule.

## Main definitions

* `RootPairing.simplyLacedForm`: the positive-definite invariant form normalized to `2` on every
  root of a finite simply-laced root system.
* `RootPairing.orbitReflection`: the commuting product of reflections over a `σ`-orbit in
  `P.weylGroup`.
* `RootPairing.orthogonalFold`: the `OrbitSumRealization` of an orthogonal diagram fold.

## Main results

* `RootPairing.InvariantForm.apply_root_root_eq_of_componentOf_eq`: when `b.cartanMatrix` is simply
  laced, every invariant form is constant on the roots of each irreducible component.
* `RootPairing.commute_coe_orbitReflection` and `RootPairing.orbitReflection_smul_of_fixed`: block
  reflections commute with `σ` and act as rank-one reflections along orbit sums on fixed weights.
* `RootPairing.pairing_eq_zero_of_mem_orbitIndices` and
  `RootPairing.isOrthogonal_of_mem_orbitIndices`: every root `σ`-orbit is pairwise orthogonal
  (Stembridge, Claim 4).
* `RootPairing.simplyLacedForm_orbitSum_self`: `(βₒ, βₒ) = 2 * |O|`.
* `RootPairing.OrbitSumRealization.coroot'_foldedIndex_apply`,
  `RootPairing.OrbitSumRealization.pairing_foldedIndex_eq_neg_card_div`, and
  `RootPairing.OrbitSumRealization.coe_reflection_foldedIndex`: coroot, oriented Cartan, and
  reflection comparisons for any `OrbitSumRealization`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, equations (1)--(3) and
  Claims 1 and 4, pages 1--3.
-/

public section

namespace RootPairing

open Finset Function Set Submodule TauCeti

/-! ### Component-normalized invariant form on a simply-laced root system -/

section SimplyLacedForm

section CommRing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsReduced] [P.IsCrystallographic]

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsReduced] in
/-- Along a walk in `diagramGraph b.cartanMatrix` of a simply-laced base `b`, any invariant form
assigns equal squared lengths to the simple roots. -/
private theorem apply_simpleRoot_eq_of_reachable (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) {u v : b.support}
    (h : (diagramGraph b.cartanMatrix).Reachable u v) :
    B.form (P.root u) (P.root u) = B.form (P.root v) (P.root v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | @cons a c d hadj _ ih =>
    rw [← ih]
    obtain ⟨hne, hmat, hmat'⟩ := diagramGraph_adj.mp hadj
    have hac : b.cartanMatrix a c = -1 := (hsl hne).resolve_left hmat
    have hca : b.cartanMatrix c a = -1 := (hsl hne.symm).resolve_left hmat'
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have hswap := B.pairing_mul_eq_pairing_mul_swap (a : ι) c
    rw [hp c a hca, hp a c hac] at hswap
    linear_combination -hswap

/-- Every root `k` has the same squared length under `B` as a simple root in its irreducible
component. -/
private theorem exists_mem_support_apply_root_eq (B : P.InvariantForm) (b : P.Base) (k : ι) :
    ∃ s : b.support, P.componentOf (s : ι) = P.componentOf k ∧
      B.form (P.root k) (P.root k) = B.form (P.root s) (P.root s) := by
  refine b.induction_reflect k
    (p := fun k ↦ ∃ s : b.support, P.componentOf (s : ι) = P.componentOf k ∧
      B.form (P.root k) (P.root k) = B.form (P.root s) (P.root s))
    (fun i ⟨s, hcomp, hlen⟩ ↦ ⟨s, hcomp.trans (componentOf_reflectionPerm i i).symm, by
      rw [root_reflectionPerm, B.apply_reflection_reflection, hlen]⟩)
    (fun i hi ↦ ⟨⟨i, hi⟩, rfl, rfl⟩)
    (fun i j ⟨s, hcomp, hlen⟩ _ ↦ ⟨s, hcomp.trans (componentOf_reflectionPerm j i).symm, by
      rw [root_reflectionPerm, B.apply_reflection_reflection, hlen]⟩)

/-- **Equal root lengths on each component.** When `b.cartanMatrix` is simply laced, every invariant
form on `P` takes the same value `B(α, α)` on all roots belonging to the same irreducible
component. -/
theorem InvariantForm.apply_root_root_eq_of_componentOf_eq (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) {i j : ι} (hij : P.componentOf i = P.componentOf j) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  obtain ⟨s₁, hc₁, hl₁⟩ := exists_mem_support_apply_root_eq B b i
  obtain ⟨s₂, hc₂, hl₂⟩ := exists_mem_support_apply_root_eq B b j
  have hreach : P.nonorthogonalGraph.Reachable (s₁ : ι) (s₂ : ι) :=
    SimpleGraph.ConnectedComponent.exact (hc₁.trans (hij.trans hc₂.symm))
  rw [hl₁, hl₂]
  exact apply_simpleRoot_eq_of_reachable B b hsl (b.reachable_nonorthogonalGraph_iff.mp hreach)

end CommRing

section OrderedField

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

omit [Finite ι] in
private theorem toInvariantForm_posDef [Fintype ι] :
    P.toInvariantForm.form.toQuadraticMap.PosDef :=
  P.rootForm_posDef

/-- Auxiliary positive-definite invariant form bundled with its positivity proof, rescaling
`P.toInvariantForm` to `2` on a representative root of each component. -/
private noncomputable def simplyLacedFormPair :
    {B : P.InvariantForm // B.form.toQuadraticMap.PosDef} :=
  letI := Fintype.ofFinite ι
  (InvariantForm.posDefEquivScale P.toInvariantForm (toInvariantForm_posDef P)).symm fun C ↦
    ⟨2 / P.toInvariantForm.form (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some),
      div_pos two_pos (P.rootForm_posDef _ (P.ne_zero _))⟩

/-- **Component-normalized invariant form.** Rescales `P.toInvariantForm` on each irreducible
component so that a representative root of that component has squared length `2`. When `P` admits a
base `b` with `b.cartanMatrix.IsSimplyLaced`, every root has squared length `2`
(`RootPairing.simplyLacedForm_root_self`), making `P.simplyLacedForm` the unique invariant form with
`B(αᵢ, αᵢ) = 2` for all `i` (`RootPairing.eq_simplyLacedForm_of_root_self`), independent of `b` and
of the component representatives. -/
noncomputable def simplyLacedForm : P.InvariantForm :=
  P.simplyLacedFormPair.1

/-- `P.simplyLacedForm` is positive definite. -/
theorem posDef_simplyLacedForm : P.simplyLacedForm.form.toQuadraticMap.PosDef :=
  P.simplyLacedFormPair.2

section SimplyLaced

variable [P.IsReduced] [P.IsCrystallographic]

theorem simplyLacedForm_root_self (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    P.simplyLacedForm.form (P.root i) (P.root i) = 2 := by
  rw [simplyLacedForm, simplyLacedFormPair,
    InvariantForm.form_posDefEquivScale_symm_apply_of_mem _ _ _
      (root_mem_componentSpace i) (root_mem_componentSpace i)]
  let : Fintype ι := Fintype.ofFinite ι
  have hcomp : P.componentOf (P.componentOf i).nonempty_supp.some = P.componentOf i :=
    ((P.componentOf i).mem_supp_iff _).mp (P.componentOf i).nonempty_supp.some_mem
  have heq := P.toInvariantForm.apply_root_root_eq_of_componentOf_eq b hsimply hcomp
  dsimp only
  rw [heq, div_mul_cancel₀ _ (P.toInvariantForm.ne_zero i)]

/-- Pairing against `P.root i` under `P.simplyLacedForm` coincides with the coroot functional
`P.coroot' i` when `b.cartanMatrix` is simply laced. -/
theorem simplyLacedForm_apply_root (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (x : M) (i : ι) :
    P.simplyLacedForm.form x (P.root i) = P.coroot' i x := by
  have h := P.simplyLacedForm.two_mul_apply_root x i
  rw [P.simplyLacedForm_root_self b hsimply i, mul_comm (P.coroot' i x)] at h
  exact mul_left_cancel₀ two_ne_zero h

theorem simplyLacedForm_root_apply (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (i : ι) (x : M) :
    P.simplyLacedForm.form (P.root i) x = P.coroot' i x := by
  have hsymm : P.simplyLacedForm.form (P.root i) x = P.simplyLacedForm.form x (P.root i) := by
    simpa using (P.simplyLacedForm.symm.eq x (P.root i)).symm
  rw [hsymm, P.simplyLacedForm_apply_root b hsimply]

/-- Uniqueness of `P.simplyLacedForm`: when `b.cartanMatrix` is simply laced, any invariant form
taking value `2` on every root equals `P.simplyLacedForm`. -/
theorem eq_simplyLacedForm_of_root_self (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    {B : P.InvariantForm} (hB : ∀ i, B.form (P.root i) (P.root i) = 2) :
    B = P.simplyLacedForm := by
  refine (InvariantForm.componentEquiv (P := P)).injective (funext fun C ↦ ?_)
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hcomp : P.componentOf i = C := (C.mem_supp_iff i).mp hi
  ext x y
  have hscale : InvariantForm.componentScale P.simplyLacedForm B C = 1 := by
    rw [← hcomp, InvariantForm.componentScale_eq_div, hB i,
      P.simplyLacedForm_root_self b hsimply i, div_self two_ne_zero]
  simp [InvariantForm.form_apply_eq_componentScale_mul P.simplyLacedForm B x.2 y.2, hscale]

/-- Every automorphism of a simply-laced root system `P` preserves `P.simplyLacedForm`. -/
theorem simplyLacedForm_weightMap (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (g : P.Aut) (x y : M) :
    P.simplyLacedForm.form (g.weightMap x) (g.weightMap y) = P.simplyLacedForm.form x y := by
  have hcomap : InvariantForm.comap g.toHom P.simplyLacedForm = P.simplyLacedForm :=
    P.eq_simplyLacedForm_of_root_self b hsimply fun i ↦ by
      rw [InvariantForm.comap_form_apply, g.toHom.root_weightMap_apply,
        P.simplyLacedForm_root_self b hsimply]
  simpa [InvariantForm.comap_form_apply] using
    congrArg (fun B : P.InvariantForm ↦ B.form x y) hcomap

end SimplyLaced

end OrderedField

end SimplyLacedForm

/-! ### Commuting block reflections -/

section OrbitReflection

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι]

/-- Auxiliary reindexing rule for `Finset.noncommProd` along an embedding. -/
private theorem noncommProd_map {α α' β : Type*} [Monoid β] (s : Finset α) (e : α ↪ α')
    (f : α' → β) (comm : ((s.map e : Finset α') : Set α').Pairwise (Commute on f)) :
    (s.map e).noncommProd f comm =
      s.noncommProd (fun x ↦ f (e x)) (fun _ hx _ hy hne ↦
        comm (mem_map_of_mem e hx) (mem_map_of_mem e hy) (e.injective.ne hne)) := by
  simp_rw [Finset.noncommProd, Finset.map_val, Multiset.map_map]
  rfl

omit [Finite ι] in
/-- Reflections in pairwise orthogonal roots pairwise commute in `P.weylGroup`. -/
theorem pairwise_commute_of_isOrthogonal {S : Finset ι}
    (hS : (S : Set ι).Pairwise P.IsOrthogonal) :
    (S : Set ι).Pairwise (Commute on weylGroup.ofIdx P) :=
  fun _ hj _ hk hne ↦ weylGroup.commute_ofIdx_of_isOrthogonal P (hS hj hk hne)

omit [Finite ι] in
/-- Auxiliary action formula for a commuting product of pairwise orthogonal root reflections. -/
private theorem noncommProd_ofIdx_smul {S : Finset ι}
    (hS : (S : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    S.noncommProd (weylGroup.ofIdx P) (pairwise_commute_of_isOrthogonal P hS) • x =
      x - ∑ j ∈ S, P.coroot' j x • P.root j := by
  induction S using Finset.cons_induction with
  | empty => rw [Finset.noncommProd_empty, one_smul, Finset.sum_empty, sub_zero]
  | cons a s ha ih =>
    rw [Finset.noncommProd_cons, mul_smul, ih (hS.mono (by intro z hz; exact mem_cons_of_mem hz)),
      weylGroup.ofIdx_smul, Equiv.reflection_smul, map_sub, map_sum, P.reflection_apply]
    have hfix : ∑ j ∈ s, (P.reflection a) (P.coroot' j x • P.root j) =
        ∑ j ∈ s, P.coroot' j x • P.root j :=
      Finset.sum_congr rfl fun j hj ↦ by
        rw [map_smul, (hS (mem_cons_self a s) (mem_cons_of_mem hj)
          (ne_of_mem_of_not_mem hj ha).symm).reflection_apply_right]
    rw [hfix, Finset.sum_cons, sub_sub]

omit [Finite ι] in
/-- Auxiliary involution identity for a commuting product of reflections in `P.weylGroup`. -/
private theorem noncommProd_ofIdx_mul_self {S : Finset ι}
    (hcomm : (S : Set ι).Pairwise (Commute on weylGroup.ofIdx P)) :
    S.noncommProd (weylGroup.ofIdx P) hcomm * S.noncommProd (weylGroup.ofIdx P) hcomm = 1 := by
  rw [← Finset.noncommProd_mul_distrib (weylGroup.ofIdx P) (weylGroup.ofIdx P) hcomm hcomm hcomm]
  exact (Finset.noncommProd_eq_pow_card S _ _ 1
    fun j _ ↦ weylGroup.ofIdx_mul_self P j).trans (one_pow _)

/-- The **orbit reflection** attached to `i : ι` under `σ`: when the reflections of
`P.orbitIndices σ i` pairwise commute in `P.weylGroup`, this is their commuting product in
`P.weylGroup` (and `1` otherwise). -/
noncomputable def orbitReflection (σ : P.Aut) (i : ι) : P.weylGroup := by
  classical
  exact if h : (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P) then
    (P.orbitIndices σ i).noncommProd (weylGroup.ofIdx P) h
  else 1

@[simp]
theorem orbitReflection_indexEquiv (σ : P.Aut) (i : ι) :
    P.orbitReflection σ (σ.indexEquiv i) = P.orbitReflection σ i := by
  classical
  exact congrArg
    (fun S : Finset ι ↦ if h : (S : Set ι).Pairwise (Commute on weylGroup.ofIdx P) then
      S.noncommProd (weylGroup.ofIdx P) h else 1)
    (P.orbitIndices_indexEquiv σ i)

variable {P} in
theorem orbitReflection_eq_of_mem {σ : P.Aut} {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.orbitReflection σ j = P.orbitReflection σ i := by
  classical
  exact congrArg
    (fun S : Finset ι ↦ if hc : (S : Set ι).Pairwise (Commute on weylGroup.ofIdx P) then
      S.noncommProd (weylGroup.ofIdx P) hc else 1)
    (P.orbitIndices_eq_of_mem h)

@[simp]
theorem orbitReflection_one (i : ι) : P.orbitReflection 1 i = weylGroup.ofIdx P i := by
  have hcomm : (({i} : Finset ι) : Set ι).Pairwise (Commute on weylGroup.ofIdx P) := by
    norm_cast
    exact Set.pairwise_singleton _ _
  simp only [orbitReflection, P.orbitIndices_one, hcomm, ↓reduceDIte, Finset.noncommProd_singleton]

section OrthogonalOrbit

variable {P} {σ : P.Aut} {i : ι}

/-- When `P.orbitIndices σ i` is pairwise orthogonal, `P.orbitReflection σ i` is the commuting
product of `weylGroup.ofIdx P j` over `j ∈ P.orbitIndices σ i`. -/
theorem orbitReflection_eq_noncommProd
    (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal) :
    P.orbitReflection σ i = (P.orbitIndices σ i).noncommProd (weylGroup.ofIdx P)
      (pairwise_commute_of_isOrthogonal P horth) := by
  classical
  simp only [orbitReflection, pairwise_commute_of_isOrthogonal P horth, ↓reduceDIte]

/-- An orthogonal orbit reflection has order dividing `2` in `P.weylGroup`. -/
theorem orbitReflection_mul_self (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal) :
    P.orbitReflection σ i * P.orbitReflection σ i = 1 := by
  rw [P.orbitReflection_eq_noncommProd horth]
  exact noncommProd_ofIdx_mul_self P _

theorem orbitReflection_inv (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal) :
    (P.orbitReflection σ i)⁻¹ = P.orbitReflection σ i :=
  inv_eq_iff_mul_eq_one.mpr (P.orbitReflection_mul_self horth)

/-- **Block reflections commute with `σ`.** Conjugating `P.orbitReflection σ i` by `σ` permutes its
commuting reflection factors along `σ.indexEquiv`, leaving the product unchanged. -/
theorem commute_coe_orbitReflection (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal) :
    Commute (P.orbitReflection σ i : P.Aut) σ := by
  have hcomm := pairwise_commute_of_isOrthogonal P horth
  have hfix : σ.weylGroupEquiv (P.orbitReflection σ i) = P.orbitReflection σ i := by
    rw [P.orbitReflection_eq_noncommProd horth, Finset.map_noncommProd]
    have hmap : (P.orbitIndices σ i).map σ.indexEquiv.toEmbedding = P.orbitIndices σ i :=
      (P.map_orbitIndices σ (fun _ ↦ rfl) i).trans (P.orbitIndices_indexEquiv σ i)
    have hcomm' : (((P.orbitIndices σ i).map σ.indexEquiv.toEmbedding : Finset ι) : Set ι).Pairwise
        (Commute on weylGroup.ofIdx P) := by
      rw [hmap]
      exact hcomm
    refine (Finset.noncommProd_congr rfl
      (fun j _ ↦ σ.weylGroupEquiv_ofIdx j) _).trans ?_
    exact (noncommProd_map (P.orbitIndices σ i) σ.indexEquiv.toEmbedding
      (weylGroup.ofIdx P) hcomm').symm.trans (Finset.noncommProd_congr hmap (fun _ _ ↦ rfl) _)
  have haut : σ * (P.orbitReflection σ i : P.Aut) * σ⁻¹ = (P.orbitReflection σ i : P.Aut) := by
    have hcoe := congrArg (Subtype.val : P.weylGroup → P.Aut) hfix
    rw [Equiv.coe_weylGroupEquiv, Equiv.autCongr_apply] at hcoe
    exact mul_assoc σ (P.orbitReflection σ i : P.Aut) σ⁻¹ ▸ hcoe
  exact Commute.symm (mul_inv_eq_iff_eq_mul.mp haut)

/-- Action of `P.orbitReflection σ i` on any ambient weight `x : M`. -/
theorem orbitReflection_smul (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    (x : M) :
    P.orbitReflection σ i • x = x - ∑ j ∈ P.orbitIndices σ i, P.coroot' j x • P.root j := by
  rw [P.orbitReflection_eq_noncommProd horth, noncommProd_ofIdx_smul P horth]

/-- On a `σ`-fixed weight `x`, all coroots in a `σ`-orbit take the same value. -/
theorem coroot'_eq_of_mem_orbitIndices_of_fixed {x : M} (hx : σ.weightMap x = x)
    {j : ι} (hj : j ∈ P.orbitIndices σ i) : P.coroot' j x = P.coroot' i x := by
  obtain ⟨m, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hj
  clear hj
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← hx, σ.toHom.coroot'_weightMap, hx, ih]

/-- **Action of `P.orbitReflection σ i` on `σ`-fixed weights.** On `E^σ`, the commuting block
reflection acts as the rank-one reflection subtracting `P.coroot' i x • P.orbitSum σ i`. -/
theorem orbitReflection_smul_of_fixed (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    {x : M} (hx : σ.weightMap x = x) :
    P.orbitReflection σ i • x = x - P.coroot' i x • P.orbitSum σ i := by
  rw [P.orbitReflection_smul horth, P.orbitSum_def, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦ by rw [P.coroot'_eq_of_mem_orbitIndices_of_fixed hx hj]

/-- For a pairwise orthogonal `σ`-orbit, `P.coroot' i (P.orbitSum σ i) = 2`. -/
theorem coroot'_orbitSum_self (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal) :
    P.coroot' i (P.orbitSum σ i) = 2 := by
  classical
  rw [P.orbitSum_def, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j hj hne
    rw [root_coroot'_eq_pairing, (horth hj (P.self_mem_orbitIndices σ i) hne).1]
  · exact fun h ↦ (h (P.self_mem_orbitIndices σ i)).elim

/-- `P.orbitReflection σ i` negates every root in `P.orbitIndices σ i`. -/
theorem weylGroupToPerm_orbitReflection_self
    (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    {j : ι} (hj : j ∈ P.orbitIndices σ i) :
    P.weylGroupToPerm (P.orbitReflection σ i) j = P.reflectionPerm j j := by
  classical
  apply P.root.injective
  rw [← P.weylGroup_apply_root, P.orbitReflection_smul horth, Finset.sum_eq_single j,
    root_coroot'_eq_pairing, pairing_same, root_reflectionPerm, reflection_apply_self]
  · abel_nf
    rw [two_smul]
    abel
  · intro k hk hne
    rw [root_coroot'_eq_pairing, (horth hj hk hne.symm).1, zero_smul]
  · exact fun h ↦ (h hj).elim

/-- Any element `w : P.weylGroup` commuting with `σ` permutes `σ`-orbits via
`P.weylGroupToPerm w`. -/
theorem map_orbitIndices_of_commute {w : P.weylGroup} (hw : Commute (w : P.Aut) σ) (r : ι) :
    (P.orbitIndices σ r).map (P.weylGroupToPerm w).toEmbedding =
      P.orbitIndices σ (P.weylGroupToPerm w r) := by
  have hidx (j : ι) : (w : P.Aut).indexEquiv (σ.indexEquiv j) =
      σ.indexEquiv ((w : P.Aut).indexEquiv j) :=
    congrArg (fun g : P.Aut ↦ g.indexEquiv j) hw.eq
  exact P.map_orbitIndices (w : P.Aut) hidx r

/-- Any element `w : P.weylGroup` commuting with `σ` carries `P.orbitSum σ r` to
`P.orbitSum σ (P.weylGroupToPerm w r)`. -/
theorem smul_orbitSum_of_commute {w : P.weylGroup} (hw : Commute (w : P.Aut) σ) (r : ι) :
    w • P.orbitSum σ r = P.orbitSum σ (P.weylGroupToPerm w r) := by
  have hidx (j : ι) : (w : P.Aut).indexEquiv (σ.indexEquiv j) =
      σ.indexEquiv ((w : P.Aut).indexEquiv j) :=
    congrArg (fun g : P.Aut ↦ g.indexEquiv j) hw.eq
  exact P.weightMap_orbitSum (w : P.Aut) hidx r

end OrthogonalOrbit

end OrbitReflection

/-! ### Height descent, Stembridge Claim 4, and orbit-sum norms -/

section OrthogonalFold

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]

section Descent

variable {P} {b : P.Base} {σ : P.Aut}

omit [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] in
/-- Under the simple-orbit orthogonality hypothesis, the `σ`-orbit of any simple root is pairwise
`P.IsOrthogonal`. -/
theorem isOrthogonal_orbitIndices_of_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s : ι} (hs : s ∈ b.support) :
    (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal := by
  intro j hj k hk hne
  have hj' : j ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs hj
  have hk' : k ∈ P.orbitIndices σ j := (P.orbitIndices_eq_of_mem hj).symm ▸ hk
  exact P.isOrthogonal_iff_pairing_eq_zero.mpr (horth j hj' k hk' hne)

/-- Under `P.simplyLacedForm`, pairing a `σ`-fixed weight `x` against `P.orbitSum σ r` multiplies
`P.coroot' r x` by `#(P.orbitIndices σ r)`. -/
theorem simplyLacedForm_apply_orbitSum_of_fixed (b : P.Base)
    (hsimply : b.cartanMatrix.IsSimplyLaced) {σ : P.Aut} {x : M} (hx : σ.weightMap x = x) (r : ι) :
    P.simplyLacedForm.form x (P.orbitSum σ r) = #(P.orbitIndices σ r) * P.coroot' r x := by
  rw [P.orbitSum_def, map_sum]
  have hterm (j : ι) (hj : j ∈ P.orbitIndices σ r) :
      P.simplyLacedForm.form x (P.root j) = P.coroot' r x := by
    rw [P.simplyLacedForm_apply_root b hsimply, P.coroot'_eq_of_mem_orbitIndices_of_fixed hx hj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- Every positive orbit sum has positive pairing with at least one simple coroot. -/
private theorem exists_mem_support_coroot'_orbitSum_pos
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced) {r : ι} (hr : b.IsPos r) :
    ∃ s ∈ b.support, 0 < P.coroot' s (P.orbitSum σ r) := by
  have hpos : 0 < P.simplyLacedForm.form (P.orbitSum σ r) (P.orbitSum σ r) :=
    P.posDef_simplyLacedForm _ (P.orbitSum_ne_zero hσ r)
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp (P.orbitSum_mem_posRootCone hσ hr)
  have hexp : P.simplyLacedForm.form (P.orbitSum σ r) (P.orbitSum σ r) =
      ∑ s ∈ b.support, f s • P.coroot' s (P.orbitSum σ r) := by
    conv_lhs =>
      arg 1
      rw [hf]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun s _ ↦ by
      rw [map_nsmul, LinearMap.smul_apply, P.simplyLacedForm_root_apply b hsimply]
  rw [hexp] at hpos
  by_contra! hle
  exact hpos.not_ge (Finset.sum_nonpos fun s hs ↦ nsmul_nonpos (hle s hs) (f s))

/-- Auxiliary arithmetic: if a sum of squares of natural numbers over `S` equals `1`, one summand
equals `1` and all other summands vanish. -/
private theorem exists_eq_one_of_sum_mul_self_eq_one {α : Type*} {S : Finset α} {f : α → ℕ}
    (h : ∑ k ∈ S, f k * f k = 1) :
    ∃ k₀ ∈ S, f k₀ = 1 ∧ ∀ k ∈ S, k ≠ k₀ → f k = 0 := by
  classical
  have hne : ∃ k₀ ∈ S, f k₀ * f k₀ ≠ 0 := by
    by_contra! h0
    rw [Finset.sum_eq_zero fun k hk ↦ h0 k hk] at h
    omega
  obtain ⟨k₀, hk₀, hfk₀⟩ := hne
  rw [← Finset.add_sum_erase S (fun k ↦ f k * f k) hk₀] at h
  have hrest : ∑ k ∈ S.erase k₀, f k * f k = 0 := by omega
  have hone : f k₀ = 1 := by nlinarith
  refine ⟨k₀, hk₀, hone, fun k hk hne' ↦ ?_⟩
  have hk0 : f k * f k = 0 :=
    (Finset.sum_eq_zero_iff.mp hrest) k (Finset.mem_erase.mpr ⟨hne', hk⟩)
  nlinarith

/-- If a positive root `r` has zero simple-root coordinate outside an orthogonal simple orbit
`P.orbitIndices σ s`, then `r` belongs to `P.orbitIndices σ s`. -/
private theorem mem_orbitIndices_of_isPos_of_repr_eq_zero
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s r : ι} (hs : s ∈ b.support) (hr : b.IsPos r)
    (hzero : ∀ t : b.support, (t : ι) ∉ P.orbitIndices σ s →
      b.toWeightBasis.repr (P.root r) t = 0) :
    r ∈ P.orbitIndices σ s := by
  classical
  obtain ⟨f, -, hf⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b r).mpr hr)
  have hrepr (t : b.support) : b.toWeightBasis.repr (P.root r) t = (f t : K) := by
    rw [hf, ← Finset.sum_coe_sort b.support, map_sum, Finsupp.finsetSum_apply]
    simp_rw [← b.toWeightBasis_apply, map_nsmul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply]
    simp
  have hsub : P.root r = ∑ k ∈ P.orbitIndices σ s, f k • P.root k := by
    rw [hf]
    refine (Finset.sum_subset (fun k hk ↦ P.mem_support_of_mem_orbitIndices hσ hs hk) ?_).symm
    intro k hk hnot
    have hfk : (f k : K) = 0 := (hrepr ⟨k, hk⟩).symm.trans (hzero ⟨k, hk⟩ hnot)
    rw [Nat.cast_eq_zero.mp hfk, zero_smul]
  have horth_s := P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs
  have hnorm : P.simplyLacedForm.form (P.root r) (P.root r) =
      ((2 * ∑ k ∈ P.orbitIndices σ s, f k * f k : ℕ) : K) := by
    conv_lhs => rw [hsub]
    simp only [map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.sum_eq_single k]
    · rw [P.simplyLacedForm_root_self b hsimply k]
      push_cast
      simp only [nsmul_eq_mul]
      ring
    · intro l hl hlk
      rw [P.simplyLacedForm_apply_root b hsimply (P.root l) k, P.root_coroot'_eq_pairing k l,
        (horth_s hl hk hlk).1, nsmul_zero]
    · exact fun h ↦ (h hk).elim
  rw [P.simplyLacedForm_root_self b hsimply r] at hnorm
  have hsq : ∑ k ∈ P.orbitIndices σ s, f k * f k = 1 := by
    have h2 : 2 * ∑ k ∈ P.orbitIndices σ s, f k * f k = 2 := by exact_mod_cast hnorm.symm
    omega
  obtain ⟨k₀, hk₀, hfk₀, hrest⟩ := exists_eq_one_of_sum_mul_self_eq_one hsq
  have hroot : P.root r = P.root k₀ := by
    rw [hsub, Finset.sum_eq_single k₀, hfk₀, one_smul]
    · exact fun k hk hne ↦ by rw [hrest k hk hne, zero_smul]
    · exact fun h ↦ (h hk₀).elim
  exact P.root.injective hroot ▸ hk₀

omit [P.IsReduced] [P.IsCrystallographic] in
/-- All roots in a `σ`-orbit have equal height, so `heightLinearMap` on `P.orbitSum σ r` equals
`#(P.orbitIndices σ r) * b.height r`. -/
private theorem heightLinearMap_orbitSum
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (r : ι) :
    heightLinearMap P b (P.orbitSum σ r) = #(P.orbitIndices σ r) * (b.height r : K) := by
  have hht (j : ι) (hj : j ∈ P.orbitIndices σ r) : b.height j = b.height r := by
    obtain ⟨m, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hj
    clear hj
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, b.height_indexEquiv σ hσ, ih]
  rw [P.orbitSum_def, map_sum]
  have hterm (j : ι) (hj : j ∈ P.orbitIndices σ r) :
      heightLinearMap P b (P.root j) = (b.height r : K) := by
    rw [heightLinearMap_root, hht j hj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- **Height descent step.** Applying a simple block reflection `P.orbitReflection σ s` with
`0 < P.coroot' s (P.orbitSum σ r)` to a positive root `r` either witnesses `r ∈ P.orbitIndices σ s`
or produces a positive root of strictly smaller height. -/
private theorem mem_orbitIndices_or_height_lt
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s r : ι} (hs : s ∈ b.support) (hr : b.IsPos r)
    (hpos : 0 < P.coroot' s (P.orbitSum σ r)) :
    r ∈ P.orbitIndices σ s ∨
      (b.IsPos (P.weylGroupToPerm (P.orbitReflection σ s) r) ∧
        b.height (P.weylGroupToPerm (P.orbitReflection σ s) r) < b.height r) := by
  have horth_s := P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs
  have hcomm_s := P.commute_coe_orbitReflection horth_s
  set r' := P.weylGroupToPerm (P.orbitReflection σ s) r
  by_cases hr' : b.IsPos r'
  · right
    refine ⟨hr', ?_⟩
    have horb : P.orbitSum σ r' =
        P.orbitSum σ r - P.coroot' s (P.orbitSum σ r) • P.orbitSum σ s := by
      rw [← P.smul_orbitSum_of_commute hcomm_s r,
        P.orbitReflection_smul_of_fixed horth_s (P.weightMap_orbitSum_self σ r)]
    have hcard : #(P.orbitIndices σ r') = #(P.orbitIndices σ r) := by
      rw [← P.map_orbitIndices_of_commute hcomm_s r, Finset.card_map]
    have hht := congrArg (heightLinearMap P b) horb
    rw [map_sub, map_smul, smul_eq_mul, P.heightLinearMap_orbitSum hσ r',
      P.heightLinearMap_orbitSum hσ r, P.heightLinearMap_orbitSum hσ s,
      b.height_eq_one_iff.mpr hs, Int.cast_one, mul_one, hcard] at hht
    have hd_pos : (0 : K) < #(P.orbitIndices σ r) := Nat.cast_pos.mpr (P.card_orbitIndices_pos σ r)
    have hs_pos : (0 : K) < #(P.orbitIndices σ s) := Nat.cast_pos.mpr (P.card_orbitIndices_pos σ s)
    have hltK : (b.height r' : K) < (b.height r : K) := by
      nlinarith [mul_pos hpos hs_pos, hd_pos]
    exact Int.cast_lt.mp hltK
  · left
    refine P.mem_orbitIndices_of_isPos_of_repr_eq_zero hσ hsimply horth hs hr fun t ht ↦ ?_
    have hge : 0 ≤ b.toWeightBasis.repr (P.root r) t :=
      toWeightBasis_repr_nonneg_of_mem_posRootCone
        (root_mem_posRootCone_of_mem_posRoots P b ((mem_posRoots P b r).mpr hr)) t
    have hneg : P.root (P.reflectionPerm r' r') ∈ posRootCone P b :=
      root_mem_posRootCone_of_mem_posRoots P b ((mem_posRoots P b _).mpr
        ((isPos_reflectionPerm_self_iff_mem_negRoots P b r').mpr ((mem_negRoots P b r').mpr hr')))
    have hle' : 0 ≤ b.toWeightBasis.repr (-P.root r') t := by
      simpa [root_reflectionPerm] using toWeightBasis_repr_nonneg_of_mem_posRootCone hneg t
    have heq_coord : b.toWeightBasis.repr (P.root r') t = b.toWeightBasis.repr (P.root r) t := by
      have hroot' : P.root r' = P.root r - ∑ k ∈ P.orbitIndices σ s,
          P.coroot' k (P.root r) • P.root k := by
        rw [← P.weylGroup_apply_root, P.orbitReflection_smul horth_s]
      rw [hroot', map_sub, map_sum, Finsupp.sub_apply, Finsupp.finsetSum_apply]
      have hsum0 : ∑ k ∈ P.orbitIndices σ s,
          b.toWeightBasis.repr (P.coroot' k (P.root r) • P.root k) t = 0 :=
        Finset.sum_eq_zero fun k hk ↦ by
          have hkb : k ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs hk
          have hne : (⟨k, hkb⟩ : b.support) ≠ t := fun h ↦ ht (h ▸ hk)
          rw [map_smul, ← b.toWeightBasis_apply ⟨k, hkb⟩, Module.Basis.repr_self,
            Finsupp.smul_apply, Finsupp.single_eq_of_ne hne.symm, smul_zero]
      rw [hsum0, sub_zero]
    rw [map_neg, Finsupp.neg_apply, heq_coord, Left.nonneg_neg_iff] at hle'
    exact le_antisymm hle' hge

omit [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] in
/-- Every element of `Subgroup.closure (P.orbitReflection σ '' b.support)` commutes with `σ`. -/
private theorem commute_of_mem_closure_orbitReflection
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {w : P.weylGroup} (hw : w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι))) :
    Commute (w : P.Aut) σ := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, rfl⟩ := hg
    exact P.commute_coe_orbitReflection (P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs)
  | one => simp
  | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_left ih₂
  | inv _ _ ih => exact ih.inv_left

/-- **Simple-orbit generation of root orbits.** The subgroup of `P.weylGroup` generated by the
simple block reflections `P.orbitReflection σ s` (`s ∈ b.support`) moves every root index into
`b.support`. -/
theorem exists_mem_closure_orbitReflection_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    ∃ w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι)),
      P.weylGroupToPerm w r ∈ b.support := by
  have hpos_case : ∀ n : ℕ, ∀ q : ι, b.IsPos q → (b.height q).toNat ≤ n →
      ∃ w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι)),
        P.weylGroupToPerm w q ∈ b.support := by
    intro n
    induction n with
    | zero =>
      intro q hq hle
      have := one_le_height_of_mem_posRoots P b ((mem_posRoots P b q).mpr hq)
      omega
    | succ n ih =>
      intro q hq hle
      obtain ⟨s, hs, hsp⟩ := P.exists_mem_support_coroot'_orbitSum_pos hσ hsimply hq
      rcases P.mem_orbitIndices_or_height_lt hσ hsimply horth hs hq hsp with hmem | ⟨hq', hlt⟩
      · exact ⟨1, Subgroup.one_mem _, P.mem_support_of_mem_orbitIndices hσ hs hmem⟩
      · have hpos' := one_le_height_of_mem_posRoots P b ((mem_posRoots P b _).mpr hq')
        obtain ⟨w', hw', hsupp⟩ := ih _ hq' (by omega)
        refine ⟨w' * P.orbitReflection σ s,
          Subgroup.mul_mem _ hw' (Subgroup.subset_closure ⟨s, hs, rfl⟩), ?_⟩
        simpa [map_mul] using hsupp
  by_cases hr : b.IsPos r
  · exact hpos_case (b.height r).toNat r hr le_rfl
  · have hr₀ : b.IsPos (P.reflectionPerm r r) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hr)
    obtain ⟨w₀, hw₀, hs₀⟩ := hpos_case _ _ hr₀ le_rfl
    set s₀ := P.weylGroupToPerm w₀ (P.reflectionPerm r r)
    have hneg : P.weylGroupToPerm w₀ r = P.reflectionPerm s₀ s₀ := by
      apply P.root.injective
      rw [← P.weylGroup_apply_root, root_reflectionPerm, reflection_apply_self,
        ← P.weylGroup_apply_root, root_reflectionPerm, reflection_apply_self, smul_neg, neg_neg]
    have hs₀_fix : P.weylGroupToPerm (P.orbitReflection σ s₀) (P.reflectionPerm s₀ s₀) = s₀ := by
      -- `orbitReflection σ s₀` is an involution negating `s₀`, so it sends `-s₀` back to `s₀`.
      apply P.root.injective
      rw [← P.weylGroup_apply_root, root_reflectionPerm, reflection_apply_self, smul_neg,
        P.weylGroup_apply_root, P.weylGroupToPerm_orbitReflection_self
          (P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs₀) (P.self_mem_orbitIndices σ s₀),
        root_reflectionPerm, reflection_apply_self, neg_neg]
    refine ⟨P.orbitReflection σ s₀ * w₀,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨s₀, hs₀, rfl⟩) hw₀, ?_⟩
    rw [map_mul, _root_.Equiv.Perm.mul_apply, hneg, hs₀_fix]
    exact hs₀

/-- **Stembridge's Claim 4.** In a finite simply-laced root system, if `σ` permutes `b.support` with
pairwise orthogonal simple orbits, then *every* root `σ`-orbit is pairwise orthogonal. -/
theorem pairing_eq_zero_of_mem_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j : ι} (hj : j ∈ P.orbitIndices σ r) (hne : r ≠ j) :
    P.pairing r j = 0 := by
  obtain ⟨w, hw, hs⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r
  have hcomm := P.commute_of_mem_closure_orbitReflection hσ horth hw
  have hj' : P.weylGroupToPerm w j ∈ P.orbitIndices σ (P.weylGroupToPerm w r) := by
    rw [← P.map_orbitIndices_of_commute hcomm r]
    exact mem_map_of_mem _ hj
  have hne' : P.weylGroupToPerm w r ≠ P.weylGroupToPerm w j :=
    (P.weylGroupToPerm w).injective.ne hne
  have hpair : P.pairing ((w : P.Aut).indexEquiv r) ((w : P.Aut).indexEquiv j) = P.pairing r j :=
    (w : P.Aut).toHom.pairing
  exact hpair.symm.trans (horth _ hs _ hj' hne')

/-- Pairwise `P.IsOrthogonal` formulation of Stembridge's Claim 4 for every root orbit. -/
theorem isOrthogonal_of_mem_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal := by
  intro j hj k hk hne
  have hk' : k ∈ P.orbitIndices σ j := (P.orbitIndices_eq_of_mem hj).symm ▸ hk
  exact P.isOrthogonal_iff_pairing_eq_zero.mpr
    (P.pairing_eq_zero_of_mem_orbitIndices hσ hsimply horth hk' hne)

/-- **Squared norm of an orbit sum** (Stembridge, equation (2)): under `P.simplyLacedForm`, each
orbit sum `P.orbitSum σ r` has squared norm `2 * #(P.orbitIndices σ r)`. -/
theorem simplyLacedForm_orbitSum_self
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    P.simplyLacedForm.form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * #(P.orbitIndices σ r) := by
  rw [P.simplyLacedForm_apply_orbitSum_of_fixed b hsimply (P.weightMap_orbitSum_self σ r) r,
    P.coroot'_orbitSum_self (P.isOrthogonal_of_mem_orbitIndices hσ hsimply horth r), mul_comm]

/-- If a positive root's orbit sum is a scalar multiple of a simple root's orbit sum, the scalar is
`1` and the root lies in that simple orbit. -/
private theorem eq_one_and_mem_of_isPos_of_orbitSum_eq_smul
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r s : ι} {c : K} (hr : b.IsPos r) (hs : s ∈ b.support)
    (heq : P.orbitSum σ r = c • P.orbitSum σ s) :
    c = 1 ∧ r ∈ P.orbitIndices σ s := by
  classical
  have hmem : r ∈ P.orbitIndices σ s := by
    refine P.mem_orbitIndices_of_isPos_of_repr_eq_zero hσ hsimply horth hs hr fun t ht ↦ ?_
    have hsum0 : ∑ j ∈ P.orbitIndices σ r, b.toWeightBasis.repr (P.root j) t = 0 := by
      have h1 := congrArg (fun v ↦ b.toWeightBasis.repr v t) heq
      rw [P.orbitSum_def, map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul, P.toWeightBasis_repr_orbitSum_of_mem_support hσ t.2 hs] at h1
      simpa only [ht, ↓reduceIte, mul_zero] using h1
    have hnn (j : ι) (hj : j ∈ P.orbitIndices σ r) : 0 ≤ b.toWeightBasis.repr (P.root j) t :=
      toWeightBasis_repr_nonneg_of_mem_posRootCone
        (root_mem_posRootCone_of_mem_posRoots P b
          ((mem_posRoots P b j).mpr ((P.isPos_iff_of_mem_orbitIndices hσ hj).mpr hr))) t
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 r (P.self_mem_orbitIndices σ r)
  have horb := P.orbitSum_eq_of_mem hmem
  rw [horb] at heq
  have hc : c - 1 = 0 := by
    have h0 : (c - 1) • P.orbitSum σ s = 0 := by
      rw [sub_smul, one_smul, ← heq, sub_self]
    exact (smul_eq_zero.mp h0).resolve_right (P.orbitSum_ne_zero hσ s)
  exact ⟨sub_eq_zero.mp hc, hmem⟩

/-- **Proportionality of orbit sums.** Under the orthogonal-fold hypotheses, `P.orbitSum σ r₁ =
c • P.orbitSum σ r₂` implies `(c = 1 ∧ r₁ ∈ P.orbitIndices σ r₂)` or
`(c = -1 ∧ r₁ ∈ P.orbitIndices σ (P.reflectionPerm r₂ r₂))`. -/
theorem eq_one_or_neg_one_of_orbitSum_eq_smul
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r₁ r₂ : ι} {c : K} (heq : P.orbitSum σ r₁ = c • P.orbitSum σ r₂) :
    (c = 1 ∧ r₁ ∈ P.orbitIndices σ r₂) ∨
      (c = -1 ∧ r₁ ∈ P.orbitIndices σ (P.reflectionPerm r₂ r₂)) := by
  obtain ⟨w, hw, hs⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r₂
  have hcomm := P.commute_of_mem_closure_orbitReflection hσ horth hw
  set r₁' := P.weylGroupToPerm w r₁
  set s := P.weylGroupToPerm w r₂
  have heq' : P.orbitSum σ r₁' = c • P.orbitSum σ s := by
    rw [← P.smul_orbitSum_of_commute hcomm r₁, ← P.smul_orbitSum_of_commute hcomm r₂, heq,
      smul_comm]
  have hpull {a b₀ : ι} (hm : P.weylGroupToPerm w a ∈ P.orbitIndices σ (P.weylGroupToPerm w b₀)) :
      a ∈ P.orbitIndices σ b₀ := by
    rw [← P.map_orbitIndices_of_commute hcomm b₀] at hm
    simpa using hm
  by_cases hpos : b.IsPos r₁'
  · obtain ⟨rfl, hm⟩ := P.eq_one_and_mem_of_isPos_of_orbitSum_eq_smul hσ hsimply horth hpos hs heq'
    exact .inl ⟨rfl, hpull hm⟩
  · have hpos_neg : b.IsPos (P.reflectionPerm r₁' r₁') :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r₁').mpr ((mem_negRoots P b r₁').mpr hpos)
    have heq_neg : P.orbitSum σ (P.reflectionPerm r₁' r₁') = (-c) • P.orbitSum σ s := by
      rw [P.orbitSum_reflectionPerm_self, heq', neg_smul]
    obtain ⟨hc, hm⟩ :=
      P.eq_one_and_mem_of_isPos_of_orbitSum_eq_smul hσ hsimply horth hpos_neg hs heq_neg
    have hneg_pull : r₁' ∈ P.orbitIndices σ (P.reflectionPerm s s) := by
      obtain ⟨m, hm⟩ := P.mem_orbitIndices_iff_exists_pow.mp hm
      have hpow (n : ℕ) : (σ.indexEquiv ^ n) (P.reflectionPerm s s) =
          P.reflectionPerm ((σ.indexEquiv ^ n) s) ((σ.indexEquiv ^ n) s) := by
        induction n with
        | zero => simp
        | succ n ih =>
          simp only [pow_succ', _root_.Equiv.Perm.mul_apply, ih,
            σ.toHom.indexEquiv_reflectionPerm]
      refine P.mem_orbitIndices_iff_exists_pow.mpr ⟨m, ?_⟩
      rw [hpow m, hm, P.reflectionPerm_reflectionPerm_self]
    have hs_neg : P.reflectionPerm s s = P.weylGroupToPerm w (P.reflectionPerm r₂ r₂) :=
      ((w : P.Aut).toHom.indexEquiv_reflectionPerm r₂ r₂).symm
    exact .inr ⟨by linear_combination -hc, hpull (hs_neg ▸ hneg_pull)⟩

/-- **Injectivity of orbit sums on `σ`-orbits.** Under the orthogonal-fold hypotheses, two root
indices define the same folded root index if and only if they belong to the same `σ`-orbit. -/
theorem foldedIndex_eq_iff_mem_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r₁ r₂ : ι) :
    P.foldedIndex σ r₁ = P.foldedIndex σ r₂ ↔ r₁ ∈ P.orbitIndices σ r₂ := by
  refine ⟨fun h ↦ ?_, P.foldedIndex_eq_of_mem⟩
  have heq : P.orbitSum σ r₁ = (1 : K) • P.orbitSum σ r₂ := by
    simpa [coe_foldedIndex] using congrArg Subtype.val h
  rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth heq with ⟨-, hm⟩ | ⟨hc, -⟩
  · exact hm
  · exfalso; norm_num at hc

end Descent

/-! ### Construction of the orthogonal fold -/

section Construction

variable (b : P.Base) (σ : P.Aut)

omit [LinearOrder K] [IsStrictOrderedRing K] [P.IsRootSystem] [P.IsReduced]
  [P.IsCrystallographic] in
/-- Root embedding of `P.foldedIndices σ` into `LinearMap.fixedSubmodule σ.weightMap`. -/
private def foldedRootEmb :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap :=
  ⟨fun u ↦ ⟨(u : M), P.coe_mem_fixedSubmodule σ u⟩,
    fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) h)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] [P.IsRootSystem] [P.IsReduced]
  [P.IsCrystallographic] in
@[simp]
private theorem coe_foldedRootEmb (u : P.foldedIndices σ) :
    (P.foldedRootEmb σ u : M) = (u : M) :=
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] [P.IsRootSystem] [P.IsReduced]
  [P.IsCrystallographic] in
private theorem coe_foldedRootEmb_foldedIndex (r : ι) :
    (P.foldedRootEmb σ (P.foldedIndex σ r) : M) = P.orbitSum σ r :=
  P.coe_foldedIndex σ r

omit [P.IsReduced] [P.IsCrystallographic] in
/-- Candidate coroot functional attached to `u : P.foldedIndices σ`, defined directly on `E^σ` from
`P.simplyLacedForm` without choosing an orbit representative. -/
private noncomputable def foldedCorootFun
    (u : P.foldedIndices σ) : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
  (2 / P.simplyLacedForm.form (u : M) (u : M)) •
    (P.simplyLacedForm.form.flip (u : M)).comp (LinearMap.fixedSubmodule σ.weightMap).subtype

private theorem foldedCorootFun_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun σ (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  have hx : σ.weightMap (x : M) = (x : M) := LinearMap.mem_fixedSubmodule_iff.mp x.2
  have hd : (#(P.orbitIndices σ r) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.card_orbitIndices_pos σ r).ne'
  rw [foldedCorootFun, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    P.simplyLacedForm.form.flip_apply, smul_eq_mul, P.coe_foldedIndex,
    P.simplyLacedForm_orbitSum_self hσ hsimply horth r,
    P.simplyLacedForm_apply_orbitSum_of_fixed b hsimply hx r]
  field_simp

private theorem foldedCorootFun_injective
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    Injective (P.foldedCorootFun σ) := by
  intro u₁ u₂ h
  obtain ⟨r₁, rfl⟩ := P.foldedIndex_surjective σ u₁
  obtain ⟨r₂, rfl⟩ := P.foldedIndex_surjective σ u₂
  have hpos₁ : 0 < P.simplyLacedForm.form (P.orbitSum σ r₁) (P.orbitSum σ r₁) :=
    P.posDef_simplyLacedForm _ (P.orbitSum_ne_zero hσ r₁)
  have hpos₂ : 0 < P.simplyLacedForm.form (P.orbitSum σ r₂) (P.orbitSum σ r₂) :=
    P.posDef_simplyLacedForm _ (P.orbitSum_ne_zero hσ r₂)
  set c₁ : K := 2 / P.simplyLacedForm.form (P.orbitSum σ r₁) (P.orbitSum σ r₁)
  set c₂ : K := 2 / P.simplyLacedForm.form (P.orbitSum σ r₂) (P.orbitSum σ r₂)
  set z : LinearMap.fixedSubmodule σ.weightMap :=
    c₁ • P.foldedRootEmb σ (P.foldedIndex σ r₁) - c₂ • P.foldedRootEmb σ (P.foldedIndex σ r₂)
  have hz_coe : (z : M) = c₁ • P.orbitSum σ r₁ - c₂ • P.orbitSum σ r₂ := by
    simp [z]
  have hz : P.simplyLacedForm.form (z : M) (z : M) = 0 := by
    have heval : c₁ * P.simplyLacedForm.form (z : M) (P.orbitSum σ r₁) =
        c₂ * P.simplyLacedForm.form (z : M) (P.orbitSum σ r₂) := by
      simpa [foldedCorootFun, coe_foldedIndex, c₁, c₂] using LinearMap.congr_fun h z
    calc P.simplyLacedForm.form (z : M) (z : M)
        = c₁ * P.simplyLacedForm.form (z : M) (P.orbitSum σ r₁) -
            c₂ * P.simplyLacedForm.form (z : M) (P.orbitSum σ r₂) := by
            conv_lhs =>
              arg 2
              rw [hz_coe]
            rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      _ = 0 := sub_eq_zero.mpr heval
  have hz0 : (z : M) = 0 := by
    by_contra hne
    exact (P.posDef_simplyLacedForm (z : M) hne).ne' hz
  have hc₁ : 0 < c₁ := div_pos two_pos hpos₁
  have hc₂ : 0 < c₂ := div_pos two_pos hpos₂
  have hsmul : P.orbitSum σ r₁ = (c₁⁻¹ * c₂) • P.orbitSum σ r₂ := by
    have hsub : c₁ • P.orbitSum σ r₁ = c₂ • P.orbitSum σ r₂ :=
      sub_eq_zero.mp (hz_coe ▸ hz0)
    rw [← inv_smul_smul₀ hc₁.ne' (P.orbitSum σ r₁), hsub, smul_smul]
  rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth hsmul with ⟨_, hm⟩ | ⟨hc, -⟩
  · exact P.foldedIndex_eq_of_mem hm
  · exfalso
    linarith [mul_pos (inv_pos.mpr hc₁) hc₂]

/-- Auxiliary construction of the folded `RootPairing` via `RootPairing.mk''`. -/
private noncomputable def orthogonalFoldPairing
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  let corootEmb : P.foldedIndices σ ↪ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
    ⟨P.foldedCorootFun σ, P.foldedCorootFun_injective b σ hσ hsimply horth⟩
  RootPairing.mk'' (Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap))
    (P.foldedRootEmb σ) corootEmb
    (fun u ↦ by
      obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
      rw [Module.Dual.eval_apply]
      exact (P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r _).trans
        (by rw [coe_foldedRootEmb_foldedIndex]; exact
          P.coroot'_orbitSum_self (P.isOrthogonal_of_mem_orbitIndices hσ hsimply horth r)))
    (by
      intro u x hx
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
      obtain ⟨t, rfl⟩ := P.foldedIndex_surjective σ v
      have horth_r := P.isOrthogonal_of_mem_orbitIndices hσ hsimply horth r
      refine ⟨P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t), Subtype.ext ?_⟩
      simp only [Module.preReflection_apply, Module.Dual.eval_apply, LinearMap.flip_apply]
      have hc := P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r
        (P.foldedRootEmb σ (P.foldedIndex σ t))
      dsimp [corootEmb]
      rw [hc, coe_foldedRootEmb_foldedIndex, P.coe_foldedIndex, P.coe_foldedIndex,
        P.coe_foldedIndex,
        ← P.orbitReflection_smul_of_fixed horth_r (P.weightMap_orbitSum_self σ t),
        P.smul_orbitSum_of_commute (P.commute_coe_orbitReflection horth_r) t]
      rfl)
    (top_unique <| (P.span_fixedSubmodule_orbitSum_support_eq_top b σ).symm.trans_le <|
      Submodule.span_mono <| by
        rintro _ ⟨s, -, rfl⟩
        exact ⟨P.foldedIndex σ s, Subtype.ext (P.coe_foldedIndex σ s)⟩)

section PrivateProperties

variable (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (hsimply : b.cartanMatrix.IsSimplyLaced)
  (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)

@[simp]
private theorem orthogonalFoldPairing_root (u : P.foldedIndices σ) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).root u = P.foldedRootEmb σ u :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_coroot (u : P.foldedIndices σ) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).coroot u = P.foldedCorootFun σ u :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_toLinearMap (x : LinearMap.fixedSubmodule σ.weightMap)
    (f : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).toLinearMap x f = f x :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_coroot' (u : P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).coroot' u x = P.foldedCorootFun σ u x :=
  rfl

private theorem orthogonalFoldPairing_int (u v : P.foldedIndices σ) :
    ∃ z : ℤ, (z : K) = (P.orthogonalFoldPairing b σ hσ hsimply horth).toLinearMap
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).root u)
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).coroot v) := by
  obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
  obtain ⟨t, rfl⟩ := P.foldedIndex_surjective σ v
  refine ⟨∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t, ?_⟩
  rw [orthogonalFoldPairing_toLinearMap, orthogonalFoldPairing_coroot, orthogonalFoldPairing_root,
    P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth t, coe_foldedRootEmb_foldedIndex,
    P.orbitSum_def, map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simpa [root_coroot'_eq_pairing] using P.algebraMap_pairingIn ℤ k t

private theorem orthogonalFoldPairing_isRootSystem :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsRootSystem := by
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  rw [orthogonalFoldPairing]
  exact RootPairing.isRootSystem_mk'' (P.orthogonalFoldPairing_int b σ hσ hsimply horth)

private theorem orthogonalFoldPairing_isCrystallographic :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsCrystallographic :=
  ⟨P.orthogonalFoldPairing_int b σ hσ hsimply horth⟩

private theorem orthogonalFoldPairing_isReduced :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsReduced where
  eq_or_eq_neg u v hdep := by
    obtain ⟨r₁, rfl⟩ := P.foldedIndex_surjective σ u
    obtain ⟨r₂, rfl⟩ := P.foldedIndex_surjective σ v
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    have hne : Ψ.root (P.foldedIndex σ r₂) ≠ 0 := fun h0 ↦
      P.orbitSum_ne_zero hσ r₂ (by
        simpa [Ψ] using congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) h0)
    rw [LinearIndependent.pair_symm_iff, LinearIndependent.pair_iff' hne] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hsmul : P.orbitSum σ r₁ = c • P.orbitSum σ r₂ := by
      simpa [Ψ] using congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) hc.symm
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth hsmul with ⟨_, hm⟩ | ⟨rfl, _⟩
    · exact .inl (congrArg Ψ.root (P.foldedIndex_eq_of_mem hm))
    · exact .inr (by simpa [Ψ] using hc.symm)

private theorem orthogonalFoldPairing_reflectionPerm (r t : ι) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).reflectionPerm
        (P.foldedIndex σ r) (P.foldedIndex σ t) =
      P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  have horth_r := P.isOrthogonal_of_mem_orbitIndices hσ hsimply horth r
  apply Ψ.root.injective
  apply Subtype.ext
  rw [Ψ.root_reflectionPerm, Ψ.reflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower]
  simp only [Ψ, orthogonalFoldPairing_coroot', orthogonalFoldPairing_root,
    P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r, coe_foldedRootEmb_foldedIndex]
  rw [← P.orbitReflection_smul_of_fixed horth_r (P.weightMap_orbitSum_self σ t),
    P.smul_orbitSum_of_commute (P.commute_coe_orbitReflection horth_r) t]

/-- One step of `ℤ`-span descent along a simple block reflection `P.orbitReflection σ s₀`. -/
private theorem orthogonalFoldPairing_inSpan_of_orbitReflection
    [DecidableEq (P.foldedIndices σ)] {s₀ q : ι} (hs₀ : s₀ ∈ b.support)
    (hq :
      let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
      let supp := b.support.image (P.foldedIndex σ)
      let q' := P.weylGroupToPerm (P.orbitReflection σ s₀) q
      Ψ.coroot (P.foldedIndex σ q') ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
        Ψ.root (P.foldedIndex σ q') ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ)))) :
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    let supp := b.support.image (P.foldedIndex σ)
    Ψ.coroot (P.foldedIndex σ q) ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root (P.foldedIndex σ q) ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ))) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  have := P.orthogonalFoldPairing_isCrystallographic b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  have hinvol : P.weylGroupToPerm (P.orbitReflection σ s₀)
      (P.weylGroupToPerm (P.orbitReflection σ s₀) q) = q := by
    rw [← _root_.Equiv.Perm.mul_apply, ← map_mul, P.orbitReflection_mul_self
      (P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs₀), map_one,
      _root_.Equiv.Perm.coe_one, id_eq]
  have hrefl := P.orthogonalFoldPairing_reflectionPerm b σ hσ hsimply horth s₀
    (P.weylGroupToPerm (P.orbitReflection σ s₀) q)
  rw [hinvol] at hrefl
  have hs₀_mem : P.foldedIndex σ s₀ ∈ (supp : Set (P.foldedIndices σ)) :=
    Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs₀)
  set u' := P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ s₀) q)
  set u₀ := P.foldedIndex σ s₀
  dsimp only
  rw [← hrefl, Ψ.coroot_reflectionPerm, Ψ.root_reflectionPerm, Ψ.coreflection_apply_coroot,
    Ψ.reflection_apply_root, ← Ψ.algebraMap_pairingIn ℤ u₀ u', ← Ψ.algebraMap_pairingIn ℤ u' u₀,
    algebraMap_int_eq, Int.coe_castRingHom, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact ⟨sub_mem hq.1 (zsmul_mem (subset_span (Set.mem_image_of_mem Ψ.coroot hs₀_mem)) _),
    sub_mem hq.2 (zsmul_mem (subset_span (Set.mem_image_of_mem Ψ.root hs₀_mem)) _)⟩

/-- Both folded roots and folded coroots lie in the `ℤ`-spans of the simple folded roots and
coroots, by induction along `Subgroup.closure (P.orbitReflection σ '' b.support)`. -/
private theorem orthogonalFoldPairing_mem_span_int
    [DecidableEq (P.foldedIndices σ)] (u : P.foldedIndices σ) :
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    let supp := b.support.image (P.foldedIndex σ)
    Ψ.coroot u ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root u ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ))) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  let inSpan (q : ι) : Prop :=
    Ψ.coroot (P.foldedIndex σ q) ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root (P.foldedIndex σ q) ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ)))
  have hclosure {w : P.weylGroup}
      (hw : w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι))) :
      ∀ q : ι, inSpan (P.weylGroupToPerm w q) → inSpan q := by
    induction hw using Subgroup.closure_induction'' with
    | one => intro q hq; simpa using hq
    | mem g hg =>
      obtain ⟨s₀, hs₀, rfl⟩ := hg
      exact fun _ hq ↦ P.orthogonalFoldPairing_inSpan_of_orbitReflection b σ hσ hsimply horth hs₀ hq
    | inv_mem g hg =>
      obtain ⟨s₀, hs₀, rfl⟩ := hg
      intro q hq
      rw [P.orbitReflection_inv (P.isOrthogonal_orbitIndices_of_mem_support hσ horth hs₀)] at hq
      exact P.orthogonalFoldPairing_inSpan_of_orbitReflection b σ hσ hsimply horth hs₀ hq
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      exact fun q hq ↦ ih₂ q (ih₁ (P.weylGroupToPerm w₂ q) (by simpa [map_mul] using hq))
  obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
  obtain ⟨w, hw, hsupp⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r
  have hmem : P.foldedIndex σ (P.weylGroupToPerm w r) ∈ (supp : Set (P.foldedIndices σ)) :=
    Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hsupp)
  exact hclosure hw r (And.intro
    (subset_span (Set.mem_image_of_mem Ψ.coroot hmem))
    (subset_span (Set.mem_image_of_mem Ψ.root hmem)))

end PrivateProperties

/-- **The orthogonal orbit-sum fold** (Stembridge, Claim 1). For a finite simply-laced root system
`P` over a linearly ordered field `K`, a base `b`, and an automorphism `σ` permuting `b.support`
with pairwise orthogonal simple orbits, the distinct orbit sums form a reduced crystallographic root
system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual with base given by the
simple-orbit sums. -/
noncomputable def orthogonalFold
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.OrbitSumRealization b σ := by
  classical
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  letI := P.orthogonalFoldPairing_isRootSystem b σ hσ hsimply horth
  letI := P.orthogonalFoldPairing_isReduced b σ hσ hsimply horth
  letI := P.orthogonalFoldPairing_isCrystallographic b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  have h₀ : LinearIndepOn K Ψ.root (supp : Set (P.foldedIndices σ)) := by
    have hcoe : (supp : Set (P.foldedIndices σ)) = P.foldedIndex σ '' (b.support : Set ι) := by
      simp [supp]
    rw [hcoe]
    have hli := P.linearIndepOn_orbitSum_support hσ
    exact LinearIndepOn.of_comp (LinearMap.fixedSubmodule σ.weightMap).subtype hli
  have h₁ : Set.Pairwise (supp : Set (P.foldedIndices σ)) fun u v ↦ Ψ.pairingIn ℤ u v ≤ 0 := by
    intro u hu v hv huv
    obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨s₂, hs₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    have hsum : Ψ.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
        ∑ k ∈ P.orbitIndices σ s₁, P.pairingIn ℤ k s₂ := by
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [Ψ.algebraMap_pairingIn ℤ, ← Ψ.root_coroot'_eq_pairing]
      simp only [Ψ, orthogonalFoldPairing_coroot', orthogonalFoldPairing_root,
        P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth s₂, coe_foldedRootEmb_foldedIndex]
      rw [P.orbitSum_def, map_sum, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by
        simpa [root_coroot'_eq_pairing] using (P.algebraMap_pairingIn ℤ k s₂).symm
    rw [hsum]
    refine Finset.sum_nonpos fun k hk ↦ ?_
    have hks₂ : k ≠ s₂ := fun h ↦ huv (h ▸ (P.foldedIndex_eq_of_mem hk).symm)
    exact b.pairingIn_le_zero_of_ne hks₂ (P.mem_support_of_mem_orbitIndices hσ hs₁ hk) hs₂
  have hspan := P.orthogonalFoldPairing_mem_span_int b σ hσ hsimply horth
  exact
    { pairing := Ψ
      base := Base.mkOfPairwiseLEZero Ψ h₀ h₁ (fun u ↦ (hspan u).1) (fun u ↦ (hspan u).2)
      rootSystem := inferInstance
      reduced := inferInstance
      crystallographic := inferInstance
      evaluation := fun _ _ ↦ rfl
      root_eq := fun _ ↦ rfl
      base_eq := fun u ↦ by
        rw [Base.mkOfPairwiseLEZero_support]
        simp only [supp, Finset.mem_image]
        exact ⟨fun ⟨j, hj, hju⟩ ↦
            ⟨j, hj, (P.coe_foldedIndex σ j).symm.trans (congrArg Subtype.val hju)⟩,
          fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext ((P.coe_foldedIndex σ j).trans hju)⟩⟩ }

/-- Existence form of `P.orthogonalFold`. -/
theorem nonempty_orbitSumRealization_of_isSimplyLaced
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    Nonempty (P.OrbitSumRealization b σ) :=
  ⟨P.orthogonalFold b σ hσ hsimply horth⟩

end Construction

/-! ### Characteristic formulas on any `OrbitSumRealization` -/

namespace OrbitSumRealization

variable {P} {b : P.Base} {σ : P.Aut} (F : P.OrbitSumRealization b σ)

/-- **Folded coroot evaluation.** On any `F : P.OrbitSumRealization b σ` under the orthogonal-fold
hypotheses, evaluating the folded coroot functional at `P.foldedIndex σ r` on a fixed weight `x`
equals `P.coroot' r x`. -/
theorem coroot'_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  obtain rfl : F = P.orthogonalFold b σ hσ hsimply horth :=
    Subsingleton.elim F (P.orthogonalFold b σ hσ hsimply horth)
  exact P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r x

@[simp]
theorem coroot_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  rw [← F.coroot'_eq_coroot, F.coroot'_foldedIndex_apply hσ hsimply horth]

/-- **Folded root-coroot pairing.** Pairing `P.foldedIndex σ r` with the coroot of
`P.foldedIndex σ t` sums `P.pairing k t` over `k ∈ P.orbitIndices σ r`. -/
theorem pairing_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r t : ι) :
    F.pairing.pairing (P.foldedIndex σ r) (P.foldedIndex σ t) =
      ∑ k ∈ P.orbitIndices σ r, P.pairing k t := by
  rw [← F.pairing.root_coroot'_eq_pairing, F.coroot'_foldedIndex_apply hσ hsimply horth,
    F.coe_root_foldedIndex, P.orbitSum_def, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ P.root_coroot'_eq_pairing t k

/-- Integer-valued form of `pairing_foldedIndex`. -/
theorem pairingIn_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r t : ι) :
    F.pairing.pairingIn ℤ (P.foldedIndex σ r) (P.foldedIndex σ t) =
      ∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [F.pairing.algebraMap_pairingIn ℤ, F.pairing_foldedIndex hσ hsimply horth, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (P.algebraMap_pairingIn ℤ k t).symm

/-- **Oriented Cartan edge-count identity in `ℤ`** (Stembridge, equation (3)): for simple roots
`s₁, s₂ ∈ b.support` in distinct `σ`-orbits, `#(P.orbitIndices σ s₂)` times the folded Cartan
integer `⟨β_{s₁}, β_{s₂}^∨⟩` equals minus the number of non-orthogonal pairs between
`P.orbitIndices σ s₁` and `P.orbitIndices σ s₂`. -/
theorem card_orbitIndices_mul_pairingIn_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s₁ s₂ : ι} (hs₁ : s₁ ∈ b.support) (hs₂ : s₂ ∈ b.support)
    (hne : P.foldedIndex σ s₁ ≠ P.foldedIndex σ s₂) :
    (#(P.orbitIndices σ s₂) : ℤ) *
        F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      -(#((P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂).filter
          fun p ↦ P.pairing p.1 p.2 ≠ 0) : ℤ) := by
  have hprod : (#(P.orbitIndices σ s₂) : ℤ) *
        F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      ∑ p ∈ P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂, P.pairingIn ℤ p.1 p.2 := by
    rw [Finset.sum_product_right]
    have hrow (t' : ι) (ht' : t' ∈ P.orbitIndices σ s₂) :
        ∑ k ∈ P.orbitIndices σ s₁, P.pairingIn ℤ k t' =
          F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) := by
      rw [← F.pairingIn_foldedIndex hσ hsimply horth, P.foldedIndex_eq_of_mem ht']
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
  rw [hprod]
  have hterm (p : ι × ι) (hp : p ∈ P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂) :
      P.pairingIn ℤ p.1 p.2 = if P.pairing p.1 p.2 ≠ 0 then -1 else 0 := by
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    have hb₁ : p.1 ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs₁ hp₁
    have hb₂ : p.2 ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs₂ hp₂
    have hpne : (⟨p.1, hb₁⟩ : b.support) ≠ ⟨p.2, hb₂⟩ := by
      intro h
      have heq : p.1 = p.2 := congrArg Subtype.val h
      exact hne ((P.foldedIndex_eq_of_mem hp₁).symm.trans (heq ▸ P.foldedIndex_eq_of_mem hp₂))
    have hzero_iff : P.pairingIn ℤ p.1 p.2 = 0 ↔ P.pairing p.1 p.2 = 0 := by
      rw [← P.algebraMap_pairingIn ℤ p.1 p.2, algebraMap_int_eq, Int.coe_castRingHom,
        Int.cast_eq_zero]
    rcases hsimply hpne with h0 | h1
    · have hp0 : P.pairingIn ℤ p.1 p.2 = 0 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using h0
      simp [hp0, hzero_iff.mp hp0]
    · have hp1 : P.pairingIn ℤ p.1 p.2 = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using h1
      have hnz : P.pairing p.1 p.2 ≠ 0 := fun hz ↦ by
        have := hzero_iff.mpr hz
        omega
      simp [hp1, hnz]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_neg_one]

/-- **Oriented Cartan entry as edge count divided by target-orbit size** (Stembridge, equation (3)):
for simple roots `s₁, s₂ ∈ b.support` in distinct `σ`-orbits,
`⟨β_{s₁}, β_{s₂}^∨⟩ = -N_{O₁, O₂} / |O₂|`. -/
theorem pairing_foldedIndex_eq_neg_card_div
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s₁ s₂ : ι} (hs₁ : s₁ ∈ b.support) (hs₂ : s₂ ∈ b.support)
    (hne : P.foldedIndex σ s₁ ≠ P.foldedIndex σ s₂) :
    F.pairing.pairing (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      -(#((P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂).filter
          fun p ↦ P.pairing p.1 p.2 ≠ 0) : K) / (#(P.orbitIndices σ s₂) : K) := by
  have hd : (#(P.orbitIndices σ s₂) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.card_orbitIndices_pos σ s₂).ne'
  have hint := congrArg (Int.cast (R := K))
    (F.card_orbitIndices_mul_pairingIn_foldedIndex hσ hsimply horth hs₁ hs₂ hne)
  push_cast at hint
  rw [eq_div_iff hd, mul_comm, ← F.pairing.algebraMap_pairingIn ℤ, algebraMap_int_eq,
    Int.coe_castRingHom]
  exact hint

/-- **Reflection comparison.** On any `F : P.OrbitSumRealization b σ`, the folded reflection in
`P.foldedIndex σ r` restricts the commuting block reflection `P.orbitReflection σ r` to the fixed
submodule `LinearMap.fixedSubmodule σ.weightMap`. -/
theorem coe_reflection_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.pairing.reflection (P.foldedIndex σ r) x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitReflection σ r • (x : M) := by
  rw [F.pairing.reflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower,
    F.coroot'_foldedIndex_apply hσ hsimply horth, F.coe_root_foldedIndex,
    P.orbitReflection_smul_of_fixed (P.isOrthogonal_of_mem_orbitIndices hσ hsimply horth r)
      (LinearMap.mem_fixedSubmodule_iff.mp x.2)]

/-- Folded `reflectionPerm` agrees with the index permutation action of `P.orbitReflection σ r`. -/
theorem reflectionPerm_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r t : ι) :
    F.pairing.reflectionPerm (P.foldedIndex σ r) (P.foldedIndex σ t) =
      P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t) := by
  obtain rfl : F = P.orthogonalFold b σ hσ hsimply horth :=
    Subsingleton.elim F (P.orthogonalFold b σ hσ hsimply horth)
  exact P.orthogonalFoldPairing_reflectionPerm b σ hσ hsimply horth r t

end OrbitSumRealization

end OrthogonalFold

end RootPairing
