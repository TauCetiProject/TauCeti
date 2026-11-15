/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.Topology.Algebra.Module.Compact
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
public import TauCeti.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Adic completeness and constructions of compact modules

Let `R` be a compact topological ring and `M` a compact `R`-module in the sense of
`TauCeti.IsCompactModule`. Every open submodule `N ≤ M` has finite quotient `M ⧸ N`, because the
quotient is both compact and discrete. When `R` is commutative and its topology is `I`-adic for an
ideal `I`, every element of the finite quotient `M ⧸ N` has open annihilator in `R`, hence is
killed by some power of `I`; taking a uniform exponent over the finite quotient shows that
`I ^ k • ⊤ ≤ N` for some `k`.

Together with the inverse-limit description `TauCeti.IsCompactModule.existsUnique_forall_mkQ_eq`,
this links the topological and algebraic filtrations of `M`:

* `M` is `I`-adically Hausdorff (`TauCeti.IsCompactModule.isHausdorff_of_isAdic`), with no finite
  generation assumption on `I`;
* when `I` is finitely generated, each submodule `I ^ n • ⊤` is compact, hence closed in `M`, and
  so `M` is `I`-adically complete (`TauCeti.IsCompactModule.isAdicComplete_of_isAdic`).

In particular, over a compact Hausdorff noetherian local ring `(R, 𝔪)` — whose topology is
`𝔪`-adic by `IsLocalRing.isAdic_maximalIdeal` — every compact `R`-module is `𝔪`-adically complete
(`TauCeti.IsCompactModule.isAdicComplete`), and `R` itself is a compact module over itself and
`𝔪`-adically complete (`IsLocalRing.isCompactModule_self`,
`IsLocalRing.isAdicComplete_maximalIdeal`).

We also record basic permanence properties of `TauCeti.IsCompactModule`: stability under
subsingletons, continuous linear equivalences, arbitrary products, and closed submodules.

## Main results

* `Submodule.isCompact_smul_of_fg`: for a finitely generated ideal `I` and a compact submodule `P`,
  `I • P` is compact.
* `TauCeti.IsCompactModule.finite_quotient_of_isOpen`: the quotient of a compact module by an open
  submodule is finite.
* `TauCeti.IsCompactModule.exists_pow_smul_top_le_of_isOpen`: over a commutative ring with `I`-adic
  topology, every open submodule of a compact module contains `I ^ k • ⊤` for some `k`.
* `TauCeti.IsCompactModule.isAdicComplete_of_isAdic`, `TauCeti.IsCompactModule.isAdicComplete`:
  every compact module over a compact ring with a finitely generated ideal of definition (in
  particular over a compact Hausdorff noetherian local ring) is adically complete.
* `IsLocalRing.totallyDisconnectedSpace_of_compactSpace`, `IsLocalRing.isCompactModule_self`,
  `IsLocalRing.isAdicComplete_maximalIdeal`: a compact Hausdorff noetherian local ring is totally
  disconnected, a compact module over itself, and `𝔪`-adically complete.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.1.
* N. Bourbaki, *Commutative Algebra*, Chapter III, §2.
-/

public section

open Filter Topology Pointwise

section CompactSmul

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

/-- For a finitely generated ideal `I` and a compact submodule `P`, the submodule `I • P` is
compact: each generator scales `P` to a compact set, and finite sums preserve compactness. -/
theorem Submodule.isCompact_smul_of_fg {I : Ideal R} (hI : I.FG) {P : Submodule R M}
    (hP : IsCompact (P : Set M)) : IsCompact ((I • P : Submodule R M) : Set M) := by
  classical
  obtain ⟨s, rfl⟩ := hI
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.coe_insert, Ideal.span_insert, sup_smul, Submodule.coe_sup,
      Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul]
    exact (hP.smul a).add ih

end CompactSmul

namespace IsLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- A compact Hausdorff noetherian local ring is a nonarchimedean topological ring, since its
topology is `𝔪`-adic. -/
theorem nonarchimedeanRing_of_compactSpace : NonarchimedeanRing R :=
  (isAdic_maximalIdeal R) ▸ (maximalIdeal R).nonarchimedean

/-- A compact Hausdorff noetherian local ring is totally disconnected. -/
theorem totallyDisconnectedSpace_of_compactSpace : TotallyDisconnectedSpace R := by
  have := nonarchimedeanRing_of_compactSpace R
  infer_instance

/-- A compact Hausdorff noetherian local ring is a compact module over itself. -/
theorem isCompactModule_self : TauCeti.IsCompactModule R R := by
  have := totallyDisconnectedSpace_of_compactSpace R
  exact .self

end IsLocalRing

namespace TauCeti.IsCompactModule

section Constructions

variable {R M N : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- Any subsingleton topological module is a compact module. -/
theorem subsingleton [Subsingleton M] : IsCompactModule R M where
  isTopologicalAddGroup :=
    { continuous_add := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
      continuous_neg := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _ }
  continuousSMul := ⟨continuous_of_const fun _ _ ↦ Subsingleton.elim _ _⟩
  compactSpace := inferInstance
  totallyDisconnectedSpace := inferInstance

/-- Compactness of a topological module transports along a continuous linear equivalence. -/
theorem of_continuousLinearEquiv (hM : IsCompactModule R M) (e : M ≃L[R] N) :
    IsCompactModule R N := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.totallyDisconnectedSpace
  have he := e.toHomeomorph
  have hadd : ContinuousAdd N := ⟨by
    have h : (fun p : N × N ↦ p.1 + p.2) = fun p ↦ e (e.symm p.1 + e.symm p.2) := by
      ext ⟨x, y⟩
      simp [← map_add]
    rw [h]
    exact e.continuous.comp ((e.symm.continuous.comp continuous_fst).add
      (e.symm.continuous.comp continuous_snd))⟩
  have hneg : ContinuousNeg N := ⟨by
    have h : (fun x : N ↦ -x) = fun x ↦ e (-e.symm x) := by
      ext x
      simp
    rw [h]
    exact e.continuous.comp e.symm.continuous.neg⟩
  have hsmul : ContinuousSMul R N := ⟨by
    have h : (fun p : R × N ↦ p.1 • p.2) = fun p ↦ e (p.1 • e.symm p.2) := by
      ext ⟨r, x⟩
      simp
    rw [h]
    exact e.continuous.comp (continuous_fst.smul (e.symm.continuous.comp continuous_snd))⟩
  exact ⟨IsTopologicalAddGroup.mk, hsmul, he.compactSpace,
    he.symm.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- Two continuously linearly equivalent topological modules are simultaneously compact modules. -/
theorem congr (e : M ≃L[R] N) : IsCompactModule R M ↔ IsCompactModule R N :=
  ⟨fun h ↦ h.of_continuousLinearEquiv e, fun h ↦ h.of_continuousLinearEquiv e.symm⟩

/-- An arbitrary product of compact modules, with the product topology, is a compact module. -/
theorem pi {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] (h : ∀ i, IsCompactModule R (M i)) :
    IsCompactModule R (∀ i, M i) := by
  have := fun i ↦ (h i).isTopologicalAddGroup
  have := fun i ↦ (h i).continuousSMul
  have := fun i ↦ (h i).compactSpace
  have := fun i ↦ (h i).totallyDisconnectedSpace
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Any power `ι → R` of a compact totally disconnected topological ring is a compact `R`-module. -/
theorem pi_self (ι : Type*) [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] :
    IsCompactModule R (ι → R) :=
  pi fun _ ↦ self

/-- A closed submodule of a compact module is a compact module. -/
theorem submodule (hM : IsCompactModule R M) (P : Submodule R M) (hP : IsClosed (P : Set M)) :
    IsCompactModule R P := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.totallyDisconnectedSpace
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isCompact
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The quotient of a compact module by an open submodule is finite, being both compact and
discrete. -/
theorem finite_quotient_of_isOpen (hM : IsCompactModule R M) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) : Finite (M ⧸ N) := by
  have := hM.isTopologicalAddGroup
  have := hM.compactSpace
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  have : CompactSpace (M ⧸ N) := ⟨by
    rw [← Set.image_univ_of_surjective N.mkQ_surjective]
    exact isCompact_univ.image N.continuous_mkQ⟩
  exact finite_of_compact_of_discrete

/-- Every closed submodule of a compact module over a compact ring is the intersection of the open
submodules containing it. -/
theorem mem_of_forall_isOpen_le (hM : IsCompactModule R M) [CompactSpace R] {P : Submodule R M}
    (hP : IsClosed (P : Set M)) {x : M}
    (hx : ∀ N : Submodule R M, IsOpen (N : Set M) → P ≤ N → x ∈ N) : x ∈ P := by
  have := hM.isTopologicalAddGroup
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  refine (hM.quotient P hP).eq_zero_of_forall_mem_of_isOpen fun U hU ↦ ?_
  exact hx (U.comap P.mkQ) (hU.preimage P.continuous_mkQ)
    (fun y hy ↦ by simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero P).mpr hy])

end Constructions

section AdicComplete

variable {R M : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] {I : Ideal R}

/-- Over a commutative ring whose topology is `I`-adic, every open submodule `N` of a compact
module `M` contains `I ^ k • ⊤` for some `k`: each element of the finite discrete quotient `M ⧸ N`
has open annihilator in `R`, hence is killed by a power of `I`. -/
theorem exists_pow_smul_top_le_of_isOpen (hM : IsCompactModule R M) (hI : IsAdic I)
    {N : Submodule R M} (hN : IsOpen (N : Set M)) :
    ∃ k : ℕ, I ^ k • (⊤ : Submodule R M) ≤ N := by
  classical
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := Submodule.Quotient.discreteTopology_of_isOpen N hN
  have := hM.finite_quotient_of_isOpen N hN
  let _ := Fintype.ofFinite (M ⧸ N)
  have hann (q : M ⧸ N) : ∃ k : ℕ, ∀ r ∈ I ^ (k + 1), r • q = 0 := by
    obtain ⟨m, rfl⟩ := N.mkQ_surjective q
    let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R (M ⧸ N) (N.mkQ m))
    have hJ : IsOpen (J : Set R) := by
      have heq : (J : Set R) = (fun r : R ↦ N.mkQ (r • m)) ⁻¹' {(0 : M ⧸ N)} := by
        ext r
        simp [J, LinearMap.mem_ker]
      rw [heq]
      exact (isOpen_discrete {(0 : M ⧸ N)}).preimage
        (N.continuous_mkQ.comp (continuous_id.smul continuous_const))
    obtain ⟨k, hk⟩ := hI.exists_pow_succ_le hJ
    exact ⟨k, fun r hr ↦ LinearMap.mem_ker.mp (hk hr)⟩
  choose k hk using hann
  refine ⟨Finset.univ.sup fun q : M ⧸ N ↦ k q + 1, Submodule.smul_le.mpr fun r hr m _ ↦ ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.map_smul]
  exact hk (N.mkQ m) r
    (Ideal.pow_le_pow_right (Finset.le_sup (f := fun q : M ⧸ N ↦ k q + 1) (Finset.mem_univ _)) hr)

variable [CompactSpace R] in
/-- Over a compact `I`-adic commutative ring, every compact module is `I`-adically Hausdorff. -/
theorem isHausdorff_of_isAdic (hM : IsCompactModule R M) (hI : IsAdic I) : IsHausdorff I M where
  haus' x hx := hM.eq_zero_of_forall_mem_of_isOpen fun N hN ↦ by
    obtain ⟨k, hk⟩ := hM.exists_pow_smul_top_le_of_isOpen hI hN
    exact hk ((SModEq.zero.mp (hx k)))

variable [CompactSpace R] in
/-- Over a compact `I`-adic commutative ring with `I` finitely generated, every compact module is
`I`-adically complete. -/
theorem isAdicComplete_of_isAdic (hM : IsCompactModule R M) (hI : IsAdic I) (hIfg : I.FG) :
    IsAdicComplete I M where
  toIsHausdorff := hM.isHausdorff_of_isAdic hI
  prec' f hf := by
    classical
    have := hM.isTopologicalAddGroup
    have := hM.continuousSMul
    have := hM.compactSpace
    have := hM.t2Space
    choose k hk using fun N : {N : Submodule R M // IsOpen (N : Set M)} ↦
      hM.exists_pow_smul_top_le_of_isOpen hI N.2
    have hcompat : ∀ ⦃N N' : {N : Submodule R M // IsOpen (N : Set M)}⦄ (h : N.1 ≤ N'.1),
        Submodule.factor h (N.1.mkQ (f (k N))) = N'.1.mkQ (f (k N')) := by
      intro N N' h
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have h1 : f (k N) - f (max (k N) (k N')) ∈ N'.1 :=
        h (hk N (SModEq.sub_mem.mp (hf (le_max_left _ _))))
      have h2 : f (k N') - f (max (k N) (k N')) ∈ N'.1 :=
        hk N' (SModEq.sub_mem.mp (hf (le_max_right _ _)))
      simpa using N'.1.sub_mem h1 h2
    obtain ⟨L, hL, -⟩ := hM.existsUnique_forall_mkQ_eq (fun N ↦ N.1.mkQ (f (k N))) hcompat
    refine ⟨L, fun n ↦ SModEq.sub_mem.mpr ?_⟩
    have hclosed : IsClosed (((I ^ n • ⊤ : Submodule R M) : Set M)) :=
      (Submodule.isCompact_smul_of_fg hIfg.pow (by simpa using isCompact_univ)).isClosed
    refine hM.mem_of_forall_isOpen_le hclosed fun N hN hle ↦ ?_
    let N' : {N : Submodule R M // IsOpen (N : Set M)} := ⟨N, hN⟩
    have hfn : f n - f (max n (k N')) ∈ N :=
      hle (SModEq.sub_mem.mp (hf (le_max_left _ _)))
    have hfk : f (max n (k N')) - f (k N') ∈ N := by
      have := SModEq.sub_mem.mp (hf (le_max_right n (k N'))).symm
      exact hk N' this
    have hLk : f (k N') - L ∈ N := by
      rw [← Submodule.Quotient.eq]
      exact (hL N').symm
    simpa [sub_add_sub_cancel] using N.add_mem (N.add_mem hfn hfk) hLk

/-- Over a compact Hausdorff noetherian local ring `(R, 𝔪)`, every compact `R`-module is
`𝔪`-adically complete. -/
theorem isAdicComplete [CompactSpace R] [IsTopologicalRing R] [T2Space R] [IsLocalRing R]
    [IsNoetherianRing R] (hM : IsCompactModule R M) :
    IsAdicComplete (IsLocalRing.maximalIdeal R) M :=
  hM.isAdicComplete_of_isAdic (IsLocalRing.isAdic_maximalIdeal R) (IsNoetherian.noetherian _)

end AdicComplete

end TauCeti.IsCompactModule

namespace IsLocalRing

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R]

/-- A compact Hausdorff noetherian local ring is adically complete with respect to its maximal
ideal. -/
instance isAdicComplete_maximalIdeal : IsAdicComplete (maximalIdeal R) R :=
  (isCompactModule_self R).isAdicComplete

end IsLocalRing
