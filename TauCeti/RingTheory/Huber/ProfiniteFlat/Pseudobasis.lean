/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ProfiniteFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.Topology.Algebra.Module.LinearTopology.ProfiniteDual
import TauCeti.Topology.Algebra.Module.Nakayama

/-!
# Pseudobases of profinite flat modules over a compact DVR

Let `O` be a discrete valuation ring carrying a compact Hausdorff ring topology, with maximal
ideal `𝔪 = (ϖ)` and finite discrete residue field `k = O ⧸ 𝔪`. Proposition 6.2 of
Chojecki–Hansen–Johansson (following `SGA 3`, Exposé VII_B, §0.2) states that a topological
`O`-module `M : Type v` is profinite flat if and only if it is topologically `O`-linearly
isomorphic to a product `I → O` for some index type `I : Type v` equipped with the product
topology. A continuous linear equivalence `e : M ≃L[O] (I → O)` (or the family of topological
generators `e.symm (Pi.single i 1)`) is called a **pseudobasis** of `M`.

The non-trivial implication (`IsProfiniteFlat O M → ∃ I, Nonempty (M ≃L[O] (I → O))`) proceeds in
three stages:

1. **Reduction to the residue field**: `𝔪 • ⊤` is compact, hence closed in `M`, so `V = M ⧸ (𝔪 • ⊤)`
   is a compact Hausdorff linearly topologized `k`-vector space. By Pontryagin–Lefschetz duality
   (`TauCeti.IsLinearTopology.exists_continuousLinearEquiv_pi`), `V ≃L[k] (I → k)` for some
   `I : Type v`.
2. **Inductive lifting of continuous linear functionals**: any continuous `O`-linear map
   `M →L[O] (O ⧸ 𝔪)` lifts to `M →L[O] O`. At each step `n ⇝ n + 1`, `ϖ`-regularity of the flat
   module `M` makes multiplication by `ϖ` a homeomorphism `M ≃ₜ ϖ • ⊤`, which isolates an open
   submodule `K ≤ M` of finite index such that `f_n` vanishes on the `ϖ`-torsion of `M ⧸ K`; finite
   Baer extension over the self-injective artinian ring `O ⧸ (ϖ ^ (n + 1))` extends the map on
   `ϖ • (M ⧸ K)` to `M ⧸ K`, and `𝔪`-adic completeness of `O` assembles the tower into a continuous
   `O`-linear functional `M →L[O] O`.
3. **Topological Nakayama**: assembling lifts of all coordinate functionals of `V ≃L[k] (I → k)`
   yields a continuous `O`-linear map `Ψ : M →L[O] (I → O)` inducing an isomorphism modulo `𝔪 • ⊤`.
   Surjectivity follows from `LinearMap.surjective_of_surjective_comp_mkQ_of_compactSpace`; the
   compact kernel `K' = ker Ψ` satisfies `K' ≤ 𝔪 • K'` by torsion-freeness of `I → O`, hence
   vanishes by `Submodule.eq_bot_of_le_smul_of_isCompact`; and compactness of `M` upgrades `Ψ` to
   `M ≃L[O] (I → O)`.

We also describe the neighbourhood basis of `0` attached to a pseudobasis `e : M ≃L[O] (I → O)`
via the open submodules `pseudobasisSubmodule e J n` (`J : Finset I`, `n ≥ 1`), and characterize
finitely generated profinite flat `O`-modules as those admitting a finite pseudobasis `Fin n → O`.

## Main definitions

* `TauCeti.Huber.pseudobasisSubmodule e J n`: the open submodule of elements of `M` whose
  `J`-coordinates under `e : M ≃L[O] (I → O)` lie in `𝔪 ^ n`.

## Main results

* `TauCeti.Huber.IsProfiniteFlat.exists_continuousLinearMap_lift_mkQ`: every continuous `O`-linear
  map `M →L[O] (O ⧸ 𝔪)` from a profinite flat `O`-module lifts to `M →L[O] O`.
* `TauCeti.Huber.IsProfiniteFlat.iff_exists_pseudobasis`: `M : Type v` is profinite flat over a
  compact Hausdorff discrete valuation ring `O` if and only if `M ≃L[O] (I → O)` for some
  `I : Type v`.
* `TauCeti.Huber.hasBasis_nhds_zero_pseudobasisSubmodule`: the submodules
  `pseudobasisSubmodule e J n` (`J` finite, `1 ≤ n`) form a basis of neighbourhoods of `0` in `M`.
* `TauCeti.Huber.IsProfiniteFlat.module_finite_iff_exists_fin_pseudobasis`: a profinite flat
  `O`-module is finitely generated if and only if it is continuously `O`-linearly equivalent to
  `Fin n → O` for some `n : ℕ`.

## References

* P. Chojecki, D. Hansen, and C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*, Doc. Math. 22 (2017), §6.1, Proposition 6.2.
* M. Demazure and A. Grothendieck, *Schémas en groupes* (`SGA 3`), Tome I, Exposé VII_B, §0.2.
-/

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

section BaerExtension

variable {O Q : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q]

/-- Colon-ideal divisibility in `O ⧸ (ϖ ^ m)`: if `{r | r • y ∈ N}` contains `ϖ ^ m`, it equals
`(ϖ ^ j)` for some `j ≤ m`, and `α ⟨ϖ ^ j • y, _⟩` is divisible by `ϖ ^ j` in `O ⧸ (ϖ ^ m)`. -/
private theorem exists_colon_exponent_and_div {ϖ : O} (hϖ : Irreducible ϖ) {m : ℕ}
    (hann : ∀ q : Q, ϖ ^ m • q = 0) {N : Submodule O Q} (y : Q)
    (α : N →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m})) :
    ∃ (j : ℕ) (hj : N.comap (LinearMap.toSpanSingleton O Q y) = Ideal.span {ϖ ^ j}) (d₀ : O),
      α ⟨ϖ ^ j • y, by
          change ϖ ^ j ∈ N.comap (LinearMap.toSpanSingleton O Q y)
          rw [hj]
          exact Ideal.mem_span_singleton_self _⟩ =
        Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (ϖ ^ j * d₀) := by
  let J : Ideal O := N.comap (LinearMap.toSpanSingleton O Q y)
  have hϖmJ : ϖ ^ m ∈ J := by simp [J, Submodule.mem_comap, hann y]
  have hJne : J ≠ ⊥ := fun hbot ↦ pow_ne_zero m hϖ.ne_zero (by simpa [hbot] using hϖmJ)
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJne hϖ
  have hjm : j ≤ m := by
    by_contra! hlt
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hj ▸ hϖmJ)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
    have h1 : ϖ ^ m * 1 = ϖ ^ m * (ϖ * (ϖ ^ d * c)) := by
      calc ϖ ^ m * 1 = ϖ ^ m := mul_one _
        _ = ϖ ^ j * c := hc
        _ = ϖ ^ (m + 1 + d) * c := by rw [hd]
        _ = ϖ ^ m * (ϖ * (ϖ ^ d * c)) := by ring
    exact hϖ.not_isUnit (isUnit_iff_exists_inv.mpr
      ⟨ϖ ^ d * c, (mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1).symm⟩)
  let w : N := ⟨ϖ ^ j • y, by
    change ϖ ^ j ∈ J; rw [hj]; exact Ideal.mem_span_singleton_self _⟩
  have hkill : ϖ ^ (m - j) • w = 0 := by
    ext
    change ϖ ^ (m - j) • (ϖ ^ j • y) = 0
    rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hjm, hann y]
  obtain ⟨c₀, hc₀⟩ := Ideal.Quotient.mk_surjective (α w)
  have h0 : Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (ϖ ^ (m - j) * c₀) = 0 := by
    calc Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (ϖ ^ (m - j) * c₀)
        = ϖ ^ (m - j) • Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) c₀ := rfl
      _ = ϖ ^ (m - j) • α w := by rw [hc₀]
      _ = α (ϖ ^ (m - j) • w) := (α.map_smul _ _).symm
      _ = 0 := by rw [hkill, map_zero]
  obtain ⟨d₀, hd₀⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hc₀_eq : c₀ = ϖ ^ j * d₀ := mul_left_cancel₀ (pow_ne_zero (m - j) hϖ.ne_zero) <| by
    calc ϖ ^ (m - j) * c₀ = ϖ ^ m * d₀ := hd₀
      _ = ϖ ^ (m - j + j) * d₀ := by rw [Nat.sub_add_cancel hjm]
      _ = ϖ ^ (m - j) * (ϖ ^ j * d₀) := by rw [pow_add, mul_assoc]
  exact ⟨j, hj, d₀, by rw [← hc₀, hc₀_eq]⟩

/-- One-element Baer extension over `O ⧸ (ϖ ^ m)`: on an `O`-module `Q` annihilated by `ϖ ^ m`, any
`O`-linear functional on a submodule `N ≤ Q` extends to `N ⊔ O ∙ y`. -/
private theorem exists_linearMap_sup_span_singleton {ϖ : O} (hϖ : Irreducible ϖ) {m : ℕ}
    (hann : ∀ q : Q, ϖ ^ m • q = 0) {N : Submodule O Q} (y : Q)
    (α : N →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m})) :
    ∃ β : ↥(N ⊔ Submodule.span O {y}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m}),
      ∀ x : N, β ⟨x.1, Submodule.mem_sup_left x.2⟩ = α x := by
  obtain ⟨j, hj, d₀, hd₀⟩ := exists_colon_exponent_and_div hϖ hann y α
  let w : N := ⟨ϖ ^ j • y, by
    change ϖ ^ j ∈ N.comap (LinearMap.toSpanSingleton O Q y)
    rw [hj]; exact Ideal.mem_span_singleton_self _⟩
  let N' : Submodule O Q := N ⊔ Submodule.span O {y}
  let π : (N × O) →ₗ[O] N' :=
    { toFun := fun p ↦ ⟨p.1.1 + p.2 • y,
        Submodule.add_mem_sup p.1.2 (Submodule.mem_span_singleton.mpr ⟨p.2, rfl⟩)⟩
      map_add' := fun p q ↦ by ext; simp [add_smul]; abel
      map_smul' := fun r p ↦ by ext; simp [smul_add, mul_smul] }
  have hπsurj : Function.Surjective π := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨(⟨x, hx⟩, r), rfl⟩
  let β₀ : (N × O) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m}) :=
    α.comp (LinearMap.fst O N O) +
      (LinearMap.toSpanSingleton O (O ⧸ Ideal.span {ϖ ^ m})
        (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) d₀)).comp (LinearMap.snd O N O)
  have hker : LinearMap.ker π ≤ LinearMap.ker β₀ := by
    rintro ⟨x, r⟩ hxr
    have hsum : (x : Q) + r • y = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hxr)
    have hrJ : r ∈ Ideal.span {ϖ ^ j} := hj ▸ show r • y ∈ N by
      rw [eq_neg_of_add_eq_zero_right hsum]; exact N.neg_mem x.2
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hrJ
    have hx_eq : x = -(s • w) := by
      ext
      calc (x : Q) = -((ϖ ^ j * s) • y) := eq_neg_of_add_eq_zero_left hsum
        _ = -(s • (ϖ ^ j • y)) := by rw [mul_comm, mul_smul]
    rw [LinearMap.mem_ker]
    change α x + (ϖ ^ j * s) • Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) d₀ = 0
    rw [hx_eq, map_neg, LinearMap.map_smul, hd₀]
    change -(s • Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (ϖ ^ j * d₀)) +
      (ϖ ^ j * s) • Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) d₀ = 0
    rw [mul_comm (ϖ ^ j) s, mul_smul]
    exact neg_add_cancel _
  let β : N' →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m}) :=
    ((LinearMap.ker π).liftQ β₀ hker).comp (π.quotKerEquivOfSurjective hπsurj).symm.toLinearMap
  refine ⟨β, fun x ↦ ?_⟩
  have hsymm : (π.quotKerEquivOfSurjective hπsurj).symm ⟨x.1, Submodule.mem_sup_left x.2⟩ =
      (LinearMap.ker π).mkQ (x, 0) :=
    (π.quotKerEquivOfSurjective hπsurj).injective (by ext; simp [π])
  simp [β, β₀, hsymm]

/-- Finite Baer extension over `O ⧸ (ϖ ^ m)`: on any finite `O`-module `Q` annihilated by `ϖ ^ m`,
every `O`-linear functional on a submodule `N ≤ Q` extends to `Q`. -/
private theorem exists_linearMap_extend_quotient_span_pow [Finite Q] {ϖ : O} (hϖ : Irreducible ϖ)
    {m : ℕ} (hann : ∀ q : Q, ϖ ^ m • q = 0) (N : Submodule O Q)
    (α : N →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m})) :
    ∃ β : Q →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m}), ∀ x : N, β x.1 = α x := by
  classical
  let _ := Fintype.ofFinite Q
  suffices ∀ k : ℕ, ∀ (N : Submodule O Q) (α : N →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m})),
      Fintype.card Q - Fintype.card N = k →
      ∃ β : Q →ₗ[O] (O ⧸ Ideal.span {ϖ ^ m}), ∀ x : N, β x.1 = α x from
    this (Fintype.card Q - Fintype.card N) N α rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro N α hk
    by_cases htop : N = ⊤
    · subst htop
      exact ⟨α.comp Submodule.topEquiv.symm.toLinearMap, fun x ↦ congrArg α (by ext; rfl)⟩
    · obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ N := by
        by_contra! h
        exact htop (top_unique fun z _ ↦ h z)
      obtain ⟨α', hα'⟩ := exists_linearMap_sup_span_singleton hϖ hann y α
      let N' : Submodule O Q := N ⊔ Submodule.span O {y}
      let ι : N → N' := fun x ↦ ⟨x.1, Submodule.mem_sup_left x.2⟩
      have hι_inj : Function.Injective ι := fun a b hab ↦
        Subtype.ext (by simpa [ι] using congrArg Subtype.val hab)
      have hι_not_surj : ¬ Function.Surjective ι := fun hsurj ↦ by
        obtain ⟨x, hx⟩ := hsurj ⟨y, Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)⟩
        have hxy : x.1 = y := congrArg Subtype.val hx
        exact hy (hxy ▸ x.2)
      have hcard_lt : Fintype.card N < Fintype.card N' :=
        Fintype.card_lt_of_injective_not_surjective ι hι_inj hι_not_surj
      have hcard_le : Fintype.card N' ≤ Fintype.card Q := Fintype.card_subtype_le _
      obtain ⟨β, hβ⟩ := ih (Fintype.card Q - Fintype.card N') (by omega) N' α' rfl
      exact ⟨β, fun x ↦ (hβ (ι x)).trans (hα' x)⟩

end BaerExtension

section QuotientMul

variable {O : Type*} [CommRing O]

/-- Multiplication by `ϖ` gives an `O`-linear map `O ⧸ (ϖ ^ n) →ₗ[O] O ⧸ (ϖ ^ (n + 1))`. -/
private noncomputable def mulIrreducibleQuotientLinearMap (ϖ : O) (n : ℕ) :
    (O ⧸ Ideal.span {ϖ ^ n}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
  (Ideal.span {ϖ ^ n}).liftQ
    ((Ideal.span {ϖ ^ (n + 1)}).mkQ.comp (LinearMap.lsmul O O ϖ)) fun r hr ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hr
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.lsmul_apply, smul_eq_mul,
        Ideal.mem_span_singleton]
      exact ⟨c, by ring⟩

private theorem mulIrreducibleQuotientLinearMap_injective [IsDomain O] {ϖ : O}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    Function.Injective (mulIrreducibleQuotientLinearMap ϖ n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hmem : ϖ * r ∈ Ideal.span {ϖ ^ (n + 1)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hq)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hr : r = ϖ ^ n * c := mul_left_cancel₀ hϖ.ne_zero (by linear_combination hc)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨c, hr⟩)

private theorem smul_eq_mulIrreducibleQuotientLinearMap_factor (ϖ : O) (n : ℕ)
    (z : O ⧸ Ideal.span {ϖ ^ (n + 1)}) :
    ϖ • z = mulIrreducibleQuotientLinearMap ϖ n
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr ⟨ϖ, by ring⟩) z) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

end QuotientMul

section Lifting

section Domain

variable {O M : Type*} [CommRing O] [IsDomain O]
  [TopologicalSpace O] [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- For an open submodule `U` of a profinite flat `O`-module `M`, multiplication by a nonzero
nonunit `ϖ` is a homeomorphism `M ≃ₜ ϖ • ⊤`, so `(ϖ • ⊤) ∩ W₀ ⊆ ϖ • U` for some open `W₀`. -/
private theorem exists_isOpen_inter_smul_subset [CompactSpace O] (hM : IsProfiniteFlat O M) {ϖ : O}
    (hϖ : Irreducible ϖ) {U : Submodule O M} (hU : IsOpen (U : Set M)) :
    ∃ W₀ : Submodule O M, IsOpen (W₀ : Set M) ∧
      ((ϖ • (⊤ : Submodule O M) : Submodule O M) : Set M) ∩ (W₀ : Set M) ⊆
        ((ϖ • U : Submodule O M) : Set M) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  have := hM.isLinearTopology
  let S : Submodule O M := ϖ • ⊤
  let s : M ≃ S := Equiv.ofBijective
    (fun m ↦ ⟨ϖ • m, Submodule.smul_mem_pointwise_smul m ϖ ⊤ trivial⟩)
    ⟨fun x y hxy ↦ hM.isSMulRegular_of_ne_zero hϖ.ne_zero (congrArg Subtype.val hxy),
      fun ⟨z, hz⟩ ↦ by
        obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z ϖ ⊤).mp hz
        exact ⟨m, rfl⟩⟩
  let shomeo : M ≃ₜ S := Continuous.homeoOfEquivCompactToT2 (f := s)
    ((continuous_const_smul ϖ).subtype_mk _)
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp (shomeo.isOpenMap _ hU)
  have hs0 : shomeo 0 = 0 := Subtype.ext (smul_zero ϖ)
  have h0V : (0 : M) ∈ V := by
    have : (0 : S) ∈ Subtype.val ⁻¹' V := hVeq ▸ ⟨0, U.zero_mem, hs0⟩
    exact this
  obtain ⟨W₀, hW₀open, hW₀V⟩ := (IsLinearTopology.hasBasis_open_submodule O (M := M)).mem_iff.mp
    (hVopen.mem_nhds h0V)
  refine ⟨W₀, hW₀open, ?_⟩
  rintro z ⟨hzS, hzW₀⟩
  have hzPre : (⟨z, hzS⟩ : S) ∈ Subtype.val ⁻¹' V := hW₀V hzW₀
  rw [hVeq] at hzPre
  obtain ⟨u, huU, huz⟩ := hzPre
  have hzu : ϖ • u = z := congrArg Subtype.val huz
  exact hzu ▸ Submodule.smul_mem_pointwise_smul u ϖ U huU

/-- Torsion-kernel lemma for the lifting step: if `(ϖ • ⊤) ∩ W₀ ⊆ ϖ • U` and
`ϖ ^ n • ⊤ ≤ U`, any `x` with `ϖ • x ∈ (W₀ ⊓ U) ⊔ (ϖ ^ (n + 1) • ⊤)` already lies in `U`. -/
private theorem mem_of_smul_mem_sup_inf (hM : IsProfiniteFlat O M) {ϖ : O} (hϖ : Irreducible ϖ)
    {n : ℕ} {U W₀ : Submodule O M} (hpowU : ϖ ^ n • (⊤ : Submodule O M) ≤ U)
    (hSW₀ : ((ϖ • (⊤ : Submodule O M) : Submodule O M) : Set M) ∩ (W₀ : Set M) ⊆
      ((ϖ • U : Submodule O M) : Set M))
    {x : M} (hxK : ϖ • x ∈ (W₀ ⊓ U) ⊔ (ϖ ^ (n + 1) • (⊤ : Submodule O M))) : x ∈ U := by
  obtain ⟨w, hw, t, ht, hwtx⟩ := Submodule.mem_sup.mp hxK
  obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists t (ϖ ^ (n + 1)) ⊤).mp ht
  have hw_eq : w = ϖ • (x - ϖ ^ n • z) := by
    rw [smul_sub, ← mul_smul, ← pow_succ']
    exact eq_sub_of_add_eq hwtx
  have hw_mem : w ∈ ((ϖ • (⊤ : Submodule O M) : Submodule O M) : Set M) ∩ (W₀ : Set M) :=
    ⟨hw_eq ▸ Submodule.smul_mem_pointwise_smul _ ϖ ⊤ trivial, hw.1⟩
  obtain ⟨u, huU, hwu⟩ := (Submodule.mem_smul_pointwise_iff_exists w ϖ U).mp (hSW₀ hw_mem)
  have hxu : x - ϖ ^ n • z = u :=
    hM.isSMulRegular_of_ne_zero hϖ.ne_zero (hw_eq.symm.trans hwu.symm)
  rw [eq_add_of_sub_eq hxu]
  exact U.add_mem huU (hpowU (Submodule.smul_mem_pointwise_smul z (ϖ ^ n) ⊤ trivial))

end Domain

section DVRStep

variable {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [CompactSpace O] [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- Inductive step of functional lifting: a continuous `O`-linear functional
`M →ₗ[O] O ⧸ (ϖ ^ n)` lifts to a continuous `O`-linear functional `M →ₗ[O] O ⧸ (ϖ ^ (n + 1))`. -/
private theorem exists_continuous_lift_step (hM : IsProfiniteFlat O M) {ϖ : O}
    (hϖ : Irreducible ϖ) {n : ℕ} (f : M →ₗ[O] (O ⧸ Ideal.span {ϖ ^ n}))
    (hf : IsOpen ((LinearMap.ker f : Submodule O M) : Set M)) :
    ∃ f' : M →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}),
      IsOpen ((LinearMap.ker f' : Submodule O M) : Set M) ∧
        ∀ x : M, Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr ⟨ϖ, by ring⟩) (f' x) = f x := by
  have := hM.isTopologicalAddGroup
  set U : Submodule O M := LinearMap.ker f
  have hpowU : ϖ ^ n • (⊤ : Submodule O M) ≤ U := fun _ hx ↦ by
    obtain ⟨x, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [LinearMap.mem_ker, LinearMap.map_smul]
    change Ideal.Quotient.mk (Ideal.span {ϖ ^ n}) (ϖ ^ n) * f x = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_mul]
  obtain ⟨W₀, hW₀, hSW₀⟩ := exists_isOpen_inter_smul_subset hM hϖ hf
  let K : Submodule O M := (W₀ ⊓ U) ⊔ (ϖ ^ (n + 1) • (⊤ : Submodule O M))
  have hKopen : IsOpen (K : Set M) := Submodule.isOpen_mono le_sup_left (hW₀.inter hf)
  have hKU : K ≤ U := sup_le inf_le_right fun _ hx ↦ by
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [pow_succ, mul_smul]
    exact hpowU (Submodule.smul_mem_pointwise_smul (ϖ • m) (ϖ ^ n) ⊤ trivial)
  let Q := M ⧸ K
  have : Finite Q := hM.finite_quotient_of_isOpen K hKopen
  have hannQ (q : Q) : ϖ ^ (n + 1) • q = 0 := by
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul x (ϖ ^ (n + 1)) ⊤ trivial)
  let μ : Q →ₗ[O] ↥(ϖ • (⊤ : Submodule O Q)) :=
    (LinearMap.lsmul O Q ϖ).codRestrict (ϖ • ⊤) fun q ↦
      Submodule.smul_mem_pointwise_smul q ϖ ⊤ trivial
  have hμsurj : Function.Surjective μ := fun ⟨z, hz⟩ ↦ by
    obtain ⟨q, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z ϖ ⊤).mp hz
    exact ⟨q, rfl⟩
  let g₀ : Q →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
    (mulIrreducibleQuotientLinearMap ϖ n).comp (K.liftQ f hKU)
  have hkerμ : LinearMap.ker μ ≤ LinearMap.ker g₀ := fun q hq ↦ by
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    have hxK : ϖ • x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp
      ((K.mkQ.map_smul ϖ x).trans (congrArg Subtype.val (LinearMap.mem_ker.mp hq)))
    have hxU := mem_of_smul_mem_sup_inf hM hϖ hpowU hSW₀ hxK
    rw [LinearMap.mem_ker]
    change mulIrreducibleQuotientLinearMap ϖ n (f x) = 0
    rw [LinearMap.mem_ker.mp hxU, map_zero]
  let α₀ : ↥(ϖ • (⊤ : Submodule O Q)) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
    ((LinearMap.ker μ).liftQ g₀ hkerμ).comp (μ.quotKerEquivOfSurjective hμsurj).symm.toLinearMap
  obtain ⟨h, hh⟩ := exists_linearMap_extend_quotient_span_pow hϖ hannQ _ α₀
  refine ⟨h.comp K.mkQ, Submodule.isOpen_mono (fun m hm ↦ ?_) hKopen, fun x ↦ ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero K).mpr hm, map_zero]
  · apply mulIrreducibleQuotientLinearMap_injective hϖ n
    rw [← smul_eq_mulIrreducibleQuotientLinearMap_factor, ← LinearMap.map_smul]
    calc h (ϖ • K.mkQ x) = α₀ (μ (K.mkQ x)) := hh (μ (K.mkQ x))
      _ = g₀ (K.mkQ x) := by simp [α₀]
      _ = mulIrreducibleQuotientLinearMap ϖ n (f x) := rfl

end DVRStep

section CompactDVRLift

variable {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- Unique `𝔪`-adic assembly of a compatible sequence of residues in `O ⧸ (ϖ ^ (k + 1))`. -/
private theorem existsUnique_lift_tower {ϖ : O} (hϖ : Irreducible ϖ)
    (u : ∀ k : ℕ, O ⧸ Ideal.span {ϖ ^ (k + 1)})
    (hu : ∀ k : ℕ, Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr ⟨ϖ, by ring⟩) (u (k + 1)) = u k) :
    ∃! y : O, ∀ k : ℕ, Ideal.Quotient.mk (Ideal.span {ϖ ^ (k + 1)}) y = u k := by
  have hmax_pow (k : ℕ) : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hu_le {i j : ℕ} (hij : i ≤ j) :
      Ideal.Quotient.factor
        (by rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
            exact Ideal.pow_le_pow_right (Nat.succ_le_succ hij))
        (u j) = u i := by
    induction j, hij using Nat.le_induction with
    | base =>
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (u i)
      rw [← hr]; rfl
    | succ j hij ih =>
      rw [← ih, ← hu j]
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (u (j + 1))
      rw [← hr]; rfl
  choose c₀ hc₀ using fun k : ℕ ↦ Ideal.Quotient.mk_surjective (u k)
  let c : ℕ → O := fun n ↦ match n with | 0 => 0 | k + 1 => c₀ k
  have hcauchy {i j : ℕ} (hij : i ≤ j) :
      c i ≡ c j [SMOD (IsLocalRing.maximalIdeal O ^ i • (⊤ : Ideal O))] := by
    rcases i with _ | i
    · simp [SModEq.sub_mem]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rw [Ideal.smul_eq_mul, Ideal.mul_top, hmax_pow (i + 1), SModEq.sub_mem, ← Ideal.Quotient.eq]
      have := hu_le (Nat.succ_le_succ_iff.mp hij)
      change Ideal.Quotient.mk _ (c₀ i) = Ideal.Quotient.mk _ (c₀ j)
      rw [← hc₀ j, Ideal.Quotient.factor_mk, ← hc₀ i] at this
      exact this.symm
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal O) inferInstance hcauchy
  have hyk (k : ℕ) : Ideal.Quotient.mk (Ideal.span {ϖ ^ (k + 1)}) y = u k := by
    have hsub := SModEq.sub_mem.mp (hy (k + 1))
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hmax_pow (k + 1), ← Ideal.Quotient.eq] at hsub
    exact hsub.symm.trans (hc₀ k)
  refine ⟨y, hyk, fun y' hy' ↦ sub_eq_zero.mp ?_⟩
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance (y' - y) fun k ↦ ?_
  rcases k with _ | k
  · simp [SModEq.zero]
  · rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, hmax_pow (k + 1),
      ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hy' k, hyk k, sub_self]

/-- Continuity into `O` of a linear map whose reductions modulo `ϖ ^ (k + 1)` have open kernels. -/
private theorem continuous_of_forall_quotient_eq [IsTopologicalAddGroup M] {ϖ : O}
    (hϖ : Irreducible ϖ) (φ_lin : M →ₗ[O] O)
    (tower : ∀ k : ℕ, {f : M →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (k + 1)}) //
      IsOpen ((LinearMap.ker f : Submodule O M) : Set M)})
    (htower : ∀ x k, Ideal.Quotient.mk (Ideal.span {ϖ ^ (k + 1)}) (φ_lin x) = (tower k).1 x) :
    Continuous φ_lin := by
  have hAdic : IsAdic (IsLocalRing.maximalIdeal O) := IsLocalRing.isAdic_maximalIdeal O
  refine continuous_of_continuousAt_zero φ_lin.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  rintro (_ | k) -
  · simp [pow_zero]
  · refine Filter.mem_of_superset ((tower k).2.mem_nhds (LinearMap.ker _).zero_mem) fun x hx ↦ ?_
    change φ_lin x ∈ IsLocalRing.maximalIdeal O ^ (k + 1)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← Ideal.Quotient.eq_zero_iff_mem,
      htower x k, LinearMap.mem_ker.mp hx]

/-- **Continuous linear lifting along `O → O ⧸ 𝔪`.** Over a compact Hausdorff discrete valuation
ring `(O, 𝔪)`, every continuous `O`-linear functional `M →L[O] (O ⧸ 𝔪)` on a profinite flat
`O`-module lifts to a continuous `O`-linear functional `M →L[O] O`. -/
theorem IsProfiniteFlat.exists_continuousLinearMap_lift_mkQ (hM : IsProfiniteFlat O M)
    (φ₀ : M →L[O] (O ⧸ IsLocalRing.maximalIdeal O)) :
    ∃ φ : M →L[O] O, ∀ m : M,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (φ m) = φ₀ m := by
  classical
  have := hM.isTopologicalAddGroup
  have := (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let e₁ : (O ⧸ IsLocalRing.maximalIdeal O) ≃ₗ[O] (O ⧸ Ideal.span {ϖ ^ 1}) :=
    Submodule.quotEquivOfEq _ _ (by rw [pow_one, hϖ.maximalIdeal_eq])
  let step0 : {f : M →ₗ[O] (O ⧸ Ideal.span {ϖ ^ 1}) //
      IsOpen ((LinearMap.ker f : Submodule O M) : Set M)} :=
    ⟨e₁.toLinearMap.comp φ₀.toLinearMap, by
      have heq : ((LinearMap.ker (e₁.toLinearMap.comp φ₀.toLinearMap) : Submodule O M) : Set M) =
          φ₀ ⁻¹' {(0 : O ⧸ IsLocalRing.maximalIdeal O)} := by
        ext x; simp [LinearMap.mem_ker]
      exact heq ▸ (isOpen_discrete _).preimage φ₀.continuous⟩
  let tower : ∀ k : ℕ, {f : M →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (k + 1)}) //
      IsOpen ((LinearMap.ker f : Submodule O M) : Set M)} :=
    Nat.rec step0 fun k prev ↦
      ⟨Classical.choose (exists_continuous_lift_step hM hϖ prev.1 prev.2),
        (Classical.choose_spec (exists_continuous_lift_step hM hϖ prev.1 prev.2)).1⟩
  have hexists (x : M) := existsUnique_lift_tower hϖ (fun k ↦ (tower k).1 x) fun k ↦
    (Classical.choose_spec (exists_continuous_lift_step hM hϖ (tower k).1 (tower k).2)).2 x
  let φ_lin : M →ₗ[O] O :=
    { toFun := fun x ↦ Classical.choose (hexists x)
      map_add' := fun x y ↦ (hexists (x + y)).unique
        (Classical.choose_spec (hexists (x + y))).1 fun k ↦ by
          rw [map_add, (Classical.choose_spec (hexists x)).1 k,
            (Classical.choose_spec (hexists y)).1 k, ← map_add]
      map_smul' := fun r x ↦ (hexists (r • x)).unique
        (Classical.choose_spec (hexists (r • x))).1 fun k ↦ by
          rw [RingHom.id_apply, smul_eq_mul, map_mul,
            (Classical.choose_spec (hexists x)).1 k, LinearMap.map_smul]
          rfl }
  exact ⟨⟨φ_lin, continuous_of_forall_quotient_eq hϖ φ_lin tower
      fun x k ↦ (Classical.choose_spec (hexists x)).1 k⟩,
    fun m ↦ e₁.injective ((Classical.choose_spec (hexists m)).1 0)⟩

end CompactDVRLift

end Lifting

end TauCeti.Huber

end

section PrivateResidueEquiv

open Filter Topology Pointwise

namespace TauCeti.Huber

universe u v

/-- Reduction modulo `𝔪 • ⊤` of a profinite flat `O`-module is continuously `(O ⧸ 𝔪)`-linearly
isomorphic to a product `I → (O ⧸ 𝔪)` with `I : Type v`. -/
private theorem exists_continuousLinearEquiv_quotient_maximalIdeal_smul
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    (hM : IsProfiniteFlat O M) :
    letI : Field (O ⧸ IsLocalRing.maximalIdeal O) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
    ∃ I : Type v, Nonempty
      ((M ⧸ (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M))) ≃L[O ⧸ IsLocalRing.maximalIdeal O]
        (I → O ⧸ IsLocalRing.maximalIdeal O)) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  let _ : Field (O ⧸ IsLocalRing.maximalIdeal O) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
  have : DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O) :=
    (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
  have hPclosed : IsClosed
      (((IsLocalRing.maximalIdeal O • (⊤ : Submodule O M) : Submodule O M) : Set M)) :=
    (Submodule.isCompact_smul_of_fg (IsNoetherian.noetherian _)
      (by simpa using isCompact_univ)).isClosed
  have hVcomp := hM.isCompactModule.quotient
    (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)) hPclosed
  have := hVcomp.isTopologicalAddGroup
  have := hVcomp.compactSpace
  have := hVcomp.t2Space
  have := hVcomp.isLinearTopology
  have : IsLinearTopology (O ⧸ IsLocalRing.maximalIdeal O)
      (M ⧸ (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M))) :=
    IsLinearTopology.mk_of_hasBasis' (O ⧸ IsLocalRing.maximalIdeal O)
      (IsLinearTopology.hasBasis_submodule O) fun U c _ hv ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact U.smul_mem r hv
  exact TauCeti.IsLinearTopology.exists_continuousLinearEquiv_pi
    (O ⧸ IsLocalRing.maximalIdeal O) (M ⧸ (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)))

/-- Topological Nakayama upgrade: if `Ψ = ContinuousLinearMap.pi φ : M →L[O] (I → O)` lifts the
coordinates of an `(O ⧸ 𝔪)`-linear equivalence `e₀ : M ⧸ (𝔪 • ⊤) ≃L[O ⧸ 𝔪] (I → O ⧸ 𝔪)`, then
`Ψ` is bijective. -/
private theorem bijective_pi_of_quotient_equiv
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    (hM : IsProfiniteFlat O M) {I : Type v}
    (e₀ : letI : Field (O ⧸ IsLocalRing.maximalIdeal O) :=
        Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
      (M ⧸ (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M))) ≃L[O ⧸ IsLocalRing.maximalIdeal O]
        (I → O ⧸ IsLocalRing.maximalIdeal O))
    (φ : I → M →L[O] O)
    (hφ : ∀ i m, Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (φ i m) =
      e₀ ((IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)).mkQ m) i) :
    Function.Bijective (ContinuousLinearMap.pi φ) := by
  have := hM.isTopologicalAddGroup
  have := hM.continuousSMul
  have := hM.compactSpace
  have := hM.t2Space
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have h𝔪_nil : ∀ a ∈ IsLocalRing.maximalIdeal O, IsTopologicallyNilpotent a :=
    fun _ ha ↦ (IsLocalRing.isAdic_maximalIdeal O).isTopologicallyNilpotent_of_mem ha
  let Ψ : M →L[O] (I → O) := ContinuousLinearMap.pi φ
  refine ⟨?_, ?_⟩
  · change Function.Injective Ψ.toLinearMap
    rw [← LinearMap.ker_eq_bot]
    have hK'closed : IsClosed ((LinearMap.ker Ψ.toLinearMap : Submodule O M) : Set M) :=
      isClosed_singleton.preimage Ψ.continuous
    refine Submodule.eq_bot_of_le_smul_of_isCompact (IsNoetherian.noetherian _) h𝔪_nil
      hK'closed.isCompact fun x hx ↦ ?_
    have hφx (i : I) : φ i x = 0 := congrFun (LinearMap.mem_ker.mp hx) i
    have hx0 : e₀ ((IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)).mkQ x) = 0 := by
      ext i; simpa [hφx i] using (hφ i x).symm
    have hxP : x ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O M) :=
      (Submodule.Quotient.mk_eq_zero _).mp (e₀.injective (hx0.trans e₀.map_zero.symm))
    rw [h𝔪, Submodule.ideal_span_singleton_smul] at hxP ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x ϖ ⊤).mp hxP
    refine Submodule.smul_mem_pointwise_smul y ϖ _ (LinearMap.mem_ker.mpr ?_)
    ext i
    have hϖΨ : ϖ * Ψ y i = 0 := by simpa [Ψ.map_smul] using congrFun (LinearMap.mem_ker.mp hx) i
    exact (mul_eq_zero.mp hϖΨ).resolve_left hϖ.ne_zero
  · refine LinearMap.surjective_of_surjective_comp_mkQ_of_compactSpace
      (IsNoetherian.noetherian _) h𝔪_nil Ψ.toLinearMap Ψ.continuous fun q ↦ ?_
    obtain ⟨g, rfl⟩ := (IsLocalRing.maximalIdeal O • (⊤ : Submodule O (I → O))).mkQ_surjective q
    obtain ⟨v, hv⟩ := e₀.surjective fun i ↦ Ideal.Quotient.mk _ (g i)
    obtain ⟨m, rfl⟩ := (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)).mkQ_surjective v
    refine ⟨m, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      h𝔪, ← pow_one (Ideal.span {ϖ}), TauCeti.mem_span_singleton_pow_smul_top_iff]
    intro i
    rw [Pi.sub_apply, pow_one, ← Ideal.mem_span_singleton, ← h𝔪, ← Ideal.Quotient.eq]
    exact (hφ i m).trans (congrFun hv i)

end TauCeti.Huber

end PrivateResidueEquiv

public section

open Filter Topology Pointwise

namespace TauCeti.Huber

section Pseudobasis

universe u v w

section LocalRing

variable {O : Type u} [CommRing O] [IsLocalRing O] [TopologicalSpace O]
  {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- Given a pseudobasis `e : M ≃L[O] (I → O)`, `pseudobasisSubmodule e J n` is the submodule of
elements whose `J`-coordinates lie in `𝔪 ^ n` (`∏_{i ∈ J} 𝔪^n × ∏_{i ∉ J} O` transported along
`e`). -/
def pseudobasisSubmodule {I : Type w} (e : M ≃L[O] (I → O)) (J : Finset I) (n : ℕ) :
    Submodule O M where
  carrier := {m : M | ∀ i ∈ J, e m i ∈ IsLocalRing.maximalIdeal O ^ n}
  add_mem' ha hb i hi := by
    rw [map_add, Pi.add_apply]
    exact (IsLocalRing.maximalIdeal O ^ n).add_mem (ha i hi) (hb i hi)
  zero_mem' i _ := by
    rw [map_zero, Pi.zero_apply]
    exact (IsLocalRing.maximalIdeal O ^ n).zero_mem
  smul_mem' r _ hx i hi := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    exact (IsLocalRing.maximalIdeal O ^ n).mul_mem_left r (hx i hi)

@[simp]
theorem mem_pseudobasisSubmodule {I : Type w} (e : M ≃L[O] (I → O)) (J : Finset I) (n : ℕ)
    (m : M) :
    m ∈ pseudobasisSubmodule e J n ↔ ∀ i ∈ J, e m i ∈ IsLocalRing.maximalIdeal O ^ n :=
  Iff.rfl

section CompactLocal

variable [CompactSpace O]

/-- A profinite flat module over a compact local ring `O` is finitely generated if and only if it
admits a finite pseudobasis `Fin n → O`. -/
theorem IsProfiniteFlat.module_finite_iff_exists_fin_pseudobasis (hM : IsProfiniteFlat O M) :
    Module.Finite O M ↔ ∃ n : ℕ, Nonempty (M ≃L[O] (Fin n → O)) where
  mpr := fun ⟨_, ⟨e⟩⟩ ↦ Module.Finite.equiv e.symm.toLinearEquiv
  mp hfin := by
    classical
    have := hM.flat
    have := hM.isTopologicalAddGroup
    have := hM.continuousSMul
    have := hM.compactSpace
    have := hM.t2Space
    have : Module.Free O M := Module.free_of_flat_of_isLocalRing
    let ι := Module.Free.ChooseBasisIndex O M
    let b : Module.Basis ι O M := Module.Free.chooseBasis O M
    let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype O M
    let b' : Module.Basis (Fin (Fintype.card ι)) O M := b.reindex (Fintype.equivFin ι)
    let φ_inv : (Fin (Fintype.card ι) → O) ≃ₗ[O] M := b'.equivFun.symm
    have hcont_inv : Continuous φ_inv := by
      have hfun : (φ_inv : (Fin (Fintype.card ι) → O) → M) =
          fun g ↦ ∑ i : Fin (Fintype.card ι), g i • b' i := by
        ext g
        exact b'.equivFun_symm_apply g
      rw [hfun]
      exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
    let hhomeo : (Fin (Fintype.card ι) → O) ≃ₜ M :=
      Continuous.homeoOfEquivCompactToT2 (f := φ_inv.toEquiv) hcont_inv
    exact ⟨Fintype.card ι, ⟨{ φ_inv.symm with
      continuous_toFun := hhomeo.symm.continuous
      continuous_invFun := hhomeo.continuous }⟩⟩

variable [IsNoetherianRing O] [IsTopologicalRing O] [T2Space O]

/-- Over a compact Hausdorff Noetherian local ring `O`, each `pseudobasisSubmodule e J n` is open
in `M`. -/
theorem isOpen_pseudobasisSubmodule {I : Type w} (e : M ≃L[O] (I → O)) (J : Finset I) (n : ℕ) :
    IsOpen ((pseudobasisSubmodule e J n : Submodule O M) : Set M) := by
  have heq : ((pseudobasisSubmodule e J n : Submodule O M) : Set M) =
      ⋂ i ∈ J, (fun m : M ↦ e m i) ⁻¹'
        ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    ext m
    simp [mem_pseudobasisSubmodule]
  rw [heq]
  exact J.finite_toSet.isOpen_biInter fun i _ ↦
    (IsLocalRing.isOpen_maximalIdeal_pow O n).preimage ((continuous_apply i).comp e.continuous)

/-- Over a compact Hausdorff Noetherian local ring `O`, for any pseudobasis `e : M ≃L[O] (I → O)`,
the submodules `pseudobasisSubmodule e J n` with `J : Finset I` and `1 ≤ n` form a basis of
neighbourhoods of `0` in `M`. -/
theorem hasBasis_nhds_zero_pseudobasisSubmodule {I : Type w} (e : M ≃L[O] (I → O)) :
    (𝓝 (0 : M)).HasBasis (fun p : Finset I × ℕ ↦ 1 ≤ p.2)
      (fun p ↦ ((pseudobasisSubmodule e p.1 p.2 : Submodule O M) : Set M)) := by
  classical
  have hAdic : IsAdic (IsLocalRing.maximalIdeal O) := IsLocalRing.isAdic_maximalIdeal O
  rw [Filter.hasBasis_iff]
  intro U
  refine ⟨fun hU ↦ ?_, ?_⟩
  · have himg : e.symm ⁻¹' U ∈ 𝓝 (0 : I → O) :=
      e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi] at himg
    obtain ⟨S, hSfin, t, ht, hSt⟩ := himg
    choose k hk using fun i : I ↦ (hAdic.hasBasis_nhds_zero.mem_iff).mp (ht i)
    let J : Finset I := hSfin.toFinset
    let n : ℕ := max 1 (J.sup k)
    refine ⟨(J, n), le_max_left 1 _, fun m hm ↦ ?_⟩
    have hm_pi : e m ∈ (S : Set I).pi t := by
      intro i hiS
      have hiJ : i ∈ J := hSfin.mem_toFinset.mpr hiS
      have hkn : k i ≤ n := le_trans (Finset.le_sup hiJ) (le_max_right 1 _)
      exact (hk i).2 (Ideal.pow_le_pow_right hkn (hm i hiJ))
    simpa using hSt hm_pi
  · rintro ⟨⟨J, n⟩, _, hJU⟩
    exact Filter.mem_of_superset
      ((isOpen_pseudobasisSubmodule e J n).mem_nhds (pseudobasisSubmodule e J n).zero_mem) hJU

end CompactLocal

end LocalRing

section CompactDVR

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  {M : Type v} [AddCommGroup M] [Module O M] [TopologicalSpace M]

/-- **Structure theorem for profinite flat modules (Chojecki–Hansen–Johansson, Proposition 6.2).**
Over a discrete valuation ring `O` carrying a compact Hausdorff ring topology, a topological
`O`-module `M : Type v` is profinite flat if and only if it is continuously `O`-linearly equivalent
to `I → O` (with the product topology) for some index type `I : Type v`. -/
theorem IsProfiniteFlat.iff_exists_pseudobasis :
    IsProfiniteFlat O M ↔ ∃ I : Type v, Nonempty (M ≃L[O] (I → O)) where
  mpr := fun ⟨I, ⟨e⟩⟩ ↦ (IsProfiniteFlat.pi_self (O := O) I).of_continuousLinearEquiv e.symm
  mp hM := by
    classical
    have := hM.isTopologicalAddGroup
    have := hM.continuousSMul
    have := hM.compactSpace
    have := hM.t2Space
    let _ : Field (O ⧸ IsLocalRing.maximalIdeal O) :=
      Ideal.Quotient.field (IsLocalRing.maximalIdeal O)
    have : DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O) :=
      (IsLocalRing.isAdic_maximalIdeal O).discreteTopology_quotient
    obtain ⟨I, ⟨e₀⟩⟩ := exists_continuousLinearEquiv_quotient_maximalIdeal_smul hM
    let mkM := (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)).mkQ
    let coord₀ (i : I) : M →L[O] (O ⧸ IsLocalRing.maximalIdeal O) :=
      { toFun := fun m ↦ e₀ (mkM m) i
        map_add' := fun x y ↦ by simp [map_add]
        map_smul' := fun r x ↦ by
          have hsmul : mkM (r • x) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) r • mkM x := rfl
          rw [hsmul, e₀.map_smul]; rfl
        cont := (continuous_apply i).comp (e₀.continuous.comp
          (IsLocalRing.maximalIdeal O • (⊤ : Submodule O M)).continuous_mkQ) }
    choose φ hφ using fun i : I ↦ hM.exists_continuousLinearMap_lift_mkQ (coord₀ i)
    let Ψ : M →L[O] (I → O) := ContinuousLinearMap.pi φ
    let e_lin : M ≃ₗ[O] (I → O) :=
      LinearEquiv.ofBijective Ψ.toLinearMap (bijective_pi_of_quotient_equiv hM e₀ φ hφ)
    let hhomeo : M ≃ₜ (I → O) :=
      Continuous.homeoOfEquivCompactToT2 (f := e_lin.toEquiv) Ψ.continuous
    exact ⟨I, ⟨{ e_lin with
      continuous_toFun := hhomeo.continuous
      continuous_invFun := hhomeo.symm.continuous }⟩⟩

end CompactDVR

end Pseudobasis

end TauCeti.Huber
